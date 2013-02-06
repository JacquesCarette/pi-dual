{-# LANGUAGE TypeOperators, GADTs, TypeSynonymInstances #-}

module Pio where

import Data.List

-----------------------------------------------------------------------
-- Isomorphisms 

type Nat = Int

data Zero 

class Eq a => B a where
  elems :: [a]

instance Eq Zero where
  _ == _ = undefined
  
instance B Zero where
  elems = []
  
instance B () where  
  elems = [()]
  
instance (B a, B b) => B (Either a b) where
  elems = map Left elems ++ map Right elems
  
instance B Bool where
  elems = [False, True]

instance B Nat where
  elems = [0..]

instance (B a, B b) => B (a,b) where
  elems = [(a,b) | a <- elems, b <- elems]

data a :<=> b where 
-- Congruence
  Id    :: B a => a :<=> a
  Sym   :: (B a, B b) => (a :<=> b) -> (b :<=> a) 
  (:.:) :: (B a, B b, B c) => (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (B a, B b, B c, B d) => (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (B a, B b, B c, B d) => (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- (+) is associative, commutative, and has a unit
  ZeroE   :: B a => Either Zero a :<=> a
  ZeroI   :: B a => a :<=> Either Zero a
  SwapP :: (B a, B b) => Either a b :<=> Either b a
  AssocLP  :: (B a, B b, B c) => Either a (Either b c) :<=> Either (Either a b) c 
  AssocRP  :: (B a, B b, B c) => Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE    :: B a => ((), a) :<=> a
  UnitI    :: B a => a :<=> ((), a)
  SwapT :: (B a, B b) => (a,b) :<=> (b,a) 
  AssocLT  :: (B a, B b, B c) => (a,(b,c)) :<=> ((a,b),c)
  AssocRT  :: (B a, B b, B c) => ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  DistribZ  :: B a => (Zero, a) :<=> Zero
  FactorZ  :: B a => Zero :<=> (Zero, a)
  Distrib  :: (B a, B b, B c) => (Either b c, a) :<=> Either (b, a) (c, a)
  Factor      :: (B a, B b, B c) => Either (b, a) (c, a) :<=> (Either b c, a)
-- Encoding of booleans
  FoldB   :: Either () () :<=> Bool
  UnfoldB :: Bool :<=> Either () ()
-- Encoding of natural numbers
  FoldN   :: Either () Nat :<=> Nat
  UnfoldN :: Nat :<=> Either () Nat
-- Trace operators for looping/recursion
  TraceP :: (B a, B b1, B b2) => (Either a b1 :<=> Either a b2) -> (b1 :<=> b2)
  TraceT :: (B a, B b1, B b2) => ((a, b1) :<=> (a, b2)) -> (b1 :<=> b2)

-- Adjoint

adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint (Sym f) = f 
adjoint (f :.: g) = adjoint g :.: adjoint f
adjoint (f :*: g) = adjoint f :*: adjoint g
adjoint (f :+: g) = adjoint f :+: adjoint g
adjoint ZeroE = ZeroI
adjoint ZeroI = ZeroE
adjoint SwapP = SwapP
adjoint AssocLP = AssocRP
adjoint AssocRP = AssocLP
adjoint UnitE = UnitI
adjoint UnitI = UnitE
adjoint SwapT = SwapT
adjoint AssocLT = AssocRT
adjoint AssocRT = AssocLT
adjoint DistribZ = FactorZ
adjoint FactorZ = DistribZ
adjoint Distrib = Factor
adjoint Factor = Distrib
adjoint FoldB = UnfoldB
adjoint UnfoldB = FoldB
adjoint FoldN = UnfoldN
adjoint UnfoldN = FoldN
adjoint (TraceP c) = TraceP (adjoint c)
adjoint (TraceT c) = TraceT (adjoint c)

-- Semantics
eval :: (a :<=> b) -> a -> [b]
eval Id a = return a
eval (Sym f) b = evalR f b
eval (f :.: g) a = do v <- eval f a
                      eval g v
eval (f :*: g) (a,b) = do v1 <- eval f a
                          v2 <- eval g b
                          return (v1,v2)
eval (f :+: g) (Left a) = do v <- eval f a 
                             return (Left v)
eval (f :+: g) (Right b) = do v <- eval g b
                              return (Right v)
eval ZeroE (Right a) = return a
eval ZeroI a = return (Right a)
eval SwapP (Left a) = return (Right a)
eval SwapP (Right b) = return (Left b)
eval AssocLP (Left a) = return (Left (Left a))
eval AssocLP (Right (Left b)) = return (Left (Right b))
eval AssocLP (Right (Right c)) = return (Right c)
eval AssocRP (Left (Left a)) = return (Left a)
eval AssocRP (Left (Right b)) = return (Right (Left b))
eval AssocRP (Right c) = return (Right (Right c))
eval UnitE ((), a) = return a
eval UnitI a = return ((), a)
eval SwapT (a,b) = return (b,a) 
eval AssocLT (a,(b,c)) = return ((a,b),c) 
eval AssocRT ((a,b),c)  = return (a,(b,c))
eval Distrib (Left b, a) = return (Left (b, a))
eval Distrib (Right c, a) = return (Right (c, a))
eval Factor (Left (b, a)) = return (Left b, a) 
eval Factor (Right (c, a)) = return (Right c, a) 
eval FoldB (Left ()) = return True
eval FoldB (Right ()) = return False
eval UnfoldB True = return (Left ())
eval UnfoldB False = return (Right ())
eval FoldN (Left ()) = return 0
eval FoldN (Right n) = return (n+1)
eval UnfoldN 0 = return (Left ())
eval UnfoldN n = return (Right (n-1))
eval (TraceP c) v = do v' <- eval c (Right v)
                       loop c v'
    where
      loop c (Left v) = do v' <- eval c (Left v)
                           loop c v'
      loop c (Right v) = return v
eval (TraceT c) v = try elems
    where try [] = []
          try (a : as) = do (a',v') <- eval c (a,v)
                            if a == a' 
                              then v' : try as
                              else try as

evalR :: (a :<=> b) -> b -> [a]
evalR Id a = return a
evalR (Sym f) b = eval f b
evalR (f :.: g) a = do v <- evalR g a 
                       evalR f v
evalR (f :*: g) (a,b) = do v1 <- evalR f a 
                           v2 <- evalR g b
                           return (v1,v2)
evalR (f :+: g) (Left a) = do v <- evalR f a 
                              return (Left v)
evalR (f :+: g) (Right b) = do v <- evalR g b
                               return (Right v)
evalR ZeroE a = return (Right a)
evalR ZeroI (Right a) = return a
evalR SwapP (Left a) = return (Right a)
evalR SwapP (Right b) = return (Left b)
evalR AssocLP (Left (Left a)) = return (Left a)
evalR AssocLP (Left (Right b)) = return (Right (Left b))
evalR AssocLP (Right c) = return (Right (Right c))
evalR AssocRP (Left a) = return (Left (Left a))
evalR AssocRP (Right (Left b)) = return (Left (Right b))
evalR AssocRP (Right (Right c)) = return (Right c)
evalR UnitE a = return ((), a)
evalR UnitI ((), a) = return a
evalR SwapT (a,b) = return (b,a) 
evalR AssocLT ((a,b),c)  = return (a,(b,c))
evalR AssocRT (a,(b,c)) = return ((a,b),c) 
evalR Distrib (Left (b, a)) = return (Left b, a) 
evalR Distrib (Right (c, a)) = return (Right c, a) 
evalR Factor (Left b, a) = return (Left (b, a))
evalR Factor (Right c, a) = return (Right (c, a))
evalR FoldB True = return (Left ())
evalR FoldB False = return (Right ())
evalR UnfoldB (Left ()) = return True
evalR UnfoldB (Right ()) = return False
evalR FoldN 0 = return (Left ())
evalR FoldN n = return (Right (n-1))
evalR UnfoldN (Left ()) = return 0
evalR UnfoldN (Right n) = return (n+1)
evalR (TraceP c) v = do v' <- evalR c (Right v)
                        loop c v'
    where
      loop c (Left v) = do v' <- evalR c (Left v)
                           loop c v'
      loop c (Right v) = return v
evalR (TraceT c) v = try elems
    where try [] = []
          try (a : as) = do (a',v') <- evalR c (a,v)
                            if a == a' 
                              then v' : try as
                              else try as

-- using nub; could use exclusive union to get modal QC or nothing to get duplicates

evalL :: (B a, B b) => (a :<=> b) -> [a] -> [b]
evalL c as = nub $ as >>= (eval c)

evalRL :: (B a, B b) => (a :<=> b) -> [b] -> [a]
evalRL c bs = nub $ bs >>= (evalR c)

------------------------------------------------------------------------
-- examples with nats

addsub :: Either Nat Nat :<=> Either Nat Nat
addsub =               -- (n1' + n2)
  (Id :+: UnfoldN) :.: -- (n1' + (1+n2'))
  AssocLP :.:          -- ((n1'+1) + n2')
  (SwapP :+: Id) :.:   -- ((1+n1') + n2')
  (FoldN :+: Id)       -- (n1 + n2')

just :: B b => b :<=> Either () b
just = TraceP c 
  where c :: B b => Either Nat b :<=> Either Nat (Either () b)
        c =                     -- (n + b)
          (UnfoldN :+: Id) :.:  -- ((1+n') + b)
          (SwapP :+: Id) :.:    -- ((n'+1) + b)
          AssocRP               -- (n'+(1+b))

add1, sub1 :: Nat :<=> Nat
add1 = just :.: FoldN
sub1 = Sym add1

introF, introT :: () :<=> Bool
introF = just :.: FoldB
introT = introF :.: inot

injectR :: B b => b :<=> Either b b
injectR = UnitI :.: (just :*: Id) :.: Distrib :.: (UnitE :+: UnitE)

introZ :: () :<=> Nat
introZ = TraceP c 
  where c :: Either Nat () :<=> Either Nat Nat
        c = SwapP :.: FoldN :.: injectR

------------------------------------------------------------------------
-- GoI??

------------------------------------------------------------------------
-- Combinational circuits 

inot :: Bool :<=> Bool
inot = UnfoldB :.: SwapP :.: FoldB

cond :: (B a, B b) => (a :<=> b) -> (a :<=> b) -> ((Bool, a) :<=> (Bool, b))
cond f g = -- T,F
  (UnfoldB :*: Id) :.: 
  Distrib :.: 
  ((Id :*: f) :+: (Id :*: g)) :.: 
  Factor :.: 
  (FoldB :*: Id) 

cond2 :: (B a, B b) => (a :<=> b) -> (a :<=> b) -> (a :<=> b) -> (a :<=> b) -> 
         ((Bool,Bool),a) :<=> ((Bool,Bool),b)
cond2 f g h m = -- TT,TF,FT,FF
  AssocRT :.: (cond (cond f g) (cond h m)) :.: AssocLT

controlled :: B a => (a :<=> a) -> ((Bool, a) :<=> (Bool, a))
controlled f = cond f Id

cnot :: (Bool, Bool) :<=> (Bool, Bool)
cnot = controlled inot

elsenot :: (Bool, Bool) :<=> (Bool, Bool)
elsenot = cond Id inot

toffoli :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
toffoli = AssocRT :.: controlled cnot :.: AssocLT

fredkin :: (Bool,(Bool,Bool)) :<=> (Bool,(Bool,Bool))
fredkin = controlled SwapT

peres :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
peres = toffoli :.: (cnot :*: Id) 

if3not :: (Bool,(Bool,(Bool,Bool))) :<=> (Bool,(Bool,(Bool,Bool)))
if3not = controlled (controlled (controlled inot))

-- clone the first 2 if the last 2 are True
clone2 :: (Bool,(Bool,(Bool,Bool))) :<=> (Bool,(Bool,(Bool,Bool)))
clone2 = shuffle :.:
         (elsenot :*: elsenot) :.:
         (Sym shuffle)
  where shuffle =              -- (a,(b,(a',b')))
          (Id :*: SwapT) :.:   -- (a,((a',b'),b))
          (Id :*: AssocRT) :.: -- (a,(a',(b',b)))
          AssocLT :.:          -- ((a,a'),(b',b))
          (Id :*: SwapT)       -- ((a,a'),(b,b'))

-- clone the first 3 if the last 3 are all True
clone3 :: (Bool,(Bool,(Bool,(Bool,(Bool,Bool))))) :<=> (Bool,(Bool,(Bool,(Bool,(Bool,Bool)))))
clone3 = shuffle :.:
         (elsenot :*: (elsenot :*: elsenot)) :.:
         (Sym shuffle)
  where shuffle =              -- (a,(b,(c,(a',(b',c')))))
          (Id :*: AssocLT) :.: -- (a,((b,c),(a',(b',c'))))
          (Id :*: SwapT)   :.: -- (a,((a',(b',c')),(b,c)))
          AssocLT :.:          -- ((a,(a',(b',c'))),(b,c))
          (AssocLT :*: Id) :.: -- (((a,a'),(b',c')),(b,c))
          AssocRT :.:          -- ((a,a'),((b',c'),(b,c)))
          (Id :*: AssocLT) :.: -- ((a,a'),(((b',c'),b),c))
          (Id :*: (SwapT :*: Id)) :.:   -- ((a,a'),((b,(b',c')),c))
          (Id :*: (AssocLT :*: Id)) :.: -- ((a,a'),(((b,b'),c'),c))
          (Id :*: AssocRT) :.:          -- ((a,a'),((b,b'),(c',c)))
          (Id :*: (Id :*: SwapT))       -- ((a,a'),((b,b'),(c,c')))

------------------------------------------------------------------------
-- Multiplicative Trace (SAT)

annihilate :: B a => a :<=> a
annihilate = TraceT c
  where c :: B a => (Bool, a) :<=> (Bool, a)
        c = inot :*: Id
        
-- example input of function to SAT
-- first input is heap; last 2 inputs are the actual inputs        
-- is heap is false, and actual 2 inputs are FF
-- the function outputs two garbage bits and True
-- in all other relevant cases (heap is F) the function outputs False
isof1 :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
-- ((heap,input-1),input-2) ==> ((garbage-1,garbage-2),satisfied?)
isof1 = (AssocRT :.: SwapT :.: toffoli :.: SwapT :.: AssocLT) :.: 
        (((inot :*: Id) :*: Id) :.: toffoli :.: ((inot :*: Id) :*: Id)) :.:
        (Id :*: inot) 

isof2 :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
isof2 = toffoli

satf :: (((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)) -> 
        ((((Bool,Bool),Bool),Bool),Bool) :<=> ((((Bool,Bool),Bool),Bool),Bool)
-- takes isof as input; produces
-- ((((heap-control,control),heap),input-1),input-2)
-- if heap=True, negate heap-control;
-- if isof produces False, negate control
satf isof = -- ((((heap-control,control),heap),input-1),input-2)
  ((SwapT :*: Id) :*: Id) :.: -- (((heap,(heap-control,control)),input-1),input-2)
  ((AssocLT :*: Id) :*: Id) :.: -- ((((heap,heap-control),control),input-1),input-2)
  (((cnot :*: Id) :*: Id) :*: Id) :.: -- ((((heap,heap-control),control),input-1),input-2)
  AssocRT :.: -- (((heap,heap-control),control),(input-1,input-2))
  (AssocRT :*: Id) :.: -- ((heap,(heap-control,control)),(input-1,input-2))
  (SwapT :*: Id) :.: -- (((heap-control,control),heap),(input-1,input-2))
  AssocRT :.: -- ((heap-control,control),(heap,(input-1,input-2)))
  (Id :*: AssocLT) :.: -- ((heap-control,control),((heap,input-1),input-2))
  (Id :*: isof) :.: -- ((heap-control,control),((garbage-1,garbage-2),satisfied?))
  SwapT :.: -- (((garbage-1,garbage-2),satisfied?),(heap-control,control))
  AssocRT :.: -- ((garbage-1,garbage-2),(satisfied?,(heap-control,control)))
  (Id :*: (Id :*: SwapT)) :.: -- ((garbage-1,garbage-2),(satisfied?,(control,heap-control)))
  (Id :*: AssocLT) :.: -- ((garbage-1,garbage-2),((satisfied?,control),heap-control))
  (Id :*: ((inot :*: Id) :*: Id)) :.:
  (Id :*: (cnot :*: Id)) :.: 
  (Id :*: ((inot :*: Id) :*: Id)) :.:
  (Id :*: AssocRT) :.: 
  (Id :*: (Id :*: SwapT)) :.: 
  AssocLT :.:
  SwapT :.:
  (Id :*: Sym isof) :.: -- ((heap-control,control),((heap,input-1),input-2))
  (Id :*: AssocRT) :.: -- ((heap-control,control),(heap,(input-1,input-2)))
  AssocLT :.: -- (((heap-control,control),heap),(input-1,input-2))
  AssocLT -- ((((heap-control,control),heap),input-1),input-2)

solve :: ((((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool))) -> 
         ((Bool,Bool) :<=> (Bool,Bool))
         -- cloning-heap :<=> inputs that satisfy isof
solve isof = TraceT body 
  where body :: ((((Bool,Bool),Bool),(Bool,Bool)),(Bool,Bool)) :<=> 
                ((((Bool,Bool),Bool),(Bool,Bool)),(Bool,Bool))
        -- ((((input-1,input-2),heap),(control,heap-control)),cloning-heap)
        body = 
          -- take input-1 and input-2 and cloning-heap and pass them to clone2
          -- as (input-1,(input-2,cloning-heap))
          -- first two ouputs of clone2 are fed back to satf; other two 
          -- become overall output
          (AssocRT :*: Id) :.: 
          -- (((input-1,input-2),(heap,(control,heap-control))),cloning-heap)
          AssocRT :.:
          -- ((input-1,input-2),((heap,(control,heap-control)),cloning-heap))
          (Id :*: SwapT) :.:
          -- ((input-1,input-2),(cloning-heap,(heap,(control,heap-control))))
          AssocLT :.:
          -- (((input-1,input-2),cloning-heap),(heap,(control,heap-control)))
          (AssocRT :*: Id) :.:
          -- ((input-1,(input-2,cloning-heap)),(heap,(control,heap-control)))
          (clone2 :*: Id) :.:
          -- ((input-1,(input-2,(input-1,input-2))),(heap,(control,heap-control)))
          SwapT :.:
          -- ((heap,(control,heap-control)),(input-1,(input-2,(input-1,input-2))))
          (SwapT :*: Id) :.:
          -- (((control,heap-control),heap),(input-1,(input-2,(input-1,input-2))))
          ((SwapT :*: Id) :*: Id) :.:
          -- (((heap-control,control),heap),(input-1,(input-2,(input-1,input-2))))
          AssocLT :.:
          -- ((((heap-control,control),heap),input-1),(input-2,(input-1,input-2)))
          AssocLT :.:
          -- (((((heap-control,control),heap),input-1),input-2),(input-1,input-2))
          ((satf isof) :*: Id) :.:
          (AssocRT :*: Id) :.:
          -- ((((heap-control,control),heap),(input-1,input-2)),(input-1,input-2))
          (SwapT :*: Id) :.: 
          -- (((input-1,input-2),((heap-control,control),heap)),(input-1,input-2))
          ((Id :*: SwapT) :*: Id) :.:
          -- (((input-1,input-2),(heap,(heap-control,control))),(input-1,input-2))
          (AssocLT :*: Id) :.:
          -- ((((input-1,input-2),heap),(heap-control,control)),(input-1,input-2))
          ((Id :*: SwapT) :*: Id)
          -- ((((input-1,input-2),heap),(control,heap-control)),(input-1,input-2))


s1 = eval (solve isof1) (True,True)
s2 = eval (solve isof2) (True,True)

b2 :: [(Bool,Bool)]
b2 = [(b1,b2) | b1 <- bs, b2 <- bs] where bs = [False,True]

b3 :: [((Bool,Bool),Bool)]
b3 = [((b1,b2),b3) | b1 <- bs, b2 <- bs, b3 <- bs] where bs = [False,True]

test1 c = mapM_ (\b -> print (b, evalL c [b])) [False,True]
test2 c = mapM_ (\b -> print (b, evalL c [b])) b2
test3 c = mapM_ (\b -> print (b, evalL c [b])) b3

------------------------------------------------------------------------
-- iterate twice

twice :: B a => (a :<=> a) -> (a :<=> a)
twice c = TraceP (((c :+: c) :+: Id) :.: r)
  where r :: B a => (Either (Either a a) a) :<=> (Either (Either a a) a)
        r =                  -- (a + b) + c
          (SwapP :+: Id) :.: -- (b + a) + c
          AssocRP :.:        -- b + (a + c)
          (Id :+: SwapP) :.: -- b + (c + a)
          AssocLP            -- (b + c) + a
          
-- of course we could have written (c ; c) but when we introduce
-- recursive types, iteration becomes essential.
-- generalize to iterate n times for fixed n

------------------------------------------------------------------------
-- Superdense coding
        
r, s, u, v, rd, sd, ud, vd, eq, g, k, gk :: Bool :<=> Bool        
r = Id
s = inot
u = TraceT cr 
  where cr :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool) 
        cr = Sym (AssocRT :.: (Id :*: cnot) :.: AssocLT :.:
                  SwapT :.: (controlled (inot :*: inot)) :.: SwapT :.: 
                  AssocRT :.: SwapT :.: toffoli :.: SwapT :.: AssocLT :.:
                  SwapT :.: AssocLT :.: (cond2 Id Id inot Id) :.: AssocRT :.: SwapT :.:
                  SwapT :.: AssocLT :.: toffoli :.: AssocRT :.: SwapT)
v = TraceT cr 
  where cr :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
        cr = Sym (SwapT :.: AssocLT :.: (cnot :*: Id) :.: AssocRT :.: SwapT :.: 
                  toffoli :.: ((SwapT :.: cnot :.: SwapT) :*: Id) :.:
                  toffoli :.: (AssocRT :.: SwapT :.: toffoli :.: SwapT :.: AssocLT) :.:
                  toffoli :.: (cnot :*: Id))
rd = inot :.: v :.: inot
sd = rd :.: inot
ud = inot
vd = Id
eq = Id
g = inot
k = sd
gk = g :.: k

alice :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
alice = cond2 Id g k gk

dotP :: (((Bool,Bool),(Bool,Bool)),Bool) :<=> (((Bool,Bool),(Bool,Bool)),Bool)
dotP = undefined

------------------------------------------------------------------------
-- Relations on Bool X Bool

r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15 :: Bool :<=> Bool

-- empty
r0 = TraceT (inot :*: Id)

-- (F,F)
r1 = TraceT (SwapT :.: cnot :.: SwapT)

-- (F,T)
r2 = r1 :.: inot

-- (T,F)
r3 = inot :.: r1

-- (T,T)
r4 = inot :.: r1 :.: inot

-- (F,F),(F,T)
r5 = r1 :.: r15

-- (F,F),(T,F)
r6 = Sym r5

-- (F,F),(T,T)
r7 = Id

-- (F,T),(T,F)
r8 = inot

-- (F,T),(T,T)
r9 = Sym (r4 :.: r14)

-- (T,F),(T,T)
r10 = r4 :.: r14

-- (F,F),(F,T),(T,F)
r11 = v

-- (F,F),(F,T),(T,T)
r12 = u

-- (F,F),(T,F),(T,T)
r13 = sd

-- (F,T),(T,F),(T,T)
r14 = rd

-- (F,F),(F,T),(T,F),(T,T)
r15 = sd :.: Sym sd

------------------------------------------------------------------------
-- Examples from book

ex1 :: () :<=> ()
ex1 = TraceT c        
  where c :: (Bool, ()) :<=> (Bool, ())
        c = Id

ex2 :: () :<=> ()
ex2 = TraceT c
  where c :: (Bool, ()) :<=> (Bool, ())
        c = inot :*: Id
        
ex3 :: () :<=> Bool        
ex3 = TraceT c 
  where c :: (Zero, ()) :<=> (Zero, Bool)
        c = DistribZ :.: FactorZ
        
-- satisfied many many many times ;-)
exn :: () :<=> ()
exn = TraceT c
  where c :: (Nat, ()) :<=> (Nat, ())
        c = Id

-- satisfy c @@ () returns () if any row of c is the identity

satisfy :: B a => (a :<=> a) -> () :<=> ()
satisfy c = TraceT (SwapT :.: UnitE :.: c :.: UnitI :.: SwapT)

sat1 = satisfy inot

sat2 = satisfy cnot

sat3 = satisfy toffoli

sat4 = satisfy fredkin

sat5 = satisfy peres

sat6 = satisfy (inot :*: inot)

-- 

block :: (Bool,(Bool,(Bool,Bool))) :<=> (Bool,(Bool,(Bool,Bool)))
block = -- (a,(b,(c,y)))
  (Id :*: (AssocLT :.: toffoli :.: AssocRT)) :.: -- (a,(b,(c,y)))
  (Id :*: SwapT) :.: -- (a,((c,y),b))
  (Id :*: (SwapT :*: Id)) :.: -- (a,((y,c),b))
  AssocLT :.: -- ((a,(y,c)),b)
  ((AssocLT :.: toffoli :.: AssocRT) :*: Id) :.: -- ((a,(y,c)),b)
  AssocRT :.: -- (a,((y,c),b))
  (Id :*: (SwapT :*: Id)) :.: -- (a,((c,y),b))
  (Id :*: SwapT) -- (a,(b,(c,y)))

ex :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
-- (a,(b,(c,y))) ((a,b),(c,y)) (((a,b),c),y) (y,((a,b),c))
ex = TraceT (SwapT :.: AssocRT :.: AssocRT :.:
             block :.:
             AssocLT :.: AssocLT :.: SwapT)

{--

ex @@ ((False,False),False) ==> ((False,False),False)
ex @@ ((False,False),True)  ==> ((False,False),True)
ex @@ ((False,True),False)  ==> ((False,True),False)
ex @@ ((False,True),True)   ==> --
ex @@ ((True,False),False)  ==> ((True,False),False)
ex @@ ((True,False),True)   ==> ((True,False),True)
ex @@ ((True,True),False)   ==> ((True,True),False)
ex @@ ((True,True),True)    ==> --

--}

------------------------------------------------------------------------
