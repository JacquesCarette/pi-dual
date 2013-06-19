{-# LANGUAGE TypeOperators, GADTs, RankNTypes, NamedFieldPuns #-}

-- new module to avoid having everything in one huge file
module ZR where

-- probably want to put the base Pi stuff in its own file?
-----------------------------------------------------------------------
-- Pi 

data Zero

instance Eq Zero where
  
data Color = Red | Green | Blue deriving (Show,Eq)

class Eq a => V a where 
  elems :: [a]

instance V Zero where
  elems = []

instance V () where
  elems = [()]

instance V Bool where
  elems = [False,True]

instance V Color where
  elems = [Red, Green, Blue]

instance (V a, V b) => V (Either a b) where
  elems = map Left elems ++ map Right elems

instance (V a, V b) => V (a,b) where
  elems = [(a,b) | a <- elems, b <- elems] 

data a :<=> b where 
-- Trace
  Trace :: (V a, V b, V c) => c -> (a, c) :<=> (b, c) -> a :<=> b
-- Congruence
  Id    :: V a => a :<=> a
  Sym   :: (V a, V b) => (a :<=> b) -> (b :<=> a) 
  (:.:) :: (V a, V b, V c) => (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (V a, V b, V c, V d) => 
           (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (V a, V b, V c, V d) => 
           (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- (+) is associative, commutative, and has a unit
  ZeroE   :: V a => Either Zero a :<=> a
  ZeroI   :: V a => a :<=> Either Zero a
  SwapP   :: (V a, V b) => Either a b :<=> Either b a
  AssocLP  :: (V a, V b, V c) => 
              Either a (Either b c) :<=> Either (Either a b) c 
  AssocRP  :: (V a, V b, V c) => 
              Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE    :: V a => ((), a) :<=> a
  UnitI    :: V a => a :<=> ((), a)
  SwapT    :: (V a, V b) => (a,b) :<=> (b,a) 
  AssocLT  :: (V a, V b, V c) => (a,(b,c)) :<=> ((a,b),c)
  AssocRT  :: (V a, V b, V c) => ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  DistribZ :: V a => (Zero, a) :<=> Zero
  FactorZ  :: V a => Zero :<=> (Zero, a)
  Distrib  :: (V a, V b, V c) => (Either b c, a) :<=> Either (b, a) (c, a)
  Factor   :: (V a, V b, V c) => Either (b, a) (c, a) :<=> (Either b c, a)
-- Encoding of booleans and colors
  FoldB   :: Either () () :<=> Bool
  UnfoldB :: Bool :<=> Either () ()
  FoldC   :: Either () (Either () ()) :<=> Color
  UnfoldC :: Color :<=> Either () (Either () ())

-- Adjoint

adjoint :: (a :<=> b) -> (b :<=> a)
adjoint (Trace v c) = Trace v (adjoint c)
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
adjoint FoldC = UnfoldC
adjoint UnfoldC = FoldC

-- Semantics
eval :: (V a, V b) => (a :<=> b) -> a -> b
eval (Trace v0 c) v = runTrace c v v0
eval Id a = a
eval (Sym f) b = evalR f b
eval (f :.: g) a = eval g (eval f a)
eval (f :*: g) (a,b) = (eval f a, eval g b) 
eval (f :+: g) (Left a) = Left (eval f a) 
eval (f :+: g) (Right b) = Right (eval g b) 
eval ZeroE (Right a) = a
eval ZeroI a = Right a
eval SwapP (Left a) = Right a
eval SwapP (Right b) = Left b 
eval AssocLP (Left a) = Left (Left a) 
eval AssocLP (Right (Left b)) = Left (Right b) 
eval AssocLP (Right (Right c)) = Right c
eval AssocRP (Left (Left a)) = Left a
eval AssocRP (Left (Right b)) = Right (Left b)
eval AssocRP (Right c) = Right (Right c)
eval UnitE ((), a) = a
eval UnitI a = ((), a)
eval SwapT (a,b) = (b,a) 
eval AssocLT (a,(b,c)) = ((a,b),c) 
eval AssocRT ((a,b),c)  = (a,(b,c))
eval Distrib (Left b, a) = Left (b, a) 
eval Distrib (Right c, a) = Right (c, a) 
eval Factor (Left (b, a)) = (Left b, a) 
eval Factor (Right (c, a)) = (Right c, a) 
eval FoldB (Left ()) = True
eval FoldB (Right ()) = False
eval UnfoldB True = Left ()
eval UnfoldB False = Right ()
eval FoldC (Left ()) = Red
eval FoldC (Right (Left ())) = Green
eval FoldC (Right (Right ())) = Blue
eval UnfoldC Red = Left ()
eval UnfoldC Green = Right (Left ())
eval UnfoldC Blue = Right (Right ())

runTrace :: (V a, V b, V c) => ((a, c) :<=> (b, c)) -> a -> c -> b
runTrace c v v0 = rt v0
  where
    rt vc = 
      let (b, v0') = eval c (v, vc) in
        if v0' == v0
        then b
        else rt v0'

runTraceB :: (V a, V b, V c) => ((a, c) :<=> (b, c)) -> b -> c -> a
runTraceB c v v0 = rt v0
  where
    rt vc = 
      let (b, v0') = evalR c (v, vc) in
        if v0' == v0
        then b
        else rt v0'

evalR :: (V a, V b) => (a :<=> b) -> b -> a
evalR (Trace v c) b = runTraceB c b v
evalR Id a = a
evalR (Sym f) b = eval f b
evalR (f :.: g) a = evalR f (evalR g a)
evalR (f :*: g) (a,b) = (evalR f a, evalR g b) 
evalR (f :+: g) (Left a) = Left (evalR f a) 
evalR (f :+: g) (Right b) = Right (evalR g b) 
evalR ZeroE a = Right a
evalR ZeroI (Right a) = a
evalR SwapP (Left a) = Right a
evalR SwapP (Right b) = Left b 
evalR AssocLP (Left (Left a)) = Left a
evalR AssocLP (Left (Right b)) = Right (Left b)
evalR AssocLP (Right c) = Right (Right c)
evalR AssocRP (Left a) = Left (Left a) 
evalR AssocRP (Right (Left b)) = Left (Right b) 
evalR AssocRP (Right (Right c)) = Right c
evalR UnitE a = ((), a)
evalR UnitI ((), a) = a
evalR SwapT (a,b) = (b,a) 
evalR AssocLT ((a,b),c)  = (a,(b,c))
evalR AssocRT (a,(b,c)) = ((a,b),c) 
evalR Distrib (Left (b, a)) = (Left b, a) 
evalR Distrib (Right (c, a)) = (Right c, a) 
evalR Factor (Left b, a) = Left (b, a) 
evalR Factor (Right c, a) = Right (c, a) 
evalR FoldB True = Left ()
evalR FoldB False = Right ()
evalR UnfoldB (Left ()) = True
evalR UnfoldB (Right ()) = False
evalR FoldC Red = Left ()
evalR FoldC Green = Right (Left ())
evalR FoldC Blue = Right (Right ())
evalR UnfoldC (Left ()) = Red
evalR UnfoldC (Right (Left ())) = Green
evalR UnfoldC (Right (Right ())) = Blue

-----------------------------------------------------------------------
-- Trace examples...

test :: (V a, V b) => (a :<=> b) -> [(a,b)]
test c = [(a,eval c a) | a <- elems]

notB :: Bool :<=> Bool
notB = UnfoldB :.: SwapP :.: FoldB

-- once:  R->G, G->B, B->R
-- twice: R->B, G->R, B->G
rotateC :: Color :<=> Color
rotateC = UnfoldC :.: AssocLP :.: SwapP :.: FoldC

caseB :: V a => (a :<=> a) -> (a :<=> a) -> (Bool,a) :<=> (Bool,a)
caseB fa tr = 
  (UnfoldB :*: Id) :.:
  Distrib :.:
  ((Id :*: fa) :+: (Id :*: tr)) :.:
  Factor :.:
  (FoldB :*: Id)

caseC :: V a => (a :<=> a) -> (a :<=> a) -> (a :<=> a) -> 
                (Color,a) :<=> (Color,a)
caseC r g b = 
  (UnfoldC :*: Id) :.:
  Distrib :.: (Id :+: Distrib) :.: 
  ((Id :*: r) :+: ((Id :*: g) :+: (Id :*: b))) :.: 
  (Id :+: Factor) :.: Factor :.:
  (FoldC :*: Id)

c1 :: (Color,Bool) :<=> (Color,Bool)
c1 = SwapT :.: (caseB rotateC (rotateC :.: rotateC)) :.: SwapT 

-- test c1
-- test (Trace False c1)
-- test (Trace True c1)

type Three = Either () (Either () ())

-- RedFalse == LL
-- RedTrue  == RL
-- GreenFalse == LRL
-- GreenTrue == TRL
-- BlueFalse == LRR
-- BlueTrue == RRR

unfoldCB :: (Color,Bool) :<=> Either Three Three
unfoldCB = 
  (UnfoldC :*: UnfoldB) :.: SwapT :.: Distrib :.: (UnitE :+: UnitE) 
                            
foldCB :: Either Three Three :<=> (Color,Bool)
foldCB = adjoint unfoldCB

{--
Consider the following permutation on (3 x 2) where I call the elements
of 3 as A,B,C and the elements of 2 as F,T.
(R,F) (R,T)
(R,T) (G,T)
(G,F) (R,F)
(G,T) (B,T)
(B,F) (G,F)
(B,T) (B,F)
--}
c2 :: (Color,Bool) :<=> (Color,Bool)
c2 = unfoldCB :.: -- (rf + (gf + bf)) + (rt + (gt + bt))
     (AssocLP :+: Id) :.: -- ((rf + gf) + bf) + (rt + (gt + bt))
     AssocRP :.: -- (rf + gf) + (bf + (rt + (gt + bt)))
     (Id :+: SwapP) :.: -- (rf + gf) + ((rt + (gt + bt)) + bf)
     (Id :+: AssocRP) :.: -- (rf + gf) + (rt + ((gt + bt) + bf))
     AssocLP :.: -- ((rf + gf) + rt) + ((gt + bt) + bf)
     (SwapP :+: AssocRP) :.: -- (rt + (rf + gf)) + (gt + (bt + bf))
     foldCB

{--
 If we trace out the elements (_,T) we get the following permutation on 3:
 R B
 G R
 B G

 If we trace out the elements (_,F) we get the following permutation on 3:
 R G
 G B
 B R
--}

-----------------------------------------------------------------------
----- Fractional Stuff

-- Ideally this would be a typeclass, but I'm not sure how to do it like that
-- If only we were programming in ML!
-- (if only ML had any of the ten billion other features that are useful here..)

data a :<==> b where
  Hat :: (V a, V b, V c, V d) =>
          b -> ((a, d) :<=> (b, c)) -> ((a, b) :<==> (c, d))

-- Definitions of eta and epsilon; note that epsilon must be parameterized in
-- this setting

eta :: V a => ((), ()) :<==> (a, a)
eta = Hat () Id

eps :: V a => a -> (a, a) :<==> ((), ())
eps v = Hat v Id

-- Given a "higher-order" combinator and a Pi combinator, this applies the
-- higher-order one to the Pi one

evalFrac :: (V a, V b, V c, V d) => (a, b) :<==> (c, d) -> a :<=> b -> c :<=> d
evalFrac (Hat v c1) c2 =
  Trace v (SwapT :.: adjoint c1 :.: (c2 :*: Id) :.: SwapT)

-- Functors!

-- Div a b c d = (a / b) / (c / d)
type Div a b c d = ((a, d), (b, c))

-- -- XXX: parameterizing this with an a2 seems like a gross hack, but I don't see
-- -- any way around it---what if b2 is 1 but a2 is 0, for instance?
-- div :: (V a1, V a2, V b1, V b2, V c1, V c2, V d1, V d2) =>
--          a2
--       -> (a1, b1) :<==> (c1, d1) -> (a2, b2) :<==> (c2, d2)
--       -> Div a1 b1 a2 b2 :<==> Div c1 d1 c2 d2
-- div v (Hat v1 c1) (Hat v2 c2) =
--   Hat (v1, v)
--       (shuffle :.: (c1 :*: (adjoint c2)) :.: shuffle)
--   where
--     shuffle :: forall a b c d. ((a, b), (c, d)) :<=> ((a, c), (d, b))
--     shuffle = AssocRT :.: (Id :*: AssocLT) :.: (Id :*: (SwapT :*: Id))
--           :.: (Id :*: AssocRT) :.: AssocLT
