{-# LANGUAGE TypeOperators, GADTs #-}

module Pi where

-----------------------------------------------------------------------
-- Isomorphisms 

data Zero 

data a :<=> b where 
-- Congruence
  Id    :: a :<=> a
  Sym   :: (a :<=> b) -> (b :<=> a) 
  (:.:) :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- (+) is associative, commutative, and has a unit
  ZeroE   :: Either Zero a :<=> a
  ZeroI   :: a :<=> Either Zero a
  SwapP :: Either a b :<=> Either b a
  AssocLP  :: Either a (Either b c) :<=> Either (Either a b) c 
  AssocRP  :: Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE    :: ((), a) :<=> a
  UnitI    :: a :<=> ((), a)
  SwapT :: (a,b) :<=> (b,a) 
  AssocLT  :: (a,(b,c)) :<=> ((a,b),c)
  AssocRT  :: ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  DistribZ  :: (Zero, a) :<=> Zero
  FactorZ  :: Zero :<=> (Zero, a)
  Distrib  :: (Either b c, a) :<=> Either (b, a) (c, a)
  Factor      :: Either (b, a) (c, a) :<=> (Either b c, a)
-- Encoding of booleans
  FoldB   :: Either () () :<=> Bool
  UnfoldB :: Bool :<=> Either () ()

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

-- Semantics
eval :: (a :<=> b) -> a -> b
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

evalR :: (a :<=> b) -> b -> a
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

------------------------------------------------------------------------
-- Combinational circuits 

-- Not works by first converting the Haskell boolean via a Unfold to
-- either Left () or Right (), where True is Left (), False is Right ().
-- not can simply use SwapP to perform a not, then Fold up the
-- bool.
-- REPL Session:
-- *Pi> inot @@ True
-- False
-- *Pi> inot @@ False
inot :: Bool :<=> Bool
inot = UnfoldB :.: SwapP :.: FoldB

-- Cond takes two isomorphisms from some type a to some type b, and 
-- creates an isomorphism between a pair of (Bool, a) which will apply
-- the first isomorphism if the Bool is True, and the second if the Bool
-- is False.
cond :: (a :<=> b) -> (a :<=> b) -> ((Bool, a) :<=> (Bool, b))
cond f g = (UnfoldB :*: Id) 
           :.: Distrib 
           :.: ((Id :*: f) :+: (Id :*: g))
           :.: Factor 
           :.: (FoldB :*: Id) 

-- controlled takes an isomorphism between a type a to type a, and 
-- creates an isomorphism (using cond) that will apply the isomorphism to
-- the second value of the pair, if the first value if True, and apply
-- Id otherwise.
controlled :: (a :<=> a) -> ((Bool, a) :<=> (Bool, a))
controlled f = cond f Id

-- cnot is Controlled Not, as found in reversible computing papers such
-- as Reversible Computing by Toffoli. It takes a pair of bools, and
-- applies not to the second Bool if the first is True, and otherwise
-- leaves the value unchanged.
-- REPL Session:
-- *Pi> cnot @@ (True, True)
-- (True, False)
-- *Pi> cnot @@ (False, True)
-- (False, True)
-- *Pi> cnot @@ (True, False)
-- (True, False)
cnot :: (Bool, Bool) :<=> (Bool, Bool)
cnot = controlled inot

-- Toffoli is the universal nand/and gate presented in Reversible
-- Computing by Toffoli.  It is equivalent to controlled controlled
-- not. It takes 3 bools, if the first is True, if applies controlled not
-- to the second 2 bools.
-- REPL Session:
-- *Pi> toffoli @@ ((True, True), False)
-- ((True, True), True)
-- *Pi> toffoli @@ ((True, False), False)
-- ((True, False), False)
-- *Pi> toffoli @@ ((True, True), True)
-- ((True, True), False)
-- *Pi> toffoli @@ ((False, True), False)
-- ((False, True), False)
toffoli :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
toffoli = AssocRT :.: controlled cnot :.: AssocLT

-- The Fredkin gate is a well known universal gate.
-- If the first bool is true, it swaps the second two, otherwise it
-- leaves the values unchanged.
fredkin :: (Bool,(Bool,Bool)) :<=> (Bool,(Bool,Bool))
fredkin = controlled SwapT

-- The Peres gate is a universal gate: it takes three inputs a, b, and c, 
-- and produces a, a xor b, (a and b) xor c
peres :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
peres = toffoli :.: (cnot :*: Id) 

-- fullAdder can be interpreted as an irreversible 2 bit adder with
-- carry, by fixing the first input to be False and interpreting the
-- inputs and outputs as follows:
--
-- Input: (Constant, ((Number1, Number2), CarryIn)))
-- Output (Garbage1, (Garbage2, (Sum, Carry_Out)))
--
-- All values should be booleans, where False is 0 and True is 1.
-- Constant must be initialized to 0.
fullAdder :: (Bool, ((Bool, Bool), Bool)) :<=> (Bool,(Bool,(Bool,Bool)))
fullAdder = SwapT :.: (SwapT :*: Id) :.: 
            AssocRT :.: SwapT :.: (peres :*: Id) :.:
            AssocRT :.: (Id :*: SwapT) :.: 
            AssocRT :.: (Id :*: AssocLT) :.:
            (Id :*: peres) :.: (Id :*: AssocRT)

--------------------------------------------------------------
