{-# LANGUAGE TypeOperators, GADTs, RankNTypes, NamedFieldPuns #-}

module H where

-----------------------------------------------------------------------
-- Pi 

data Zero 

instance Eq Zero where
  (==) = undefined

class Eq a => V a where 
  points :: [a]

instance V Zero where
  points = []

instance V () where
  points = [()]

instance V Bool where
  points = [False,True]

instance (V a, V b) => V (Either a b) where
  points = map Left points ++ map Right points

instance (V a, V b) => V (a,b) where
  points = [(a,b) | a <- points, b <- points] 

-- a/b is the set of paths from b to a
data a :/ b = Path (b,a) deriving Eq

type Recip a = () :/ a

instance (V a, V b) => V (a :/ b) where
  points = [ Path (b,a) | b <- points, a <- points ]

data a :<=> b where 
  Eta :: V a => () :<=> (a, Recip a) 
  Epsilon :: V a => (a, Recip a) :<=> ()
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
eval :: (V a, V b) => (a :<=> b) -> a -> [b]
eval Eta () = [(a, Path (a,())) | a <- points]
eval Epsilon (a, Path (a',())) | a==a' = [()]
                               | otherwise = []
eval Id a = [a]

{--

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

evalR :: (V a, V b) => (a :<=> b) -> b -> a
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
--} 



-----------------------------------------------------------------------
