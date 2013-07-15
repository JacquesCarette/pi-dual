{-# LANGUAGE TypeOperators, GADTs, RankNTypes, NamedFieldPuns #-}

module H where

import Data.List

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
adjoint Eta = Epsilon
adjoint Epsilon = Eta 
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

evalR :: (V a, V b) => (a :<=> b) -> b -> [a]
evalR Eta (a, Path (a',())) | a==a' = [()]
                            | otherwise = []
evalR Epsilon () = [(a, Path (a,())) | a <- points]
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

evalL :: (V a, V b) => (a :<=> b) -> [a] -> [b]
evalL c as = nub $ as >>= (eval c)

evalRL :: (V a, V b) => (a :<=> b) -> [b] -> [a]
evalRL c bs = nub $ bs >>= (evalR c)

-----------------------------------------------------------------------
-- Examples

type a :-* b = (Recip a, b)

name :: (V b1, V b2) => (b1 :<=> b2) -> (() :<=> (b1 :-* b2))
name f = -- () 
  Eta :.: -- b1 * 1/b1
  SwapT :.: -- 1/b1 * b1
  (Id :*: f) -- 1/b1 * b2

-----------------------------------------------------------------------