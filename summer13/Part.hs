{-# LANGUAGE TypeOperators, GADTs, RankNTypes, NamedFieldPuns #-}

-- new module to avoid having everything in one huge file
module Part where

-- probably want to put the base Pi stuff in its own file?
-----------------------------------------------------------------------
-- Pi 

import Data.Functor
import Data.Either
import Control.Arrow

data Zero

instance Eq Zero where
  
data Color = Red | Green | Blue deriving (Show,Eq)

-- class Eq a => V a where 
class V a where 
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

instance (V a, V b) => V (a -> b) where
  elems = [] -- XXX: placeholder

data a :<=> b where 
-- Congruence
  Id    :: V a => a :<=> a
  Sym   :: (V a, V b) => (a :<=> b) -> (b :<=> a) 
  (:.:) :: (V a, V b, V c) => (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (V a, V b, V c, V d) => 
           (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (V a, V b, V c, V d) => 
           (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- to keep things slightly cleaner
  Iso   :: a :<~> b -> a :<=> b

-- The type of (base) isomorphisms
data a :<~> b where
-- (+) is associative, commutative, and has a unit
  ZeroE   :: V a => Either Zero a :<~> a
  ZeroI   :: V a => a :<~> Either Zero a
  SwapP   :: (V a, V b) => Either a b :<~> Either b a
  AssocLP  :: (V a, V b, V c) => 
              Either a (Either b c) :<~> Either (Either a b) c 
  AssocRP  :: (V a, V b, V c) => 
              Either (Either a b) c :<~> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE    :: V a => ((), a) :<~> a
  UnitI    :: V a => a :<~> ((), a)
  SwapT    :: (V a, V b) => (a,b) :<~> (b,a) 
  AssocLT  :: (V a, V b, V c) => (a,(b,c)) :<~> ((a,b),c)
  AssocRT  :: (V a, V b, V c) => ((a,b),c) :<~> (a,(b,c))
-- (*) distributes over (+) 
  DistribZ :: V a => (Zero, a) :<~> Zero
  FactorZ  :: V a => Zero :<~> (Zero, a)
  Distrib  :: (V a, V b, V c) => (Either b c, a) :<~> Either (b, a) (c, a)
  Factor   :: (V a, V b, V c) => Either (b, a) (c, a) :<~> (Either b c, a)
-- Encoding of booleans and colors
  FoldB   :: Either () () :<~> Bool
  UnfoldB :: Bool :<~> Either () ()
  FoldC   :: Either () (Either () ()) :<~> Color
  UnfoldC :: Color :<~> Either () (Either () ())

-- Adjoint

adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint (Sym f) = f 
adjoint (f :.: g) = adjoint g :.: adjoint f
adjoint (f :*: g) = adjoint f :*: adjoint g
adjoint (f :+: g) = adjoint f :+: adjoint g
adjoint (Iso i) = Iso $ adjointIso i

adjointIso :: (a :<~> b) -> (b :<~> a)
adjointIso ZeroE = ZeroI
adjointIso ZeroI = ZeroE
adjointIso SwapP = SwapP
adjointIso AssocLP = AssocRP
adjointIso AssocRP = AssocLP
adjointIso UnitE = UnitI
adjointIso UnitI = UnitE
adjointIso SwapT = SwapT
adjointIso AssocLT = AssocRT
adjointIso AssocRT = AssocLT
adjointIso DistribZ = FactorZ
adjointIso FactorZ = DistribZ
adjointIso Distrib = Factor
adjointIso Factor = Distrib
adjointIso FoldB = UnfoldB
adjointIso UnfoldB = FoldB
adjointIso FoldC = UnfoldC
adjointIso UnfoldC = FoldC

-- Semantics
-- eval :: Functor f => (a :<=> b) -> f a -> f b
eval :: (a :<=> b) -> [a] -> [b]
eval Id a = a
eval (Sym f) b = evalR f b
eval (f :.: g) a = eval g (eval f a)
eval (f :*: g) as = uncurry zip . (eval f *** eval g) $ unzip as
-- NB: this is hideous. there might be a better way? it actually feels
-- partition-y...
eval (f :+: g) as =
    uncurry (++) . (map Left *** map Right) . (eval f *** eval g) 
  $ partitionEithers as
eval (Iso i) as = fmap (evalIso i) as

evalIso :: a :<~> b -> a -> b
evalIso ZeroE (Right a) = a
evalIso ZeroI a = Right a
evalIso SwapP (Left a) = Right a
evalIso SwapP (Right b) = Left b 
evalIso AssocLP (Left a) = Left (Left a) 
evalIso AssocLP (Right (Left b)) = Left (Right b) 
evalIso AssocLP (Right (Right c)) = Right c
evalIso AssocRP (Left (Left a)) = Left a
evalIso AssocRP (Left (Right b)) = Right (Left b)
evalIso AssocRP (Right c) = Right (Right c)
evalIso UnitE ((), a) = a
evalIso UnitI a = ((), a)
evalIso SwapT (a,b) = (b,a) 
evalIso AssocLT (a,(b,c)) = ((a,b),c) 
evalIso AssocRT ((a,b),c)  = (a,(b,c))
evalIso Distrib (Left b, a) = Left (b, a) 
evalIso Distrib (Right c, a) = Right (c, a) 
evalIso Factor (Left (b, a)) = (Left b, a) 
evalIso Factor (Right (c, a)) = (Right c, a) 
evalIso FoldB (Left ()) = True
evalIso FoldB (Right ()) = False
evalIso UnfoldB True = Left ()
evalIso UnfoldB False = Right ()
evalIso FoldC (Left ()) = Red
evalIso FoldC (Right (Left ())) = Green
evalIso FoldC (Right (Right ())) = Blue
evalIso UnfoldC Red = Left ()
evalIso UnfoldC Green = Right (Left ())
evalIso UnfoldC Blue = Right (Right ())


evalR :: (a :<=> b) -> [b] -> [a]
evalR Id a = a
evalR (Sym f) b = eval f b
evalR (f :.: g) a = evalR f (evalR g a)
evalR (f :*: g) as = uncurry zip . (evalR f *** evalR g) $ unzip as
evalR (f :+: g) as =
    uncurry (++) . (map Left *** map Right) . (evalR f *** evalR g) 
  $ partitionEithers as
evalR (Iso i) as = map (evalIsoR i) as

evalIsoR :: a :<~> b -> b -> a
evalIsoR ZeroE a = Right a
evalIsoR ZeroI (Right a) = a
evalIsoR SwapP (Left a) = Right a
evalIsoR SwapP (Right b) = Left b 
evalIsoR AssocLP (Left (Left a)) = Left a
evalIsoR AssocLP (Left (Right b)) = Right (Left b)
evalIsoR AssocLP (Right c) = Right (Right c)
evalIsoR AssocRP (Left a) = Left (Left a) 
evalIsoR AssocRP (Right (Left b)) = Left (Right b) 
evalIsoR AssocRP (Right (Right c)) = Right c
evalIsoR UnitE a = ((), a)
evalIsoR UnitI ((), a) = a
evalIsoR SwapT (a,b) = (b,a) 
evalIsoR AssocLT ((a,b),c)  = (a,(b,c))
evalIsoR AssocRT (a,(b,c)) = ((a,b),c) 
evalIsoR Distrib (Left (b, a)) = (Left b, a) 
evalIsoR Distrib (Right (c, a)) = (Right c, a) 
evalIsoR Factor (Left b, a) = Left (b, a) 
evalIsoR Factor (Right c, a) = Right (c, a) 
evalIsoR FoldB True = Left ()
evalIsoR FoldB False = Right ()
evalIsoR UnfoldB (Left ()) = True
evalIsoR UnfoldB (Right ()) = False
evalIsoR FoldC Red = Left ()
evalIsoR FoldC Green = Right (Left ())
evalIsoR FoldC Blue = Right (Right ())
evalIsoR UnfoldC (Left ()) = Red
evalIsoR UnfoldC (Right (Left ())) = Green
evalIsoR UnfoldC (Right (Right ())) = Blue

-- Okay, time for the actual partition stuff!

-- Type for runtime values
--
-- Represents a set of values of type b, but on the level of a
--
-- Or in other words, a partition of the type a into |b| classes, where each
-- class is labeled by an element of b. So there could be two distinct
-- partitions that represent the same equivalence relation, but label the
-- resulting classes differently.
--
-- Restriction: the function *must* be surjective
type RT a b = (a, a -> b)

-- Get an external handle on the set
observe :: RT a b -> b
observe (s, e) = e s

data a :<==> b where
  Eta :: V b => (b, ()) :<==> (b, (b, b -> ()))
  Eps :: (V a, V c) => (c, (a, a -> ())) :<==> (a, ())
  Com :: a :<=> b -> (c, a) :<==> (c, b)
  (:..:) :: (c1, a) :<==> (c2, b) -> (c2, b) :<==> (c3, c) ->
              (c1, a) :<==> (c3, c)

-- Eta exposes the underlying set
-- Epsilon observes it & collapses it all back down to ()

evalP :: ((c1, a) :<==> (c2, b)) -> RT c1 a -> RT c2 b
evalP Eta (s, e) = (s, \s -> (s, e))
evalP Eps rt@(s, e) = (fst $ observe rt, const ())
-- We have to do the computation here in the continuation for it to typecheck
evalP (Com c) rt@(s, e) = (s, \s -> head $ eval c [observe (s, e)])
evalP (f :..: g) rt = evalP g (evalP f rt)

-- A couple of tests

-- should be ()
t1 = observe $ evalP (Eta :..: Eps) (True, const ())

-- should be True
t2 = fst . observe $ evalP (Eps :..: Eta) ((True, const ()), id)

-- trace :: (?, (a, c)) :<==> (?, (b, c)) -> (?, a) :<==> (?, b)
-- trace c =
--   (Com UnitI) :..: (Eta :*: Id) :.: AssocRT :.: (Id :*: c) :.: AssocLT :.:
--   (Eps :*: Id) :.: UnitE
