-- {-# OPTIONS_GHC -XGADTs -XTypeOperators #-} -- 7.0.1
{-# LANGUAGE TypeFamilies, FlexibleContexts, GADTs #-}

-- Based on code
-- Copyright (c) 2011, William J. Bowman, Roshan P. James, and Amr
-- Sabry. The code is released under the MIT license.
--
-- Original code used GADTs.  Now do 'tagless final' using classes.
--   (Jacques Carette)
-- This code tested with GHC version 7.0.3

module Lang where

import Prelude hiding (id)
import qualified Prelude as P
import Control.Monad

class Pi eq where
-- Congruence
  id :: eq a a  -- refl
  (%.) :: eq a b -> eq b c -> eq a c -- trans
-- defn of (+) and (*)
  (%*) :: eq a b -> eq c d -> eq (a,c) (b,d)
  (%+) :: eq a b -> eq c d -> eq (Either a c) (Either b d)
-- (+) is associative, commutative, and has a unit
  plusZeroL :: eq (Either Zero a) a
  plusZeroR :: eq a (Either Zero a)
  commutePlus :: eq (Either a b) (Either b a)
  assocPlusL :: eq (Either a (Either b c)) (Either (Either a b) c)
  assocPlusR :: eq (Either (Either a b) c) (Either a (Either b c))
-- (*) is associative, commutative, and has a unit
  timesOneL    :: eq ((), a)  a
  timesOneR    :: eq a ((), a)
  commuteTimes :: eq (a,b) (b,a) 
  assocTimesL  :: eq (a,(b,c)) ((a,b),c)
  assocTimesR  :: eq ((a,b),c) (a,(b,c))
-- (*) distributes over (+) 
  timesZeroL  :: eq (Zero, a) Zero
  timesZeroR  :: eq Zero (Zero, a)
  distribute  :: eq (Either b c, a) (Either (b, a) (c, a))
  factor      :: eq (Either (b, a) (c, a)) (Either b c, a)

class Pi eq => PiBool eq where
-- Encoding of booleans
  foldB   :: eq (Either () ()) Bool
  unfoldB :: eq Bool (Either () ())

class Pi eq => PiNat eq where
-- Encoding of natural numbers using the isorecursive type (mu x.1+x)
  foldN   :: eq (Either () Int) Int
  unfoldN :: eq Int (Either () Int)

class PiNat eq => PiLNat eq where
-- Encoding of lists of natural numbers using the isorecursive type
-- (mu x.1+nat*x)
  foldLN :: eq (Either () (Int, [Int])) [Int]
  unfoldLN :: eq [Int] (Either () (Int, [Int]))
-- Encoding of lists of natural numbers using the isorecursive type
-- (mu x.1+nat*x)
  foldL :: eq (Either () (a, [a])) [a]
  unfoldL :: eq [a] (Either () (a, [a]))

class Pi eq => PiTracePlus eq where
-- Trace operator for looping/recursion
  tracePlus :: eq (Either a b1) (Either a b2) -> eq b1 b2

class Pi eq => PiN eq where
  adjo :: eq a b -> eq (Neg b) (Neg a)
-- etaPlus, epsPlus
  etaPlus :: eq Zero (Either (Neg a) a)
  epsPlus :: eq (Either a (Neg a)) Zero 

class Pi eq => PiInv eq where
-- etaTimes, epsTimes
  etaTimes :: eq () (Inv a,a)
  epsTimes :: Eq a => eq (Inv a, a) ()

-- This class says that, the u a's can be unified (as an effect) and generated
-- should also constrain W to be a monad, but I don't know how?
class Unifyable u where
  type W :: * -> *
  unify :: u a -> u a -> W ()
  fresh :: W (u a)

class DS v where
    unit :: v ()
    neg :: v a -> v (Neg a)
    inv :: v a -> v (Inv a)
    pair :: v a -> v b -> v (a,b)
    left :: v a -> v (Either a b)
    right :: v b -> v (Either a b)

class Extract eq where
  (@!) :: (Unifyable u, DS u) => eq a b -> u a -> W (u b)

class Unpack r where
  unLeft :: r (Either a b) -> r a
  unRight :: r (Either a b) -> r b
  proj1 :: r (a,b) -> r a
  proj2 :: r (a,b) -> r b
  unNeg :: r (Neg a) -> r a
  
-----------------------------------------------------------------------
-- Isomorphisms 

data Zero
data Neg a = Negative a deriving Show
data Inv a = Inv a deriving Eq

instance Show Zero where 
  show _ = error "Empty type has no values to show"

instance Eq Zero where 
  _ == _ = error "Cannot use == at type 0"

instance Show a => Show (Inv a) where
  show (Inv a) = "1/" ++ show a

newtype Flip eq b a = Flip { unFlip :: eq a b }

flip0 :: Pi eq => eq a b -> Flip eq b a
flip0 = Flip
flip1 :: (Pi eq,Pi t) => (t x y -> eq a b) -> Flip t y x -> Flip eq b a
flip1 f (Flip a) = Flip (f a)
flip2 :: (Pi eq, Pi t1, Pi t2) => (t1 x y -> t2 x' y' -> eq a b) ->
    Flip t1 y x -> Flip t2 y' x' -> Flip eq b a
flip2 f (Flip a) (Flip b) = Flip (f a b)

-- Adjoint
instance Pi eq => Pi (Flip eq) where
  id = flip0 id
  (Flip a) %. (Flip b) = Flip (b %. a)
  (%+)  = flip2 (%+)
  (%*) = flip2 (%*)
  plusZeroL = flip0 plusZeroR
  plusZeroR = flip0 plusZeroL
  commutePlus = flip0 commutePlus
  assocPlusL = flip0 assocPlusR
  assocPlusR = flip0 assocPlusL
  timesOneL = flip0 timesOneR
  timesOneR = flip0 timesOneL
  commuteTimes = flip0 commuteTimes
  assocTimesL = flip0 assocTimesR
  assocTimesR = flip0 assocTimesL
  timesZeroL = flip0 timesZeroR
  timesZeroR = flip0 timesZeroL
  distribute = flip0 factor
  factor = flip0 distribute

instance PiBool eq => PiBool (Flip eq) where
  foldB = flip0 unfoldB
  unfoldB = flip0 foldB

instance PiNat eq => PiNat (Flip eq) where
  foldN = flip0 unfoldN
  unfoldN = flip0 foldN

instance PiLNat eq => PiLNat (Flip eq) where
  foldLN = flip0 unfoldLN
  unfoldLN = flip0 foldLN
  foldL = flip0 unfoldL
  unfoldL = flip0 foldL

instance PiTracePlus eq => PiTracePlus (Flip eq) where
  tracePlus (Flip c) = Flip (tracePlus c)
instance PiN eq => PiN (Flip eq) where
  adjo = flip1 adjo
  etaPlus = flip0 (commutePlus %. epsPlus)
  epsPlus = flip0 (etaPlus %. commutePlus)

adj :: Flip eq a b -> eq b a
adj x = unFlip x

----------
-- Helper fn
orV :: MonadPlus m => (v a -> m b) -> (v a -> m b) -> (v a -> m b)
orV f g = \v -> f v `mplus` g v

fresh1 :: (Unifyable v, Monad W) => (v a -> v b) -> v b -> W (v a)
fresh1 f v =
  do x <- fresh
     unify (f x) v
     return x

fresh2 :: (Unifyable v, Monad W) => (v a1 -> v a2 -> v b) -> v b -> W (v a1, v a2)
fresh2 f v =
  do x1 <- fresh
     x2 <- fresh
     unify (f x1 x2) v
     return (x1,x2)

fresh3 :: (Unifyable v, Monad W) => (v a1 -> v a2 -> v a3 -> v b) 
                           -> v b -> W (v a1, v a2, v a3)
fresh3 f v =
  do x1 <- fresh
     x2 <- fresh
     x3 <- fresh
     unify (f x1 x2 x3) v
     return (x1,x2,x3)

lift1 :: Monad m => (t -> m a) -> (a -> r) -> t -> m r
lift1 f g v = liftM g (f v)

-- mar = match >=> act >=> return
mar :: (Unifyable v, DS v, Monad W) => 
    (v a -> v b) -> (v a -> W c) -> (c -> d) -> (v b -> W d)
mar f g h = fresh1 f >=> g >=> (return . h)
-- mr = match >=> return
mr :: (Unifyable u, Monad W) => (u a -> u b) -> (u a -> c) -> (u b -> W c)
mr f h = fresh1 f >=> (return . h)

-- mr2 = match >=> return (on 2 args)
mr2 :: (Unifyable v, Monad W) => 
    (v a1 -> v a2 -> v b) -> ((v a1, v a2) -> c) -> v b -> W c
mr2 f h = fresh2 f >=> (return . h)

data Eval eq a b where
   At :: eq a b -> Eval eq a b

instance Pi eq => Pi (Eval eq) where
  id = At id
  (At f) %. (At g) = At (f %. g)
  (At f) %* (At g) = At (f %* g)
  (At f) %+ (At g) = At (f %+ g)
  plusZeroL = At plusZeroL
  plusZeroR = At plusZeroR
  commutePlus = At commutePlus
  assocPlusL = At assocPlusL
  assocPlusR = At assocPlusR
  timesOneL = At timesOneL
  timesOneR = At timesOneR
  commuteTimes = At commuteTimes
  assocTimesL = At assocTimesL
  assocTimesR = At assocTimesR
  timesZeroL = At timesZeroL
  timesZeroR = At timesZeroR
  distribute = At distribute
  factor = At factor
