-- {-# OPTIONS_GHC -XGADTs -XTypeOperators #-} -- 7.0.1

-- Based on code
-- Copyright (c) 2011, William J. Bowman, Roshan P. James, and Amr
-- Sabry. The code is released under the MIT license.
--
-- Original code used GADTs.  Now do 'tagless final' using classes.
--   (Jacques Carette)
-- This code tested with GHC version 7.0.3

module Lang where

import Prelude hiding (id)

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
-- Encoding of booleans
  foldB   :: eq (Either () ()) Bool
  unfoldB :: eq Bool (Either () ())
-- Encoding of natural numbers using the isorecursive type (mu x.1+x)
  foldN   :: eq (Either () Int) Int
  unfoldN :: eq Int (Either () Int)
-- Encoding of lists of natural numbers using the isorecursive type
-- (mu x.1+nat*x)
  foldLN :: eq (Either () (Int, [Int])) [Int]
  unfoldLN :: eq [Int] (Either () (Int, [Int]))
-- Encoding of lists of natural numbers using the isorecursive type
-- (mu x.1+nat*x)
  foldL :: eq (Either () (a, [a])) [a]
  unfoldL :: eq [a] (Either () (a, [a]))
-- Trace operators for looping/recursion
  tracePlus :: eq (Either a b1) (Either a b2) -> eq b1 b2

class Pi eq => PiN eq where
  adjo :: eq a b -> eq (Neg b) (Neg a)
-- etaPlus, epsPlus
  etaPlus :: eq Zero (Either (Neg a) a)
  epsPlus :: eq (Either a (Neg a)) Zero 

class Pi eq => PiInv eq where
-- etaTimes, epsTimes
  etaTimes :: eq () (Inv a,a)
  epsTimes :: eq (a, Inv a) ()

class Extract eq where
  (@!) :: eq a b -> a -> b

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
data Inv a = Inv a deriving Show

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
  foldB = flip0 unfoldB
  unfoldB = flip0 foldB
  foldN = flip0 unfoldN
  unfoldN = flip0 foldN
  foldLN = flip0 unfoldLN
  unfoldLN = flip0 foldLN
  foldL = flip0 unfoldL
  unfoldL = flip0 foldL
  tracePlus (Flip c) = Flip (tracePlus c)

instance PiN eq => PiN (Flip eq) where
  adjo = flip1 adjo
  etaPlus = flip0 (commutePlus %. epsPlus)
  epsPlus = flip0 (etaPlus %. commutePlus)

adj :: Flip eq a b -> eq b a
adj x = unFlip x
