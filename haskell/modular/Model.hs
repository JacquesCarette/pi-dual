-- {-# OPTIONS_GHC -XGADTs -XTypeOperators #-} -- 7.0.1
{-# LANGUAGE GADTs, TypeOperators, ScopedTypeVariables, EmptyDataDecls #-} -- 7.0.3, 6.12.1

-- Based on code
-- Copyright (c) 2011, William J. Bowman, Roshan P. James, and Amr
-- Sabry. The code is released under the MIT license.
--
-- Original code used GADTs.  Now do 'tagless final' using classes.
-- 
-- This code tested with GHC version 7.0.3

module Model where

import Prelude hiding (id)
import Lang

-----------------------------------------------------------------------
-- Isomorphisms 

data a :<=> b where 
-- Congruence
  Id    :: a :<=> a
  Adj   :: (a :<=> b) -> (Neg b :<=> Neg a)
  (:.:) :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- (+) is associative, commutative, and has a unit
  PlusZeroL   :: Either Zero a :<=> a
  PlusZeroR   :: a :<=> Either Zero a
  CommutePlus :: Either a b :<=> Either b a
  AssocPlusL  :: Either a (Either b c) :<=> Either (Either a b) c 
  AssocPlusR  :: Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  TimesOneL    :: ((), a) :<=> a
  TimesOneR    :: a :<=> ((), a)
  CommuteTimes :: (a,b) :<=> (b,a) 
  AssocTimesL  :: (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  TimesZeroL  :: (Zero, a) :<=> Zero
  TimesZeroR  :: Zero :<=> (Zero, a)
  Distribute  :: (Either b c, a) :<=> Either (b, a) (c, a)
  Factor      :: Either (b, a) (c, a) :<=> (Either b c, a)
-- Eta and Eps over the monoid (*, 1)
  EtaTimes :: () :<=> (Inv a, a)
  EpsTimes :: (a, Inv a) :<=> () 
-- Eta and Eps over the monoid (+, 0)
  EtaPlus :: Zero :<=> Either (Neg a) a
  EpsPlus :: Either a (Neg a) :<=> Zero
-- Encoding of booleans
  FoldB   :: Either () () :<=> Bool
  UnfoldB :: Bool :<=> Either () ()
-- Encoding of natural numbers using the isorecursive type (mu x.1+x)
  FoldN   :: Either () Int :<=> Int
  UnfoldN :: Int :<=> Either () Int
-- Encoding of lists of natural numbers using the isorecursive type
-- (mu x.1+nat*x)
  FoldLN :: Either () (Int, [Int]) :<=> [Int]
  UnfoldLN :: [Int] :<=> Either () (Int, [Int])
-- Encoding of lists of natural numbers using the isorecursive type
-- (mu x.1+nat*x)
  FoldL :: Either () (a, [a]) :<=> [a]
  UnfoldL :: [a] :<=> Either () (a, [a])
-- Trance operators for looping/recursion
  TracePlus :: (Either a b1 :<=> Either a b2) -> (b1 :<=> b2)

instance Pi (:<=>) where
  id = Id
  (%.) = (:.:)
  (%*) = (:*:)
  (%+) = (:+:)
  plusZeroL = PlusZeroL
  plusZeroR = PlusZeroR
  commutePlus = CommutePlus
  assocPlusL = AssocPlusL
  assocPlusR = AssocPlusR
  timesOneL = TimesOneL
  timesOneR = TimesOneR
  commuteTimes = CommuteTimes
  assocTimesL = AssocTimesL
  assocTimesR = AssocTimesR
  timesZeroL = TimesZeroL
  timesZeroR = TimesZeroR
  distribute = Distribute
  factor = Factor

instance PiBool (:<=>) where
  foldB = FoldB
  unfoldB = UnfoldB

instance PiNat (:<=>) where
  foldN = FoldN
  unfoldN = UnfoldN

instance PiLNat (:<=>) where
  foldLN = FoldLN
  unfoldLN = UnfoldLN
  foldL = FoldL
  unfoldL = UnfoldL

instance PiTracePlus (:<=>) where
  tracePlus = TracePlus

instance PiN (:<=>) where
  adjo = Adj
  etaPlus = EtaPlus
  epsPlus = EpsPlus

instance PiInv (:<=>) where
  etaTimes = EtaTimes
  epsTimes = EpsTimes

-- Adjoint
adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint (Adj f) = Adj (adjoint f)
adjoint (f :.: g) = adjoint g :.: adjoint f
adjoint (f :*: g) = adjoint f :*: adjoint g
adjoint (f :+: g) = adjoint f :+: adjoint g
adjoint PlusZeroL = PlusZeroR
adjoint PlusZeroR = PlusZeroL
adjoint CommutePlus = CommutePlus
adjoint AssocPlusL = AssocPlusR
adjoint AssocPlusR = AssocPlusL
adjoint TimesOneL = TimesOneR
adjoint TimesOneR = TimesOneL
adjoint CommuteTimes = CommuteTimes
adjoint AssocTimesL = AssocTimesR
adjoint AssocTimesR = AssocTimesL
adjoint TimesZeroL = TimesZeroR
adjoint TimesZeroR = TimesZeroL
adjoint Distribute = Factor
adjoint Factor = Distribute
adjoint EtaTimes = CommuteTimes :.: EpsTimes
adjoint EpsTimes = EtaTimes :.: CommuteTimes
adjoint EtaPlus = CommutePlus :.: EpsPlus
adjoint EpsPlus = EtaPlus :.: CommutePlus
adjoint FoldB = UnfoldB
adjoint UnfoldB = FoldB
adjoint FoldN = UnfoldN
adjoint UnfoldN = FoldN
adjoint FoldLN = UnfoldLN
adjoint UnfoldLN = FoldLN
adjoint FoldL = UnfoldL
adjoint UnfoldL = FoldL
adjoint (TracePlus c) = TracePlus (adjoint c)

data I a = I a
unI :: I a -> a
unI (I a) = a

instance Unpack I where
  -- neither of the error can actually happen, for type reasons
  unLeft (I (Left a)) = I a
  unLeft (I (Right _)) = error "unLeft on a Right"
  unRight (I (Right a)) = I a
  unRight (I (Left _)) = error "unRight on a Left"
  proj1 (I (a,_)) = I a
  proj2 (I (_,b)) = I b
  unNeg (I (Negative a)) = I a

-- This allows us to pattern match and typecheck too
unL :: Either a b -> a
unL = unI . unLeft . I
unR :: Either a b -> b
unR = unI . unRight . I
projL :: (a,b) -> a
projL = unI . proj1 . I
projR :: (a,b) -> b
projR = unI . proj2 . I
unN :: Neg a -> a
unN = unI . unNeg . I

unList :: a -> (b -> [b] -> a) -> [b] -> a
unList f _ []    = f
unList _ g (h:t) = g h t

-- (simple) Semantics.  4 cases missing
-- 0*a = 0, 0 = 0*a, 1 = 1/a*a, 1/a*a = 1
-- instance Extract (:<=>) where
--   Id           @! v = v
--   (Adj f)      @! v = Negative ((adjoint f) @@ (unN v))
--   (f :.: g)    @! v = ((g @!) . (f @!)) v
--   (f :*: g)    @! v = (,) (f @! projL v) (g @! projR v) 
--   (f :+: g)    @! v = either (Left . (f @!)) (Right . (g @!)) v
--   PlusZeroL    @! v = unR v
--   PlusZeroR    @! v = Right v
--   CommutePlus  @! v = either Right Left v
--   AssocPlusL   @! v = either (Left . Left) (either (Left . Right) Right) v
--   AssocPlusR   @! v = either (either Left (Right . Left)) (Right . Right) v
--   TimesOneL    @! v = projR v
--   TimesOneR    @! v = ((), v)
--   CommuteTimes @! v = (projR v, projL v)
--   AssocTimesL  @! v = ((projL v, projL . projR $ v), projR . projR $ v)
--   AssocTimesR  @! v = (projL . projL $ v, (projR . projL $ v, projR v))
--   Distribute   @! v = let w = projR v in 
--                       either (\z -> Left (z, w)) (\z -> Right (z,w)) (projL v)
--   Factor       @! v = either (\z -> (Left $ projL z, projR z))
--                              (\z -> (Right $ projL z, projR z)) v
--   FoldB        @! v = either (\() -> True) (\() -> False) v
--   UnfoldB      @! v = if v then Left () else Right ()
--   FoldN        @! v = either (const 0) (1+) v
--   FoldLN       @! v = either (\() -> []) (\(h,t) -> h : t) v
--   FoldL        @! v = either (\() -> []) (\(h,t) -> h : t) v
--   UnfoldN      @! v = if v == 0 then Left () else Right (v-1)
--   UnfoldLN     @! v = unList (Left ()) (\a b -> Right (a,b)) v
--   UnfoldL      @! v = unList (Left ()) (\a b -> Right (a,b)) v
--   (TracePlus c) @! v = loop c (c @! (Right v))
--       where
--         loop d = either (\z -> loop d (d @! (Left z))) (\z -> z)

-- for interactive convenience
-- (@@) :: (a :<=> b) -> a -> b
-- (@@) = (@!)
