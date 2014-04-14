{-# LANGUAGE GADTs, TypeOperators, DataKinds #-}
{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS -Wall #-}

module Neg where

import qualified Prelude
import Prelude (Either(..), undefined, error, ($), (.), id)

-----------------------------------------------------------------------
-- The abstract type of isomorphisms and their semantics

data Zero

abort :: a
abort = error "Impossible: Empty type"

class Pi iso where 
-- Congruence
  idIso        :: iso a a
  sym          :: iso a b -> iso b a
  (%.)         :: iso a b -> iso b c -> iso a c
  (%*)         :: iso a b -> iso c d -> iso (a,c) (b,d)
  (%+)         :: iso a b -> iso c d -> iso (Either a c) (Either b d)
-- (+) is associative, commutative, and has a unit
  plusZeroL    :: iso (Either Zero a) a
  plusZeroR    :: iso a (Either Zero a)
  commutePlus  :: iso (Either a b) (Either b a)
  assocPlusL   :: iso (Either a (Either b c)) (Either (Either a b) c)
  assocPlusR   :: iso (Either (Either a b) c) (Either a (Either b c))
-- (*) is associative, commutative, and has a unit
  timesOneL    :: iso ((), a) a
  timesOneR    :: iso a ((), a)
  commuteTimes :: iso (a,b) (b,a) 
  assocTimesL  :: iso (a,(b,c)) ((a,b),c)
  assocTimesR  :: iso ((a,b),c) (a,(b,c))
-- (*) distributes over (+) 
  timesZeroL   :: iso (Zero, a) Zero
  timesZeroR   :: iso Zero (Zero, a)
  distribute   :: iso (Either b c, a) (Either (b, a) (c, a))
  factor       :: iso (Either (b, a) (c, a)) (Either b c, a)
-- Trace operators for looping/recursion
  trace        :: iso (Either a b) (Either a c) -> iso b c

-----------------------------------------------------------------------
-- Term model and rewriting semantics

data a :<=> b where 
  Id           :: a :<=> a
  Sym          :: (a :<=> b) -> (b :<=> a) 
  (:.:)        :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:)        :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:)        :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
  PlusZeroL    :: Either Zero a :<=> a
  PlusZeroR    :: a :<=> Either Zero a
  CommutePlus  :: Either a b :<=> Either b a
  AssocPlusL   :: Either a (Either b c) :<=> Either (Either a b) c 
  AssocPlusR   :: Either (Either a b) c :<=> Either a (Either b c) 
  TimesOneL    :: ((), a) :<=> a
  TimesOneR    :: a :<=> ((), a)
  CommuteTimes :: (a,b) :<=> (b,a) 
  AssocTimesL  :: (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: ((a,b),c) :<=> (a,(b,c))
  TimesZeroL   :: (Zero, a) :<=> Zero
  TimesZeroR   :: Zero :<=> (Zero, a)
  Distribute   :: (Either b c, a) :<=> Either (b, a) (c, a)
  Factor       :: Either (b, a) (c, a) :<=> (Either b c, a)
  Trace        :: (Either a b :<=> Either a c) -> (b :<=> c)

instance Pi (:<=>) where
  idIso        = Id
  sym          = Sym
  (%.)         = (:.:)
  (%*)         = (:*:)
  (%+)         = (:+:)
  plusZeroL    = PlusZeroL
  plusZeroR    = PlusZeroR
  commutePlus  = CommutePlus
  assocPlusL   = AssocPlusL
  assocPlusR   = AssocPlusR
  timesOneL    = TimesOneL
  timesOneR    = TimesOneR
  commuteTimes = CommuteTimes
  assocTimesL  = AssocTimesL
  assocTimesR  = AssocTimesR
  timesZeroL   = TimesZeroL
  timesZeroR   = TimesZeroR
  distribute   = Distribute
  factor       = Factor
  trace        = Trace
  
-- The basic semantics:
--   maps each syntactic type 'a' to a denotation 'td a'
--   maps each iso 'a :<=> b' to a morphism (td a -> td b)
--     and another morphism (td b -> td a)

-- Denotations of types

class TD td where
  zero  :: td Zero
  unit  :: td ()
  pair  :: td a -> td b -> td (a,b)
  fst   :: td (a, b) -> td a
  snd   :: td (a, b) -> td b
  left  :: td a -> td (Either a b)
  right :: td b -> td (Either a b)
  eithr :: td (Either a b) -> (td a -> td c) -> (td b -> td c) -> td c

-- Standard interpretation of types

newtype I a = I a

instance TD I where
  zero                = abort
  unit                = I ()
  pair  (I a) (I b)   = I (a,b)
  fst   (I (a,_))     = I a
  snd   (I (_,b))     = I b
  left  (I a)         = I (Left a)
  right (I b)         = I (Right b)
  eithr (I (Left a))  = \f _ -> f (I a)
  eithr (I (Right a)) = \_ g -> g (I a)

-- Denotations of isos

class MD iso where
  (@!) :: TD td => iso a b -> td a -> td b
  (!@) :: TD td => iso a b -> td b -> td a

instance MD (:<=>) where
  Id @! x           = x
  (Sym f) @! b      = f !@ b
  (f :.: g) @! a    = g @! (f @! a)
  (f :*: g) @! x    = pair (f @! (fst x)) (g @! (snd x)) 
  (f :+: g) @! x    = eithr x (left . (f @!)) (right . (g @!))
  PlusZeroL @! x    = eithr x abort id
  PlusZeroR @! a    = right a
  CommutePlus @! x  = eithr x right left
  AssocPlusL @! x   = eithr x 
                        (left . left) 
                        (\z -> eithr z (left . right) (right))
  AssocPlusR @! x   = eithr x 
                        (\z -> eithr z left (right . left)) 
                        (right . right)
  TimesOneL @! x    = snd x
  TimesOneR @! x    = pair unit x
  CommuteTimes @! x = pair (snd x) (fst x)
  AssocTimesL @! x  = pair (pair (fst x) (fst (snd x))) (snd (snd x))
  AssocTimesR @! x  = pair (fst (fst x)) (pair (snd (fst x)) (snd x))
  TimesZeroL @! _   = abort
  TimesZeroR @! _   = abort
  Distribute @! x   = eithr (fst x) 
                        (\z -> left (pair z (snd x)))
                        (\z -> right (pair z (snd x)))
  Factor @! x       = eithr x 
                        (\z -> pair (left (fst z)) (snd z))
                        (\z -> pair (right (fst z)) (snd z))
  (Trace c) @! v    = loop (c @! (right v))
    where loop w = eithr w (\z -> loop (c @! (left z))) id
        

  Id !@ x           = x
  (Sym f) !@ b      = f @! b
  (f :.: g) !@ a    = f !@ (g !@ a)
  (f :*: g) !@ x    = pair (f !@ (fst x)) (g !@ (snd x)) 
  (f :+: g) !@ x    = eithr x (left . (f !@)) (right . (g !@))
  PlusZeroL !@ a    = right a
  PlusZeroR !@ x    = eithr x abort id
  CommutePlus !@ x  = eithr x right left
  AssocPlusL !@ x   = eithr x 
                        (\z -> eithr z left (right . left)) 
                        (right . right)
  AssocPlusR !@ x   = eithr x 
                        (left . left) 
                        (\z -> eithr z (left . right) (right))
  TimesOneL !@ x    = pair unit x
  TimesOneR !@ x    = snd x
  CommuteTimes !@ x = pair (snd x) (fst x)
  AssocTimesL !@ x  = pair (fst (fst x)) (pair (snd (fst x)) (snd x))
  AssocTimesR !@ x  = pair (pair (fst x) (fst (snd x))) (snd (snd x))
  TimesZeroL !@ _   = abort
  TimesZeroR !@ _   = abort
  Distribute !@ x   = eithr x 
                        (\z -> pair (left (fst z)) (snd z))
                        (\z -> pair (right (fst z)) (snd z))
  Factor !@ x       = eithr (fst x) 
                        (\z -> left (pair z (snd x)))
                        (\z -> right (pair z (snd x)))
  (Trace c) !@ v    = loop (c !@ (right v))
    where loop w = eithr w (\z -> loop (c !@ (left z))) id

-----------------------------------------------------------------------
-- Resumptions

newtype R i o = R { r :: i -> (o, R i o) }

idR :: R a a 
idR = R $ \a -> (a, idR)

composeR :: R a b -> R b c -> R a c
composeR (R f) (R g) = R $ \a -> 
  let (b , f') = f a
      (c , g') = g b
  in (c , composeR f' g')

timesR :: R a b -> R c d -> R (a,c) (b,d)
timesR (R f) (R g) = R $ \(a,c) -> 
  let (b , f') = f a
      (d , g') = g c
  in ((b,d) , timesR f' g')

plusR :: R a b -> R c d -> R (Either a c) (Either b d)
plusR (R f) (R g) = R $ \x -> 
  case x of 
    Left a  -> let (b , f') = f a 
               in (Left b , plusR f' (R g))
    Right c -> let (d , g') = g c
               in (Right d , plusR (R f) g')

plusZeroLR :: R (Either Zero a) a
plusZeroLR = R $ \ (Right a) -> (a , plusZeroLR)

plusZeroRR :: R a (Either Zero a) 
plusZeroRR = R $ \a -> (Right a , plusZeroRR)

commutePlusR :: R (Either a b) (Either b a)
commutePlusR = R $ \v -> case v of 
  Left a  -> (Right a , commutePlusR)
  Right b -> (Left b  , commutePlusR)

assocPlusLR :: R (Either a (Either b c)) (Either (Either a b) c)
assocPlusLR = R $ \v -> case v of 
  Left a          -> (Left (Left a)  , assocPlusLR)
  Right (Left b)  -> (Left (Right b) , assocPlusLR)
  Right (Right c) -> (Right c        , assocPlusLR)

assocPlusRR :: R (Either (Either a b) c) (Either a (Either b c)) 
assocPlusRR = R $ \v -> case v of 
  Left (Left a)  -> (Left a          , assocPlusRR)
  Left (Right b) -> (Right (Left b)  , assocPlusRR)
  Right c        -> (Right (Right c) , assocPlusRR)

timesOneLR :: R ((),a) a
timesOneLR = R $ \((),a) -> (a , timesOneLR)

timesOneRR :: R a ((),a)
timesOneRR = R $ \a -> (((),a) , timesOneRR)

commuteTimesR :: R (a,b) (b,a)
commuteTimesR = R $ \(a,b) -> ((b,a) , commuteTimesR)

assocTimesLR :: R (a,(b,c)) ((a,b),c)
assocTimesLR = R $ \(a,(b,c)) -> (((a,b),c) , assocTimesLR)

assocTimesRR :: R ((a,b),c) (a,(b,c))
assocTimesRR = R $ \((a,b),c) -> ((a,(b,c)) , assocTimesRR)

timesZeroLR :: R (Zero,a) Zero
timesZeroLR = R $ \_ -> abort

timesZeroRR :: R Zero (Zero,a)
timesZeroRR = R $ \_ -> abort

distributeR :: R (Either b c , a) (Either (b,a) (c,a))
distributeR = R $ \(v,a) -> case v of 
  Left b  -> (Left (b,a) , distributeR)
  Right c -> (Right (c,a) , distributeR)    

factorR :: R (Either (b,a) (c,a)) (Either b c , a)
factorR = R $ \v -> case v of 
  Left (b,a)  -> ((Left b, a)  , factorR)
  Right (c,a) -> ((Right c, a) , factorR)

traceR :: R (Either a b) (Either a c) -> R b c
traceR f = R $ \a -> loop f (Right a)
  where loop (R g) v = case g v of
                         (Left b  , f') -> loop f' (Left b)
                         (Right c , f') -> (c , traceR f')

-----------------------------------------------------------------------
-- Int (or G) construction

-- Objects in the G category are pairs of objects 

class GT p where
  type Pos p :: *
  type Neg p :: *

instance GT (ap,am) where
  type Pos (ap,am) = ap
  type Neg (ap,am) = am

-- Morphisms in the G category

newtype GM a b = 
  GM { rg :: R (Either (Pos a) (Neg b)) (Either (Neg a) (Pos b)) } 

-- 

idG :: GM a a
idG = GM commutePlusR

composeG :: GM a b -> GM b c -> GM a c
composeG (GM f) (GM g) = GM $ traceR h 
  where 
    (>>) = composeR
    h = 
    -- (Either (Neg b) (Either (Pos a) (Neg c))
       assoc1 >>
    -- (Either (Either (Pos a) (Neg b)) (Neg c))
       (plusR f idR) >>
    -- (Either (Either (Neg a) (Pos b)) (Neg c))
       assoc2 >>
    -- (Either (Either (Pos b) (Neg c)) (Neg a))
       (plusR g idR) >>
    -- (Either (Either (Neg b) (Pos c)) (Neg a))
       assoc3
    -- (Neither (Neg b) (Either (Neg a) (Pos c))
    assoc1 = R $ \v -> case v of 
      Left nb -> (Left (Right nb) , assoc1)
      Right (Left pa) -> (Left (Left pa) , assoc1)
      Right (Right nc) -> (Right nc , assoc1)
    assoc2 = R $ \v -> case v of 
      Left (Left na) -> (Right na , assoc2)
      Left (Right pb) -> (Left (Left pb) , assoc2)
      Right nc -> (Left (Right nc) , assoc2)
    assoc3 = R $ \v -> case v of 
      Left (Left nb) -> (Left nb , assoc3)
      Left (Right pc) -> (Right (Right pc) , assoc3)
      Right na -> (Right (Left na) , assoc3)

plusG :: GM a b -> GM c d -> GM (Either a c) (Either b d)
plusG = undefined

-- dualize :: 
                            
              

-----------------------------------------------------------------------
