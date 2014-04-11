{-# LANGUAGE GADTs, TypeOperators #-} 
{-# OPTIONS -Wall #-}

module Neg where

import qualified Prelude
import Prelude (Either(..), undefined, error, ($), (.), id)

-----------------------------------------------------------------------
-- The abstract type of isomorphisms and their semantics

data Zero 

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
  tracePlus    :: iso (Either a b1) (Either a b2) -> iso b1 b2

-- Any semantics must:
--   map each type 'a' to a denotation 'td a'
--   map each iso 'a :<=> b' to a morphism (td a -> td b)

-- denotations of types

class TD td where
  zero  :: td Zero
  unit  :: td ()
  pair  :: td a -> td b -> td (a,b)
  fst   :: td (a, b) -> td a
  snd   :: td (a, b) -> td b
  left  :: td a -> td (Either a b)
  right :: td b -> td (Either a b)
  eithr :: td (Either a b) -> (td a -> td c) -> (td b -> td c) -> td c

-- denotations of isos

class MD iso where
  (@!) :: TD td => iso a b -> td a -> td b
  (!@) :: TD td => iso a b -> td b -> td a

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
  TracePlus    :: (Either a b1 :<=> Either a b2) -> (b1 :<=> b2)

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
  tracePlus    = TracePlus
  
newtype I a = I a

instance TD I where
  zero              = error "Impossible: empty type"
  unit              = I ()
  pair  (I a) (I b) = I (a,b)
  fst   (I (a,_))   = I a
  snd   (I (_,b))   = I b
  left  (I a)       = I (Left a)
  right (I b)       = I (Right b)
  eithr (I (Left a))  = \f _ -> f (I a)
  eithr (I (Right a)) = \_ g -> g (I a)

instance MD (:<=>) where
  Id @! x           = x
  (Sym f) @! b      = f !@ b
  (f :.: g) @! a    = g @! (f @! a)
  (f :*: g) @! x    = pair (f @! (fst x)) (g @! (snd x)) 
  (f :+: g) @! x    = eithr x (left . (f @!)) (right . (g @!))
  PlusZeroL @! x    = eithr x (undefined) (id)
  PlusZeroR @! a    = right a
  CommutePlus @! x  = eithr x right left
  AssocPlusL @! x   = eithr x (left . left) 
                              (\z -> eithr z (left . right) (right))
  AssocPlusR @! x   = eithr x (\z -> eithr z left (right . left)) (right . right)
  TimesOneL @! x    = snd x
  TimesOneR @! x    = pair unit x
  CommuteTimes @! x = pair (snd x) (fst x)
  AssocTimesL @! x  = pair (pair (fst x) (fst (snd x))) (snd (snd x))
  AssocTimesR @! x  = pair (fst (fst x)) (pair (snd (fst x)) (snd x))
  TimesZeroL @! _   = error "Impossible: empty type"
  TimesZeroR @! _   = error "Impossible: empty type"
  Distribute @! x   = eithr (fst x) (\z -> left (pair z (snd x)))
                                    (\z -> right (pair z (snd x)))
  Factor @! x       = eithr x (\z -> pair (left (fst z)) (snd z))
                              (\z -> pair (right (fst z)) (snd z))
  (TracePlus c) @! v = loop (c @! (right v))
      where
        loop w = eithr w (\z -> loop (c @! (left z))) id

  Id !@ x           = x
  (Sym f) !@ b      = f @! b
  (f :.: g) !@ a    = f !@ (g !@ a)
  (f :*: g) !@ x    = pair (f !@ (fst x)) (g !@ (snd x)) 
  (f :+: g) !@ x    = eithr x (left . (f !@)) (right . (g !@))
  PlusZeroL !@ a    = right a
  PlusZeroR !@ x    = eithr x (undefined) (id)
  CommutePlus !@ x  = eithr x right left
  AssocPlusL !@ x   = eithr x (\z -> eithr z left (right . left)) (right . right)
  AssocPlusR !@ x   = eithr x (left . left) 
                              (\z -> eithr z (left . right) (right))
  TimesOneL !@ x    = pair unit x
  TimesOneR !@ x    = snd x
  CommuteTimes !@ x = pair (snd x) (fst x)
  AssocTimesL !@ x  = pair (fst (fst x)) (pair (snd (fst x)) (snd x))
  AssocTimesR !@ x  = pair (pair (fst x) (fst (snd x))) (snd (snd x))
  TimesZeroL !@ _   = error "Impossible: empty type"
  TimesZeroR !@ _   = error "Impossible: empty type"
  Distribute !@ x   = eithr x (\z -> pair (left (fst z)) (snd z))
                              (\z -> pair (right (fst z)) (snd z))
  Factor !@ x       = eithr (fst x) (\z -> left (pair z (snd x)))
                                    (\z -> right (pair z (snd x)))
  (TracePlus c) !@ v = loop (c !@ (right v))
      where
        loop w = eithr w (\z -> loop (c !@ (left z))) id
-----------------------------------------------------------------------
-- Resumptions

data R i o = R (i -> (o, R i o))

idR :: R a a 
idR = R (\a -> (a, idR))

composeR :: R a b -> R b c -> R a c
composeR (R f) (R g) = R $ \a -> 
  let (b , f') = f a
      (c , g') = g b
  in (c , composeR f' g')

plusR :: R a b -> R c d -> R (Either a c) (Either b d)
plusR (R f) (R g) = R $ \x -> 
  case x of 
    Left a  -> let (b , f') = f a 
               in (Left b , plusR f' (R g))
    Right c -> let (d , g') = g c
               in (Right d , plusR (R f) g')

timesR :: R a b -> R c d -> R (a,c) (b,d)
timesR (R f) (R g) = R $ \(a,c) -> 
  let (b , f') = f a
      (d , g') = g c
  in ((b,d) , timesR f' g')

traceR :: R (Either a b) (Either a c) -> R a c
traceR f = R $ \a -> loop f (Left a)
  where loop (R g) v = case g v of
                         (Left a , f')  -> loop f' (Left a)
                         (Right c , f') -> (c , traceR f')

instance Pi R where
  idIso        = idR
  sym          = undefined
  (%.)         = composeR
  (%*)         = timesR
  (%+)         = plusR
  plusZeroL    = undefined
  plusZeroR    = undefined
  commutePlus  = undefined
  assocPlusL   = undefined
  assocPlusR   = undefined
  timesOneL    = undefined
  timesOneR    = undefined
  commuteTimes = undefined
  assocTimesL  = undefined
  assocTimesR  = undefined
  timesZeroL   = undefined
  timesZeroR   = undefined
  distribute   = undefined
  factor       = undefined
  tracePlus    = undefined
  
instance MD R where
  (R f) @! v = undefined
  (R f) !@ v = undefined
  

-----------------------------------------------------------------------
