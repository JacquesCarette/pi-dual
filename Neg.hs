{-# LANGUAGE GADTs, TypeOperators #-} 

module Neg where

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
  left  :: td a -> td (Either a b)
  right :: td b -> td (Either a b)

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
  left  (I a)       = I (Left a)
  right (I b)       = I (Right b)
  
instance MD (:<=>) where
{--
  Id @! a = a
  (Sym f) @! b                    = f !@ b
  (f :.: g) @! a                  = g @! (f @! a)
  (f :*: g) @! (a,b)              = (f @! a, g @! b) 
  (f :+: g) @! (Left a)           = Left (f @! a) 
  (f :+: g) @! (Right b)          = Right (g @! b) 
  PlusZeroL @! (Right a)          = a
--}
  PlusZeroR @! a                  = right a
  CommutePlus @! (Left a)         = right a
  CommutePlus @! (Right b)        = left b 
{--
  AssocPlusL @! (Left a)          = Left (Left a) 
  AssocPlusL @! (Right (Left b))  = Left (Right b) 
  AssocPlusL @! (Right (Right c)) = Right c
  AssocPlusR @! (Left (Left a))   = Left a
  AssocPlusR @! (Left (Right b))  = Right (Left b)
  AssocPlusR @! (Right c)         = Right (Right c)
  TimesOneL @! ((), a)            = a
  TimesOneR @! a                  = ((), a)
  CommuteTimes @! (a,b)           = (b,a) 
  AssocTimesL @! (a,(b,c))        = ((a,b),c) 
  AssocTimesR @! ((a,b),c)        = (a,(b,c))
  TimesZeroL @! _                 = error "Impossible: empty type"
  TimesZeroR @! _                 = error "Impossible: empty type"
  Distribute @! (Left b, a)       = Left (b, a) 
  Distribute @! (Right c, a)      = Right (c, a) 
  Factor @! (Left (b, a))         = (Left b, a) 
  Factor @! (Right (c, a))        = (Right c, a) 
  (TracePlus c) @! v              = loop c (c @! (Right v))
      where
        loop c (Left v) = loop c (c @! (Left v))
        loop c (Right v) = v
--}

  Id !@ (I b)                         = I b
{--
  (Sym f) !@ a                    = f @! a
  (f :.: g) !@ b                  = f !@ (g !@ b)
  (f :*: g) !@ (a,b)              = (f !@ a, g !@ b) 
  (f :+: g) !@ (Left a)           = Left (f !@ a) 
  (f :+: g) !@ (Right b)          = Right (g !@ b) 
  PlusZeroL !@ a                  = Right a
  PlusZeroR !@ (Right a)          = a
  CommutePlus !@ (Left a)         = Right a
  CommutePlus !@ (Right b)        = Left b 
  AssocPlusL !@ (Left (Left a))   = Left a
  AssocPlusL !@ (Left (Right b))  = Right (Left b)
  AssocPlusL !@ (Right c)         = Right (Right c)
  AssocPlusR !@ (Left a)          = Left (Left a) 
  AssocPlusR !@ (Right (Left b))  = Left (Right b) 
  AssocPlusR !@ (Right (Right c)) = Right c
  TimesOneL !@ a                  = ((), a)
  TimesOneR !@ ((), a)            = a
  CommuteTimes !@ (a,b)           = (b,a) 
  AssocTimesL !@ ((a,b),c)        = (a,(b,c))
  AssocTimesR !@ (a,(b,c))        = ((a,b),c) 
  TimesZeroL !@ _                 = error "Impossible: empty type"
  TimesZeroR !@ _                 = error "Impossible: empty type"
  Distribute !@ (Left (b, a))     = (Left b, a) 
  Distribute !@ (Right (c, a))    = (Right c, a) 
  Factor !@ (Left b, a)           = Left (b, a) 
  Factor !@ (Right c, a)          = Right (c, a) 
  (TracePlus c) !@ v              = loop c (c !@ (Right v))
      where
        loop c (Left v) = loop c (c !@ (Left v))
        loop c (Right v) = v
--}

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
  where loop (R f) v = case f v of
                         (Left a , f')  -> loop f' (Left a)
                         (Right c , f') -> (c , traceR f')


-----------------------------------------------------------------------
--}