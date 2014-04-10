{-# LANGUAGE GADTs, TypeOperators #-} 

module Neg where

-----------------------------------------------------------------------
-- Isomorphisms 

data Zero 

data a :<=> b where 
-- Congruence
  Id          :: a :<=> a
  Sym         :: (a :<=> b) -> (b :<=> a) 
  (:.:)       :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:)       :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:)       :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
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
-- Trance operators for looping/recursion
  TracePlus   :: (Either a b1 :<=> Either a b2) -> (b1 :<=> b2)

-- Semantics
(@@>) :: (a :<=> b) -> a -> b
Id @@> a                         = a
(Sym f) @@> b                    = f @@< b
(f :.: g) @@> a                  = g @@> (f @@> a)
(f :*: g) @@> (a,b)              = (f @@> a, g @@> b) 
(f :+: g) @@> (Left a)           = Left (f @@> a) 
(f :+: g) @@> (Right b)          = Right (g @@> b) 
PlusZeroL @@> (Right a)          = a
PlusZeroR @@> a                  = Right a
CommutePlus @@> (Left a)         = Right a
CommutePlus @@> (Right b)        = Left b 
AssocPlusL @@> (Left a)          = Left (Left a) 
AssocPlusL @@> (Right (Left b))  = Left (Right b) 
AssocPlusL @@> (Right (Right c)) = Right c
AssocPlusR @@> (Left (Left a))   = Left a
AssocPlusR @@> (Left (Right b))  = Right (Left b)
AssocPlusR @@> (Right c)         = Right (Right c)
TimesOneL @@> ((), a)            = a
TimesOneR @@> a                  = ((), a)
CommuteTimes @@> (a,b)           = (b,a) 
AssocTimesL @@> (a,(b,c))        = ((a,b),c) 
AssocTimesR @@> ((a,b),c)        = (a,(b,c))
TimesZeroL @@> _                 = error "Impossible: empty type"
TimesZeroR @@> _                 = error "Impossible: empty type"
Distribute @@> (Left b, a)       = Left (b, a) 
Distribute @@> (Right c, a)      = Right (c, a) 
Factor @@> (Left (b, a))         = (Left b, a) 
Factor @@> (Right (c, a))        = (Right c, a) 
(TracePlus c) @@> v              = loop c (c @@> (Right v))
    where
      loop c (Left v) = loop c (c @@> (Left v))
      loop c (Right v) = v

(@@<) :: (a :<=> b) -> b -> a
Id @@< b                         = b
(Sym f) @@< a                    = f @@> a
(f :.: g) @@< b                  = f @@< (g @@< b)
(f :*: g) @@< (a,b)              = (f @@< a, g @@< b) 
(f :+: g) @@< (Left a)           = Left (f @@< a) 
(f :+: g) @@< (Right b)          = Right (g @@< b) 
PlusZeroL @@< a                  = Right a
PlusZeroR @@< (Right a)          = a
CommutePlus @@< (Left a)         = Right a
CommutePlus @@< (Right b)        = Left b 
AssocPlusL @@< (Left (Left a))   = Left a
AssocPlusL @@< (Left (Right b))  = Right (Left b)
AssocPlusL @@< (Right c)         = Right (Right c)
AssocPlusR @@< (Left a)          = Left (Left a) 
AssocPlusR @@< (Right (Left b))  = Left (Right b) 
AssocPlusR @@< (Right (Right c)) = Right c
TimesOneL @@< a                  = ((), a)
TimesOneR @@< ((), a)            = a
CommuteTimes @@< (a,b)           = (b,a) 
AssocTimesL @@< ((a,b),c)        = (a,(b,c))
AssocTimesR @@< (a,(b,c))        = ((a,b),c) 
TimesZeroL @@< _                 = error "Impossible: empty type"
TimesZeroR @@< _                 = error "Impossible: empty type"
Distribute @@< (Left (b, a))     = (Left b, a) 
Distribute @@< (Right (c, a))    = (Right c, a) 
Factor @@< (Left b, a)           = Left (b, a) 
Factor @@< (Right c, a)          = Right (c, a) 
(TracePlus c) @@< v              = loop c (c @@< (Right v))
    where
      loop c (Left v) = loop c (c @@< (Left v))
      loop c (Right v) = v

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
