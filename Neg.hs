{-# LANGUAGE GADTs, TypeOperators, DataKinds, RankNTypes #-}
{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS -Wall #-}

module Neg where

import qualified Prelude
import Prelude (Either(..), undefined, error, ($), (.), id)

-----------------------------------------------------------------------
-- Some very abstract kit that will allow lots of different instances
-- First, the two normal monoidal structures
type family Zero (rep :: * -> *) :: *
type family Prod (rep :: * -> *) :: * -> * -> *

type family One (rep :: * -> *) :: *
type family Sum (rep :: * -> *) :: * -> * -> *

-- Second, Polarized is a pair (+A,-A) of positive and negative 'parts'
type family Polarized (rep :: * -> *) :: * -> * -> *

-- Third, Dual and linear functions
type family Dual (rep :: * -> *) :: * -> *
type family Lolli (rep :: * -> *) :: * -> * -> *

-----------------------------------------------------------------------
-- Very general notion of Type

class Type td where
  zeroT  :: td (Zero rep)
  unitT  :: td (One rep)
  pairT  :: td a -> td b -> td (Prod rep a b)
  fstT   :: td (Prod rep a b) -> td a
  sndT   :: td (Prod rep a b) -> td b
  leftT  :: td a -> td (Sum rep a b)
  rightT :: td b -> td (Sum rep a b)
  eithrT :: td (Sum rep a b) -> (td a -> td c) -> (td b -> td c) -> td c

-----------------------------------------------------------------------
-- The abstract type of isomorphisms and their semantics
-- An even more general version of same

class TD rep => Pi iso rep where 
-- Congruence
  idIso       :: iso a a
  sym         :: iso a b -> iso b a
  (%.)        :: iso a b -> iso b c -> iso a c
  (%*)        :: iso a b -> iso c d -> iso (Prod rep a c) (Prod rep b d)
  (%+)        :: iso a b -> iso c d -> iso (Sum rep a c) (Sum rep b d)
-- (+) is associative, commutative, and has a unit
  plusZeroL   :: iso (Sum rep (Zero rep) a) a
  plusZeroR   :: iso a (Sum rep (Zero rep) a)
  commutePlus :: iso (Sum rep a b) (Sum rep b a)
  assocPlusL  :: iso (Sum rep a (Sum rep b c)) (Sum rep (Sum rep a b) c)
  assocPlusR  :: iso (Sum rep (Sum rep a b) c) (Sum rep a (Sum rep b c))
-- (*) is associative, commutative, and has a unit
  timesOneL   :: iso (Prod rep (One rep) a) a
  timesOneR   :: iso a (Prod rep (One rep) a)
  commuteTimes:: iso (Prod rep a b) (Prod rep b a) 
  assocTimesL :: iso (Prod rep a (Prod rep b c)) (Prod rep (Prod rep a b) c)
  assocTimesR :: iso (Prod rep (Prod rep a b) c) (Prod rep a (Prod rep b c))
-- (*) distributes over (+) 
  timesZeroL  :: iso (Prod rep (Zero rep) a) (Zero rep)
  timesZeroR  :: iso (Zero rep) (Prod rep (Zero rep) a)
  distribute  :: iso (Prod rep (Sum rep b c) a) (Sum rep (Prod rep b a) (Prod rep c a))
  factor      :: iso (Sum rep (Prod rep b a) (Prod rep c a)) (Prod rep (Sum rep b c) a)
-- Trace operators for looping/recursion
  trace       :: iso (Sum rep a b) (Sum rep a c) -> iso b c

-----------------------------------------------------------------------
-- Term model and rewriting semantics

data Void

data a :<=> b where 
  Id           :: a :<=> a
  Sym          :: (a :<=> b) -> (b :<=> a) 
  (:.:)        :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:)        :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:)        :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
  PlusZeroL    :: Either Void a :<=> a
  PlusZeroR    :: a :<=> Either Void a
  CommutePlus  :: Either a b :<=> Either b a
  AssocPlusL   :: Either a (Either b c) :<=> Either (Either a b) c 
  AssocPlusR   :: Either (Either a b) c :<=> Either a (Either b c) 
  TimesOneL    :: ((), a) :<=> a
  TimesOneR    :: a :<=> ((), a)
  CommuteTimes :: (a,b) :<=> (b,a) 
  AssocTimesL  :: (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: ((a,b),c) :<=> (a,(b,c))
  TimesZeroL   :: (Void, a) :<=> Void
  TimesZeroR   :: Void :<=> (Void, a)
  Distribute   :: (Either b c, a) :<=> Either (b, a) (c, a)
  Factor       :: Either (b, a) (c, a) :<=> (Either b c, a)
  Trace        :: (Either a b :<=> Either a c) -> (b :<=> c)

instance Pi (:<=>) I where
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
  zero  :: td Void
  unit  :: td ()
  pair  :: td a -> td b -> td (a,b)
  fst   :: td (a, b) -> td a
  snd   :: td (a, b) -> td b
  left  :: td a -> td (Either a b)
  right :: td b -> td (Either a b)
  eithr :: td (Either a b) -> (td a -> td c) -> (td b -> td c) -> td c

-- Standard interpretation of types

newtype I a = I a

abort :: a
abort = error "Impossible: Empty type"

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

type instance Prod I = (,)
type instance Sum I = Either
type instance Zero I = Void
type instance One I = ()

-- Denotations of isos

class TD td => MD iso td where
  (@!) :: iso a b -> td a -> td b
  (!@) :: iso a b -> td b -> td a

instance TD td => MD (:<=>) td where
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

data R i o = R { r :: i -> (o, R i o), rr :: o -> (i, R o i) }

idR :: R a a 
idR = R f f where f a = (a, idR)

symR :: R a b -> R b a
symR (R f fr) = R fr f

composeR :: R a b -> R b c -> R a c
composeR (R f fr) (R g gr) = R {
  r = \a -> let (b , f') = f a
                (c , g') = g b
            in (c , composeR f' g'),
  rr = \c -> let (b , gr') = gr c
                 (a , fr') = fr b
             in (a , composeR gr' fr') 
  }

timesR :: R a b -> R c d -> R (a,c) (b,d)
timesR (R f fr) (R g gr) = R {
  r = \(a,c) -> let (b , f') = f a
                    (d , g') = g c
                in ((b,d) , timesR f' g'), 
  rr = \(b,d) -> let (a , fr') = fr b
                     (c , gr') = gr d
                 in ((a,c) , timesR fr' gr')
  }

plusR :: R a b -> R c d -> R (Either a c) (Either b d)
plusR (R f fr) (R g gr) = R {
  r = \x -> case x of 
              Left a  -> let (b , f') = f a 
                         in (Left b , plusR f' (R g gr))
              Right c -> let (d , g') = g c
                         in (Right d , plusR (R f fr) g'), 
  rr = \x -> case x of 
              Left b  -> let (a , fr') = fr b 
                         in (Left a , plusR fr' (R gr g))
              Right d -> let (c , gr') = gr d
                         in (Right c , plusR (R fr f) gr')
  }                  

plusZeroLR :: R (Either Void a) a
plusZeroLR = R {
  r = \ (Right a) -> (a , plusZeroLR) ,
  rr = \ a -> (Right a , plusZeroRR)
  } 

plusZeroRR :: R a (Either Void a) 
plusZeroRR = R {
  r = \a -> (Right a , plusZeroRR), 
  rr = \ (Right a) -> (a , plusZeroLR) 
  } 

commutePlusR :: R (Either a b) (Either b a)
commutePlusR = R f fr where
  f (Left a) = (Right a , commutePlusR)
  f (Right b) = (Left b  , commutePlusR)
  fr (Left b) = (Right b , commutePlusR)
  fr (Right a) = (Left a  , commutePlusR)

assocPlusLR :: R (Either a (Either b c)) (Either (Either a b) c)
assocPlusLR = R {
  r = \v -> case v of 
              Left a          -> (Left (Left a)  , assocPlusLR)
              Right (Left b)  -> (Left (Right b) , assocPlusLR)
              Right (Right c) -> (Right c        , assocPlusLR), 
  rr = \v -> case v of 
               Left (Left a)  -> (Left a          , assocPlusRR)
               Left (Right b) -> (Right (Left b)  , assocPlusRR)
               Right c        -> (Right (Right c) , assocPlusRR)
  } 

assocPlusRR :: R (Either (Either a b) c) (Either a (Either b c)) 
assocPlusRR = R {
  r = \v -> case v of 
              Left (Left a)  -> (Left a          , assocPlusRR)
              Left (Right b) -> (Right (Left b)  , assocPlusRR)
              Right c        -> (Right (Right c) , assocPlusRR),
  rr = \v -> case v of 
              Left a          -> (Left (Left a)  , assocPlusLR)
              Right (Left b)  -> (Left (Right b) , assocPlusLR)
              Right (Right c) -> (Right c        , assocPlusLR)
  }

timesOneLR :: R ((),a) a
timesOneLR = R {
  r = \((),a) -> (a , timesOneLR), 
  rr = \a -> (((),a) , timesOneRR)
  }

timesOneRR :: R a ((),a)
timesOneRR = R {
  r = \a -> (((),a) , timesOneRR),
  rr = \((),a) -> (a , timesOneLR)
  }

commuteTimesR :: R (a,b) (b,a)
commuteTimesR = R {
  r = \(a,b) -> ((b,a) , commuteTimesR),
  rr = \(b,a) -> ((a,b) , commuteTimesR)
  }

assocTimesLR :: R (a,(b,c)) ((a,b),c)
assocTimesLR = R {
  r = \(a,(b,c)) -> (((a,b),c) , assocTimesLR),
  rr = \((a,b),c) -> ((a,(b,c)) , assocTimesRR)
  } 

assocTimesRR :: R ((a,b),c) (a,(b,c))
assocTimesRR = R {
  r = \((a,b),c) -> ((a,(b,c)) , assocTimesRR),
  rr = \(a,(b,c)) -> (((a,b),c) , assocTimesLR)
  } 

timesZeroLR :: R (Void,a) Void
timesZeroLR = R {
  r = \_ -> abort,
  rr = \_ -> abort
  }

timesZeroRR :: R Void (Void,a)
timesZeroRR = R {
  r = \_ -> abort,
  rr = \_ -> abort
  }

distributeR :: R (Either b c , a) (Either (b,a) (c,a))
distributeR = R {
  r = \(v,a) -> case v of 
                  Left b  -> (Left (b,a) , distributeR)
                  Right c -> (Right (c,a) , distributeR),
  rr = \v -> case v of 
               Left (b,a)  -> ((Left b, a)  , factorR)
               Right (c,a) -> ((Right c, a) , factorR)
  }

factorR :: R (Either (b,a) (c,a)) (Either b c , a)
factorR = R {
  r = \v -> case v of 
               Left (b,a)  -> ((Left b, a)  , factorR)
               Right (c,a) -> ((Right c, a) , factorR),
  rr = \(v,a) -> case v of 
                  Left b  -> (Left (b,a) , distributeR)
                  Right c -> (Right (c,a) , distributeR)
  }

traceR :: R (Either a b) (Either a c) -> R b c
traceR f = R {
  r = \b -> loop1 f (Right b),
  rr = \c -> loop2 f (Right c)
  } 
  where 
    loop1 :: R (Either a b) (Either a c) -> Either a b -> (c , R b c)
    loop1 (R g _) v = case g v of
                        (Left a  , f') -> loop1 f' (Left a)
                        (Right c , f') -> (c , traceR f')

    loop2 :: R (Either a b) (Either a c) -> Either a c -> (b , R c b) 
    loop2 (R _ gr) v = case gr v of
                         (Left a  , g') -> loop1 g' (Left a)
                         (Right b , g') -> (b , traceR g')

instance Pi R I where
  idIso        = idR
  sym          = symR
  (%.)         = composeR
  (%*)         = timesR
  (%+)         = plusR
  plusZeroL    = plusZeroLR
  plusZeroR    = plusZeroRR
  commutePlus  = commutePlusR
  assocPlusL   = assocPlusLR
  assocPlusR   = assocPlusRR
  timesOneL    = timesOneLR
  timesOneR    = timesOneRR
  commuteTimes = commuteTimesR
  assocTimesL  = assocTimesLR
  assocTimesR  = assocTimesRR
  timesZeroL   = timesZeroLR
  timesZeroR   = timesZeroRR
  distribute   = distributeR
  factor       = factorR
  trace        = traceR
  
{--
-----------------------------------------------------------------------
-- Int (or G) construction

-- Objects in the G category are pairs of objects 

class GT p where
  type Pos p      :: *  -- to access the components
  type Neg p      :: *  
  type ZeroG      :: *  -- the new structure 0,1,+,* 
  type OneG       :: *
  type PlusG p q  :: *
  type TimesG p q :: *
  type DualG p    :: *  -- as a bonus we get DualG (unary negation) and
  type LolliG p q :: *  -- linear functions

data Pair a b = P a b

instance GT (ap,am) where
  type Pos (ap,am) = ap
  type Neg (ap,am) = am
  type ZeroG = (Void,Void)
  type OneG = ((),())
  type PlusG (ap,am) (bp,bm) = (Either ap bp , Either am bm)
  type TimesG (ap,am) (bp,bm) = 
    (Either (Pair ap bp) (Pair am bm), Either (Pair am bp) (Pair ap bm))
  type DualG (ap,am) = (am,ap)
  type LolliG (ap,am) (bp,bm) = (Either am bp , Either ap bm)
                              -- PlusG (DualG (ap,am)) (bp,bm)

-- Morphisms in the G category

newtype GM a b = 
  GM { rg :: R (Either (Pos a) (Neg b)) (Either (Neg a) (Pos b)) } 

-- 

idG :: GM a a
idG = GM commutePlusR

symG :: GM a b -> GM b a
symG = undefined

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

timesG :: GM a b -> GM c d -> GM (TimesG a c) (TimesG b c)
timesG = undefined

plusG :: (Neg (PlusG b d) ~ Either (Neg b) (Neg d),
          Neg (PlusG a c) ~ Either (Neg a) (Neg c),
          Pos (PlusG a c) ~ Either (Pos a) (Pos c),
          Pos (PlusG b d) ~ Either (Pos b) (Pos d)) =>
         GM a b -> GM c d -> GM (PlusG a c) (PlusG b d)
plusG (GM f) (GM g) = GM h
  where
    (>>) = composeR
    h = 
    -- Either (Either ap cp) (Either bm dm)
       assoc1 >>
    -- Either (Either ap bm) (Either cp dm)
       plusR f g >>
    -- Either (Either am bp) (Either cm dp)
       assoc2 
    -- Either (Either am cm) (Either bp dp)
    assoc1 = R $ \v -> case v of 
      Left (Left ap) -> (Left (Left ap) , assoc1)
      Left (Right cp) -> (Right (Left cp) , assoc1)
      Right (Left bm) -> (Left (Right bm) , assoc1)
      Right (Right dm) -> (Right (Right dm) , assoc1)
    assoc2 = R $ \v -> case v of 
      Left (Left am) -> (Left (Left am) , assoc2)
      Left (Right bp) -> (Right (Left bp) , assoc2)
      Right (Left cm) -> (Left (Right cm) , assoc2)
      Right (Right dp) -> (Right (Right dp) , assoc2)

-- If we instantiate the abstract G types to pairs, the contraints are
-- automatically satisfied.
test :: GM (ap,am) (bp,bm) -> GM (cp,cm) (dp,dm) -> 
        GM (PlusG (ap,am) (cp,cm)) (PlusG (bp,bm) (dp,dm))
test = plusG 

plusZeroLG :: GM (PlusG ZeroG a) a
plusZeroLG = undefined

plusZeroRG :: GM a (PlusG ZeroG a)
plusZeroRG = undefined

commutePlusG :: GM (PlusG a b) (PlusG b a)
commutePlusG = undefined

assocPlusLG :: GM (PlusG a (PlusG b c)) (PlusG (PlusG a b) c)
assocPlusLG = undefined

assocPlusRG :: GM (PlusG (PlusG a b) c) (PlusG a (PlusG b c))
assocPlusRG = undefined

timesOneLG :: GM (TimesG OneG a) a
timesOneLG = undefined

timesOneRG :: GM a (TimesG OneG a)
timesOneRG = undefined

commuteTimesG :: GM (TimesG a b) (TimesG b a)
commuteTimesG = undefined

assocTimesLG :: GM (TimesG a (TimesG b c)) (TimesG (TimesG a b) c)
assocTimesLG = undefined

assocTimesRG :: GM (TimesG (TimesG a b) c) (TimesG a (TimesG b c))
assocTimesRG = undefined

timesZeroLG :: GM (TimesG ZeroG a) ZeroG
timesZeroLG = undefined

timesZeroRG :: GM ZeroG (TimesG ZeroG a)
timesZeroRG = undefined

distributeG :: GM (TimesG (PlusG b c) a) (PlusG (TimesG b a) (TimesG c a))
distributeG = undefined

factorG :: GM (PlusG (TimesG b a) (TimesG c a)) (TimesG (PlusG b c) a)
factorG = undefined

traceG :: GM (PlusG a b) (PlusG a c) -> GM b c
traceG = undefined

dualG :: (Pos (DualG a) ~ Neg a, Pos (DualG b) ~ Neg b, 
          Neg (DualG a) ~ Pos a, Neg (DualG b) ~ Pos b) => 
         GM a b -> GM (DualG b) (DualG a)
dualG (GM (R f)) = GM (dual f) 
  where dual h = R $ \v -> 
                 let (v',_) = h (swap v)
                 in (swap v', dual h)
        swap (Left a) = Right a
        swap (Right a) = Left a
                            
curryG :: (Pos (PlusG a b) ~ Either (Pos a) (Pos b),
           Neg (PlusG a b) ~ Either (Neg a) (Neg b),
           Pos (LolliG b c) ~ Either (Neg b) (Pos c),
           Neg (LolliG b c) ~ Either (Pos b) (Neg c)) =>
          GM (PlusG a b) c -> GM a (LolliG b c)
curryG (GM f) = GM (curry f)
  where curry (R h) = R $ \v -> 
          let (v',h') = h (assoc1 v)
              v'' = assoc2 v'
          in (v'' , curry h')
        assoc1 (Left v) = Left (Left v)
        assoc1 (Right (Left v)) = Left (Right v)
        assoc1 (Right (Right v)) = Right v
        assoc2 (Left (Left v)) = Left v
        assoc2 (Left (Right v)) = Right (Left v)
        assoc2 (Right v) = Right (Right v)
                                   
uncurryG :: (Pos (PlusG a b) ~ Either (Pos a) (Pos b),
             Neg (PlusG a b) ~ Either (Neg a) (Neg b),
             Pos (LolliG b c) ~ Either (Neg b) (Pos c),
             Neg (LolliG b c) ~ Either (Pos b) (Neg c)) => 
            GM a (LolliG b c) -> GM (PlusG a b) c
uncurryG (GM f) = GM (uncurry f) 
  where uncurry (R h) = R $ \v -> 
          let (v',h') = h (assoc2 v)
              v'' = assoc1 v'
          in (v'' , uncurry h')
        assoc1 (Left v) = Left (Left v)
        assoc1 (Right (Left v)) = Left (Right v)
        assoc1 (Right (Right v)) = Right v
        assoc2 (Left (Left v)) = Left v
        assoc2 (Left (Right v)) = Right (Left v)
        assoc2 (Right v) = Right (Right v)
--}
-----------------------------------------------------------------------
{--
Neel's post:
http://semantic-domain.blogspot.com/2012/11/in-this-post-ill-show-how-to-turn.html

See also: 
http://www.kurims.kyoto-u.ac.jp/~hassei/papers/tmcc.pdf
--}
