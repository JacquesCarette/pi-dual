{-# LANGUAGE GADTs, TypeOperators, DataKinds, RankNTypes #-}
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

newtype R i o = R { r :: i -> (o, R i o) }

idR :: R a a 
idR = R $ \a -> (a, idR)

-- symR :: R a b -> R b a
-- symR (R f) = R $ \b ->  ???

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

instance Pi R where
  idIso        = idR
  sym          = undefined -- ???
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
  type ZeroG = (Zero,Zero)
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

-----------------------------------------------------------------------
{--
Neel's post:
http://semantic-domain.blogspot.com/2012/11/in-this-post-ill-show-how-to-turn.html

See also: 
http://www.kurims.kyoto-u.ac.jp/~hassei/papers/tmcc.pdf
--}