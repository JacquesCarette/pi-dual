{-# OPTIONS_GHC -XTypeOperators  #-}
{-# OPTIONS_GHC -XGADTs          #-}

-- Fractional types introduce non-determinism; instead of having one value we
-- have a sequence of possible values

module ND where

import Prelude hiding (id)
import Control.Monad
import Lang hiding (PiInv(..))

-- Returns a list of all the elements of the type

class Eq a => V a where
  elems :: [a]

instance V Zero where
  elems = []

instance V () where
  elems = [()] 

instance (V a, V b) => V (Either a b) where
  elems = map Left elems ++ map Right elems

instance (V a, V b) => V (a,b) where
  elems = [(a,b) | a <- elems, b <- elems] 

instance V a => V (Inv a) where
  elems = map Inv elems

data a :<=> b where 
-- Congruence
  Id    :: a :<=> a
  (:.:) :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- (+) is associative, commutative, and has a unit
  ZeroE       :: Either Zero a :<=> a
  ZeroI       :: a :<=> Either Zero a
  CommutePlus :: Either a b :<=> Either b a
  AssocPlusL  :: Either a (Either b c) :<=> Either (Either a b) c 
  AssocPlusR  :: Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE        :: ((), a) :<=> a
  UnitI        :: a :<=> ((), a)
  CommuteTimes :: (a,b) :<=> (b,a) 
  AssocTimesL  :: (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  TimesZeroL  :: (Zero, a) :<=> Zero
  TimesZeroR  :: Zero :<=> (Zero, a)
  Distribute  :: (Either b c, a) :<=> Either (b, a) (c, a)
  Factor      :: Either (b, a) (c, a) :<=> (Either b c, a)
-- Multiplicative inverses (a cannot be 0) 
  EtaTimes :: V a => () :<=> (Inv a, a)
  EpsTimes :: Eq a => (Inv a, a) :<=> ()

instance Pi (:<=>) where
  id = Id
  (%.) = (:.:)
  (%*) = (:*:)
  (%+) = (:+:)
  plusZeroL = ZeroE
  plusZeroR = ZeroI
  commutePlus = CommutePlus
  assocPlusL = AssocPlusL
  assocPlusR = AssocPlusR
  timesOneL = UnitE
  timesOneR = UnitI
  commuteTimes = CommuteTimes
  assocTimesL = AssocTimesL
  assocTimesR = AssocTimesR
  timesZeroL = TimesZeroL
  timesZeroR = TimesZeroR
  distribute = Distribute
  factor = Factor

class Pi eq => PiInv eq where
-- etaTimes, epsTimes
  etaTimes :: V a => eq () (Inv a,a)
  epsTimes :: Eq a => eq (Inv a, a) ()

instance PiInv (:<=>) where
  etaTimes = EtaTimes
  epsTimes = EpsTimes

------------------------------------------------------------------------------
-- Non-determinism monad (implemented using []) 
-- 
-- We have non-determinism because of eta*/epsilon*. In particular eta*
-- non-deterministically maps () to (1/v,v) to where v is a value of the
-- appropriate type; epsilon* takes a pair (1/v',v) and checks whether
-- v==v'. If so we return () and otherwise we fail.

class Pi eq => EvIso eq where
  eval :: eq a b -> a -> [b]

instance EvIso (:<=>) where
  eval Id a = return a
  eval (f :.: g) a = do b <- eval f a 
                        eval g b
  eval (f :*: g) (a,c) = do b <- eval f a
                            d <- eval g c
                            return (b,d)
  eval (f :+: g) v = 
    case v of 
      Left a -> do b <- eval f a
                   return (Left b)
      Right c -> do b <- eval g c 
                    return (Right b)
  -- ZeroE @@ (Right a) = a
  eval ZeroE v = 
    case v of 
      Right a -> return a
      Left _ -> error "Impossible: ZeroE applied to Left"

  -- ZeroI @@ a = Right a
  eval ZeroI v = return (Right v) 

  -- CommutePlus @@ (Left a) = Right a
  -- CommutePlus @@ (Right b) = Left b 
  eval CommutePlus v = 
    case v of 
      Left a -> return (Right a) 
      Right b -> return (Left b) 

  -- AssocPlusL @@ (Left a) = Left (Left a) 
  -- AssocPlusL @@ (Right (Left b)) = Left (Right b) 
  -- AssocPlusL @@ (Right (Right c)) = Right c
  eval AssocPlusL v = 
    case v of 
      Left a -> return (Left (Left a)) 
      Right (Left b) -> return (Left (Right b))
      Right (Right c) -> return (Right c) 

  -- AssocPlusR @@ (Left (Left a)) = Left a
  -- AssocPlusR @@ (Left (Right b)) = Right (Left b)
  -- AssocPlusR @@ (Right c) = Right (Right c)
  eval AssocPlusR v = 
    case v of 
      Left (Left a) -> return (Left a)
      Left (Right b) -> return (Right (Left b)) 
      Right c -> return (Right (Right c))

  -- UnitE @@ ((), a) = a
  eval UnitE ((),a) = return a

  -- UnitI @@ a = ((), a)
  eval UnitI v = return ((),v) 
  
  -- CommuteTimes @@ (a,b) = (b,a) 
  eval CommuteTimes (a,b) = return (b,a) 

  -- AssocTimesL @@ (a,(b,c)) = ((a,b),c) 
  eval AssocTimesL (a,(b,c)) = return ((a,b),c) 

  -- AssocTimesR @@ ((a,b),c)  = (a,(b,c))
  eval AssocTimesR ((a,b),c) = return (a,(b,c)) 

  --  TimesZeroL  :: V a => (Zero, a) :<=> Zero
  eval TimesZeroL _ = error "Impossible: TimesZeroL applied"

  --  TimesZeroR  :: V a => Zero :<=> (Zero,a)
  eval TimesZeroR _ = error "Impossible: TimesZeroR applied"

  -- Distribute @@ (Left b, a) = Left (b,a) 
  -- Distribute @@ (Right c, a) = Right (c,a) 
  eval Distribute v = 
    case v of 
      (Left b, a) -> return (Left (b,a)) 
      (Right c, a) -> return (Right (c,a)) 

  -- Factor @@ (Left (b, a)) = (Left b, a) 
  -- Factor @@ (Right (c, a)) = (Right c, a) 
  eval Factor v = 
    case v of 
      Left (b,a) -> return (Left b, a) 
      Right (c,a) -> return (Right c, a) 

  -- eta times 
  -- if EtaTimes is used at the empty, the list elems is empty and EtaTimes ()
  -- returns mzero
  eval EtaTimes () = msum [ return (Inv a, a) | a <- elems] 

  -- epsilon times
  eval EpsTimes (Inv a, a') | a == a' = return ()
                            | otherwise = mzero

-- If the input is non-deterministic use:

eval_iso :: (V a, V b) => (a :<=> b) -> [a] -> [b] 
eval_iso c xs = xs >>= eval c

------------------------------------------------------------------------------
-- Examples

type B = Either () ()

cohTimes :: V a => a :<=> a           -- [v]
cohTimes = UnitI                      -- [((),v)]
           :.: (EtaTimes :*: Id)      -- [((1/v),v),v)] ++ [((1/v',v'),v)]
           :.: (CommuteTimes :*: Id)  -- [((v,1/v),v)] ++ [((v',1/v'),v)]
           :.: AssocTimesR            -- [(v,(1/v,v))] ++ [(v',(1/v',v))]
           :.: (Id :*: EpsTimes)      -- [(v,())] ++ []
           :.: CommuteTimes           -- [((),v)]
           :.: UnitE                  -- [v]

test1, test2 :: [B]
test1 = eval cohTimes (Left ())
test2 = eval cohTimes (Right ())

cohTimesG :: (Eq a, V a, PiInv eq) => eq a a
cohTimesG = timesOneR
      %. (etaTimes %* id)
      %. (commuteTimes %* id)
      %. assocTimesR
      %. (id %* epsTimes)
      %. commuteTimes
      %. timesOneL

justTimes1 :: (V a, PiInv eq) => eq d ((Inv a, a), d)
justTimes1 = timesOneR %. (etaTimes %* id)

justTimes2 :: (V a, V b) => a :<=> ((Inv b, b), a)
justTimes2 = UnitI :.: (EtaTimes :*: Id)

-- can't convince GHC of this, even without monomorphism
-- test4 :: (V a) => [((Inv a,a), (B,B))]
-- test4 = eval justTimes1 (Left (), Right ())

test5 :: V a => [((Inv a, a), (B,B))]
test5 = eval justTimes2 (Left (), Right ())

------------------------------------------------------------------------------
