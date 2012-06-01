{-# OPTIONS_GHC -XTypeOperators  #-}
{-# OPTIONS_GHC -XGADTs          #-}
{-# OPTIONS_GHC -XEmptyDataDecls #-} 

-- eta+/epsilon+ undefined in this model

module ND where

import Control.Monad

------------------------------------------------------------------------------
-- Base types 
-- 1, t+t, t*t are modeled using built-in Haskell types
-- 0, -t, 1/t are modeled using the following types

data Zero -- empty type

data Inv a = Inv a deriving Eq -- fractional types (a should not be zero) 

data Neg a = Neg a deriving Eq -- negative types

instance Show Zero where 
  show _ = error "Empty type has no values to show"

instance Eq Zero where 
  _ == _ = error "Cannot use == at type 0"

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

instance V a => V (Neg a) where
  elems = map Neg elems

instance V a => V (Inv a) where
  elems = map Inv elems

------------------------------------------------------------------------------
-- Isomorphisms 

data a :<=> b where 
-- Congruence
  Id    :: V a => a :<=> a
  (:.:) :: (V a, V b, V c) => (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (V a, V b, V c, V d) => 
             (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (V a, V b, V c, V d) => 
             (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- (+) is associative, commutative, and has a unit
  ZeroE       :: V a => Either Zero a :<=> a
  ZeroI       :: V a => a :<=> Either Zero a
  CommutePlus :: (V a, V b) => Either a b :<=> Either b a
  AssocPlusL  :: (V a, V b, V c) => 
                   Either a (Either b c) :<=> Either (Either a b) c 
  AssocPlusR  :: (V a, V b, V c) => 
                   Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE        :: V a => ((), a) :<=> a
  UnitI        :: V a => a :<=> ((), a)
  CommuteTimes :: (V a, V b) => (a,b) :<=> (b,a) 
  AssocTimesL  :: (V a, V b, V c) => (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: (V a, V b, V c) => ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  TimesZeroL  :: V a => (Zero, a) :<=> Zero
  TimesZeroR  :: V a => Zero :<=> (Zero, a)
  Distribute  :: (V a, V b, V c) => 
                   (Either b c, a) :<=> Either (b, a) (c, a)
  Factor      :: (V a, V b, V c) => 
                   Either (b, a) (c, a) :<=> (Either b c, a)
-- Additive inverses
  EtaPlus :: V a => Zero :<=> (Either (Neg a) a)
  EpsPlus :: V a => (Either (Neg a) a) :<=> Zero
-- Multiplicative inverses (a cannot be 0) 
  EtaTimes :: V a => () :<=> (Inv a, a)
  EpsTimes :: V a => (Inv a, a) :<=> ()

adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint (f :.: g) = adjoint g :.: adjoint f
adjoint (f :*: g) = adjoint f :*: adjoint g
adjoint (f :+: g) = adjoint f :+: adjoint g
adjoint ZeroE = ZeroI
adjoint ZeroI = ZeroE
adjoint CommutePlus = CommutePlus
adjoint AssocPlusL = AssocPlusR
adjoint AssocPlusR = AssocPlusL
adjoint UnitE = UnitI
adjoint UnitI = UnitE
adjoint CommuteTimes = CommuteTimes
adjoint AssocTimesL = AssocTimesR
adjoint AssocTimesR = AssocTimesL
adjoint TimesZeroL = TimesZeroR
adjoint TimesZeroR = TimesZeroL
adjoint Distribute = Factor
adjoint Factor = Distribute
adjoint EtaPlus = EpsPlus
adjoint EpsPlus = EtaPlus
adjoint EtaTimes = EpsTimes
adjoint EpsTimes = EtaTimes

------------------------------------------------------------------------------
-- Non-determinism monad (implemented using []) 
-- 
-- We have non-determinism because of eta*/epsilon*. In particular eta*
-- non-deterministically maps () to (1/v,v) to where v is a value of the
-- appropriate type; epsilon* takes a pair (1/v',v) and checks whether
-- v==v'. If so we return () and otherwise we fail.

eval_iso1 :: (V a, V b) => (a :<=> b) -> a -> [b]

eval_iso1 Id a = return a

eval_iso1 (f :.: g) a = do b <- eval_iso1 f a 
                           eval_iso1 g b

eval_iso1 (f :*: g) (a,c) = do b <- eval_iso1 f a 
                               d <- eval_iso1 g c
                               return (b,d) 

eval_iso1 (f :+: g) v = 
  case v of 
    Left a -> do b <- eval_iso1 f a
                 return (Left b) 
    Right c -> do d <- eval_iso1 g c
                  return (Right d) 

-- ZeroE @@ (Right a) = a
eval_iso1 ZeroE v = 
  case v of 
    Right a -> return a
    Left _ -> error "Impossible: ZeroE applied to Left"

-- ZeroI @@ a = Right a
eval_iso1 ZeroI v = return (Right v) 

-- CommutePlus @@ (Left a) = Right a
-- CommutePlus @@ (Right b) = Left b 
eval_iso1 CommutePlus v = 
  case v of 
    Left a -> return (Right a) 
    Right b -> return (Left b) 

-- AssocPlusL @@ (Left a) = Left (Left a) 
-- AssocPlusL @@ (Right (Left b)) = Left (Right b) 
-- AssocPlusL @@ (Right (Right c)) = Right c
eval_iso1 AssocPlusL v = 
  case v of 
    Left a -> return (Left (Left a)) 
    Right (Left b) -> return (Left (Right b))
    Right (Right c) -> return (Right c) 

-- AssocPlusR @@ (Left (Left a)) = Left a
-- AssocPlusR @@ (Left (Right b)) = Right (Left b)
-- AssocPlusR @@ (Right c) = Right (Right c)
eval_iso1 AssocPlusR v = 
  case v of 
    Left (Left a) -> return (Left a)
    Left (Right b) -> return (Right (Left b)) 
    Right c -> return (Right (Right c))

-- UnitE @@ ((), a) = a
eval_iso1 UnitE ((),a) = return a

-- UnitI @@ a = ((), a)
eval_iso1 UnitI v = return ((),v) 

-- CommuteTimes @@ (a,b) = (b,a) 
eval_iso1 CommuteTimes (a,b) = return (b,a) 

-- AssocTimesL @@ (a,(b,c)) = ((a,b),c) 
eval_iso1 AssocTimesL (a,(b,c)) = return ((a,b),c) 

-- AssocTimesR @@ ((a,b),c)  = (a,(b,c))
eval_iso1 AssocTimesR ((a,b),c) = return (a,(b,c)) 

--  TimesZeroL  :: V a => (Zero, a) :<=> Zero
eval_iso1 TimesZeroL _ = error "Impossible: TimesZeroL applied"

--  TimesZeroR  :: V a => Zero :<=> (Zero,a)
eval_iso1 TimesZeroR _ = error "Impossible: TimesZeroR applied"

-- Distribute @@ (Left b, a) = Left (b,a) 
-- Distribute @@ (Right c, a) = Right (c,a) 
eval_iso1 Distribute v = 
  case v of 
    (Left b, a) -> return (Left (b,a)) 
    (Right c, a) -> return (Right (c,a)) 

-- Factor @@ (Left (b, a)) = (Left b, a) 
-- Factor @@ (Right (c, a)) = (Right c, a) 
eval_iso1 Factor v = 
  case v of 
    Left (b,a) -> return (Left b, a) 
    Right (c,a) -> return (Right c, a) 

-- eta times
eval_iso1 EtaTimes () = msum [ return (Inv a, a) | a <- elems] 

-- epsilon times
eval_iso1 EpsTimes (Inv a, a') | a == a' = return ()
                               | otherwise = mzero

-- eta plus :: Zero :<=> (Either (Neg a) a)
eval_iso1 EtaPlus _ = error "Impossible: eta+ encountered in forward eval"

-- epsilon plus :: (Either (Neg a) a) :<=> Zero
eval_iso1 EpsPlus v = undefined

-- If the input is non-deterministic use:

eval_iso :: (V a, V b) => (a :<=> b) -> [a] -> [b] 
eval_iso c xs = xs >>= eval_iso1 c

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
test1 = eval_iso1 cohTimes (Left ())
test2 = eval_iso1 cohTimes (Right ())

cohPlus :: V a => a :<=> a
cohPlus = ZeroI                      
          :.: (EtaPlus :+: Id)       
          :.: (CommutePlus :+: Id)  
          :.: AssocPlusR            
          :.: (Id :+: EpsPlus)      
          :.: CommutePlus
          :.: ZeroE                  

test3, test4 :: [B]
test3 = eval_iso1 cohPlus (Left ())
test4 = eval_iso1 cohPlus (Right ())

------------------------------------------------------------------------------
