{-# OPTIONS_GHC -XGADTs -XTypeOperators -XExistentialQuantification #-}
{-# OPTIONS_GHC -XFlexibleContexts -XEmptyDataDecls #-} 

module Dual where

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
  Sym   :: (V a, V b) => (a :<=> b) -> (b :<=> a)
  (:.:) :: (V a, V b, V c) => (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (V a, V b, V c, V d) => (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (V a, V b, V c, V d) => (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
  -- (a :<=> b) -> (Neg a :<=> Neg b) ??
  -- (a :<=> b) -> (Inv a :<=> Inv b) ??
-- (+) is associative, commutative, and has a unit
  ZeroE       :: V a => Either Zero a :<=> a
  ZeroI       :: V a => a :<=> Either Zero a
  CommutePlus :: (V a, V b) => Either a b :<=> Either b a
  AssocPlusL  :: (V a, V b, V c) => Either a (Either b c) :<=> Either (Either a b) c 
  AssocPlusR  :: (V a, V b, V c) => Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE        :: V a => ((), a) :<=> a
  UnitI        :: V a => a :<=> ((), a)
  CommuteTimes :: (V a, V b) => (a,b) :<=> (b,a) 
  AssocTimesL  :: (V a, V b, V c) => (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: (V a, V b, V c) => ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  TimesZeroL  :: V a => (Zero, a) :<=> Zero
  TimesZeroR  :: V a => Zero :<=> (Zero, a)
  Distribute  :: (V a, V b, V c) => (Either b c, a) :<=> Either (b, a) (c, a)
  Factor      :: (V a, V b, V c) => Either (b, a) (c, a) :<=> (Either b c, a)
-- Additive inverses
  EtaPlus :: V a => Zero :<=> (Either (Neg a) a)
  EpsPlus :: V a => (Either (Neg a) a) :<=> Zero
-- Multiplicative inverses (a cannot be 0) 
  EtaTimes :: V a => () :<=> (Inv a, a)
  EpsTimes :: V a => (Inv a, a) :<=> ()

adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint (Sym f) = f
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
-- Non-determisnism monad
-- 
-- We have non-determinism because of eta*/epsilon*. In particular eta* maps
-- () non-deterministically to (1/v,v) to where v is a value of the
-- approriate type; epsilon* takes a pair (1/v',v) and checks whether
-- v==v'. If so we return () and otherwise we fail.

eval_iso :: (V a, V b) => (a :<=> b) -> [a] -> [b] 
eval_iso c xs = xs >>= eval_iso1 c

eval_iso1 :: (V a, V b) => (a :<=> b) -> a -> [b]
eval_iso1 Id a = return a

-- ZeroE @@ (Right a) = a
eval_iso1 ZeroE v = 
  case v of 
    Left _ -> mzero
    Right a -> return a

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

-- Distribute @@ (Left b, a) = Left (b, a) 
-- Distribute @@ (Right c, a) = Right (c, a) 
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

-- epsilon times
eval_iso1 EpsTimes (Inv a, a') | a == a' = return ()
                               | otherwise = mzero

-- eta times
eval_iso1 EtaTimes () = msum [return (Inv a, a) | a <- elems] 

-- epsilon plus
eval_iso1 EpsPlus v = 
  case v of 
    Left (Neg a) -> undefined
    Right a -> undefined

-- eta plus
eval_iso1 EtaPlus _ = undefined


{--

------------------------------------------------------------------------------
-- forward and backward evaluators

-- Evaluation Contexts
-- 
-- These contexts are used in the definition of the composition
-- combinators.

data K a b c d where
    KEmpty :: K a b a b 
    Fst :: (b :<=> c) -> K a c i o -> K a b i o 
    Snd :: (a :<=> b) -> K a c i o -> K b c i o 
    LftPlus :: (c :<=> d) -> K (Either a c) (Either b d) i o -> K a b i o 
    RgtPlus :: (a :<=> b) -> K (Either a c) (Either b d) i o -> K c d i o 
    LftTimes :: V c -> (c :<=> d) -> K (a,c) (b,d) i o -> K a b i o 
    RgtTimes :: (a :<=> b) -> V b -> K (a,c) (b,d) i o -> K c d i o 
     
-- Explore current combinator 
eval_c :: (a :<=> b) -> V a -> K a b c d -> M (V d)

eval_c (Sym f) a k = undefined

-- (f :.: g) @@ a = g @@ (f @@ a)
eval_c (f :.: g) a k = 
    eval_c f a (Fst g k)
         
-- (f :*: g) @@ (a,c) = (f @@ a, g @@ c)
eval_c (f :*: g) v k = 
    do x1 <- freshM 
       x2 <- freshM 
       unifyM (Pr x1 x2) v
       eval_c f x1 (LftTimes x2 g k)

-- (f :+: g) @@ (Left a) = Left (f @@ a) 
-- (f :+: g) @@ (Right b) = Right (g @@ b) 
eval_c (f :+: g) v k = 
    do v1 <- freshM 
       unifyM (L v1) v 
       eval_c f v1 (LftPlus g k)
    `orM`
    do v1 <- freshM 
       unifyM (R v1) v
       eval_c g v1 (RgtPlus f k)

-- eps : switch to the other evaluator
eval_c EpsPlus v k = 
    do v1 <- freshM 
       unifyM (L (Ng v1)) v 
       back_eval_k EpsPlus (R v1) k
    `orM`
    do v1 <- freshM 
       unifyM (R v1) v
       back_eval_k EpsPlus (L (Ng v1)) k

-- all primitive isomorphisms are executed using eval_iso1
eval_c c v k = 
    do v' <- eval_iso1 c v
       eval_k c v' k

-- Explore current stack
eval_k :: (a :<=> b) -> V b -> K a b c d -> M (V d)
eval_k c v KEmpty = return v

eval_k f v (Fst g k) = eval_c g v (Snd f k)
eval_k g v (Snd f k) = eval_k (f :.: g) v k

eval_k f v (LftPlus g k) = 
    do v' <- freshM 
       unifyM v' (L v)
       eval_k (f :+: g) v' k 
eval_k g v (RgtPlus f k) =
    do v' <- freshM 
       unifyM v' (R v)
       eval_k (f :+: g) v' k 
                              
eval_k f v1 (LftTimes v2 g k) = eval_c g v2 (RgtTimes f v1 k)
eval_k g v2 (RgtTimes f v1 k) = 
    do v' <- freshM 
       unifyM v' (Pr v1 v2)
       eval_k (f :*: g) v' k 


-- backward evaluator 

-- Explore the combinator
back_eval_c :: (a :<=> b) -> V b -> K a b c d -> M (V d)

back_eval_c (Sym f) a k = undefined 

-- (f :.: g) @@ a = g @@ (f @@ a)
back_eval_c (f :.: g) a k = 
    back_eval_c g a (Snd f k)
         
-- (f :*: g) @@ (a,c) = (f @@ a, g @@ c)
back_eval_c (f :*: g) v k = 
    do x1 <- freshM 
       x2 <- freshM 
       unifyM (Pr x1 x2) v
       back_eval_c g x2 (RgtTimes f x1 k)

-- (f :+: g) @@ (Left a) = Left (f @@ a) 
-- (f :+: g) @@ (Right b) = Right (g @@ b) 
back_eval_c (f :+: g) v k = 
    do v1 <- freshM 
       unifyM (L v1) v 
       back_eval_c f v1 (LftPlus g k)
    `orM`
    do v1 <- freshM 
       unifyM (R v1) v
       back_eval_c g v1 (RgtPlus f k)

-- eta : switch to the other evaluator
back_eval_c EtaPlus v k = 
    do v1 <- freshM 
       unifyM (L (Ng v1)) v 
       eval_k EtaPlus (R v1) k
    `orM`
    do v1 <- freshM 
       unifyM (R v1) v
       eval_k EtaPlus (L (Ng v1)) k

-- all primitive isomorphisms are executed backwards.
back_eval_c c v k = 
    do v' <- eval_iso1 (adjoint c) v
       back_eval_k c v' k


-- Explore the stack
back_eval_k :: (a :<=> b) -> V a -> K a b c d -> M (V d)
back_eval_k c v KEmpty = error "Cannot terminate in backwards evaluator"

back_eval_k g v (Snd f k) = back_eval_c f v (Fst g k)
back_eval_k f v (Fst g k) = back_eval_k (f :.: g) v k

back_eval_k f v (LftPlus g k) = 
    do v' <- freshM 
       unifyM v' (L v)
       back_eval_k (f :+: g) v' k 
back_eval_k g v (RgtPlus f k) =
    do v' <- freshM 
       unifyM v' (R v)
       back_eval_k (f :+: g) v' k 
                              
back_eval_k g v2 (RgtTimes f v1 k) = back_eval_c f v1 (LftTimes v2 g k)
back_eval_k f v1 (LftTimes v2 g k) = 
    do v' <- freshM 
       unifyM v' (Pr v1 v2)
       back_eval_k (f :*: g) v' k 

-- Note: We could explore an alternate semantics that allows for
-- termination in the backward evaluator.
--  back_eval_k c v KEmpty = return v

------------------------------------------------------------------------------
-- Eval
-- 
-- We use eval to run a Pi computation. Evaluation starts in the
-- forward evaluator with a user supplied value.
eval :: (ToV a, Show (V a)) => (a :<=> b) -> a -> [V b]
eval c v = run (eval_c c (makeV v) KEmpty)

------------------------------------------------------------------------------
--}
