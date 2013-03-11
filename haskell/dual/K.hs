{-# OPTIONS_GHC -XTypeOperators  #-}
{-# OPTIONS_GHC -XGADTs          #-}
{-# OPTIONS_GHC -XEmptyDataDecls #-} 

module K where

-- Negative types introduce some notion of continuations; instead of having
-- one value we have a molecule (Neg b, a) 

------------------------------------------------------------------------------
-- Base types 
-- 1, t+t, t*t are modeled using built-in Haskell types
-- 0, -t, 1/t are modeled using the following types

data Zero -- empty type

data Inv a = Inv a deriving Eq -- fractional types (a should not be zero) 

data Neg a = Neg a deriving Eq

instance Show Zero where 
  show _ = error "Empty type has no values to show"

instance Eq Zero where 
  _ == _ = error "Cannot use == at type 0"

instance Show a => Show (Inv a) where
  show (Inv a) = "1/" ++ show a

instance Show a => Show (Neg a) where
  show (Neg a) = "-" ++ show a

------------------------------------------------------------------------------
-- Isomorphisms 

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
-- Additive inverses
  EtaPlus :: Zero :<=> (Either (Neg a) a)
  EpsPlus :: (Either (Neg a) a) :<=> Zero

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

------------------------------------------------------------------------------
-- eval on plain values

eval :: (a :<=> b) -> a -> b
eval Id a = a 
eval (f :.: g) a = eval g (eval f a)
eval (f :*: g) (a,b) = (eval f a, eval g b) 
eval (f :+: g) (Left a) = Left (eval f a) 
eval (f :+: g) (Right b) = Right (eval g b) 
eval ZeroE (Right a) = a
eval ZeroI a = Right a
eval CommutePlus (Left a) = Right a
eval CommutePlus (Right b) = Left b
eval AssocPlusL (Left a) = Left (Left a)
eval AssocPlusL (Right (Left b)) = Left (Right b)
eval AssocPlusL (Right (Right c)) = Right c
eval AssocPlusR (Left (Left a)) = Left a
eval AssocPlusR (Left (Right b)) = Right (Left b)
eval AssocPlusR (Right c) = Right (Right c)
eval UnitE ((),a) = a
eval UnitI a = ((),a) 
eval CommuteTimes (a,b) = (b,a) 
eval AssocTimesL (a,(b,c)) = ((a,b),c)
eval AssocTimesR ((a,b),c) = (a,(b,c))
eval Distribute (Left b, a) = Left (b,a)
eval Distribute (Right c, a) = Right (c,a)
eval Factor (Left (b,a)) = (Left b, a)
eval Factor (Right (c,a)) = (Right c, a)

--

eval_iso1 :: (a :<=> b) -> (Neg b, a) -> (Neg a, b) 

-- epsilon+ :: V a => (Either (Neg a) a) :<=> Zero
eval_iso1 EpsPlus (Neg z, Left (Neg mv)) = (Neg (Right mv), z)
eval_iso1 EpsPlus (Neg z, Right v) = (Neg (Left (Neg v)), z) 

-- eta+ :: V a => Zero :<=> (Either (Neg a) a)
eval_iso1 EtaPlus (Neg (Left (Neg a)), z) = (Neg z, Left (Neg a))
eval_iso1 EtaPlus (Neg (Right a), z) = (Neg z, Right a) 

eval_iso c (Neg b, a) = (Neg (eval (adjoint c) b), eval c a)

------------------------------------------------------------------------------
-- Examples

type B = Either () ()

cohPlus :: a :<=> a           
cohPlus = ZeroI                      
           :.: (EtaPlus :+: Id)      
           :.: (CommutePlus :+: Id)  
           :.: AssocPlusR            
           :.: (Id :+: EpsPlus)      
           :.: CommutePlus           
           :.: ZeroE                 

-- test1, test2 :: B
test1 = eval_iso cohPlus (Neg (Left ()), Left ())
test2 = eval_iso cohPlus (Neg (Right ()), Right ())


------------------------------------------------------------------------------
