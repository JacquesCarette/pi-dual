{-# OPTIONS_GHC -XGADTs -XTypeOperators -XExistentialQuantification -XFlexibleContexts #-} -- 7.0.1, 7.0.3

-- {-# OPTIONS_GHC -fglasgow-exts #-} -- 6.12.3
-- Dont know: This code tested with GHC version 6.12.3, and version 7.0.1

module OldDual where

import Data.Typeable
import Unsafe.Coerce -- needed for polymorphic lookup. 


-----------------------------------------------------------------------
-- Base types 

data Zero 
data Neg a = Ng a
data Inv a = In a

type (:+:) a b = Either a b
type (:*:) a b = (a, b)

data Three = One 
           | Two 
           | Three
             deriving (Eq, Show)

-----------------------------------------------------------------------
-- Values 
-- 
-- Values of the form 'V a' are values used by the interpreter. 


-- Values can contain non-grounded fresh variables
type Var a = Int
data V a where
    Unit :: V () 
    Pair :: V a -> V b -> V (a, b) 
    L :: V a -> V (Either a b) 
    R :: V b -> V (Either a b) 
    Neg :: V a -> V (Neg a)
    Inv :: V a -> V (Inv a)
    Lift :: (Eq a, Show a) => a -> V a
    Fresh :: Var a -> V a


instance Show (V a) where 
    show Unit = "()"
    show (Pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (L a) = "L " ++ (show a) 
    show (R a) = "R " ++ (show a)
    show (Neg a) = "Neg " ++ (show a)
    show (Inv a) = "Inv " ++ (show a)
    show (Lift a) = show a
    show (Fresh n) = show n

------------------------------------------------------------------------------------
-- Translate a normal value to value usable by the interpreter.
-- a -> V a

class ToV a where 
    makeV :: a -> V a

instance ToV () where 
    makeV () = Unit

instance (ToV a, ToV b) => ToV (Either a  b) where 
    makeV (Left a) = L (makeV a)
    makeV (Right a) = R (makeV a)

instance (ToV a, ToV b) => ToV (a, b) where 
    makeV (a, b) = Pair (makeV a) (makeV b)

instance (Show a, ToV a) => ToV (Inv a) where 
    makeV (In a) = Inv (makeV a)

instance (Show a, ToV a) => ToV (Neg a) where 
    makeV (Ng a) = Neg (makeV a)

instance ToV Bool where 
    makeV b = Lift b

instance ToV Three where 
    makeV b = Lift b



-----------------------------------------------------------------------
-- Isomorphisms 

data a :<=> b where 
-- Congruence
  Id    :: a :<=> a
  Adj   :: (a :<=> b) -> (Neg b :<=> Neg a) 
  (:.:) :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- (+) is associative, commutative, and has a unit
  ZeroE   :: Either Zero a :<=> a
  ZeroI   :: a :<=> Either Zero a
  CommutePlus :: Either a b :<=> Either b a
  AssocPlusL  :: Either a (Either b c) :<=> Either (Either a b) c 
  AssocPlusR  :: Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE    :: ((), a) :<=> a
  UnitI    :: a :<=> ((), a)
  CommuteTimes :: (a,b) :<=> (b,a) 
  AssocTimesL  :: (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  TimesZeroL  :: (Zero, a) :<=> Zero
  TimesZeroR  :: Zero :<=> (Zero, a)
  Distribute  :: (Either b c, a) :<=> Either (b, a) (c, a)
  Factor      :: Either (b, a) (c, a) :<=> (Either b c, a)
-- Eta and Eps over the monoid (*, 1)
  EtaTimes:: () :<=> (Inv a, a)
  EpsTimes :: (Inv a, a) :<=> ()
-- EtaTimesand EpsTimes over the monoid (+, 0)
  EtaPlus :: Zero :<=> (Neg a :+: a)
  EpsPlus :: (Neg a :+: a) :<=> Zero
-- Some handy constant types 
-- Encoding of Booleans
  FoldB   :: Either () () :<=> Bool
  UnfoldB :: Bool :<=> Either () ()
-- Encoding of Three
  FoldThree   :: Either () (Either () ()) :<=> Three
  UnfoldThree :: Three :<=> Either () (Either () ())

---------------------------------------------------------------------------
-- Adjoint
adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint (Adj f) = Adj (adjoint f)
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
adjoint EtaTimes= EpsTimes
adjoint EpsTimes = EtaTimes
adjoint EtaPlus = EpsPlus
adjoint EpsPlus = EtaPlus
adjoint FoldB = UnfoldB
adjoint UnfoldB = FoldB
adjoint FoldThree = UnfoldThree
adjoint UnfoldThree = FoldThree

---------------------------------------------------------------------------
-- Unification and Reification of values

data Binding = forall a. Binding (Var a) (V a)
type World = ([Binding], Int)

type Wave a = (V a, World)

instance Show Binding where 
    show (Binding n v) = (show n) ++ " -> " 


extendW :: Var a -> V a -> [Binding] -> [Binding]
extendW x v w = (Binding x v):w

lookupW :: V a -> [Binding] -> V a
lookupW (Fresh n) w = find n w 
    where 
      find :: Var a -> [Binding] -> V a 
      find n ((Binding n' v):w') | n == n'   = lookupW (unsafeCoerce v) w
                                 | otherwise = find n w'
      find n [] = Fresh n
lookupW v _ = v
    

unify :: V a -> V a -> [Binding] -> Maybe [Binding]
unify v v' w = unify' (lookupW v w) (lookupW v' w) w
    where 
      unify' :: V a -> V a -> [Binding] -> Maybe [Binding]
      unify' (Fresh x) v w = Just (extendW x v w)
      unify' v (Fresh x) w = Just (extendW x v w)
      unify' (L v) (L v') w = unify v v' w
      unify' (R v) (R v') w = unify v v' w
      unify' (Neg v) (Neg v') w = unify v v' w
      unify' (Inv v) (Inv v') w = unify v v' w
      unify' (Pair a b) (Pair a' b') w = case (unify b b' w) of 
                                           Nothing -> Nothing 
                                           Just w' -> unify a a' w'
      unify' Unit Unit w = Just w
      unify' (Lift a) (Lift a') w | a == a' = Just w
      unify' _ _ _ = Nothing

unifyW :: V a -> V a -> World -> Maybe World 
unifyW v1 v2 (bs, n) = 
    case (unify v1 v2 bs) of 
      Nothing -> Nothing
      Just bs -> Just (bs, n)


fresh :: World -> (V a, World)
fresh (bs, n) = (Fresh n, (bs, n+1))

reify :: (V a, World) -> V a
reify (v, (bs, _)) = reify' (lookupW v bs) bs 
    where 
      reify' :: V a -> [Binding] -> V a
      reify' Unit _ = Unit
      reify' (Lift v) _ = Lift v
      reify' (Fresh n) _ = Fresh n 
      reify' (L v) bs = L (reify' (lookupW v bs) bs)
      reify' (R v) bs = R (reify' (lookupW v bs) bs)
      reify' (Neg v) bs = Neg (reify' (lookupW v bs) bs)
      reify' (Inv v) bs = Inv (reify' (lookupW v bs) bs)
      reify' (Pair a b) bs = Pair (reify' (lookupW a bs) bs) (reify' (lookupW b bs) bs)

-------------------------------------------------------
-- A Unification Monad

data M a = M (World -> [(a, World)])

instance Monad M where 
    return a = M (\w -> [(a, w)])
    (M f) >>= g = M (\w -> foldl (\acc (v, w) -> acc ++ (g v `app` w)) [] (f w))

app :: M a -> World -> [(a, World)]
app (M f) w = f w

unifyM :: V a -> V a -> M () 
unifyM v1 v2 = M (\w -> 
                      case (unifyW v1 v2 w) of 
                        Nothing -> []
                        Just w' -> [((), w')])

freshM :: M (V a)
freshM = M (\w -> [fresh w])

orM :: M a -> M a -> M a
orM e1 e2 = M (\w -> (e1 `app` w) ++ (e2 `app` w))
          
-- Run the monadic computation
run :: Show (V a) => M (V a) -> [V a]
run e = map (\w->reify w) (e `app` ([], 100)) 

-- Note: I start with the 100 as the first system generated fresh
-- variable thus reserving fresh variables 0..99 for user input. This
-- is just a hack.

----------------------------------------------------------------------
-- Eval Simple
-- 
-- Operational semantics of primtive isomorphisms expressed using the
-- unification monad. Morphisms eta/eps for (*, 1) are also included
-- here.
 
eval_iso :: (a :<=> b) -> (V a) -> M (V b)
eval_iso Id a = return a

-- ZeroE @@ (Right a) = a
eval_iso ZeroE v = 
    do v1 <- freshM 
       unifyM (R v1) v 
       return v1
-- ZeroI @@ a = Right a
eval_iso ZeroI v = 
    return (R v)
-- CommutePlus @@ (Left a) = Right a
-- CommutePlus @@ (Right b) = Left b 
eval_iso CommutePlus v = 
    do v1 <- freshM 
       unifyM (L v1) v 
       return (R v1)
    `orM`
    do v1 <- freshM 
       unifyM (R v1) v
       return (L v1)

-- AssocPlusL @@ (Left a) = Left (Left a) 
-- AssocPlusL @@ (Right (Left b)) = Left (Right b) 
-- AssocPlusL @@ (Right (Right c)) = Right c
eval_iso AssocPlusL v = 
    do x <- freshM 
       unifyM (L x) v
       return (L (L x))
    `orM`
    do x <- freshM 
       unifyM (R (L x)) v
       return (L (R x))
    `orM`
    do x <- freshM 
       unifyM (R (R x)) v
       return (R x)

-- AssocPlusR @@ (Left (Left a)) = Left a
-- AssocPlusR @@ (Left (Right b)) = Right (Left b)
-- AssocPlusR @@ (Right c) = Right (Right c)
eval_iso AssocPlusR v = 
    do x <- freshM 
       unifyM (L (L x)) v
       return (L x)
    `orM`
    do x <- freshM 
       unifyM (L (R x)) v
       return (R (L x))
    `orM`
    do x <- freshM 
       unifyM (R x) v
       return (R (R x))

-- UnitE @@ ((), a) = a
eval_iso UnitE v = 
    do x <- freshM 
       unifyM (Pair Unit x) v
       return x
-- UnitI @@ a = ((), a)
eval_iso UnitI v = 
    return (Pair Unit v)

-- CommuteTimes @@ (a,b) = (b,a) 
eval_iso CommuteTimes v = 
    do x <- freshM 
       y <- freshM
       unifyM (Pair x y) v
       return (Pair y x)

-- AssocTimesL @@ (a,(b,c)) = ((a,b),c) 
eval_iso AssocTimesL v = 
    do x <- freshM 
       y <- freshM
       z <- freshM 
       unifyM (Pair x (Pair y z)) v
       return (Pair (Pair x y) z)
-- AssocTimesR @@ ((a,b),c)  = (a,(b,c))
eval_iso AssocTimesR v = 
    do x <- freshM 
       y <- freshM
       z <- freshM 
       unifyM (Pair (Pair x y) z) v
       return (Pair x (Pair y z))

-- Distribute @@ (Left b, a) = Left (b, a) 
-- Distribute @@ (Right c, a) = Right (c, a) 
eval_iso Distribute v = 
    do x <- freshM 
       y <- freshM
       unifyM (Pair (L x) y) v
       return (L (Pair x y))
    `orM`
    do x <- freshM 
       y <- freshM
       unifyM (Pair (R x) y) v
       return (R (Pair x y))

-- Factor @@ (Left (b, a)) = (Left b, a) 
-- Factor @@ (Right (c, a)) = (Right c, a) 
eval_iso Factor v = 
    do x <- freshM 
       y <- freshM
       unifyM (L (Pair x y)) v
       return (Pair (L x) y)
    `orM`
    do x <- freshM 
       y <- freshM
       unifyM (R (Pair x y)) v
       return (Pair (R x) y)

-- EtaTimesand EpsTimes as U shaped connectors
eval_iso EtaTimes v = 
    do x <- freshM 
       unifyM Unit v 
       return  (Pair (Inv x) x)
eval_iso EpsTimes v = 
    do x <- freshM 
       unifyM (Pair (Inv x) x) v 
       return Unit

-- Fold, Unfold : Bool
eval_iso FoldB v = 
    do unifyM (L Unit) v 
       return (Lift True)
    `orM`
    do unifyM (R Unit) v
       return (Lift False)
eval_iso UnfoldB v = 
    do unifyM (Lift True) v 
       return (L Unit)
    `orM`
    do unifyM (Lift False) v
       return (R Unit)
    
-- Fold, Unfold : Three
eval_iso FoldThree v = 
    do unifyM (L Unit) v 
       return (Lift One)
    `orM`
    do unifyM (R (L Unit)) v
       return (Lift Two)
    `orM`
    do unifyM (R (R Unit)) v
       return (Lift Three)
eval_iso UnfoldThree v = 
    do unifyM (Lift One) v 
       return (L Unit)
    `orM`
    do unifyM (Lift Two) v
       return (R (L Unit))
    `orM`
    do unifyM (Lift Three) v
       return (R (R Unit))


----------------------------------------------------------------------
-- Evaluation Contexts
-- 
-- These contexts are used in the definition of the composition
-- combinators.

data K a b c d where
    KEmpty :: K a b a b 
    Fst :: (b :<=> c) -> K a c i o -> K a b i o 
    Snd :: (a :<=> b) -> K a c i o -> K b c i o 
    LftPlus :: (c :<=> d) -> K (a:+:c) (b:+:d) i o -> K a b i o 
    RgtPlus :: (a :<=> b) -> K (a:+:c) (b:+:d) i o -> K c d i o 
    LftTimes :: V c -> (c :<=> d) -> K (a:*:c) (b:*:d) i o -> K a b i o 
    RgtTimes :: (a :<=> b) -> V b -> K (a:*:c) (b:*:d) i o -> K c d i o 
     

--------------------------------------------------------
-- Operational semantics for the Forward evaluator

-- Explore current combinator 
eval_c :: (a :<=> b) -> V a -> K a b c d -> M (V d)
-- (f :.: g) @@ a = g @@ (f @@ a)
eval_c (f :.: g) a k = 
    eval_c f a (Fst g k)
         
-- (f :*: g) @@ (a,c) = (f @@ a, g @@ c)
eval_c (f :*: g) v k = 
    do x1 <- freshM 
       x2 <- freshM 
       unifyM (Pair x1 x2) v
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
       unifyM (L (Neg v1)) v 
       back_eval_k EpsPlus (R v1) k
    `orM`
    do v1 <- freshM 
       unifyM (R v1) v
       back_eval_k EpsPlus (L (Neg v1)) k

-- all primitive isomorphisms are executed using eval_iso
eval_c c v k = 
    do v' <- eval_iso c v
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
       unifyM v' (Pair v1 v2)
       eval_k (f :*: g) v' k 

--------------------------------------------------------
-- Operational semantics for the Backward evaluator

-- Explore the combinator
back_eval_c :: (a :<=> b) -> V b -> K a b c d -> M (V d)
-- (f :.: g) @@ a = g @@ (f @@ a)
back_eval_c (f :.: g) a k = 
    back_eval_c g a (Snd f k)
         
-- (f :*: g) @@ (a,c) = (f @@ a, g @@ c)
back_eval_c (f :*: g) v k = 
    do x1 <- freshM 
       x2 <- freshM 
       unifyM (Pair x1 x2) v
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
       unifyM (L (Neg v1)) v 
       eval_k EtaPlus (R v1) k
    `orM`
    do v1 <- freshM 
       unifyM (R v1) v
       eval_k EtaPlus (L (Neg v1)) k

-- all primitive isomorphisms are executed backwards.
back_eval_c c v k = 
    do v' <- eval_iso (adjoint c) v
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
       unifyM v' (Pair v1 v2)
       back_eval_k (f :*: g) v' k 

-- Note: We could explore an alternate semantics that allows for
-- termination in the backward evaluator.
--  back_eval_k c v KEmpty = return v

----------------------------------------------------------------------
-- Eval
-- 
-- We use eval to run a Pi computation. Evaluation starts in the
-- forward evaluator with a user supplied value.
eval :: (ToV a, Show (V a)) => (a :<=> b) -> a -> [V b]
eval c v = run (eval_c c (makeV v) KEmpty)

