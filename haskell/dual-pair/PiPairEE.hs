{-# OPTIONS_GHC -fglasgow-exts #-} -- 6.12.3
-- {-# OPTIONS_GHC -XGADTs -XTypeOperators #-} -- 7.0.1

-- Dont know: This code tested with GHC version 6.12.3, and version 7.0.1

module PiCont where

import Data.Typeable
import Unsafe.Coerce -- needed for polymorphic lookup. 

-----------------------------------------------------------------------
-- Isomorphisms 

data Zero 
data Show a => Neg a = Negative a
             deriving Show

data a :<=> b where 
-- Congruence
  Id    :: a :<=> a
  Adj   :: (a :<=> b) -> (Neg b :<=> Neg a) 
  (:.:) :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
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
-- Eta and Eps over the monoid (*, 1)
  Eta :: () :<=> (Neg a, a)
  Eps :: (a, Neg a) :<=> ()

-- -- Encoding of booleans
--   FoldB   :: Either () () :<=> Bool
--   UnfoldB :: Bool :<=> Either () ()
-- -- Encoding of natural numbers using the isorecursive type (mu x.1+x)
--   FoldN   :: Either () Int :<=> Int
--   UnfoldN :: Int :<=> Either () Int
-- -- Encoding of lists of natural numbers using the isorecursive type
-- -- (mu x.1+nat*x)
--   FoldLN :: Either () (Int, [Int]) :<=> [Int]
--   UnfoldLN :: [Int] :<=> Either () (Int, [Int])
-- -- Encoding of lists of natural numbers using the isorecursive type
-- -- (mu x.1+nat*x)
--   FoldL :: Either () (a, [a]) :<=> [a]
--   UnfoldL :: [a] :<=> Either () (a, [a])
-- -- Trance operators for looping/recursion
--   TracePlus :: (Either a b1 :<=> Either a b2) -> (b1 :<=> b2)

-- Adjoint

adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint (Adj f) = Adj (adjoint f)
adjoint (f :.: g) = adjoint g :.: adjoint f
adjoint (f :*: g) = adjoint f :*: adjoint g
adjoint (f :+: g) = adjoint f :+: adjoint g
adjoint PlusZeroL = PlusZeroR
adjoint PlusZeroR = PlusZeroL
adjoint CommutePlus = CommutePlus
adjoint AssocPlusL = AssocPlusR
adjoint AssocPlusR = AssocPlusL
adjoint TimesOneL = TimesOneR
adjoint TimesOneR = TimesOneL
adjoint CommuteTimes = CommuteTimes
adjoint AssocTimesL = AssocTimesR
adjoint AssocTimesR = AssocTimesL
adjoint TimesZeroL = TimesZeroR
adjoint TimesZeroR = TimesZeroL
adjoint Distribute = Factor
adjoint Factor = Distribute
adjoint Eta = CommuteTimes :.: Eps
adjoint Eps = Eta :.: CommuteTimes
-- adjoint FoldB = UnfoldB
-- adjoint UnfoldB = FoldB
-- adjoint FoldN = UnfoldN
-- adjoint UnfoldN = FoldN
-- adjoint FoldLN = UnfoldLN
-- adjoint UnfoldLN = FoldLN
-- adjoint FoldL = UnfoldL
-- adjoint UnfoldL = FoldL
-- adjoint (TracePlus c) = TracePlus (adjoint c)


-- Structure of Pi Values that may contain non-grounded fresh variables.
type Var a = Int
data V a where
    Unit :: V () 
    Pair :: V a -> V b -> V (a, b) 
    L :: V a -> V (Either a b) 
    R :: V b -> V (Either a b) 
    Neg :: V a -> V (Neg a)
    Fresh :: Var a -> V a

    -- Unit :: V () 
    -- Pair :: (Typeable a, Typeable b) => V a -> V b -> V (a, b) 
    -- L :: (Typeable a, Typeable b) => V a -> V (Either a b) 
    -- R :: (Typeable a, Typeable b) => V b -> V (Either a b) 
    -- Fresh :: Var a -> V a


-- data V a where
--     Unit :: V () 
--     Pair :: V a -> V b -> V (a, b) 
--     L :: V a -> V (Either a b) 
--     R :: V b -> V (Either a b) 
--     Fresh :: Int -> V a




instance Show (V a) where 
    show Unit = "()"
    show (Pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (L a) = "L " ++ (show a) 
    show (R a) = "R " ++ (show a)
    show (Neg a) = "Neg " ++ (show a)
    show (Fresh n) = show n

-- instance Typeable arg => Typeable (V arg) where 
--     typeOf Unit = mkTyConApp (mkTyCon "Unit") [typeOf ()]
--     typeOf (Pair a b) = mkTyConApp (mkTyCon "Pair") [typeOf (undefined :: arg)]
    -- typeOf1 (L a) = mkTyConApp (mkTyCon "L") [typeOf a]



    

---------------------------------------------------------------------------
-- Unification
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
      unify' (Pair a b) (Pair a' b') w = case (unify b b' w) of 
                                           Nothing -> Nothing 
                                           Just w' -> unify a a' w'
      unify' Unit Unit w = Just w
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
      reify' (Fresh n) _ = Fresh n 
      reify' (L v) bs = L (reify' (lookupW v bs) bs)
      reify' (R v) bs = R (reify' (lookupW v bs) bs)
      reify' (Neg v) bs = Neg (reify' (lookupW v bs) bs)
      reify' (Pair a b) bs = Pair (reify' (lookupW a bs) bs) (reify' (lookupW b bs) bs)

-------------------------------------------------------
-- A monad for unifcation based Pi

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
          



----------------------------------------------------------------------
-- Run the computation
run :: Show (V a) => M (V a) -> [V a]
run e = map (\w->reify w) (e `app` ([], 100)) 


-- Note: I start with the 100 as the first system generated fresh
-- variable thus reserving fresh variables 0..99 for user input. 

----------------------------------------------------------------------
-- Semantics
-- 
-- These semantics are a straightforward translation of the older
-- semantics. In each case we attempt to unify the input with the
-- expected shape of the value and then express the output in terms of
-- that. As fresh variables move through the system, they get more and
-- more grounded based on how closely they are inspected. 
-- 
-- A grounded value (with no fresh varaibles) takes a fixed path
-- through a Pi circuit. A value with unspecified components (with
-- fresh vars) will take all the possible paths that satisfy the shape
-- of the values.
--
-- Logic programming often smells like it has some
-- quantumness/reversibility. This code essentially leverages that for
-- Pi.
(@@) :: (a :<=> b) -> V a -> M (V b)
Id @@ a = return a 
(Adj f) @@ v = 
    do x <- freshM 
       unifyM (Neg x) v
       v1 <- (adjoint f) @@ x
       return (Neg v1)

-- (f :.: g) @@ a = g @@ (f @@ a)
(f :.: g) @@ a = 
    do b <- f @@ a
       g @@ b

-- (f :*: g) @@ (a,c) = (f @@ a, g @@ c)
(f :*: g) @@ v = 
    do x1 <- freshM 
       x2 <- freshM 
       unifyM (Pair x1 x2) v
       v1 <- f @@ x1
       v2 <- g @@ x2
       return (Pair v1 v2)

-- (f :+: g) @@ (Left a) = Left (f @@ a) 
-- (f :+: g) @@ (Right b) = Right (g @@ b) 
(f :+: g) @@ v = 
    do v1 <- freshM 
       unifyM (L v1) v 
       v2 <- f @@ v1 
       return (L v2)
    `orM`
    do v1 <- freshM 
       unifyM (R v1) v 
       v2 <- g @@ v1 
       return (R v2)

-- PlusZeroL @@ (Right a) = a
PlusZeroL @@ v = 
    do v1 <- freshM 
       unifyM (R v1) v 
       return v1
-- PlusZeroR @@ a = Right a
PlusZeroR @@ v = 
    return (R v)

-- CommutePlus @@ (Left a) = Right a
-- CommutePlus @@ (Right b) = Left b 
CommutePlus @@ v = 
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
AssocPlusL @@ v = 
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
AssocPlusR @@ v = 
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

-- TimesOneL @@ ((), a) = a
TimesOneL @@ v = 
    do x <- freshM 
       unifyM (Pair Unit x) v
       return x
-- TimesOneR @@ a = ((), a)
TimesOneR @@ v = 
    return (Pair Unit v)

-- CommuteTimes @@ (a,b) = (b,a) 
CommuteTimes @@ v = 
    do x <- freshM 
       y <- freshM
       unifyM (Pair x y) v
       return (Pair y x)

-- AssocTimesL @@ (a,(b,c)) = ((a,b),c) 
AssocTimesL @@ v = 
    do x <- freshM 
       y <- freshM
       z <- freshM 
       unifyM (Pair x (Pair y z)) v
       return (Pair (Pair x y) z)
-- AssocTimesR @@ ((a,b),c)  = (a,(b,c))
AssocTimesR @@ v = 
    do x <- freshM 
       y <- freshM
       z <- freshM 
       unifyM (Pair (Pair x y) z) v
       return (Pair x (Pair y z))

-- Distribute @@ (Left b, a) = Left (b, a) 
-- Distribute @@ (Right c, a) = Right (c, a) 
Distribute @@ v = 
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
Factor @@ v = 
    do x <- freshM 
       y <- freshM
       unifyM (L (Pair x y)) v
       return (Pair (L x) y)
    `orM`
    do x <- freshM 
       y <- freshM
       unifyM (R (Pair x y)) v
       return (Pair (R x) y)

-- Eta and Eps as U shaped connectors
Eta @@ v = 
    do x <- freshM 
       unifyM Unit v 
       return (Pair (Neg x) x)
Eps @@ v = 
    do x <- freshM 
       unifyM (Pair x (Neg x)) v 
       return Unit


-- FoldB @@ (Left ()) = True
-- FoldB @@ (Right ()) = False
-- UnfoldB @@ True = Left ()
-- UnfoldB @@ False = Right ()
-- FoldN @@ (Left ()) = 0
-- FoldN @@ (Right n) = 1 + n
-- UnfoldN @@ 0 = Left ()
-- UnfoldN @@ n = Right (n-1) 
-- FoldLN @@ Left () = []
-- FoldLN @@ Right (h, t) = h : t
-- UnfoldLN @@ [] = Left ()
-- UnfoldLN @@ (h : t) = Right (h, t)
-- FoldL @@ Left () = []
-- FoldL @@ Right (h, t) = h : t
-- UnfoldL @@ [] = Left ()
-- UnfoldL @@ (h : t) = Right (h, t)
-- (TracePlus c) @@ v = loop c (c @@ (Right v))
--     where
--       loop c (Left v) = loop c (c @@ (Left v))
--       loop c (Right v) = v


--------------------------------------------------------------
-- Sample interaction

-- *Pi> :t (CommutePlus @@ (L Unit))
-- (CommutePlus @@ (L Unit)) :: M (V (Either b ()))
-- *Pi> run $ (CommutePlus @@ (R Unit))
-- [L ()]

-- *Pi> :t (CommutePlus @@ (R Unit))
-- (CommutePlus @@ (R Unit)) :: M (V (Either () a))
-- *Pi> run $ (CommutePlus @@ (L Unit))
-- [R ()]

-- *Pi> :t (CommutePlus @@ (Fresh 0))
-- (CommutePlus @@ (Fresh 0)) :: M (V (Either b a))
-- *Pi> run $ (CommutePlus @@ (Fresh 0))
-- [R 100,L 100]

-- Given a fresh input, the output has 4 possibilities. 
-- *Pi> run $ (CommutePlus :*: CommutePlus) @@ (Fresh 0)
-- [(R 102, R 103),(R 102, L 103),(L 102, R 103),(L 102, L 103)]

-- Given entagled values, the output has only 2 possibilities. 
-- *Pi> run $ (CommutePlus :*: CommutePlus) @@ (Pair (Fresh 0) (Fresh 0))
-- [(R 102, R 102),(L 102, L 102)]

-- Given a fully grounded value, the output has exactly one possibility. 
-- *Pi> run $ (CommutePlus :*: CommutePlus) @@ (Pair (L Unit) (R Unit))
-- [(R (), L ())]

-------------------------------------------------------------------------
-- With Eta and Eps


-- This is a wire with two U-shaped bends:
-- *Pi> :t (Eta :*: Id) :.: AssocTimesR :.: (Id :*: Eps)
-- (Eta :*: Id) :.: AssocTimesR :.: (Id :*: Eps)
--   :: ((), c) :<=> (c, ())

-- *Pi> run $ (Eta :*: Id) :.: AssocTimesR :.: (Id :*: Eps) @@ (Pair Unit (Fresh 0))
-- [(102, ())]
-- This logic variable is unified with the one supplied by the
-- user. However I dont know how to show that in the output.

-- Any particular value is passed through as unchanged. 
-- *Pi> run $ (Eta :*: Id) :.: AssocTimesR :.: (Id :*: Eps) @@ (Pair Unit (L Unit))
-- [(L (), ())]


------------------------------------------------------------------------------------
-- Constructions

-- Some shorthands 
type (:=>>) a b = (Neg a, b)
type (:<<=) a b = (a, Neg b)
type P a = () :<=> a
type N a = a  :<=> ()

makeFunc :: (a :<=> b) -> P (a :=>> b)
makeFunc c = Eta :.: (Id :*: c)

-- Many apply's to be written here based on what interface we want:
-- apply : P (a :=>> b) -> P a -> P b
-- apply : P (a :=>> b) -> (c :<=> a) -> (c :<=> b)
-- apply : ((a :=>> b), a) :<=> b

applyFunc :: ((a :=>> b), a) :<=> b 
applyFunc = CommuteTimes 
            :.: AssocTimesL 
            :.: (Eps :*: Id) 
            :.: TimesOneL

-- These 
makeDC :: (a :<=> b) -> N (a :<<= b)
makeDC c = (c :*: Id) :.: Eps


-- A similar apply is possible, but I dont know what it means. 

-- Trace
traceTimes :: (a, b) :<=> (a, c) -> b :<=> c
traceTimes c = TimesOneR 
               :.: (Eta :*: Id) 
               :.: AssocTimesR 
               :.: (Id :*: c) 
               :.: AssocTimesL 
               :.: ((CommuteTimes :.: Eps) :*: Id)
               :.: TimesOneL

-- This is the yanking lemma for trace. 
e1 :: a :<=> a
e1 = traceTimes CommuteTimes

-- Here I make 'not' a first-class function and then apply it:
-- *Pi> :t TimesOneR :.: ((makeFunc CommuteTimes) :*: Id) :.: applyFunc
-- TimesOneR :.: ((makeFunc CommuteTimes) :*: Id) :.: applyFunc
--   :: (a, b) :<=> (b, a)

---------------------------------------------------------------------------------
-- So now can we try some of the Hasegawa-Hyland fixpoint constructions? 

