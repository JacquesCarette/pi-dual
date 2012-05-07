-- {-# OPTIONS_GHC -fglasgow-exts #-} -- 6.12.3
{-# LANGUAGE GADTs, TypeOperators, ExistentialQuantification,
             TypeFamilies #-} -- 7.0.1

--  This code tested with GHC version 7.0.3

module Model2 where

import Model hiding ((@@))
import Lang (Neg,Inv,Unpack(..))
import Control.Monad
import Unsafe.Coerce -- needed for polymorphic lookup. 

-- Structure of Pi Values that may contain non-grounded fresh variables.
type Var a = Int
data V a where
    Unit :: V () 
    Pair :: V a -> V b -> V (a, b) 
    L :: V a -> V (Either a b) 
    R :: V b -> V (Either a b) 
    Neg :: V a -> V (Neg a)
    Inv :: V a -> V (Inv a)
    Fresh :: Var a -> V a

instance Show (V a) where 
    show Unit = "()"
    show (Pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (L a) = "L " ++ (show a) 
    show (R a) = "R " ++ (show a)
    show (Neg a) = "Neg " ++ (show a)
    show (Inv a) = "Inv " ++ (show a)
    show (Fresh n) = show n

instance Unpack V where
    unLeft (L a) = a
    unRight (R a) = a
    proj1 (Pair a _) = a
    proj2 (Pair _ b) = b
    unNeg (Neg a) = a

---------------------------------------------------------------------------
-- Unification

-- This class says that, the u a's can be unified (as an effect) and generated
class Unifyable u where
  type W :: * -> *
  unify :: u a -> u a -> W ()
  fresh :: W (u a)

data Binding = forall a. Binding (Var a) (V a)
type World = ([Binding], Int)

instance Show Binding where 
    show (Binding n _) = (show n) ++ " -> " 

instance Unifyable V where
  type W = M
  unify = unifyM
  fresh = freshM

extendW :: Var a -> V a -> [Binding] -> [Binding]
extendW x v w = (Binding x v):w

lookupW :: V a -> [Binding] -> V a
lookupW (Fresh nm) w = find nm w 
    where 
      find :: Var a -> [Binding] -> V a 
      find n ((Binding n' v):w') | n == n'   = lookupW (unsafeCoerce v) w
                                 | otherwise = find n w'
      find n [] = Fresh n
lookupW v _ = v
    
unify_ :: V a -> V a -> [Binding] -> Maybe [Binding]
unify_ a a' b = unify' (lookupW a b) (lookupW a' b) b
    where 
      unify' :: V a -> V a -> [Binding] -> Maybe [Binding]
      unify' (Fresh x) v w = Just (extendW x v w)
      unify' v (Fresh x) w = Just (extendW x v w)
      unify' (L v) (L v') w = unify_ v v' w
      unify' (R v) (R v') w = unify_ v v' w
      unify' (Neg v) (Neg v') w = unify_ v v' w
      unify' (Pair x y) (Pair x' y') w = case (unify_ y y' w) of 
                                           Nothing -> Nothing 
                                           Just z' -> unify_ x x' z'
      unify' Unit Unit w = Just w
      unify' _ _ _ = Nothing

unifyW :: V a -> V a -> World -> Maybe World 
unifyW v1 v2 (bs, n) = 
    case (unify_ v1 v2 bs) of 
      Nothing -> Nothing
      Just cs -> Just (cs, n)

freshW :: World -> (V a, World)
freshW (bs, n) = (Fresh n, (bs, n+1))

reify :: (V a, World) -> V a
reify (x, (cs, _)) = reify' (lookupW x cs) cs 
    where 
      reify' :: V a -> [Binding] -> V a
      reify' Unit _ = Unit
      reify' (Fresh n) _ = Fresh n 
      reify' (L v) bs = L (reify' (lookupW v bs) bs)
      reify' (R v) bs = R (reify' (lookupW v bs) bs)
      reify' (Neg v) bs = Neg (reify' (lookupW v bs) bs)
      reify' (Inv v) bs = Inv (reify' (lookupW v bs) bs)
      reify' (Pair a b) bs = Pair (reify' (lookupW a bs) bs) (reify' (lookupW b bs) bs)

-------------------------------------------------------
-- A monad for unification based Pi

data M a = M (World -> [(a, World)])

instance Monad M where 
    return a = M (\w -> [(a, w)])
    (M f) >>= g = M (\w -> foldl (\acc (v, z) -> acc ++ (g v `app` z)) [] (f w))

app :: M a -> World -> [(a, World)]
app (M f) w = f w

unifyM :: V a -> V a -> M () 
unifyM v1 v2 = M (\w -> 
                      case (unifyW v1 v2 w) of 
                        Nothing -> []
                        Just w' -> [((), w')])

freshM :: M (V a)
freshM = M (\w -> [freshW w])

orM :: M a -> M a -> M a
orM e1 e2 = M (\w -> (e1 `app` w) ++ (e2 `app` w))
          
zeroM :: M a
zeroM = M(\_ -> [])

instance MonadPlus M where
  mzero = zeroM
  mplus = orM

orV :: MonadPlus m => (v a -> m b) -> (v a -> m b) -> (v a -> m b)
orV f g = \v -> f v `mplus` g v

----------------------------------------------------------------------
-- Run the computation
run :: M (V a) -> [V a]
run e = map reify (e `app` ([], 100)) 

-- Note: I start with the 100 as the first system generated fresh
-- variable thus reserving fresh variables 0..99 for user input. 

----------
-- Helper fn
fresh1 :: (Unifyable v) => (v a -> v b) -> v b -> W (v a)
fresh1 f v =
  do x <- fresh
     unify (f x) v
     return x

fresh2 :: (Unifyable v) => (v a1 -> v a2 -> v b) -> v b -> W (v a1, v a2)
fresh2 f v =
  do x1 <- fresh
     x2 <- fresh
     unify (f x1 x2) v
     return (x1,x2)

fresh3 :: (Unifyable v) => (v a1 -> v a2 -> v a3 -> v b) 
                           -> v b -> W (v a1, v a2, v a3)
fresh3 f v =
  do x1 <- fresh
     x2 <- fresh
     x3 <- fresh
     unify (f x1 x2 x3) v
     return (x1,x2,x3)

lift1 :: Monad m => (t -> m a) -> (a -> r) -> t -> m r
lift1 f g v = liftM g (f v)

-- mar = match >=> act >=> return
mar :: Unifyable v => (v a -> v b) -> (v a -> W c) -> (c -> d) -> (v b -> W d)
mar f g h = fresh1 f >=> g >=> (return . h)
-- mr = match >=> return
mr :: (V a -> V b) -> (V a -> c) -> (V b -> M c)
mr f h = fresh1 f >=> (return . h)

-- mr2 = match >=> return (on 2 args)
mr2 :: Unifyable v => (v a1 -> v a2 -> v b) -> ((v a1, v a2) -> c) -> v b -> W c
mr2 f h = fresh2 f >=> (return . h)

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
-- Id @@ a = return a 
Id @@ a = mr id id a
(Adj f) @@ v = mar Neg ((adjoint f) @@) Neg v

-- (f :.: g) @@ a = g @@ (f @@ a)
(f :.: g) @@ a = ((f @@) >=> (g @@)) a

-- (f :*: g) @@ (a,c) = (f @@ a, g @@ c)
(f :*: g) @@ v = 
     do (x1,x2) <- fresh2 Pair v
        liftM2 Pair (f @@ x1) (g @@ x2)

-- (f :+: g) @@ (Left a) = Left (f @@ a) 
-- (f :+: g) @@ (Right b) = Right (g @@ b) 
(f :+: g) @@ v = (mar L (f @@) L `orV` mar R (g @@) R) v

-- PlusZeroL @@ (Right a) = a
PlusZeroL @@ v = mr R id v
-- PlusZeroR @@ a = Right a
PlusZeroR @@ v = mr id R v

-- CommutePlus @@ (Left a) = Right a
-- CommutePlus @@ (Right b) = Left b 
CommutePlus @@ v = (mr L R `orV` mr R L) v

-- AssocPlusL @@ (Left a) = Left (Left a) 
-- AssocPlusL @@ (Right (Left b)) = Left (Right b) 
-- AssocPlusL @@ (Right (Right c)) = Right c
AssocPlusL @@ v = (mr L (L . L) `orV` mr (R . L) (L . R) `orV` mr (R . R) R) v

-- AssocPlusR @@ (Left (Left a)) = Left a
-- AssocPlusR @@ (Left (Right b)) = Right (Left b)
-- AssocPlusR @@ (Right c) = Right (Right c)
AssocPlusR @@ v = (mr (L . L) L `orV` mr (L . R) (R . L) `orV` mr R (R . R)) v

-- TimesOneL @@ ((), a) = a
TimesOneL @@ v = fresh1 (Pair Unit) v
-- TimesOneR @@ a = ((), a)
TimesOneR @@ v = return (Pair Unit v)

-- CommuteTimes @@ (a,b) = (b,a) 
CommuteTimes @@ v = mr2 Pair (uncurry $ flip Pair) v

-- AssocTimesL @@ (a,(b,c)) = ((a,b),c) 
AssocTimesL @@ v = 
    do (x,y,z) <- fresh3 (\a b c -> Pair a (Pair b c)) v
       return (Pair (Pair x y) z)
-- AssocTimesR @@ ((a,b),c)  = (a,(b,c))
AssocTimesR @@ v = 
    do (x,y,z) <- fresh3 (\a b c -> Pair (Pair a b) c) v
       return (Pair x (Pair y z))

-- Distribute @@ (Left b, a) = Left (b, a) 
-- Distribute @@ (Right c, a) = Right (c, a) 
Distribute @@ v = 
      (mr2 (\x y -> Pair (L x) y) (L . uncurry Pair) `orV`
       mr2 (\x y -> Pair (R x) y) (R . uncurry Pair)) v

-- Factor @@ (Left (b, a)) = (Left b, a) 
-- Factor @@ (Right (c, a)) = (Right c, a) 
Factor @@ v = 
      (mr2 (\x y -> L (Pair x y)) (\(x,y) -> Pair (L x) y) `orV`
       mr2 (\x y -> R (Pair x y)) (\(x,y) -> Pair (R x) y)) v

-- EtaTimes and EpsTimes as U shaped connectors
EtaTimes @@ v = mr (\_ -> Unit) (\x -> Pair (Inv x) x) v
EpsTimes @@ v = mr (\x -> Pair x (Inv x)) (\_ -> Unit) v

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
type (:=>>) a b = (Inv a, b)
type (:<<=) a b = (a, Inv b)
type P a = () :<=> a
type N a = a  :<=> ()

makeFunc :: (a :<=> b) -> P (a :=>> b)
makeFunc c = EtaTimes :.: (Id :*: c)

-- Many apply's to be written here based on what interface we want:
-- apply : P (a :=>> b) -> P a -> P b
-- apply : P (a :=>> b) -> (c :<=> a) -> (c :<=> b)
-- apply : ((a :=>> b), a) :<=> b

applyFunc :: ((a :=>> b), a) :<=> b 
applyFunc = CommuteTimes 
            :.: AssocTimesL 
            :.: (EpsTimes :*: Id) 
            :.: TimesOneL

-- These 
makeDC :: (a :<=> b) -> N (a :<<= b)
makeDC c = (c :*: Id) :.: EpsTimes

-- A similar apply is possible, but I dont know what it means. 

-- Trace
traceTimes :: (a, b) :<=> (a, c) -> b :<=> c
traceTimes c = TimesOneR 
               :.: (EtaTimes :*: Id) 
               :.: AssocTimesR 
               :.: (Id :*: c) 
               :.: AssocTimesL 
               :.: ((CommuteTimes :.: EpsTimes) :*: Id)
               :.: TimesOneL

-- This is the yanking lemma for trace. 
yank :: a :<=> a
yank = traceTimes CommuteTimes

-- Here I make 'not' a first-class function and then apply it:
-- *Pi> :t TimesOneR :.: ((makeFunc CommuteTimes) :*: Id) :.: applyFunc
-- TimesOneR :.: ((makeFunc CommuteTimes) :*: Id) :.: applyFunc
--   :: (a, b) :<=> (b, a)

---------------------------------------------------------------------------------
-- So now can we try some of the Hasegawa-Hyland fixpoint constructions? 

