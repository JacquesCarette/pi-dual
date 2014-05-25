{-# LANGUAGE TypeOperators, GADTs, TypeFamilies #-}

module Pi1 where

-- Pi0 is the usual Pi

-- Pi1 is the next up based on the Int construction (only possible after we
-- liberate ourselves from the brain-damaging notion that t1-t2 is a sum
-- type). In particular we only do part of the Int construction by adding the
-- types t1-t2 but keeping them separate. We don't get a compact closed
-- category. We only get 2nd-order functions. Note that the Int construction
-- gives you integers but without multiplication. If you want multiplication
-- you have to do something much more involved like the ring completion
-- paper.

------------------------------------------------------------------------------
-- Pi0

data Zero

data a :<-> b where 
  Id           :: a :<-> a
  Sym          :: (a :<-> b) -> (b :<-> a) 
  (:.:)        :: (a :<-> b) -> (b :<-> c) -> (a :<-> c)
  (:*:)        :: (a :<-> b) -> (c :<-> d) -> ((a,c) :<-> (b,d))
  (:+:)        :: (a :<-> b) -> (c :<-> d) -> (Either a c :<-> Either b d)
  PlusZeroL    :: Either Zero a :<-> a
  PlusZeroR    :: a :<-> Either Zero a
  CommutePlus  :: Either a b :<-> Either b a
  AssocPlusL   :: Either a (Either b c) :<-> Either (Either a b) c 
  AssocPlusR   :: Either (Either a b) c :<-> Either a (Either b c) 
  TimesOneL    :: ((), a) :<-> a
  TimesOneR    :: a :<-> ((), a)
  CommuteTimes :: (a,b) :<-> (b,a) 
  AssocTimesL  :: (a,(b,c)) :<-> ((a,b),c)
  AssocTimesR  :: ((a,b),c) :<-> (a,(b,c))
  TimesZeroL   :: (Zero, a) :<-> Zero
  TimesZeroR   :: Zero :<-> (Zero, a)
  Distribute   :: (Either b c, a) :<-> Either (b, a) (c, a)
  Factor       :: Either (b, a) (c, a) :<-> (Either b c, a)

-- values are boring at this level

type Val0 a = a

eval0 :: (a :<-> b) -> Val0 a -> Val0 b
eval0 Id a = a
eval0 c0 _ = error "I am not writing this again; get it from somewhere"

------------------------------------------------------------------------------
-- Pi1 

class Type1 p where
  type Pos p      :: *
  type Neg p      :: *  
  type Zero1      :: * 
  type One1       :: *
  type Plus1 p q  :: *

data a :- b = a :- b

instance Type1 (ap :- am) where
  type Pos (ap :- am) = ap
  type Neg (ap :- am) = am
  type Zero1 = Zero :- Zero
  type One1 = () :- Zero
  type Plus1  (ap :- am) (bp :- bm) = (Either ap bp) :- (Either am bm)

data a :<=> b where 
  Id1           :: (a ~ (ap :- am)) => a :<=> a
  Sym1          :: (a ~ (ap :- am), b ~ (bp :- bm)) => (a :<=> b) -> (b :<=> a) 
  (:..:)        :: (a ~ (ap :- am), b ~ (bp :- bm), c ~ (cp :- cm)) => 
                   (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:++:)        :: 
    -- (p ~ (a :- b), q ~ (c :- d), r ~ (e :- f), s ~ (g :- h)) => 
    (p :<=> q) -> (r :<=> s) -> (Plus1 p r :<=> Plus1 q s)
  PlusZeroL1    :: (a ~ (ap :- am)) => Plus1 Zero1 a :<=> a
  PlusZeroR1    :: (a ~ (ap :- am)) => a :<=> Plus1 Zero1 a
  CommutePlus1  :: (a ~ (ap :- am), b ~ (bp :- bm)) => Plus1 a b :<=> Plus1 b a
  AssocPlusL1   :: (a ~ (ap :- am), b ~ (bp :- bm), c ~ (cp :- cm)) => 
                   Plus1 a (Plus1 b c) :<=> Plus1 (Plus1 a b) c 
  AssocPlusR1   :: (a ~ (ap :- am), b ~ (bp :- bm), c ~ (cp :- cm)) => 
                   Plus1 (Plus1 a b) c :<=> Plus1 a (Plus1 b c) 

{-- 

Adding:

  Eta :: Zero1 :<=> (ap :- ap)
  Epsilon :: (ap :- ap) :<=> Zero1

eval1 Eta (Val1 ca) = Val1 { c = Id } 
eval1 Epsilon (Val1 ca) = Val1 { c = Id } 

is definitely wrong as it would allow us to introduce a 2-path 
between any 1-path : t -> t and refl_t. 

allid :: (a :- a) :<=> (a :- a)
allid = Epsilon :..: Eta

This would identify id and not on Bool. 

Similarly we are not compact closed yet so 

  Curry1 :: (a ~ (ap :- am), b ~ (bp :- bm), c ~ (cp :- cm)) => 
            (Plus1 a b :<=> c) -> (a :<=> Lolli1 b c)

  Uncurry1 :: (a ~ (ap :- am), b ~ (bp :- bm), c ~ (cp :- cm)) => 
              (a :<=> Lolli1 b c) -> (Plus1 a b :<=> c)

as well as name/coname, compose/apply, etc. won't work just yet.
   
Remove Dual: it adds a 2-path between c and !c trivializing all proofs

  Dual :: (a ~ (ap :- am)) => a :<=> Dual1 a

--}

{-- 
Not sure if I get a 2-path between c;id and c ??? 
--}

data Val1 p = Val1 { c :: Neg p :<-> Pos p }

-- eval1 :: (a ~ (ap :- am), b ~ (bp :- bm)) => 
eval1 :: (Type1 a, Type1 b) =>
         (a :<=> b) -> Val1 a -> Val1 b
eval1 Id1 v = v
eval1 (Sym1 c1) v = eval1B c1 v
eval1 (c1 :..: c2) v = eval1 c2 (eval1 c1 v)
eval1 (alpha :++: beta) (Val1 pOPLUSr) = 
  -- alpha   :: p => q where p : a -> b, q : c -> d
  -- beta    :: r => s where r : e -> f, s : g -> h
  -- pOPLUSr :: a+e -> b+f
  -- want    :: c+g -> h+d
  error "is that possible?"
eval1 PlusZeroL1 (Val1 c0) = 
  Val1 { c = PlusZeroR :.: c0 :.: PlusZeroL }
eval1 PlusZeroR1 (Val1 c0) = 
  Val1 { c = PlusZeroL :.: c0 :.: PlusZeroR }
eval1 CommutePlus1 (Val1 c0) = 
  Val1 { c = CommutePlus :.: c0 :.: CommutePlus } 
eval1 AssocPlusL1 (Val1 c0) =
  Val1 { c = AssocPlusR :.: c0 :.: AssocPlusL }
eval1 AssocPlusR1 (Val1 c0) =
  Val1 { c = AssocPlusL :.: c0 :.: AssocPlusR }

eval1B :: (a ~ (ap :- am), b ~ (bp :- bm)) => 
          (a :<=> b) -> Val1 b -> Val1 a
eval1B Id1 v = v
eval1B (Sym1 c1) v = eval1 c1 v
eval1B (c1 :..: c2) v = eval1B c1 (eval1B c2 v)
eval1B (c1 :++: c2) v = undefined
eval1B PlusZeroL1 (Val1 c0) =
  Val1 { c = PlusZeroL :.: c0 :.: PlusZeroR }
eval1B PlusZeroR1 (Val1 c0) =
  Val1 { c = PlusZeroR :.: c0 :.: PlusZeroL }
eval1B CommutePlus1 (Val1 c0) =
  Val1 { c = CommutePlus :.: c0 :.: CommutePlus }
eval1B AssocPlusL1 (Val1 c0) =
  Val1 { c = AssocPlusL :.: c0 :.: AssocPlusR }
eval1B AssocPlusR1 (Val1 c0) =
  Val1 { c = AssocPlusR :.: c0 :.: AssocPlusL }

------------------------------------------------------------------------------
