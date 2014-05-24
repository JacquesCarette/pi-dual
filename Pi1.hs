{-# LANGUAGE TypeOperators, GADTs, TypeFamilies #-}

module Pi1 where

-- Pi0 is the usual Pi

-- Pi1 is the next up based on the Int construction (only possible after we
-- liberate ourselves from the brain-damaging notion that t1-t2 is a sum
-- type)

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
eval0 c _ = error "I am not writing this again; get it from somewhere"

------------------------------------------------------------------------------
-- Pi1 

class Type1 p where
  type Pos p      :: *
  type Neg p      :: *  
  type Zero1      :: * 
  type One1       :: *
  type Plus1 p q  :: *
  type Dual1 p    :: * 
  type Lolli1 p q :: * 

data a :- b = a :- b

instance Type1 (ap :- am) where
  type Pos (ap :- am) = ap
  type Neg (ap :- am) = am
  type Zero1 = Zero :- Zero
  type One1 = () :- Zero
  type Plus1  (ap :- am) (bp :- bm) = (Either ap bp) :- (Either am bm)
  type Dual1  (ap :- am) = am :- ap
  type Lolli1 (ap :- am) (bp :- bm) = (Either am bp) :- (Either ap bm)

data a :<=> b where 
  Id1           :: a :<=> a
  Sym1          :: (a :<=> b) -> (b :<=> a) 
  (:..:)        :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:++:)        :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
  PlusZeroL1    :: Plus1 Zero1 a :<=> a
  PlusZeroR1    :: a :<=> Plus1 Zero1 a
  CommutePlus1  :: Plus1 a b :<=> Plus1 b a
  AssocPlusL1   :: Plus1 a (Plus1 b c) :<=> Plus1 (Plus1 a b) c 
  AssocPlusR1   :: Plus1 (Plus1 a b) c :<=> Plus1 a (Plus1 b c) 

data Val1 p = Val1 { c :: Neg p :<-> Pos p }

eval1 :: (a ~ (ap :- am), b ~ (bp :- bm)) => 
         (a :<=> b) -> Val1 a -> Val1 b
eval1 Id1 v = v
eval1 (Sym1 c) v = eval1B c v
eval1 (c1 :..: c2) v = undefined
eval1 PlusZeroL1 (Val1 c0) = 
    -- c :: 0+am <-> 0+ap
    -- we want :: am <-> ap
    Val1 {
       c = PlusZeroR :.: c0 :.: PlusZeroL
    }
eval1 PlusZeroR1 v = undefined
eval1 CommutePlus1 v = undefined
eval1 AssocPlusL1 v = undefined
eval1 AssocPlusR1 v = undefined

eval1B :: (a ~ (ap :- am), b ~ (bp :- bm)) => 
          (a :<=> b) -> Val1 b -> Val1 a
eval1B Id1 v = v
eval1B (Sym1 c) v = eval1 c v
eval1B (c1 :..: c2) v = undefined
eval1B PlusZeroL1 v = undefined
eval1B PlusZeroR1 v = undefined
eval1B CommutePlus1 v = undefined
eval1B AssocPlusL1 v = undefined
eval1B AssocPlusR1 v = undefined

------------------------------------------------------------------------------
