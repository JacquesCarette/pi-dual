{-# LANGUAGE TypeOperators, GADTs, RankNTypes #-}

module R where

-----------------------------------------------------------------------
-- Pi 

data Zero 

class V a where
instance V Zero
instance V ()
instance V Bool
instance (V a, V b) => V (Either a b) 
instance (V a, V b) => V (a,b) 

data a :<=> b where 
-- Congruence
  Id    :: V a => a :<=> a
  Sym   :: (V a, V b) => (a :<=> b) -> (b :<=> a) 
  (:.:) :: (V a, V b, V c) => (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (V a, V b, V c, V d) => 
           (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:) :: (V a, V b, V c, V d) => 
           (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
-- (+) is associative, commutative, and has a unit
  ZeroE   :: V a => Either Zero a :<=> a
  ZeroI   :: V a => a :<=> Either Zero a
  SwapP   :: (V a, V b) => Either a b :<=> Either b a
  AssocLP  :: (V a, V b, V c) => 
              Either a (Either b c) :<=> Either (Either a b) c 
  AssocRP  :: (V a, V b, V c) => 
              Either (Either a b) c :<=> Either a (Either b c) 
-- (*) is associative, commutative, and has a unit
  UnitE    :: V a => ((), a) :<=> a
  UnitI    :: V a => a :<=> ((), a)
  SwapT    :: (V a, V b) => (a,b) :<=> (b,a) 
  AssocLT  :: (V a, V b, V c) => (a,(b,c)) :<=> ((a,b),c)
  AssocRT  :: (V a, V b, V c) => ((a,b),c) :<=> (a,(b,c))
-- (*) distributes over (+) 
  DistribZ :: V a => (Zero, a) :<=> Zero
  FactorZ  :: V a => Zero :<=> (Zero, a)
  Distrib  :: (V a, V b, V c) => (Either b c, a) :<=> Either (b, a) (c, a)
  Factor   :: (V a, V b, V c) => Either (b, a) (c, a) :<=> (Either b c, a)
-- Encoding of booleans
  FoldB   :: Either () () :<=> Bool
  UnfoldB :: Bool :<=> Either () ()

-- Adjoint

adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint (Sym f) = f 
adjoint (f :.: g) = adjoint g :.: adjoint f
adjoint (f :*: g) = adjoint f :*: adjoint g
adjoint (f :+: g) = adjoint f :+: adjoint g
adjoint ZeroE = ZeroI
adjoint ZeroI = ZeroE
adjoint SwapP = SwapP
adjoint AssocLP = AssocRP
adjoint AssocRP = AssocLP
adjoint UnitE = UnitI
adjoint UnitI = UnitE
adjoint SwapT = SwapT
adjoint AssocLT = AssocRT
adjoint AssocRT = AssocLT
adjoint DistribZ = FactorZ
adjoint FactorZ = DistribZ
adjoint Distrib = Factor
adjoint Factor = Distrib
adjoint FoldB = UnfoldB
adjoint UnfoldB = FoldB

-- Semantics
eval :: (V a, V b) => (a :<=> b) -> a -> b
eval Id a = a
eval (Sym f) b = evalR f b
eval (f :.: g) a = eval g (eval f a)
eval (f :*: g) (a,b) = (eval f a, eval g b) 
eval (f :+: g) (Left a) = Left (eval f a) 
eval (f :+: g) (Right b) = Right (eval g b) 
eval ZeroE (Right a) = a
eval ZeroI a = Right a
eval SwapP (Left a) = Right a
eval SwapP (Right b) = Left b 
eval AssocLP (Left a) = Left (Left a) 
eval AssocLP (Right (Left b)) = Left (Right b) 
eval AssocLP (Right (Right c)) = Right c
eval AssocRP (Left (Left a)) = Left a
eval AssocRP (Left (Right b)) = Right (Left b)
eval AssocRP (Right c) = Right (Right c)
eval UnitE ((), a) = a
eval UnitI a = ((), a)
eval SwapT (a,b) = (b,a) 
eval AssocLT (a,(b,c)) = ((a,b),c) 
eval AssocRT ((a,b),c)  = (a,(b,c))
eval Distrib (Left b, a) = Left (b, a) 
eval Distrib (Right c, a) = Right (c, a) 
eval Factor (Left (b, a)) = (Left b, a) 
eval Factor (Right (c, a)) = (Right c, a) 
eval FoldB (Left ()) = True
eval FoldB (Right ()) = False
eval UnfoldB True = Left ()
eval UnfoldB False = Right ()

evalR :: (V a, V b) => (a :<=> b) -> b -> a
evalR Id a = a
evalR (Sym f) b = eval f b
evalR (f :.: g) a = evalR f (evalR g a)
evalR (f :*: g) (a,b) = (evalR f a, evalR g b) 
evalR (f :+: g) (Left a) = Left (evalR f a) 
evalR (f :+: g) (Right b) = Right (evalR g b) 
evalR ZeroE a = Right a
evalR ZeroI (Right a) = a
evalR SwapP (Left a) = Right a
evalR SwapP (Right b) = Left b 
evalR AssocLP (Left (Left a)) = Left a
evalR AssocLP (Left (Right b)) = Right (Left b)
evalR AssocLP (Right c) = Right (Right c)
evalR AssocRP (Left a) = Left (Left a) 
evalR AssocRP (Right (Left b)) = Left (Right b) 
evalR AssocRP (Right (Right c)) = Right c
evalR UnitE a = ((), a)
evalR UnitI ((), a) = a
evalR SwapT (a,b) = (b,a) 
evalR AssocLT ((a,b),c)  = (a,(b,c))
evalR AssocRT (a,(b,c)) = ((a,b),c) 
evalR Distrib (Left (b, a)) = (Left b, a) 
evalR Distrib (Right (c, a)) = (Right c, a) 
evalR Factor (Left b, a) = Left (b, a) 
evalR Factor (Right c, a) = Right (c, a) 
evalR FoldB True = Left ()
evalR FoldB False = Right ()
evalR UnfoldB (Left ()) = True
evalR UnfoldB (Right ()) = False

-----------------------------------------------------------------------
-- Pi-frac

data Frac a b =
  forall a' b'. (V a', V b') => Frac { iso :: (a,b') :<=> (a',b) }

recip :: (V a, V b) => Frac a b -> Frac b a
recip (Frac f) = Frac (SwapT :.: adjoint f :.: SwapT) 

times :: (V a, V b, V c, V d) => 
         Frac a b -> Frac c d -> Frac (a,c) (b,d) 
times (Frac f) (Frac g) = 
  -- f :: (a,b') :<=> (a',b) 
  -- g :: (c,d') :<=> (c',d)
  -- want ((a,c),y') :<=> (x',(b,d))
  -- choose y' = (b',d'), x' = (a',c')
  -- input ((a,c),(b',d')) 
    Frac (shuffle :.: -- ((a,b'),(c,d'))
          (f :*: g) :.: -- ((a',b),(c',d))
          adjoint shuffle) -- ((a',c'),(b,d))
  where shuffle :: (V a, V b, V c, V d) => 
                   ((a,c),(b,d)) :<=> ((a,b),(c,d))
        shuffle = AssocRT :.: -- (a,(c,(b,d)))
                  (Id :*: AssocLT) :.: -- (a,((c,b),d))
                  (Id :*: (SwapT :*: Id)) :.: -- (a,((b,c),d))
                  (Id :*: AssocRT) :.: -- (a,(b,(c,d)))
                  AssocLT -- ((a,b),(c,d))

plus :: (V a, V b, V c, V d) => 
        Frac a b -> Frac c d -> Frac (Either a c) (Either b d) 
plus (Frac f) (Frac g) =          
  -- f :: (a,b') :<=> (a',b) 
  -- g :: (c,d') :<=> (c',d)
  -- want (Either a c, y') :<=> (x',Either b d)
  undefined


    


-----------------------------------------------------------------------
