-- {-# OPTIONS_GHC -fglasgow-exts #-} -- 6.12.3
{-# OPTIONS_GHC -XGADTs -XTypeOperators #-} -- 7.0.1


module PiCont where

import Data.Typeable
-- needed for polymorphic lookup. 
import qualified Unsafe.Coerce as Coerce 
import qualified Debug.Trace as Trace

-----------------------------------------------------------------------
-- Isomorphisms 

data Zero 
data Neg a = Neg a

instance Show a => Show (Neg a) where 
    show (Neg a) = "(Neg " ++ (show a) ++ ")"

data Three = One 
           | Two 
           | Three
             deriving Show

data Tree = Leaf 
          | Node Tree Tree
            deriving Show

data a :<=> b where 
-- Congruence
  Id    :: a :<=> a
  IdTrace :: a :<=> a
  Adj   :: (a :<=> b) -> (Neg b :<=> Neg a) 
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
-- Encoding of booleans
  FoldB   :: Either () () :<=> Bool
  UnfoldB :: Bool :<=> Either () ()
  FoldThree   :: Either () (Either () ()) :<=> Three
  UnfoldThree :: Three :<=> Either () (Either () ())
  FoldTree   :: Either () (Tree, Tree) :<=> Tree
  UnfoldTree :: Tree :<=> Either () (Tree, Tree)
-- Eta and Eps over the monoid (*, 1)
  Eta :: Zero :<=> Either a (Neg a)
  Eps :: Either (Neg a) a :<=> Zero


-- Note: Negative types are opaque in this sytem. Once we have a
-- negative value, we cant really do anything with it, except pass it
-- around and eventually make it positive using a Eta. 
-- 
-- It would be good if there were isomorphisms on negative values to
-- reveal more of their structure. One possible such isomorphism is
-- -(a+b) <-> (-a) + (-b) 
-- 
-- However adding such laws should not add any expressive power to
-- this language because their computational equivalent can always be
-- achieved by make the value positive, computing, and then making it
-- negative again i.e. uzing a z shaped circuit. 

instance Show (a :<=> b) where 
    show Id = "Id"
    show IdTrace = "IdTrace"
    show (Adj a) = "(Adj " ++ (show a) ++ ")"
    show (f :*: g) = "(" ++ (show f) ++ " :*: " ++ (show g) ++ ")"
    show (f :+: g) = "(" ++ (show f) ++ " :+: " ++ (show g) ++ ")"
    show (f :.: g) = "(" ++ (show f) ++ " :.: " ++ (show g) ++ ")"
    --
    show ZeroE = "ZeroE"
    show ZeroI = "ZeroI"
    show CommutePlus = "CommutePlus"
    show AssocPlusL = "AssocPlusL"
    show AssocPlusR = "AssocPlusR"
    --
    show UnitI = "UnitI"
    show UnitE = "UnitE"
    show CommuteTimes = "CommuteTimes"
    show AssocTimesR = "AssocTimesR"
    show AssocTimesL = "AssocTimesL"
    --
    show TimesZeroR = "TimesZeroR"
    show TimesZeroL = "TimesZeroL"
    show Distribute = "Distribute"
    show Factor = "Factor"
    --
    show FoldB = "FoldB"
    show UnfoldB = "UnfoldB"
    --
    show Eta = "Eta"
    show Eps = "Eps"

-- Adjoint

adjoint :: (a :<=> b) -> (b :<=> a)
adjoint Id = Id
adjoint IdTrace = IdTrace
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
adjoint FoldB = UnfoldB
adjoint UnfoldB = FoldB
adjoint FoldThree = UnfoldThree
adjoint UnfoldThree = FoldThree
adjoint FoldTree = UnfoldTree
adjoint UnfoldTree = FoldTree
adjoint Eta = CommutePlus :.: Eps
adjoint Eps = Eta :.: CommutePlus

------------------------------------------------------------------------


data SeqContext a b where 
    EmptySeq :: SeqContext a a
    Cons :: (a :<=> b) -> SeqContext b c -> SeqContext a c

data App a b where 
    Tbd :: (a :<=> b) -> a -> App a b
    Don :: b -> (b :<=> a) -> App a b

-- hole input and output
-- external input and output
data Dumps hi ho ei eo where 
    EmptyD :: Dumps ei eo ei eo 
    ConsD :: Dump hi ho ei' eo' -> 
             Dumps ei' eo' ei eo -> 
             Dumps hi ho ei eo

data Dump hi ho ei eo where 
    SumRight :: SeqContext (Either a c) ei -> 
                (a :<=> b) -> 
                SeqContext (Either b d) eo -> 
                Dump c d ei eo
    SumLeft :: SeqContext (Either a c) ei -> 
               (c :<=> d) -> 
               SeqContext (Either b d) eo -> 
               Dump a b ei eo
    PairFstTbd :: SeqContext (a, c) ei -> 
                  (c :<=> d) -> 
                  c -> 
                  SeqContext (b, d) eo -> 
                  Dump a b ei eo
    PairFstDon :: SeqContext (a, c) ei -> 
                  d -> 
                  (d :<=> c) -> 
                  SeqContext (b, d) eo -> 
                  Dump a b ei eo
    PairSndTbd :: SeqContext (a, c) ei -> 
                  (a :<=> b) -> 
                  a -> 
                  SeqContext (b, d) eo -> 
                  Dump c d ei eo
    PairSndDon :: SeqContext (a, c) ei -> 
                  b -> 
                  (b :<=> a) -> 
                  SeqContext (b, d) eo -> 
                  Dump c d ei eo



adjointDumps :: Dumps hi ho ei eo -> Dumps ho hi eo ei
adjointDumps EmptyD = EmptyD
adjointDumps (ConsD d ds) = ConsD (adjointDump d) (adjointDumps ds)

adjointDump :: Dump hi ho ei eo -> Dump ho hi eo ei
adjointDump (SumRight p c f) = SumRight f (adjoint c) p
adjointDump (SumLeft p c f) = SumLeft f (adjoint c) p
adjointDump (PairFstTbd p c v f) = PairFstDon f v c p
adjointDump (PairFstDon p v c f) = PairFstTbd f c v p
adjointDump (PairSndTbd p c v f) = PairSndDon f v c p
adjointDump (PairSndDon p v c f) = PairSndTbd f c v p


eval_iso :: (a :<=> b) -> a -> (b, b :<=> a)
eval_iso c v = (c @@ v, adjoint c)


-- show_force :: a -> String
-- show_force a = (coerce (Coerce.unsafeCoerce a))
--     where 
--       coerce :: Show a => a -> String
--       coerce x = show x



(@@) :: (a :<=> b) ->  a ->  b
Id @@ a = a
-- IdTrace @@ a = Trace.trace (show_force a) a
(Adj f) @@ _ = error "Unexpected adjoint in @@"
(f :+: g) @@ _ = error "Unexpected :+: in @@"
(f :*: g) @@ (a,c) = error "Unexpected :*: in @@"
(f :.: g) @@ a = error "Unexpected :.: in @@"
---
ZeroE @@ (Right a) = a
ZeroE @@ (Left a) = error "ZeroE (Left _) : Type system is broken"
ZeroI @@ a = Right a 
CommutePlus @@ (Left a) = Right a
CommutePlus @@ (Right b) = Left b
AssocPlusL @@ (Left a) = Left (Left a)
AssocPlusL @@ (Right (Left b)) = Left (Right b)
AssocPlusL @@ (Right (Right c)) = Right c
AssocPlusR @@ (Left (Left a)) = Left a
AssocPlusR @@ (Left (Right b)) = Right (Left b) 
AssocPlusR @@ (Right c) = Right (Right c)
---
UnitE @@ ((), a) = a
UnitI @@ a = ((), a)
CommuteTimes @@ (a,b) = (b,a)
AssocTimesL @@ (a,(b,c)) = ((a,b),c)
AssocTimesR @@ ((a,b),c) = (a,(b,c))
---
TimesZeroL @@ _ = error "TimesZero b elim" 
TimesZeroR @@ _ = error "TimesZero b intro"
Distribute @@ (Left b, a) = Left (b, a) 
Distribute @@ (Right c, a) = Right (c, a) 
Factor @@ (Left (b, a)) = (Left b, a)
Factor @@ (Right (c, a)) = (Right c, a) 
--
FoldB @@ (Left ()) = True
FoldB @@ (Right ()) = False
UnfoldB @@ True = Left ()
UnfoldB @@ False = Right ()
--
FoldThree @@ (Left ()) = One 
FoldThree @@ (Right (Left ())) = Two
FoldThree @@ (Right (Right ())) = Three
UnfoldThree @@ One = Left ()
UnfoldThree @@ Two = Right (Left ())
UnfoldThree @@ Three = Right (Right ())
--
FoldTree @@ (Left ()) = Leaf
FoldTree @@ (Right (t1, t2)) = Node t1 t2
UnfoldTree @@ Leaf = Left ()
UnfoldTree @@ (Node t1 t2) = Right (t1, t2)
--
Eta @@ _ = error "Unexpected Eta in @@"
Eps @@ _ = error "Unexpected Eps in @@"
--
-- f @@ _ = error $ "Found " ++ (show f)


-- op @@ v = error (show op) ++ " and " ++ (show v)
-- (f :+: g) @@ (Left a) = Left (f @@ a)
-- (f :+: g) @@ (Right c) = Right (g @@ c)
-- (f :*: g) @@ (a,c) = (f @@ a, g @@ c)
-- (f :.: g) @@ a = g @@ (f @@ a)

rebuild :: SeqContext b c -> (a :<=> b) -> (a :<=> c)
rebuild EmptySeq c = c
rebuild (Cons c' cs) c = rebuild cs (c :.: c')


eval :: (a :<=> b) -> a -> b
eval c v = fwd EmptySeq EmptySeq (Tbd c v) EmptyD
    where 
      fwd :: SeqContext a b -> SeqContext c d -> App a c -> Dumps b d ei eo -> eo
      -- Unload.
      fwd p EmptySeq (Don v c) EmptyD = v
      -- Sequencing with Past and Future
      fwd p f (Tbd (c1 :.: c2) v) ds = fwd p (Cons c2 f) (Tbd c1 v) ds
      fwd p (Cons c2 f) (Don v c1) ds = fwd (Cons c1 p) f (Tbd c2 v) ds
      -- Products Fst
      fwd p f (Tbd (c1 :*: c2) (v1, v2)) ds = 
          let d = PairFstTbd p c2 v2 f
          in fwd EmptySeq EmptySeq (Tbd c1 v1) (ConsD d ds)
      -- Products Snd
      fwd p EmptySeq (Don v1 c1) (ConsD (PairFstTbd p' c2 v2 f') ds) = 
          let d = PairSndDon p' v1 (rebuild p c1) f'
          in fwd EmptySeq EmptySeq (Tbd c2 v2) (ConsD d ds)
      fwd p EmptySeq (Don v2 c2) (ConsD (PairSndTbd p' c1 v1 f') ds) = 
          let d = PairFstDon p' v2 (rebuild p c2) f'
          in fwd EmptySeq EmptySeq (Tbd c1 v1) (ConsD d ds)
      -- Products Pop
      fwd p EmptySeq (Don v2 c2) (ConsD (PairSndDon p' v1 c1 f') ds) = 
          let c2' = rebuild p c2
          in fwd p' f' (Don (v1, v2) (c1 :*: c2')) ds
      fwd p EmptySeq (Don v1 c1) (ConsD (PairFstDon p' v2 c2 f') ds) = 
          let c1' = rebuild p c1
          in fwd p' f' (Don (v1, v2) (c1' :*: c2)) ds
      -- Pushing Sums (Left and Right)
      fwd p f (Tbd (c1 :+: c2) (Left v)) ds = 
          let d = SumLeft p c2 f
          in fwd EmptySeq EmptySeq (Tbd c1 v) (ConsD d ds)
      fwd p f (Tbd (c1 :+: c2) (Right v)) ds = 
          let d = SumRight p c1 f
          in fwd EmptySeq EmptySeq (Tbd c2 v) (ConsD d ds)
      -- Popping sums (Left and Right)
      fwd p EmptySeq (Don v c1) (ConsD (SumLeft p' c2 f') d) = 
          let c1' = rebuild p c1
              c2' = adjoint c2
          in fwd p' f' (Don (Left v) (c1' :+: c2')) d
      fwd p EmptySeq (Don v c2) (ConsD (SumRight p' c1 f') d) = 
          let c2' = rebuild p c2
              c1' = adjoint c1
          in fwd p' f' (Don (Right v) (c1' :+: c2')) d
      -- Eps rule : flips the world
      fwd p f (Tbd Eps (Right v)) ds = 
          bck f p (Don (Left (Neg v)) Eps) (adjointDumps ds)
      fwd p f (Tbd Eps (Left (Neg v))) ds = 
          bck f p (Don (Right v) Eps) (adjointDumps ds)
      -- Primitive Isos
      fwd p f (Tbd c v) ds = 
          --Trace.trace ("fwd:" ++ (show c)) $
          let (v', adj) = eval_iso c v
          in fwd p f (Don v' adj) ds

      -- This is a not a backward evaluator, but it exists to capture
      -- the idea that evaluation is now happening in the opposite
      -- direction. When this happens if the function terminates, it
      -- means that a negative value has "fallen off" the left end of
      -- a circuit. Well typed circuits should map positives to
      -- positives.
      bck :: SeqContext a b -> SeqContext c d -> App a c -> Dumps b d ei eo -> ei
      -- Unload.
      bck p EmptySeq (Don v c) EmptyD = error "backwards execution cannot return"
      -- Sequencing with Past and Future
      bck p f (Tbd (c1 :.: c2) v) ds = bck p (Cons c2 f) (Tbd c1 v) ds
      bck p (Cons c2 f) (Don v c1) ds = bck (Cons c1 p) f (Tbd c2 v) ds
      -- Products Fst
      bck p f (Tbd (c1 :*: c2) (v1, v2)) ds = 
          let d = PairFstTbd p c2 v2 f
          in bck EmptySeq EmptySeq (Tbd c1 v1) (ConsD d ds)
      -- Products Snd
      bck p EmptySeq (Don v1 c1) (ConsD (PairFstTbd p' c2 v2 f') ds) = 
          let d = PairSndDon p' v1 (rebuild p c1) f'
          in bck EmptySeq EmptySeq (Tbd c2 v2) (ConsD d ds)
      bck p EmptySeq (Don v2 c2) (ConsD (PairSndTbd p' c1 v1 f') ds) = 
          let d = PairFstDon p' v2 (rebuild p c2) f'
          in bck EmptySeq EmptySeq (Tbd c1 v1) (ConsD d ds)
      -- Products Pop
      bck p EmptySeq (Don v2 c2) (ConsD (PairSndDon p' v1 c1 f') ds) = 
          let c2' = rebuild p c2
          in bck p' f' (Don (v1, v2) (c1 :*: c2')) ds
      bck p EmptySeq (Don v1 c1) (ConsD (PairFstDon p' v2 c2 f') ds) = 
          let c1' = rebuild p c1
          in bck p' f' (Don (v1, v2) (c1' :*: c2)) ds
      -- Pushing Sums (Left and Right)
      bck p f (Tbd (c1 :+: c2) (Left v)) ds = 
          let d = SumLeft p c2 f
          in bck EmptySeq EmptySeq (Tbd c1 v) (ConsD d ds)
      bck p f (Tbd (c1 :+: c2) (Right v)) ds = 
          let d = SumRight p c1 f
          in bck EmptySeq EmptySeq (Tbd c2 v) (ConsD d ds)
      -- Popping sums (Left and Right)
      bck p EmptySeq (Don v c1) (ConsD (SumLeft p' c2 f') d) = 
          let c1' = rebuild p c1
              c2' = adjoint c2
          in bck p' f' (Don (Left v) (c1' :+: c2')) d
      bck p EmptySeq (Don v c2) (ConsD (SumRight p' c1 f') d) = 
          let c2' = rebuild p c2
              c1' = adjoint c1
          in bck p' f' (Don (Right v) (c1' :+: c2')) d
      -- Eps rule : flips the world
      bck p f (Tbd Eps (Left (Neg v))) ds = 
          fwd f p (Don (Right v) Eps) (adjointDumps ds)
      bck p f (Tbd Eps (Right v)) ds = 
          fwd f p (Don (Left (Neg v)) Eps) (adjointDumps ds)
      -- Primitive Isos
      bck p f (Tbd c v) ds = 
          --Trace.trace ("bck:" ++ (show c)) $
          let (v', adj) = eval_iso c v
          in bck p f (Don v' adj) ds




--------------------------------------------------------------------
-- Tests

-- Not works by first converting the Haskell boolean via a Unfold to
-- either Left () or Right (), where True is Left (), False is Right ().
-- not can simply use CommutePlus to perform a not, then Fold up the
-- bool.
-- REPL Session:
-- *Pi> inot @@ True
-- False
-- *Pi> inot @@ False
inot :: Bool :<=> Bool
inot = UnfoldB :.: CommutePlus :.: FoldB

-- Cond takes two isomorphisms from some type a to some type b, and 
-- creates an isomorphism between a pair of (Bool, a) which will apply
-- the first isomorphism if the Bool is True, and the second if the Bool
-- is False.
cond :: (a :<=> b) -> (a :<=> b) -> ((Bool, a) :<=> (Bool, b))
cond f g = (UnfoldB :*: Id) 
           :.: Distribute 
           :.: ((Id :*: f) :+: (Id :*: g))
           :.: Factor 
           :.: (FoldB :*: Id) 

-- controlled takes an isomorphism between a type a to type a, and 
-- creates an isomorphism (using cond) that will apply the isomorphism to
-- the second value of the pair, if the first value if True, and apply
-- Id otherwise.
controlled :: (a :<=> a) -> ((Bool, a) :<=> (Bool, a))
controlled f = cond f Id

-- cnot is Controlled Not, as found in reversible computing papers such
-- as Reversible Computing by Toffoli. It takes a pair of bools, and
-- applies not to the second Bool if the first is True, and otherwise
-- leaves the value unchanged.
-- REPL Session:
-- *Pi> cnot @@ (True, True)
-- (True, False)
-- *Pi> cnot @@ (False, True)
-- (False, True)
-- *Pi> cnot @@ (True, False)
-- (True, False)
cnot :: (Bool, Bool) :<=> (Bool, Bool)
cnot = controlled inot

-- Toffoli is the universal nand/and gate presented in Reversible
-- Computing by Toffoli.  It is equivalent to controlled controlled
-- not. It takes 3 bools, if the first is True, if applies controlled not
-- to the second 2 bools.
-- REPL Session:
-- *Pi> toffoli @@ ((True, True), False)
-- ((True, True), True)
-- *Pi> toffoli @@ ((True, False), False)
-- ((True, False), False)
-- *Pi> toffoli @@ ((True, True), True)
-- ((True, True), False)
-- *Pi> toffoli @@ ((False, True), False)
-- ((False, True), False)
toffoli :: ((Bool,Bool),Bool) :<=> ((Bool,Bool),Bool)
toffoli = AssocTimesR :.: controlled cnot :.: AssocTimesL

-- The Fredkin gate is a well known universal gate.
-- If the first bool is true, it swaps the second two, otherwise it
-- leaves the values unchanged.
fredkin :: (Bool,(Bool,Bool)) :<=> (Bool,(Bool,Bool))
fredkin = controlled CommuteTimes



-- Teleportation (??)
-- Also the coherence condition for eta/eps for compact closed categories. 
-- *PiCont> eval z_shape False
-- False
-- *PiCont> eval z_shape True
-- True
-- *PiCont> eval z_shape (True, False)
-- (True,False)
z_shape :: b :<=> b
z_shape = ZeroI 
           :.: (Eta :+: Id)
           :.: AssocPlusR
           :.: (Id :+: Eps)
           :.: CommutePlus
           :.: ZeroE


-- We can now construct a trace using eta and eps. 
trace :: (Either a b :<=> Either a c) -> (b :<=> c)
trace c = ZeroI 
          :.: ((Eta :.: CommutePlus) :+: Id)
          :.: AssocPlusR
          :.: (Id :+: c)
          :.: AssocPlusL
          :.: (Eps :+: Id)
          :.: ZeroE

-- Yanking 
-- Should be Id
yank :: b :<=> b
yank = trace CommutePlus


-- Yank Not : bool -> bool
-- *PiCont> eval yank_not True
-- False
-- *PiCont> eval yank_not False
-- True
yank_not :: Bool :<=> Bool
yank_not = trace (CommutePlus :.: (inot :+: Id))


-- eta and eps over products
eta_fst :: Zero :<=> Either (a,b) (Neg a, b)
eta_fst = TimesZeroR
          :.: (Eta :*: Id)
          :.: Distribute

eta_snd :: Zero :<=> Either (a,b) (a, Neg b)
eta_snd = eta_fst :.: (CommuteTimes :+: CommuteTimes)

eps_fst :: Either (a,b) (Neg a, b) :<=> Zero
eps_fst = adjoint eta_fst

eps_snd :: Either (a,b) (a, Neg b) :<=> Zero
eps_snd = adjoint eta_snd



-- *PiCont> eval neg_fst (Neg True, False)
-- (Neg (True,False))
neg_fst :: (Neg a, b) :<=> Neg (a, b)
neg_fst = ZeroI 
          :.: ((Eta :.: CommutePlus) :+: Id)
          :.: AssocPlusR
          :.: (Id :+: eps_fst)
          :.: CommutePlus
          :.: ZeroE


neg_swap :: (Neg a, b) :<=> (Neg b, a)
neg_swap = neg_fst 
           :.: neg_lift CommuteTimes 
           :.: (adjoint neg_fst) 

-- Lifts an isomorphisms to work on negatives. 
neg_lift :: (a :<=> b) -> ((Neg a) :<=> (Neg b))
neg_lift c = ZeroI 
             :.: ((Eta :.: CommutePlus) :+: Id)
             :.: AssocPlusR
             :.: (Id :+: ((adjoint c) :+: Id))
             :.: (Id :+: (CommutePlus :.: Eps))
             :.: CommutePlus
             :.: ZeroE



fiore3 :: (Tree, (Tree, Tree)) :<=> (Neg ())
fiore3 = (Id :*: (ZeroI :.: CommutePlus))
         :.: (Id :*: (Id :+: Eta))
         :.: (Id :*: AssocPlusL)
         :.: (Id :*: ((CommutePlus :.: FoldTree) :+: Id))
         :.: CommuteTimes
         :.: Distribute
         :.: ((ZeroI :.: ((Eta :.: CommutePlus) :+: Id)) :+: Id)
         :.: (AssocPlusR :+: Id)
         :.: ((Id :+: FoldTree) :+: Id)
         :.: (Id :+: neg_fst)
         :.: (Id :+: (neg_lift UnitE))
         :.: AssocPlusR
         :.: (Id :+: (CommutePlus :.: Eps))
         :.: CommutePlus
         :.: ZeroE


