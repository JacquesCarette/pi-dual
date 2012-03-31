{-# OPTIONS_GHC -XGADTs -XTypeOperators -XExistentialQuantification -XFlexibleContexts #-} -- 7.0.1

import Dual 

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
-- Constructions

-- Some shorthands 
type (:=>>) a b = (Inv a, b)
type (:<<=) a b = (a, Inv b)
type P a = () :<=> a
type N a = a  :<=> ()

makeFunc :: (a :<=> b) -> P (a :=>> b)
makeFunc c = EtaTimes:.: (Id :*: c)

-- Many apply's to be written here based on what interface we want:
-- apply : P (a :=>> b) -> P a -> P b
-- apply : P (a :=>> b) -> (c :<=> a) -> (c :<=> b)
-- apply : ((a :=>> b), a) :<=> b

applyFunc :: ((a :=>> b), a) :<=> b 
applyFunc = CommuteTimes 
            :.: AssocTimesL 
            :.: ((CommuteTimes :.: EpsTimes) :*: Id) 
            :.: UnitE

-- These 
makeDC :: (a :<=> b) -> N (a :<<= b)
makeDC c = (c :*: Id) :.: CommuteTimes :.:  EpsTimes


-- A similar apply is possible, but I dont know what it means. 

-- Trace
traceTimes :: (a, b) :<=> (a, c) -> b :<=> c
traceTimes c = UnitI 
               :.: (EtaTimes:*: Id) 
               :.: AssocTimesR 
               :.: (Id :*: c) 
               :.: AssocTimesL 
               :.: (EpsTimes :*: Id)
               :.: UnitE

-- This is the yanking lemma for trace. 
yankTimes :: a :<=> a
yankTimes = traceTimes CommuteTimes


z_shapeTimes :: a :<=> a
z_shapeTimes = UnitI
               :.: (EtaTimes:*: Id) 
               :.: (CommuteTimes :*: Id)
               :.: AssocTimesR 
               :.: (Id :*: EpsTimes)
               :.: CommuteTimes
               :.: UnitE
               

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
cnot :: (Bool, Bool) :<=> (Bool, Bool)
cnot = controlled inot

-- Toffoli is the universal nand/and gate presented in Reversible
-- Computing by Toffoli.  It is equivalent to controlled controlled
-- not. It takes 3 bools, if the first is True, if applies controlled not
-- to the second 2 bools.
-- REPL Session:
-- *Dual> eval toffoli ((True, True), False)
-- [((True, True), True)]
-- *Dual> eval toffoli ((True, True), True)
-- [((True, True), False)]
-- *Dual> eval toffoli ((True, False), True)
-- [((True, False), True)]
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
           :.: ((EtaPlus :.: CommutePlus) :+: Id)
           :.: AssocPlusR
           :.: (Id :+: EpsPlus)
           :.: CommutePlus
           :.: ZeroE


-- We can now construct a trace using eta and eps. 
trace :: (Either a b :<=> Either a c) -> (b :<=> c)
trace c = ZeroI 
          :.: (EtaPlus :+: Id)
          :.: AssocPlusR
          :.: (Id :+: c)
          :.: AssocPlusL
          :.: (EpsPlus :+: Id)
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
          :.: ((EtaPlus :.: CommutePlus) :*: Id)
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
          :.: (EtaPlus :+: Id)
          :.: AssocPlusR
          :.: (Id :+: eps_fst)
          :.: CommutePlus
          :.: ZeroE


neg_swap :: (Neg a, b) :<=> (a, Neg b)
neg_swap = neg_fst 
           :.: neg_lift CommuteTimes 
           :.: (adjoint neg_fst) 
           :.: CommuteTimes

-- Lifts an isomorphisms to work on negatives. 
neg_lift :: (a :<=> b) -> ((Neg a) :<=> (Neg b))
neg_lift c = ZeroI 
             :.: (EtaPlus :+: Id)
             :.: AssocPlusR
             :.: (Id :+: ((adjoint c) :+: Id))
             :.: (Id :+: (CommutePlus :.: EpsPlus))
             :.: CommutePlus
             :.: ZeroE


type Frac a b = (a, Inv b)

-- So now can we try some of the Hasegawa-Hyland fixpoint
-- constructions?
-- fiore3 :: (

addNumerator :: (Frac a c :+: Frac b c) :<=> Frac (a :+: b) c
addNumerator = Factor


-- *Main> eval (adjoint addHalfs) ()
-- [L ((), Inv True),R ((), Inv False)]
addHalfs :: (Frac () Bool :+: Frac () Bool) :<=> ()
addHalfs = Factor 
           :.: (FoldB :*: Id)
           :.: CommuteTimes
           :.: EpsTimes

-- *Main> eval (adjoint addHalfs2) ()
-- [R ((), Inv True),L ((), Inv False)]
addHalfs2 :: (Frac () Bool :+: Frac () Bool) :<=> ()
addHalfs2 = Factor 
            :.: (FoldB :*: Id)
            :.: (inot :*: Id)
            :.: CommuteTimes
            :.: EpsTimes

-- *Main> eval (adjoint addThirds) ()
-- [L ((), Inv One),R (True, Inv Two),R (False, Inv Three)]
addThirds :: (Frac () Three :+: Frac Bool Three) :<=> ()
addThirds = Factor
            :.: ((Id :+: UnfoldB) :*: Id)
            :.: (FoldThree :*: Id)
            :.: CommuteTimes
            :.: EpsTimes

-- Algebra
-- 1 
-- (-1 + 1) + 1 
-- -1 + (1 + 1)
-- -1 + 1 * 2
-- -1 + (1/2 * 2) * 2
-- -1 + (1/2 * (2 * 2))
-- -1 + (1/2 * ((1+1) + 2) -- swap/not
-- -1 + (1/2 * (2 * 2))
-- -1 + (1/2 * 2) * 2
-- -1 + 1 * 2
-- -1 + (1 + 1)
-- (-1 + 1) + 1 
-- 1 
inf_stream :: () :<=> ()
inf_stream = trace (FoldB :.: inner :.: UnfoldB)
    where 
      inner :: Bool :<=> Bool 
      inner = 
          UnitI
          :.: (EtaTimes :*: Id)
          :.: AssocTimesR
          :.: (Id :*: cnot)
          :.: AssocTimesL
          :.: (EpsTimes :*: Id)
          :.: UnitE
