{-# OPTIONS_GHC -XGADTs -XTypeOperators -XExistentialQuantification -XFlexibleContexts -XScopedTypeVariables #-} -- 7.0.1, 7.0.3

import Dual 

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
-- Constructions

traceTimes :: (a, b) :<=> (a, c) -> b :<=> c
traceTimes c = UnitI 
               :.: (EtaTimes :*: Id) 
               :.: AssocTimesR 
               :.: (Id :*: c) 
               :.: AssocTimesL 
               :.: (EpsTimes :*: Id)
               :.: UnitE

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
               

----------------------------------------------------------------

tracePlus :: (Either a b :<=> Either a c) -> (b :<=> c)
tracePlus c = ZeroI 
          :.: (EtaPlus :+: Id)
          :.: AssocPlusR
          :.: (Id :+: c)
          :.: AssocPlusL
          :.: (EpsPlus :+: Id)
          :.: ZeroE

yankPlus :: b :<=> b
yankPlus = trace CommutePlus

-- Teleportation (??)
-- Also the coherence condition for eta/eps for compact closed categories. 
-- *PiCont> eval z_shape False
-- False
-- *PiCont> eval z_shape True
-- True
-- *PiCont> eval z_shape (True, False)
-- (True,False)
z_shapePlus :: b :<=> b
z_shapePlus = ZeroI 
           :.: ((EtaPlus :.: CommutePlus) :+: Id)
           :.: AssocPlusR
           :.: (Id :+: EpsPlus)
           :.: CommutePlus
           :.: ZeroE




-- Yank Not : bool -> bool
-- *PiCont> eval yank_not True
-- False
-- *PiCont> eval yank_not False
-- True
yank_not :: Bool :<=> Bool
yank_not = trace (CommutePlus :.: (inot :+: Id))

----------------------------------------------------------------
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

----------------------------------------------------------------
-- Operations on fractions

type Frac a b = (a, Inv b)

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

--------------------------------------------------------------------
-- Simple Conditionals

-- inot works by first converting the Haskell boolean via a Unfold to
-- either Left () or Right (), where True is Left (), False is Right
-- ().  inot can simply use CommutePlus to perform a not, then Fold up
-- the bool.
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


------------------------------------------------------------------
-- Weak Normalization

-- 1 
-- (-1 + 1) + 1 
-- -1 + (1 + 1)
-- -1 + 1 * 2
-- -1 + (1/2 * 2) * 2
-- -1 + (1/2 * (2 * 2))
-- -1 + (1/2 * ((1+1) * 2) -- swap/not
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

inf_three :: (Three :<=> Three) -> Either () () :<=> Either () ()
inf_three f = trace (FoldThree :.: inner :.: UnfoldThree)
    where 
      inner = 
          UnitI
          :.: (EtaTimes :*: Id)
          :.: AssocTimesR
          :.: (Id :*: controlled f)
          :.: AssocTimesL
          :.: (EpsTimes :*: Id)
          :.: UnitE


----------------------------------------------------------------
-- Some shorthands 

type (:=>>) a b = (Inv a, b)
type (:<<=) a b = (a, Inv b)
type P a = () :<=> a
type N a = a  :<=> ()

makeFunc :: (a :<=> b) -> P (a :=>> b)
makeFunc c = EtaTimes:.: (Id :*: c)

applyFunc :: ((a :=>> b), a) :<=> b 
applyFunc = CommuteTimes 
            :.: AssocTimesL 
            :.: ((CommuteTimes :.: EpsTimes) :*: Id) 
            :.: UnitE

makeDC :: (a :<=> b) -> N (a :<<= b)
makeDC c = (c :*: Id) :.: CommuteTimes :.:  EpsTimes



