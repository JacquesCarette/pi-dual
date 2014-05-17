{-# LANGUAGE TypeFamilies, TypeOperators, GADTs #-}

module Strategies where

------------------------------------------------------------------------------
-- Every type corresponds to an arena in which black and white can play a
-- game

-- Every value correspods to a move for black. The white player starts the
-- game and is the opponent.

{-- 

Conventionally we have: data Arena = A [Arena] [Arena] where we maintain
lists of games corresponding to left options and to right options. I am going
to call these 'black' options and 'white' options. We play black and the
opponent plays white. The opponent (white) starts. Using that conventional
representation, a move simply selects an index in the list. P.77 of the book
gives examples where it is beneficial to maintain the structure of the games
keeping them separate at the cost of complicating the definition of moves. So
instead of collapsing the structure when we add games:

plusA :: Arena -> Arena -> Arena
g@(Arena gls grs) `plusA` h@(Arena hls hrs) = 
  Arena
    ((map (`plusA` h) gls) ++ (map (g `plusA`) hls))
    ((map (`plusA` h) grs) ++ (map (g `plusA`) hrs))

We maintain the two games as PlusA g1 g2 and when you make a move you can
specify move in the left game which takes you to PlusA (leftOption_of_g1) g2

--}

-- Arenas...

class Arena a where
  type BlackView a :: * 
  type WhiteView a :: *

  type ZeroA        :: *  
  type OneA         :: *  
  type PlusA a1 a2  :: *
  type TimesA a1 a2 :: *
  type NegA a       :: *  

data black :|: white = black :|: white 

data Void 

data BlackProduct bw1 bw2 = 
    BlackBlackLeft (BlackView bw1) 
  | BlackBlackRight (BlackView bw2)
  | BlackBlackBlack (BlackView bw1) (BlackView bw2) -- negated
  | BlackWhiteLeft (WhiteView bw1)
  | BlackWhiteRight (WhiteView bw2)
  | BlackWhiteWhite (WhiteView bw1) (WhiteView bw2) -- negated

data WhiteProduct bw1 bw2 = 
    WhiteBlackLeft (BlackView bw1)
  | WhiteWhiteRight (WhiteView bw2)
  | WhiteBlackWhite (BlackView bw1) (WhiteView bw2) -- negated
  | WhiteWhiteLeft (WhiteView bw1)
  | WhiteBlackRight (BlackView bw2)
  | WhiteWhiteBlack (WhiteView bw1) (BlackView bw2) -- negated

instance Arena (black :|: white) where

  type BlackView (black :|: white) = black
  type WhiteView (black :|: white) = white

  -- in the arena ZeroA, there are no moves for either Black or White
  type ZeroA = Void :|: Void

  -- in the arena OneA, there is one move for Black and none for White
  type OneA = () :|: Void

  -- in the sum of two arenas a1 and a2, Black can move in either arena
  -- and so can White 
  type PlusA (black1 :|: white1) (black2 :|: white2) = 
     (Either black1 black2 :|: Either white1 white2)

  -- in the product arena, it is complicated
  type TimesA (black1 :|: white1) (black2 :|: white2) = 
    (BlackProduct (black1 :|: white1) (black2 :|: white2) :|:
     WhiteProduct (black1 :|: white1) (black2 :|: white2))

  -- in the dual arena, the roles of Black and White are reversed
  type NegA (black :|: white) = (white :|: black) 

-- Some sample arenas

type TwoA    = PlusA OneA OneA  
-- (Either () () :|: Either Void Void)

type ThreeA  = PlusA OneA TwoA
-- (Either () (Either () ()) :|: Either Void (Either Void Void))

type MOneA   = NegA OneA
-- (Void :|: ())

type MTwoA   = NegA TwoA
-- (Either Void Void :|: Either () ())

type ComplicatedOneA = PlusA ThreeA MTwoA
-- (Either (Either () (Either () ())) (Either Void Void) :|:
--  Either (Either Void (Either Void Void)) (Either () ()))

-- Some sample moves 

blackMoveOneA :: BlackView OneA -- ()
blackMoveOneA = ()

blackMoveTwoA1, blackMoveTwoA2 :: BlackView TwoA -- Either () ()
blackMoveTwoA1 = Left ()
blackMoveTwoA2 = Right () 

blackMoveComplicatedOneA :: BlackView ComplicatedOneA
-- Either (Either () (Either () ())) (Either Void Void)
blackMoveComplicatedOneA = Left (Right (Left ()))

whiteMoveComplicatedOneA :: WhiteView ComplicatedOneA
-- Either (Either Void (Either Void Void)) (Either () ())
whiteMoveComplicatedOneA = Right (Left ())

{--

Since the game ComplicatedOneA is presumably equivalent to the game OneA,
it should be possible to have a 1-1 correspondence between the moves in OneA
and the moves in ComplicatedOneA. That's what the pi combinators witness.
Computationally given that I know how to win OneA, I can derive moves 
for ComplicatedOneA that are guaranteed to win.

Note that actually playing games changes the types of the arenas: if I make a
move in arena OneA we are now in arena ZeroA. This is weird

--}

------------------------------------------------------------------------------
-- Pi 
-- Types are arenas
-- Values are moves for Black
-- combinators are black arrows mapping black moves to black moves

type BlackArrow a b = BlackView a -> BlackView b

plusZeroL :: (a ~ (aBlack :|: aWhite)) => BlackArrow (PlusA ZeroA a) a
plusZeroL (Right m) = m

plusZeroR :: (a ~ (aBlack :|: aWhite)) => BlackArrow a (PlusA ZeroA a) 
plusZeroR m = Right m

commutePlus :: (a ~ (aBlack :|: aWhite), b ~ (bBlack :|: bWhite)) => 
               BlackArrow (PlusA a b) (PlusA b a)
commutePlus (Left m) = Right m
commutePlus (Right m) = Left m

timesOneL :: (a ~ (aBlack :|: aWhite)) => BlackArrow (TimesA OneA a) a
timesOneL (BlackBlackLeft ()) = undefined
timesOneL (BlackBlackRight mB) = mB
timesOneL (BlackBlackBlack () mB) = undefined -- negated
timesOneL (BlackWhiteLeft _) = error "Impossible"
timesOneL (BlackWhiteRight mW) = undefined
timesOneL (BlackWhiteWhite _ mW) = error "Impossible"

{--
BlackProduct (() :|: Void) (aB :|: aW) = 
    BlackBlackLeft ()
  | BlackBlackRight aBlack
  | BlackBlackBlack () aBlack -- negated
  | BlackWhiteLeft Void
  | BlackWhiteRight aWhite
  | BlackWhiteWhite Void aWhite -- negated
-> 
aBlack
--}


{--

  assocPlusL   :: PlusA a (PlusA b c) :<=> PlusA (PlusA a b) c 
  assocPlusR   :: PlusA (PlusA a b) c :<=> PlusA a (PlusA b c) 
  TimesOneL    :: TimesA OneA a :<=> a
  TimesOneR    :: a :<=> TimesA OneA a
  CommuteTimes :: TimesA a b :<=> TimesA b a
  AssocTimesL  :: TimesA a (TimesA b c) :<=> TimesA (TimesA a b) c
  AssocTimesR  :: TimesA (TimesA a b) c :<=> TimesA a (TimesA b c)
  TimesZeroL   :: TimesA ZeroA a :<=> ZeroA
  TimesZeroR   :: ZeroA :<=> TimesA ZeroA a
  Distribute   :: TimesA (PlusA b c) a :<=> PlusA (TimesA b a) (TimesA c a)
  Factor       :: PlusA (TimesA b a) (TimesA c a) :<=> TimesA (PlusA b c) a

  Id           :: a :<=> a
  Sym          :: (a :<=> b) -> (b :<=> a) 
  (:.:)        :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:)        :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:)        :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)

  Fold
  Unfold
  TracePlus
  TraceTimes
  EtaPlus
  EpsilonPlus
  EtaTimes
  EpsilonTimes

--}

-----------------------------------------------------------------------

