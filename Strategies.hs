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

Since the game ComplicatedOneA is presumably equivalent to the game OneA, it
should be possible to have a 1-1 correspondence between the moves in OneA and
the moves in ComplicatedOneA. However it is clear that in OneA, White has no
moves but that in ComplicatedOneA, White has a move. So a 1-1 correspondence
between moves won't work. What will work is matching winning
strategies. White has no winning strategy in OneA (obvious) but White also
has no winning strategy in ComplicatedOneA. That's what the pi combinators
witness.  Computationally given that I know how to win OneA, I can derive
a strategy for ComplicatedOneA that is guaranteed to win.

In ComplicatedOneA, White has two opening moves 
  Right (Left ()) or Right (Right ()). 
They are really similar. Consider the following game:
-- original arena: 
-- = PlusA (PlusA (() :|: Void) (PlusA (() :|: Void) (() :|: Void)))
--         (Neg (PlusA (() :|: Void) (() :|: Void)))
-- White's has two similar moves, say White chooses Right (Left ())
-- new arena
-- = PlusA (PlusA (() :|: Void) (PlusA (() :|: Void) (() :|: Void)))
--         (Neg (PlusA (Void :|: Void) (() :|: Void)))
-- Black has three moves in the left part of the game. They are all similar
-- so assume black chooses Left (Left ())
-- new arena is:
-- = PlusA (PlusA (Void :|: Void) (PlusA (() :|: Void) (() :|: Void)))
--         (Neg (PlusA (Void :|: Void) (() :|: Void)))
-- White has only one possible move Right (Right ()) which leads to:
-- = PlusA (PlusA (Void :|: Void) (PlusA (() :|: Void) (() :|: Void)))
--         (Neg (PlusA (Void :|: Void) (Void :|: Void)))
-- Black has two moves to choose from; we move to:
-- = PlusA (PlusA (Void :|: Void) (PlusA (Void :|: Void) (() :|: Void)))
--         (Neg (PlusA (Void :|: Void) (Void :|: Void)))
-- White has no moves; Black wins
-- To summarize, Black's strategy in the game (ThreeA `plusA` MTwoA) is to
-- counter any move by White in MTwoA by a move in ThreeA

There should be a Pi combinator mapping 3-2 to 1. That circuit is probably
what we want to compute the above:

3 - 2 <==> 1
(3 :|: 0) + (0 :|: 2) <==> (1 :|: 0)
(3 + 0 :|: 0 + 2) <==> (1 :|: 0)

A map (b1 :|: w1) <==> (b2 :|: w2)
is a map (b1 + w2 <==> b2 + w1) in plain Pi

So the above is the following map in plain Pi
(3 + 0) + 0 <==> 1 + (0 + 2)
which is easy to implement in Pi
It show that the one move advantage for Black in the arena '1' plus the two
move advantage for white in the arena '-2' are equivalent to the '3' move
advantage for black in the arena 3.

So we are back to mapping moves to moves but in a way that balances the
advantage for black against the advantage for white

--}

-- So what we want is to map between (b1 :|: w1) and (b2 :|: w2) as follows:

type M a b = 
  Either (BlackView a) (WhiteView b) :<=> Either (WhiteView a) (BlackView b)

data a :<=> b where 
  Id           :: a :<=> a
  Sym          :: (a :<=> b) -> (b :<=> a) 
  (:.:)        :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:)        :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  (:+:)        :: (a :<=> b) -> (c :<=> d) -> (Either a c :<=> Either b d)
  PlusZeroL    :: Either Void a :<=> a
  PlusZeroR    :: a :<=> Either Void a
  CommutePlus  :: Either a b :<=> Either b a
  AssocPlusL   :: Either a (Either b c) :<=> Either (Either a b) c 
  AssocPlusR   :: Either (Either a b) c :<=> Either a (Either b c) 
  TimesOneL    :: ((), a) :<=> a
  TimesOneR    :: a :<=> ((), a)
  CommuteTimes :: (a,b) :<=> (b,a) 
  AssocTimesL  :: (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: ((a,b),c) :<=> (a,(b,c))
  TimesZeroL   :: (Void, a) :<=> Void
  TimesZeroR   :: Void :<=> (Void, a)
  Distribute   :: (Either b c, a) :<=> Either (b, a) (c, a)
  Factor       :: Either (b, a) (c, a) :<=> (Either b c, a)

plusZeroL :: (a ~ (aBlack :|: aWhite)) => M (PlusA ZeroA a) a
plusZeroL = AssocPlusR :.: (Id :+: CommutePlus) :.: AssocPlusL

{--

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

