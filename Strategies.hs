{-# LANGUAGE TypeFamilies, TypeOperators #-}

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

data TODO

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
  type TimesA (black1 :|: white1) (black2 :|: white2) = TODO

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


