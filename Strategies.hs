module Strategies where

import Debug.Trace

------------------------------------------------------------------------------
-- Every type corresponds to an arena. 
-- Every value correspods to a move (or perhaps strategy) for black

{-- 

Conventionally we have: data Arena = A [Arena] [Arena] where we maintain
lists of games corresponding to left options and to right options. I am going
to call these 'black' options and 'white' options. We play black and the
opponent plays white. The opponent (white) starts. A move simply selects an
index in the list. P.77 of the book gives examples where it is beneficial to
maintain the structure of the games keeping them separate at the cost of
complicating the definition of moves. So instead of collapsing the structure
when we add games:

plusA :: Arena -> Arena -> Arena
g@(Arena gls grs) `plusA` h@(Arena hls hrs) = 
  Arena
    ((map (`plusA` h) gls) ++ (map (g `plusA`) hls))
    ((map (`plusA` h) grs) ++ (map (g `plusA`) hrs))

We maintain the two games as PlusA g1 g2 and when you make a move you can
specify move in the left game which takes you to PlusA (leftOption_of_g1) g2

--}

data Arena = ZeroA
           | OneA 
           | PlusA Arena Arena
           | TimesA Arena Arena
           | NegA Arena
  deriving Show

------------------------------------------------------------------------------
-- Play games!

-- alternate moves between player (black) and opponent (white)

data Moves = End | Black Move Moves | White Move Moves

-- a move should be able to pick any option: if there is just on option the
-- move is Singleton; if the game is the sum of two games, the move specifies
-- whether to play in the left game or the right game; if the game is the
-- product of two games, it is complicated; if the game is the dual of
-- another game then copy the opponent's move in that game

data Move = NoM
          | SingletonM 
          | LeftM Move | RightM Move 
          | PPL Move | PPR Move | PPBoth Move Move
          | MML Move | MMR Move | MMBoth Move Move
          | PML Move | PMR Move | PMBoth Move Move 
          | MPL Move | MPR Move | MPBoth Move Move
          | OpponentM Move
  deriving Show

data Result = BlackWins | WhiteWins 
  deriving Show

-- play starts with white (opponent) move

playGame :: Arena -> Moves -> Result
playGame a End = error ("Incomplete game:\n " ++ show a)
playGame a (White m ms) = 
  trace ("\nArena: " ++ show a ++ ";\nwhite move: " ++ show m) $ 
  loopWhite (whiteMove a m) ms
  where loopWhite Nothing _ = BlackWins
        loopWhite (Just a') (Black m' ms') = 
            trace ("\nArena: " ++ show a' ++ ";\nblack move: " ++ show m') $ 
            loopBlack (blackMove a' m') ms'
        loopWhite (Just a') End = 
            error ("Incomplete game:\n " ++ show a')
        loopBlack Nothing _ = WhiteWins
        loopBlack (Just a') (White m' ms') = 
            trace ("\nArena: " ++ show a' ++ ";\nwhite move: " ++ show m') $ 
            loopWhite (whiteMove a' m') ms'
        loopBlack (Just a') End = 
            error ("Incomplete game:\n " ++ show a')

{--
playGame OneA (White NoM End) ==> 
  BlackWins
--}

-- black moves: returns the new game configuration (if any) after the move

blackMove :: Arena -> Move -> Maybe Arena
blackMove ZeroA _ = Nothing
blackMove OneA SingletonM = Just ZeroA
blackMove (PlusA a1 a2) (LeftM m) = do g <- blackMove a1 m
                                       return $ PlusA g a2
blackMove (PlusA a1 a2) (RightM m) = do g <- blackMove a2 m
                                        return $ PlusA a1 g
blackMove (TimesA a1 a2) (PPL m1) = do g1 <- blackMove a1 m1
                                       return $ TimesA g1 a2
blackMove (TimesA a1 a2) (PPR m2) = do g2 <- blackMove a2 m2
                                       return $ TimesA a1 g2
blackMove (TimesA a1 a2) (PPBoth m1 m2) = do g1 <- blackMove a1 m1
                                             g2 <- blackMove a2 m2
                                             return $ NegA (TimesA g1 g2)
blackMove (TimesA a1 a2) (MML m1) = do g1 <- whiteMove a1 m1
                                       return $ TimesA g1 a2
blackMove (TimesA a1 a2) (MMR m2) = do g2 <- whiteMove a2 m2
                                       return $ TimesA a1 g2
blackMove (TimesA a1 a2) (MMBoth m1 m2) = do g1 <- whiteMove a1 m1
                                             g2 <- whiteMove a2 m2
                                             return $ NegA (TimesA g1 g2)
blackMove (TimesA a1 a2) (PML m1) = do g1 <- blackMove a1 m1
                                       return $ TimesA g1 a2
blackMove (TimesA a1 a2) (PMR m2) = do g2 <- whiteMove a2 m2
                                       return $ TimesA a1 g2
blackMove (TimesA a1 a2) (PMBoth m1 m2) = do g1 <- blackMove a1 m1
                                             g2 <- whiteMove a2 m2
                                             return $ NegA (TimesA g1 g2)
blackMove (TimesA a1 a2) (MPL m1) = do g1 <- whiteMove a1 m1
                                       return $ TimesA g1 a2
blackMove (TimesA a1 a2) (MPR m2) = do g2 <- blackMove a2 m2
                                       return $ TimesA a1 g2
blackMove (TimesA a1 a2) (MPBoth m1 m2) = do g1 <- whiteMove a1 m1
                                             g2 <- blackMove a2 m2
                                             return $ NegA (TimesA g1 g2)
blackMove (NegA a) (OpponentM m) = do g <- whiteMove a m
                                      return $ NegA g
blackMove a m = error ("malformed play:\n " ++ show a ++ "\n " ++ show m)

-- opponnent's moves

whiteMove :: Arena -> Move -> Maybe Arena
whiteMove ZeroA _ = Nothing
whiteMove OneA _ = Nothing
whiteMove (PlusA a1 a2) (LeftM m) = do g <- whiteMove a1 m
                                       return $ PlusA g a2
whiteMove (PlusA a1 a2) (RightM m) = do g <- whiteMove a2 m
                                        return $ PlusA a1 g
whiteMove (TimesA a1 a2) (PPL m1) = do g1 <- whiteMove a1 m1
                                       return $ TimesA g1 a2
whiteMove (TimesA a1 a2) (PPR m2) = do g2 <- whiteMove a2 m2
                                       return $ TimesA a1 g2
whiteMove (TimesA a1 a2) (PPBoth m1 m2) = do g1 <- whiteMove a1 m1
                                             g2 <- whiteMove a2 m2
                                             return $ NegA (TimesA g1 g2)
whiteMove (TimesA a1 a2) (MML m1) = do g1 <- blackMove a1 m1
                                       return $ TimesA g1 a2
whiteMove (TimesA a1 a2) (MMR m2) = do g2 <- blackMove a2 m2
                                       return $ TimesA a1 g2
whiteMove (TimesA a1 a2) (MMBoth m1 m2) = do g1 <- blackMove a1 m1
                                             g2 <- blackMove a2 m2
                                             return $ NegA (TimesA g1 g2)
whiteMove (TimesA a1 a2) (PML m1) = do g1 <- whiteMove a1 m1
                                       return $ TimesA g1 a2
whiteMove (TimesA a1 a2) (PMR m2) = do g2 <- blackMove a2 m2
                                       return $ TimesA a1 g2
whiteMove (TimesA a1 a2) (PMBoth m1 m2) = do g1 <- whiteMove a1 m1
                                             g2 <- blackMove a2 m2
                                             return $ NegA (TimesA g1 g2)
whiteMove (TimesA a1 a2) (MPL m1) = do g1 <- blackMove a1 m1
                                       return $ TimesA g1 a2
whiteMove (TimesA a1 a2) (MPR m2) = do g2 <- whiteMove a2 m2
                                       return $ TimesA a1 g2
whiteMove (TimesA a1 a2) (MPBoth m1 m2) = do g1 <- blackMove a1 m1
                                             g2 <- whiteMove a2 m2
                                             return $ NegA (TimesA g1 g2)
whiteMove (NegA a) (OpponentM m) = do g <- blackMove a m
                                      return $ NegA g
whiteMove a m = error ("malformed play:\n " ++ show a ++ "\n " ++ show m)

{--
plusA :: Arena -> Arena -> Arena
g@(Arena gls grs) `plusA` h@(Arena hls hrs) = 
  Arena
    ((map (`plusA` h) gls) ++ (map (g `plusA`) hls))
    ((map (`plusA` h) grs) ++ (map (g `plusA`) hrs))

negA :: Arena -> Arena
negA (Arena gls grs) = Arena (map negA grs) (map negA gls) 

timesA :: Arena -> Arena -> Arena
x@(Arena xls xrs) `timesA` y@(Arena yls yrs) = 
  Arena 
    ([ (xl `timesA` y) `plusA` (x `timesA` yl) `minusA` (xl `timesA` yl) ]
     [ (xr `timesA` y) `plusA` (x `timesA` yr) `minusA` (xr `timesA` yr) ])
    ([ (xl `timesA` y) `plusA` (x `timesA` yr) `minusA` (xl `timesA` yr) ]
     [ (xr `timesA` y) `plusA` (x `timesA` yl) `minusA` (xr `timesA` yl) ])
--}

two    = PlusA OneA OneA
three  = PlusA OneA (PlusA OneA OneA)
negOne = NegA OneA
negTwo = NegA (PlusA OneA OneA)

test0 = blackMove ZeroA NoM
test1 = whiteMove ZeroA NoM
test2 = blackMove OneA SingletonM
test3 = whiteMove OneA NoM
test4 = blackMove (PlusA OneA OneA) (LeftM SingletonM)
test5 = whiteMove (PlusA OneA OneA) (LeftM NoM)
test6 = blackMove (PlusA three negTwo)
          (LeftM (RightM (LeftM SingletonM)))
test7 = whiteMove (PlusA three negTwo)
          (RightM (OpponentM (LeftM SingletonM)))
test8 = playGame 
          (PlusA three negTwo)
          (White (RightM (OpponentM (LeftM SingletonM)))
          (Black (LeftM (RightM (LeftM SingletonM)))
          (White (RightM (OpponentM (RightM SingletonM)))
          (Black (LeftM (LeftM SingletonM))
          (White (LeftM (LeftM NoM))
          End)))))
test9 = playGame (TimesA two negOne)
        -- white tries to move in the game "two" and loses
        (White (PPL (LeftM SingletonM))     
        End)
test10 = playGame (TimesA two negOne)
         -- white moves in the game "negOne" 
         (White (PPR (OpponentM SingletonM))
         -- black now moves in "two"
         (Black (PPL (LeftM SingletonM))
         -- white tries to move and loses
         (White (PPL (LeftM NoM))
         End)))
test11 = playGame (TimesA two negOne)
         -- white moves simultaneously 
         (White (MPBoth (LeftM SingletonM) (OpponentM SingletonM))
         (Black (OpponentM (PPR (OpponentM NoM)))
         End))

------------------------------------------------------------------------------

{-- 

A strategy specifies moves for black. Every value corresponds to a move (or
perhaps to a winning strategy for black); our strategies are
deterministic. In the arena PlusA OneA OneA, black has two winning strategies
so things are matching.

--}

type Strategy = Moves -- with only black moves

-- take black strategy and white moves
-- white starts

playGameS :: Arena -> Strategy -> Moves -> Result
playGameS a _ End = error ("Incomplete game:\n " ++ show a)
playGameS a bs (White w ws) = 
  trace ("\nArena: " ++ show a ++ ";\nwhite move: " ++ show w) $ 
  loopWhite (whiteMove a w) bs ws
  where loopWhite Nothing _ _ = BlackWins
        loopWhite (Just a') (Black b bs) ws = 
            trace ("\nArena: " ++ show a' ++ ";\nblack move: " ++ show b) $ 
            loopBlack (blackMove a' b) bs ws
        loopWhite (Just a') End _ = 
            error ("Incomplete game:\n " ++ show a')
        loopBlack Nothing _ _ = WhiteWins
        loopBlack (Just a') bs (White w ws) = 
            trace ("\nArena: " ++ show a' ++ ";\nwhite move: " ++ show w) $ 
            loopWhite (whiteMove a' w) bs ws
        loopBlack (Just a') _ End = 
            error ("Incomplete game:\n " ++ show a')

-- the two strategies for black in the arena (PlusA OneA OneA) 

strategy1, strategy2 :: Strategy 

strategy1 = Black (LeftM SingletonM) $
            Black (RightM SingletonM) $
            End

strategy2 = Black (RightM SingletonM) $
            Black (LeftM SingletonM) $
            End


------------------------------------------------------------------------------
-- Pi
-- Types are arenas
-- values are moves for black
-- combinators manipulate moves: you can moves for a complicated game
-- from elementary moves in simple games

data Comb = Id
          | Sym Comb
          | Comb :.: Comb
          | Comb :*: Comb
          | Comb :+: Comb
          | PlusZeroL
          | PlusZeroR
          | CommutePlus
          | AssocPlusL
          | AssocPlusR
          | TimesOneL
          | TimesOneR
          | CommuteTimes
          | AssocTimesL
          | AssocTimesR
          | TimesZeroL
          | TimesZeroR
          | Distribute
          | Factor

evalComb :: Comb -> Move -> Move
evalComb Id m = m
evalComb (Sym c) m = undefined
evalComb (c1 :.: c2) m = evalComb c2 (evalComb c1 m)
evalComb (c1 :*: c2) m = undefined
evalComb (c1 :+: c2) (LeftM m) = LeftM (evalComb c1 m)
evalComb (c1 :+: c2) (RightM m) = RightM (evalComb c1 m)
evalComb PlusZeroL (RightM m) = m
evalComb PlusZeroR m = RightM m
evalComb CommutePlus (LeftM m) = RightM m
evalComb CommutePlus (RightM m) = LeftM m
evalComb AssocPlusL (LeftM m) = LeftM (LeftM m)
evalComb AssocPlusL (RightM (LeftM m)) = LeftM (RightM m)
evalComb AssocPlusL (RightM (RightM m)) = RightM m
evalComb AssocPlusR (LeftM (LeftM m)) = (LeftM m)
evalComb AssocPlusR (LeftM (RightM m)) = RightM (LeftM m)
evalComb AssocPlusR (RightM m) = RightM (RightM m)
evalComb TimesOneL m = undefined
evalComb TimesOneR m = undefined
evalComb CommuteTimes m = undefined
evalComb AssocTimesL m = undefined
evalComb AssocTimesR m = undefined
evalComb TimesZeroL m = undefined
evalComb TimesZeroR m = undefined
evalComb Distribute m = undefined
evalComb Factor m = undefined

-- we can build a move in PlusA ZeroA OneA from a move in OneA

test12 = blackMove OneA SingletonM
test13 = blackMove (PlusA ZeroA OneA) (evalComb PlusZeroR SingletonM)

------------------------------------------------------------------------------

