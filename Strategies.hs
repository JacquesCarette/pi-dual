module Strategies where

import Data.List

------------------------------------------------------------------------------
-- Every type corresponds to an arena 

data Arena = Arena [Arena] [Arena]
  deriving (Show,Eq)

leftOptions :: Arena -> [Arena]
leftOptions (Arena gls _) = gls

rightOptions :: Arena -> [Arena]
rightOptions (Arena _ grs) = grs

data T = Zero | One | Plus T T | Times T T | Neg T

arena :: T -> Arena
arena Zero = Arena [] []
arena One = Arena [ Arena [] [] ] []
arena (Plus t1 t2) = arena t1 `plusA` arena t2
arena (Times t1 t2) = arena t1 `timesA` arena t2
arena (Neg t) = negA (arena t) 

plusA :: Arena -> Arena -> Arena
g@(Arena gls grs) `plusA` h@(Arena hls hrs) = 
  Arena
    ((map (`plusA` h) gls) `union` (map (g `plusA`) hls))
    ((map (`plusA` h) grs) `union` (map (g `plusA`) hrs))

negA :: Arena -> Arena
negA (Arena gls grs) = Arena (map negA grs) (map negA gls) 

minusA :: Arena -> Arena -> Arena
g1 `minusA` g2 = g1 `plusA` (negA g2) 

timesA :: Arena -> Arena -> Arena
x@(Arena xls xrs) `timesA` y@(Arena yls yrs) = 
  Arena 
    ([ (xl `timesA` y) `plusA` (x `timesA` yl) `minusA` (xl `timesA` yl)
     | xl <- xls, yl <- yls] `union`
     [ (xr `timesA` y) `plusA` (x `timesA` yr) `minusA` (xr `timesA` yr)
     | xr <- xrs, yr <- yrs])
    ([ (xl `timesA` y) `plusA` (x `timesA` yr) `minusA` (xl `timesA` yr)
     | xl <- xls, yr <- yrs] `union`
     [ (xr `timesA` y) `plusA` (x `timesA` yl) `minusA` (xr `timesA` yl)
     | xr <- xrs, yl <- yls])

------------------------------------------------------------------------------
-- Play games!

-- alternate L/R
data Play = Null | L Int Play | R Int Play
data Result = LeftWins | RightWins | Incomplete
  deriving Show

-- play starts with right move
game :: Arena -> Play -> Result
game = gameR
  where gameL (Arena [] rs) _ = RightWins
        gameL (Arena ls rs) (L i p) = gameR (ls !! i) p
        gameL (Arena ls rs) Null = Incomplete
        gameL (Arena ls rs) (R i p) = error "malformed play"

        gameR (Arena ls []) _ = LeftWins
        gameR (Arena ls rs) (R i p) = gameL (rs !! i) p
        gameR (Arena ls rs) Null = Incomplete
        gameR (Arena ls rs) (L i p) = error "malformed play"

three  = Plus One (Plus One One)
negTwo = Neg (Plus One One)

test0 = game (arena Zero) Null
test1 = game (arena One) Null
test2 = game (arena (Plus One One)) Null
test3 = game (arena (Plus three negTwo)) (R 0 (L 0 (R 0 (L 0 Null))))

------------------------------------------------------------------------------
-- Every value corresponds to a strategy

-- A strategy is a left move for each possible right move

data Strategy = S (Int -> Strategy) 

data Val = Unit | InL Val | InR Val | Pair Val Val

val2Strategy :: (Val,T) -> (Strategy,Arena)
val2Strategy (Unit,One) = (s,a)
  where a = arena One 
        s = S (\_ -> undefined)
val2Strategy (InL v, Plus t1 t2) = (s,a)
  where a = arena (Plus t1 t2)
        s = undefined
val2Strategy (InR v, Plus t1 t2) = (s,a)
  where a = arena (Plus t1 t2)
        s = undefined
val2Strategy (Pair v1 v2, Times t1 t2) = (s,a)
  where a = arena (Times t1 t2)
        s = undefined

-- take left strategy and right moves; right starts
gameWithStrategy :: Arena -> Strategy -> Play -> Result
gameWithStrategy (Arena ls []) (S s) Null = LeftWins
gameWithStrategy (Arena ls rs) (S s) Null = Incomplete
gameWithStrategy (Arena ls rs) (S s) (R i p) = 
  gameWithStrategy (rs !! i) (s i) p

test4 = gameWithStrategy a s Null
  where (s,a) = val2Strategy (Unit,One)

------------------------------------------------------------------------------
{--
arena One = Arena [ Arena [] [] ] []
arena (Plus t1 t2) = arena t1 `plusA` arena t2
arena (Times t1 t2) = arena t1 `timesA` arena t2

g@(Arena gls grs) `plusA` h@(Arena hls hrs) = 
  Arena
    ((map (`plusA` h) gls) `union` (map (g `plusA`) hls))
    ((map (`plusA` h) grs) `union` (map (g `plusA`) hrs))

x@(Arena xls xrs) `timesA` y@(Arena yls yrs) = 
  Arena 
    ([ (xl `timesA` y) `plusA` (x `timesA` yl) `minusA` (xl `timesA` yl)
     | xl <- xls, yl <- yls] `union`
     [ (xr `timesA` y) `plusA` (x `timesA` yr) `minusA` (xr `timesA` yr)
     | xr <- xrs, yr <- yrs])
    ([ (xl `timesA` y) `plusA` (x `timesA` yr) `minusA` (xl `timesA` yr)
     | xl <- xls, yr <- yrs] `union`
     [ (xr `timesA` y) `plusA` (x `timesA` yl) `minusA` (xr `timesA` yl)
     | xr <- xrs, yl <- yls])
--}