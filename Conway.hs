{-# LANGUAGE TypeFamilies #-}

module Conway where

import Data.List

------------------------------------------------------------------------------
-- Definition; a few constants; several show functions

{--
Conventional definition:

data Game = Game [Game] [Game]
  deriving (Eq, Show)
--}

data Game a b = Game a b

data Void

type ZERO  = Game Void () 

type ONE   = Game ZERO ()
type TWO   = Game ONE  ()
type THREE = Game TWO  ()

type NEG_ONE   = Game Void ZERO
type NEG_TWO   = Game Void NEG_ONE
type NEG_THREE = Game Void NEG_TWO

zeroG :: ZERO
zeroG = Game undefined ()

oneG :: ONE
oneG = Game zeroG ()

twoG :: TWO
twoG = Game oneG ()

threeG :: THREE
threeG = Game twoG ()

neg_oneG :: NEG_ONE
neg_oneG = Game undefined zeroG

neg_twoG :: NEG_TWO
neg_twoG = Game undefined neg_oneG

neg_threeG :: NEG_THREE
neg_threeG = Game undefined neg_twoG

--

class G a where
  type Neg a :: *

instance G Void where
  type Neg Void = ()

instance G () where
  type Neg () = Void

negG :: Game a b -> Game (Neg a) (Neg b) 
negG (Game x y) = Game (negG x) (negG y) 

{--
plusG :: Game -> Game -> Game
g@(Game gls grs) `plusG` h@(Game hls hrs) = 
  Game 
    ((map (`plusG` h) gls) `union` (map (g `plusG`) hls))
    ((map (`plusG` h) grs) `union` (map (g `plusG`) hrs))

negG :: Game -> Game
negG (Game gls grs) = Game (map negG grs) (map negG gls) 
--}






{--
leftOptions :: Game -> [Game]
leftOptions (Game gls _) = gls

rightOptions :: Game -> [Game]
rightOptions (Game _ grs) = grs

zeroG, oneG, negoneG, starG :: Game
zeroG   = Game []      []
oneG    = Game [zeroG] []
negoneG = Game []      [zeroG]
starG   = Game [zeroG] [zeroG]

int2Game :: Int -> Game
int2Game n | n < 0 = Game []               [int2Game (n+1)]
int2Game n | n > 0 = Game [int2Game (n-1)] []
int2Game n | otherwise = zeroG

--

showG :: Game -> String
showG (Game [] []) = "0"
showG (Game [Game [] []] []) = "1"
showG (Game [] [Game [] []]) = "-1"
showG (Game [Game [] []] [Game [] []]) = "*"
showG (Game gls grs) = 
  "<[" ++ concatMap showG gls ++ "] , [" ++ concatMap showG grs ++ "]>"

showT :: String -> Game -> String
showT _ (Game [] []) = "(empty-tree)"
showT s (Game [g] []) = 
  "(tree " ++ s ++ " " ++ showT "'*" g ++ " (empty-tree))"
showT s (Game [] [g]) = 
  "(tree " ++ s ++ " (empty-tree) " ++ showT "'*" g ++ ")"
showT s (Game [g1] [g2]) = 
  "(tree " ++ s ++ " " ++ showT "'*" g1 ++ showT "'*" g2 ++ ")"
showT s (Game [g1,g2] [g3]) = 
  "(tree " ++ s ++ " " ++ 
           showT "#\\space" (Game [g1] [g2]) ++ showT "'*" g3 ++ ")"
showT s (Game [g1] [g2,g3]) = 
  "(tree " ++ s ++ " " ++ 
           showT "'*" g1 ++ showT "#\\space" (Game [g2] [g3]) ++ ")"

------------------------------------------------------------------------------
-- addition and subtraction

plusG :: Game -> Game -> Game
g@(Game gls grs) `plusG` h@(Game hls hrs) = 
  Game 
    ((map (`plusG` h) gls) `union` (map (g `plusG`) hls))
    ((map (`plusG` h) grs) `union` (map (g `plusG`) hrs))

negG :: Game -> Game
negG (Game gls grs) = Game (map negG grs) (map negG gls) 

minusG :: Game -> Game -> Game
g1 `minusG` g2 = g1 `plusG` (negG g2) 

-- zeroG is a unit for addition
-- negG o negG is the identity
-- negG (G `plusG` H) = (negG G) `plusG` (negG H)
-- addition is also associative and commutative

twoG, threeG, fourG, negtwoG :: Game
twoG    = oneG `plusG` oneG
threeG  = twoG `plusG` oneG
fourG   = threeG `plusG` oneG
negtwoG = negoneG `minusG` oneG

{--
*Conway> twoG
<1,>
*Conway> threeG
<<1,>,>
*Conway> fourG
<<<1,>,>,>
*Conway> negtwoG
<,-1>
--}

------------------------------------------------------------------------------
-- Predicates: players must alternate
-- Equivalence relation on games
-- two games are equal if `eqG` holds

geq0, leq0 :: Game -> Bool
-- left wins as second player; right has no good opening move
geq0 (Game gls grs) = not $ or (map leq0 grs) 
-- 
leq0 (Game gls grs) = not $ or (map geq0 gls) 

-- only geq0 and leq0 are fundamental; the remaining predicates are defined
-- using them; fuzzy0 is new: it means that g is neither >= 0 nor <= 0
eq0, greater0, less0, fuzzy0, right0, left0 :: Game -> Bool
-- second player always wins
eq0      g = geq0 g && leq0 g 
-- left always wins
greater0 g = geq0 g && not (leq0 g)
-- right always wins
less0    g = leq0 g && not (geq0 g)
-- first player wins
fuzzy0   g = not (geq0 g) && not (leq0 g)
-- left can win when moving first
right0   g = not (leq0 g)
left0    g = not (geq0 g)

{--

*Conway> eq0 $ oneG `plusG` negoneG
True
*Conway> eq0 $ starG `plusG` starG
True

*Conway> eq0 zeroG
True
*Conway> greater0 oneG
True
*Conway> less0 negoneG
True
*Conway> fuzzy0 starG
True

--}

geqG, leqG, eqG, greaterG, lessG, fuzzyG, rightG, leftG :: Game -> Game -> Bool
geqG     g1 g2 = geq0     (g1 `minusG` g2)
leqG     g1 g2 = leq0     (g1 `minusG` g2) 
eqG      g1 g2 = eq0      (g1 `minusG` g2) 
greaterG g1 g2 = greater0 (g1 `minusG` g2) 
lessG    g1 g2 = less0    (g1 `minusG` g2) 
fuzzyG   g1 g2 = fuzzy0   (g1 `minusG` g2) 
rightG   g1 g2 = right0   (g1 `minusG` g2) 
leftG    g1 g2 = left0    (g1 `minusG` g2) 

-- if G >= 0 and H >= 0 then G+H >= 0
-- if G >= 0 and H right 0 then G+H right 0

------------------------------------------------------------------------------
-- Simplifying games

fix :: Eq a => (a -> a) -> a -> a
fix f a = let a' = f a in if a == a' then a else f a'

normalizeG :: Game -> Game
normalizeG = fix (introduceReversibleShortcuts . deleteDominatedOptions)

-- deleteDominatedOptions 

deleteDominatedOptions :: Game -> Game
deleteDominatedOptions (Game gls grs) = 
  Game (helper gls gls leftDominatedBy) (helper grs grs rightDominatedBy)
  where helper [] gls _ = []
        helper (g:gs) allgs pred = 
            if any (pred g) (delete g allgs)
            then helper gs allgs pred
            else g : helper gs allgs pred
        leftDominatedBy  = leqG
        rightDominatedBy = geqG

-- introduceReversibleShortcuts
introduceReversibleShortcuts :: Game -> Game
introduceReversibleShortcuts g@(Game gls grs) = 
  Game (helperL g gls) (helperR g grs) 
  where helperL g [] = []
        helperL g (gl:gls) = 
          case find (`leqG` g) (rightOptions gl) of 
            Nothing  -> gl : helperL g gls
            Just glr -> leftOptions glr `union` helperL g gls
        helperR g [] = []
        helperR g (gr:grs) = 
          case find (`geqG` g) (leftOptions gr) of 
            Nothing  -> gr : helperR g grs
            Just grl -> rightOptions grl `union` helperR g grs

------------------------------------------------------------------------------
-- Number games

isNumberGame :: Game -> Bool
isNumberGame (Game gls grs) = 
  all isNumberGame gls && all isNumberGame grs && 
  and [ gl `lessG` gr | gl <- gls, gr <- grs ]

halfG         = Game [zeroG] [oneG]  -- 1/2 + 1/2 is indeed 1 
quarterG = Game [zeroG] [halfG]

-- If we have three player games, we can presumably get multiples of 3
-- easily. If we have five player games, we can presumably get multiples of 5
-- and so on. Is that related to the p-adics? Is there a groupoid structure
-- here? 

-- multiplication (only defined for number games)

timesG :: Game -> Game -> Game
x@(Game xls xrs) `timesG` y@(Game yls yrs) = 
  Game 
    ([ (xl `timesG` y) `plusG` (x `timesG` yl) `minusG` (xl `timesG` yl)
     | xl <- xls, yl <- yls] `union`
     [ (xr `timesG` y) `plusG` (x `timesG` yr) `minusG` (xr `timesG` yr)
     | xr <- xrs, yr <- yrs])
    ([ (xl `timesG` y) `plusG` (x `timesG` yr) `minusG` (xl `timesG` yr)
     | xl <- xls, yr <- yrs] `union`
     [ (xr `timesG` y) `plusG` (x `timesG` yl) `minusG` (xr `timesG` yl)
     | xr <- xrs, yl <- yls])

testM0 = zeroG `timesG` oneG   -- zeroG
testM1 = oneG  `timesG` oneG   -- oneG
testM2 = twoG  `timesG` twoG   -- fourG

-- remove negative options

-- reciprocal (x is not 0)
recipG :: Game -> Game
recipG = undefined

-- division (h is not 0)
divG :: Game -> Game -> Game
x `divG` y = x `timesG` (recipG y)

------------------------------------------------------------------------------
-- A morphism between games < xls | xrs > and < yls | yrs > 
-- is a game < yls + xrs | xls + yrs > 

-- Joyal: focus on strategies which are sequences of moves

{-- 

A strategy is a rule that tells us how to choose a move. 

Given a game < x1=< z1, z2 | w1, w2, w3 >, x2, x3 | y1, y2 > 

A strategy for left consists of choosing one of x1, x2, or x3 and then
choosing a new strategy for each possible response from right. Say left chose
x1 which is < z1, z2 | w1, w2, w3 >. Then the rest of left's strategy
consists of the product of three strategies (Sw1, Sw2, Sw3) which are left's
responses to each possible move from right. If we get to a game where right
has no moves, then left's response is (). Let's assume that w1=<a1,a2|>,
w2=<b|>, and that w3=<|c>. So we can say a strategy for left in the above
game is:

  ((S(a1) + S(a2)),b,0) + S(x2) + S(x3)

The 0 means that we have lost in this branch.

So instead of sets of games in left and right positions, we should think of
sums and pairs of games!!!

--}


------------------------------------------------------------------------------
-- Pi

{--
types ::= 0 | 1 | t+t | -t 
c ::= unit+ | commute+ | assoc+ 
    | id | sym c | c;c | c + c 
meaning of the type 0 is all the games g such that (eq0 g)
meaning of the type 1 is all the games g such that (eq0 (g `minusG` oneG))
meaning of the type 2 ...
meaning of the type constructor + is plusG
meaning of the type constructor neg is negG
semantics justifies commutatity, associativity, equivalence, etc. 
--}

data Combinator = 
  Id | Sym Combinator | 
  (:.:) Combinator Combinator | 
  (:*:) Combinator Combinator | 
  (:+:) Combinator Combinator | 
  ZeroE | ZeroI | SwapP | AssocLP | AssocRP |
  UnitE | UnitI | SwapT | AssocLT | AssocRT | 
  DistribZ | FactorZ | Distrib | Factor 

-- data Val = ???

--}
