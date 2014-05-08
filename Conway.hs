{-# LANGUAGE TypeFamilies #-}

module Conway where

import Data.List

------------------------------------------------------------------------------
{--
Some random thoughts about how to "type" Conway games

Our definition:

 GL ::= < S | P >
 GR ::= < P | S >

  S ::= 0 | GR | S + S

  P ::= 1 | GL | P * P

data GL = GL S P
data GR = GR P S
data S  = Lose | S GR | Choice S S 
data P  = Win  | P GL | Opponent P P 

dualL :: GL -> GR
dualL (GL s p) = GR (dualS s) (dualP p)

dualR :: GR -> GL
dualR (GR p s) = GL (dualP p) (dualS s)

dualP :: P -> S
dualP Win = Lose
dualP (P gl) = S (dualL gl)
dualP (Opponent p1 p2) = Choice (dualP p1) (dualP p2)

dualS :: S -> P
dualS Lose = Win
dualS (S gr) = P (dualR gr)
dualS (Choice s1 s2) = Opponent (dualS s1) (dualS s2)

--

zeroGL, oneGL, twoGL, threeGL :: GL
zeroGL  = GL Lose Win
oneGL   = GL (S (dualL zeroGL)) Win
twoGL   = GL (S (dualL oneGL)) Win
threeGL = GL (S (dualL twoGL)) Win

neg_oneGL, neg_twoGL, neg_threeGL :: GL
neg_oneGL   = GL Lose (P zeroGL)
neg_twoGL   = GL Lose (P neg_oneGL)
neg_threeGL = GL Lose (P neg_twoGL)

-- unary negation

negGL :: GL -> GL
negGL (GL s p) = GL (dualP p) (dualS s)

plusGL :: GL -> GL -> GL
g@(GL s1 p1) `plusGL` h@(GL s2 p2) = 
  GL (Choice (s1 `plusSL` h) (g `plusLS` s2))
     (Opponent (p1 `plusPL` h) (g `plusLP` p2))

plusSL :: S -> GL -> S
plusSL Lose gl = Lose
plusSL (S gr) gl = undefined
plusSL (Choice s1 s2) gl = Choice (plusSL s1 gl) (plusSL s2 gl)

plusLS :: GL -> S -> S
plusLS gl Lose = Lose
plusLS gl (S gr) = undefined
plusLS gl (Choice s1 s2) = Choice (plusLS gl s1) (plusLS gl s2)

plusPL :: P -> GL -> P
plusPL Win gl = Win
plusPL (P gl1) gl2 = undefined
plusPL (Opponent p1 p2) gl = Opponent (plusPL p1 gl) (plusPL p2 gl)

plusLP :: GL -> P -> P
plusLP gl Win = Win
plusLP gl1 (P gl2) = undefined
plusLP gl (Opponent p1 p2) = Opponent (plusLP gl p1) (plusLP gl p2)

--plusG :: Game -> Game -> Game
--g@(Game gls grs) `plusG` h@(Game hls hrs) = 
--  Game 
--    ((map (`plusG` h) gls) `union` (map (g `plusG`) hls))
--    ((map (`plusG` h) grs) `union` (map (g `plusG`) hrs))

-- A morphism between games < xls | xrs > and < yls | yrs > 
-- is a game < yls + xrs | xls + yrs > 

-- Joyal: focus on strategies which are sequences of moves

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

So games (from left perspective) are sums of products of sums of products
etc. So their types would be:

  G ::= S 

  S ::= 0 | P | S + S

  P ::= 1 | S | P * P 

------------------------------------------------------------------------------
-- Pi

types ::= 0 | 1 | t+t | -t 
c ::= unit+ | commute+ | assoc+ 
    | id | sym c | c;c | c + c 
meaning of the type 0 is all the games g such that (eq0 g)
meaning of the type 1 is all the games g such that (eq0 (g `minusG` oneG))
meaning of the type 2 ...
meaning of the type constructor + is plusG
meaning of the type constructor neg is negG
semantics justifies commutatity, associativity, equivalence, etc. 

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

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- Using conventional definition of Conway games...

data Game = Game [Game] [Game]
  deriving (Eq, Show)

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
-- Predicates: players must alternate
-- Equivalence relation on games
-- Two games are equal if `eqG` holds

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

------------------------------------------------------------------------------
-- Addition and subtraction

plusG :: Game -> Game -> Game
g@(Game gls grs) `plusG` h@(Game hls hrs) = 
  Game 
    ((map (`plusG` h) gls) `union` (map (g `plusG`) hls))
    ((map (`plusG` h) grs) `union` (map (g `plusG`) hrs))

negG :: Game -> Game
negG (Game gls grs) = Game (map negG grs) (map negG gls) 

minusG :: Game -> Game -> Game
g1 `minusG` g2 = g1 `plusG` (negG g2) 

twoG, threeG, fourG, negtwoG :: Game
twoG    = oneG `plusG` oneG
threeG  = twoG `plusG` oneG
fourG   = threeG `plusG` oneG
negtwoG = negoneG `minusG` oneG

------------------------------------------------------------------------------
-- Congruence relation on games

geqG, leqG, eqG, greaterG, lessG, fuzzyG, rightG, leftG :: Game -> Game -> Bool
geqG     g1 g2 = geq0     (g1 `minusG` g2)
leqG     g1 g2 = leq0     (g1 `minusG` g2) 
eqG      g1 g2 = eq0      (g1 `minusG` g2) 
greaterG g1 g2 = greater0 (g1 `minusG` g2) 
lessG    g1 g2 = less0    (g1 `minusG` g2) 
fuzzyG   g1 g2 = fuzzy0   (g1 `minusG` g2) 
rightG   g1 g2 = right0   (g1 `minusG` g2) 
leftG    g1 g2 = left0    (g1 `minusG` g2) 

-- zeroG is a unit for addition
-- negG o negG is the identity
-- negG (G `plusG` H) = (negG G) `plusG` (negG H)
-- addition is also associative and commutative
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
  where helper [] allgs _ = []
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

halfG    = Game [zeroG] [oneG]  -- 1/2 + 1/2 is indeed 1 

-- short numbers are of the of the following four forms:
-- Game [] []
-- Game [x] []
-- Game [] [y]
-- Game [x] [y]
-- in other words, there is at most one position in each set of options
-- the first two gives us the natural numbers
-- the third one gives us the integers
-- the fourth one gives us the dyadic fractions; to get other fractions,
--   we need to have infinite sequences

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

