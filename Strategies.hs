module Strategies where

------------------------------------------------------------------------------
-- Every type corresponds to an arena 

data Arena = ZeroA
           | OneA 
           | PlusA Arena Arena
           | TimesA Arena Arena
           | NegA Arena
  deriving Show

data T = Zero | One | Plus T T | Times T T | Neg T

arena :: T -> Arena
arena Zero = ZeroA
arena One = OneA
arena (Plus t1 t2) = PlusA (arena t1) (arena t2)
arena (Times t1 t2) = TimesA (arena t1) (arena t2)
arena (Neg t) = NegA (arena t) 

------------------------------------------------------------------------------
-- Play games!

-- alternate left and right moves

data Play = NullP | L Move | R Move
data Move = SingletonM 
          | LeftM Move 
          | RightM Move 
          | PPL Move
          | PPR Move
          | PPBoth Move Move
          | MML Move
          | MMR Move
          | MMBoth Move Move
          | PML Move
          | PMR Move
          | PMBoth Move Move 
          | MPL Move
          | MPR Move
          | MPBoth Move Move
          | OpponentM Move

data Result = LeftWins | RightWins 
  deriving Show

-- play starts with right move

-- left moves

gameL :: Arena -> Move -> Maybe Arena
gameL ZeroA _ = Nothing
gameL OneA SingletonM = Just ZeroA
gameL (PlusA a1 a2) (LeftM m) = do g <- gameL a1 m
                                   return $ PlusA g a2
gameL (PlusA a1 a2) (RightM m) = do g <- gameL a2 m
                                    return $ PlusA a1 g

gameL (TimesA a1 a2) (PPL m1) = do g1 <- gameL a1 m1
                                   return $ TimesA g1 a2
gameL (TimesA a1 a2) (PPR m2) = do g2 <- gameL a2 m2
                                   return $ TimesA a1 g2
gameL (TimesA a1 a2) (PPBoth m1 m2) = do g1 <- gameL a1 m1
                                         g2 <- gameL a2 m2
                                         return $ NegA (TimesA g1 g2)

gameL (TimesA a1 a2) (MML m1) = do g1 <- gameR a1 m1
                                   return $ TimesA g1 a2
gameL (TimesA a1 a2) (MMR m2) = do g2 <- gameR a2 m2
                                   return $ TimesA a1 g2
gameL (TimesA a1 a2) (MMBoth m1 m2) = do g1 <- gameR a1 m1
                                         g2 <- gameR a2 m2
                                         return $ NegA (TimesA g1 g2)

gameL (TimesA a1 a2) (PML m1) = do g1 <- gameL a1 m1
                                   return $ TimesA g1 a2
gameL (TimesA a1 a2) (PMR m2) = do g2 <- gameR a2 m2
                                   return $ TimesA a1 g2
gameL (TimesA a1 a2) (PMBoth m1 m2) = do g1 <- gameL a1 m1
                                         g2 <- gameR a2 m2
                                         return $ NegA (TimesA g1 g2)

gameL (TimesA a1 a2) (MPL m1) = do g1 <- gameR a1 m1
                                   return $ TimesA g1 a2
gameL (TimesA a1 a2) (MPR m2) = do g2 <- gameL a2 m2
                                   return $ TimesA a1 g2
gameL (TimesA a1 a2) (MPBoth m1 m2) = do g1 <- gameR a1 m1
                                         g2 <- gameL a2 m2
                                         return $ NegA (TimesA g1 g2)
                                     
gameL (NegA a) (OpponentM m) = do g <- gameR a m
                                  return $ NegA g

gameL _ _ = error "malformed play"

gameR :: Arena -> Move -> Maybe Arena
gameR ZeroA _ = Nothing
gameR OneA SingletonM = Just ZeroA
gameR (PlusA a1 a2) (LeftM m) = do g <- gameR a1 m
                                   return $ PlusA g a2
gameR (PlusA a1 a2) (RightM m) = do g <- gameR a2 m
                                    return $ PlusA a1 g

gameR (TimesA a1 a2) (PPL m1) = do g1 <- gameR a1 m1
                                   return $ TimesA g1 a2
gameR (TimesA a1 a2) (PPR m2) = do g2 <- gameR a2 m2
                                   return $ TimesA a1 g2
gameR (TimesA a1 a2) (PPBoth m1 m2) = do g1 <- gameR a1 m1
                                         g2 <- gameR a2 m2
                                         return $ NegA (TimesA g1 g2)

gameR (TimesA a1 a2) (MML m1) = do g1 <- gameL a1 m1
                                   return $ TimesA g1 a2
gameR (TimesA a1 a2) (MMR m2) = do g2 <- gameL a2 m2
                                   return $ TimesA a1 g2
gameR (TimesA a1 a2) (MMBoth m1 m2) = do g1 <- gameL a1 m1
                                         g2 <- gameL a2 m2
                                         return $ NegA (TimesA g1 g2)

gameR (TimesA a1 a2) (PML m1) = do g1 <- gameR a1 m1
                                   return $ TimesA g1 a2
gameR (TimesA a1 a2) (PMR m2) = do g2 <- gameL a2 m2
                                   return $ TimesA a1 g2
gameR (TimesA a1 a2) (PMBoth m1 m2) = do g1 <- gameR a1 m1
                                         g2 <- gameL a2 m2
                                         return $ NegA (TimesA g1 g2)

gameR (TimesA a1 a2) (MPL m1) = do g1 <- gameL a1 m1
                                   return $ TimesA g1 a2
gameR (TimesA a1 a2) (MPR m2) = do g2 <- gameR a2 m2
                                   return $ TimesA a1 g2
gameR (TimesA a1 a2) (MPBoth m1 m2) = do g1 <- gameL a1 m1
                                         g2 <- gameR a2 m2
                                         return $ NegA (TimesA g1 g2)
gameR (NegA a) (OpponentM m) = do g <- gameL a m
                                  return $ NegA g

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

three  = Plus One (Plus One One)
negTwo = Neg (Plus One One)

test0 = gameL (arena Zero) SingletonM
test1 = gameL (arena One) SingletonM
test2 = gameL (arena (Plus One One)) (LeftM SingletonM)
test3 = gameL (arena (Plus three negTwo)) (RightM (LeftM SingletonM))
-- (R 0 (L 0 (R 0 (L 0 Null))))

{--
------------------------------------------------------------------------------
-- Every value corresponds to a strategy; hence our strategies are
-- deterministic; hopefully negatives allow backtracking and hence more
-- flexible strategies

-- Need to also build a dual strategy and switch to it for neg

type Strategy = Play -- with only left moves

data Val = Unit | InL Val | InR Val | Pair Val Val | Opponent Val

val2Strategy :: (Val,T) -> (Strategy,Arena)
val2Strategy (Unit,One) = (s,a)
  where a = arena One 
        s = L 0 Null
val2Strategy (InL v, Plus t1 t2) = (s,a)
  where a = arena (Plus t1 t2)
        (sl,g) = val2Strategy (v,t1)
        s = L undefined sl -- pick the group of moves to the left of ++ in plusA
val2Strategy (InR v, Plus t1 t2) = (s,a)
  where a = arena (Plus t1 t2)
        (sr,h) = val2Strategy (v,t2)
        s = R undefined sr -- pick the group of moves to the right of ++ in plusA
{--
look at the definition of plusA:

plusA :: Arena -> Arena -> Arena
g@(Arena gls grs) `plusA` h@(Arena hls hrs) = 
  Arena
    ((map (`plusA` h) gls) ++ (map (g `plusA`) hls))
    ((map (`plusA` h) grs) ++ (map (g `plusA`) hrs))

Given a strategy sl for g, i.e., given sl that selects one the gls, we can
build a new strategy L ??? sl that selects the moves in (map (`plusA` h) gls)
and then uses sl to select a move in gls. 

Given a strategy sr for h, i.e., given sr that selects one the hls, we can
build a new strategy R ??? sr that selects the moves in (map (g `plusA`) hls)
and then uses sr to select a move in hls. 

So as far as + is concerned, we need to keep the options in separate lists
instead of ++ or use a binary tree
--}
val2Strategy (Pair v1 v2, Times t1 t2) = (s,a)
  where a = arena (Times t1 t2)
        (s1,g1) = val2Strategy (v1,t1)
        (s2,g2) = val2Strategy (v2,t2) 
        s = undefined
{--
look at the definition of timesA:
timesA :: Arena -> Arena -> Arena
x@(Arena xls xrs) `timesA` y@(Arena yls yrs) = 
  Arena 
    ([ (xl `timesA` y) `plusA` (x `timesA` yl) `minusA` (xl `timesA` yl)
     | xl <- xls, yl <- yls] ++
     [ (xr `timesA` y) `plusA` (x `timesA` yr) `minusA` (xr `timesA` yr)
     | xr <- xrs, yr <- yrs])
    ([ (xl `timesA` y) `plusA` (x `timesA` yr) `minusA` (xl `timesA` yr)
     | xl <- xls, yr <- yrs] ++
     [ (xr `timesA` y) `plusA` (x `timesA` yl) `minusA` (xr `timesA` yl)
     | xr <- xrs, yl <- yls])

Given s1 for selecting xl and given s2 for selecting yl, we can build a new 
strategy ??? that first selects the moves in:
  [ (xl `timesA` y) `plusA` (x `timesA` yl) `minusA` (xl `timesA` yl) ]
or in 
  [ (xr `timesA` y) `plusA` (x `timesA` yr) `minusA` (xr `timesA` yr) ]
and then select among the plus/minus alternatives. But note that 
we need a strategy to also select from xrs and yrs
--}
val2Strategy (Opponent v, Neg t) = (s,a)
  where a = arena (Neg t)
        (s',g') = val2Strategy (v,t) 
        s = undefined -- ???
{--
Given a strategy s' for g', i.e., given s' that selects one of the gls, we
can build a new strategy ??? that selects a move in (map negA grs)
--}

-- take left strategy and right moves; right starts
gameWithStrategy :: Arena -> Strategy -> Play -> Result
gameWithStrategy = gameR
  where gameL (Arena [] rs) _ _ = RightWins
        gameL (Arena ls rs) (L i s) p = gameR (ls !! i) s p
        gameL _ _ _ = error "malformed play"

        gameR (Arena ls []) _ _ = LeftWins
        gameR (Arena ls rs) s (R i p) = gameL (rs !! i) s p
        gameR _ _ _ = error "malformed play"

test4 = gameWithStrategy a s Null
  where (s,a) = val2Strategy (Unit,One)

------------------------------------------------------------------------------

plusA :: Arena -> Arena -> Arena
g@(Arena gls grs) `plusA` h@(Arena hls hrs) = 
  Arena
    ((map (`plusA` h) gls) ++ (map (g `plusA`) hls))
    ((map (`plusA` h) grs) ++ (map (g `plusA`) hrs))

negA :: Arena -> Arena
negA (Arena gls grs) = Arena (map negA grs) (map negA gls) 

minusA :: Arena -> Arena -> Arena
g1 `minusA` g2 = g1 `plusA` (negA g2) 

timesA :: Arena -> Arena -> Arena
x@(Arena xls xrs) `timesA` y@(Arena yls yrs) = 
  Arena 
    ([ (xl `timesA` y) `plusA` (x `timesA` yl) `minusA` (xl `timesA` yl)
     | xl <- xls, yl <- yls] ++
     [ (xr `timesA` y) `plusA` (x `timesA` yr) `minusA` (xr `timesA` yr)
     | xr <- xrs, yr <- yrs])
    ([ (xl `timesA` y) `plusA` (x `timesA` yr) `minusA` (xl `timesA` yr)
     | xl <- xls, yr <- yrs] ++
     [ (xr `timesA` y) `plusA` (x `timesA` yl) `minusA` (xr `timesA` yl)
     | xr <- xrs, yl <- yls])
--}