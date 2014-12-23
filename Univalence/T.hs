module T where

import Test.QuickCheck

transpose1 :: Int -> Int -> Int -> Int
transpose1 m n i = 
  if i == m * n - 1
  then m * n - 1
  else (m * i) `mod` (m * n - 1)

transpose2 :: Int -> Int -> Int -> Int
transpose2 m n i = 
  let (b , d) = i `divMod` n
  in (d * m + b)

xx = quickCheck (\ m n i -> m >= 0 && n >= 0 && i >= 0 && i < m * n ==> 
     		 transpose1 m n i == transpose2 m n i)

