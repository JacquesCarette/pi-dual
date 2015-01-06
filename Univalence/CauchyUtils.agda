{-# OPTIONS --without-K #-}
module CauchyUtils where

open import Cauchy
open import Data.String using (String) renaming (_++_ to _++S_)
open import Data.Vec using (Vec; _∷_; []; zipWith; allFin)
open import Data.Fin using (toℕ; fromℕ; inject+)
open import Data.Nat.Show using (show)

showCauchy : ∀ {n} → Cauchy n → Vec String n
showCauchy {n} = 
  zipWith (λ i j → show (toℕ i) ++S " → " ++S show (toℕ j)) (allFin n)

-- Ex:

cauchyEx1 cauchyEx2 : Cauchy 6
-- cauchyEx1 (0 1 2 3 4 5)
--           (2 0 4 3 1 5)
cauchyEx1 = 
  (inject+ 3 (fromℕ 2)) ∷
  (inject+ 5 (fromℕ 0)) ∷
  (inject+ 1 (fromℕ 4)) ∷
  (inject+ 2 (fromℕ 3)) ∷
  (inject+ 4 (fromℕ 1)) ∷
  (inject+ 0 (fromℕ 5)) ∷ []
-- cauchyEx2 (0 1 2 3 4 5)
--           (3 2 1 0 5 4)
cauchyEx2 = 
  (inject+ 2 (fromℕ 3)) ∷
  (inject+ 3 (fromℕ 2)) ∷
  (inject+ 4 (fromℕ 1)) ∷
  (inject+ 5 (fromℕ 0)) ∷
  (inject+ 0 (fromℕ 5)) ∷
  (inject+ 1 (fromℕ 4)) ∷ []
