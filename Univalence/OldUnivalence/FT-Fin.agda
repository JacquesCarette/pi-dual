{-# OPTIONS --without-K #-}
module FT-Fin where

import Data.Fin as F
import Data.Nat as N

open import FT
open import FT-Nat using (toℕ)

------------------------------------------------------------------
-- Finite Types and the natural numbers are intimately related.
--
toFin : (b : FT) → F.Fin (N.suc (toℕ b))
toFin b = F.fromℕ (toℕ b)

------------------------------------------------------------------
