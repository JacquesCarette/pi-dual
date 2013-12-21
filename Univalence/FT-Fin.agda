{-# OPTIONS --without-K #-}
module FT-Fin where

open import Data.Empty
open import Data.Unit
import Data.Fin as F
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product
open import Data.Vec
import Data.List as L
open import Function renaming (_∘_ to _○_)

open import FT
open import FT-Nat

------------------------------------------------------------------
-- Finite Types and the natural numbers are intimately related.
--
toFin : (B : FT) → F.Fin (suc (toℕ B))
toFin ZERO = F.zero
toFin ONE = F.suc F.zero
toFin (PLUS b₀ b₁) with toFin b₀ | toFin b₁ 
... | f₀ | f₁ = ? -- f₀ F.+ f₁
toFin (TIMES b₀ b₁) = {!!} -- (toℕ b₀) * (toℕ b₁)

--F.toℕ f₀ + suc (toℕ b₁) != suc (toℕ b₀ + toℕ b₁) 


-- f₀ : F.Fin (suc (toℕ b₀))
-- f₁ : F.Fin (suc (toℕ b₁))
-- f₀ + f₁ : F.Fin (suc (suc (toℕ b₀ + toℕ b₁)))
--?0 : F.Fin (suc (toℕ b₀ + toℕ b₁))


fromFin : {n : ℕ} → F.Fin n → FT
fromFin F.zero = ZERO
fromFin (F.suc n) = {!!} -- PLUS ONE (fromℕ n)

------------------------------------------------------------------
