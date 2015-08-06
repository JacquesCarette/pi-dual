{-# OPTIONS --without-K #-}

module FiniteType where

open import Equiv using (_≃_)
open import Data.Product using (Σ;_,_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

--------------------------------------------------------------------------
--
-- A finite type is a type which is equivalent to Fin n
--

FiniteType : Set → Set
FiniteType A = Σ ℕ (λ n → A ≃ Fin n)

∣_∣ : {A : Set} → FiniteType A → ℕ
∣ (n , _) ∣ = n
