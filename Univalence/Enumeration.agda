{-# OPTIONS --without-K #-}

module Enumeration where

open import Equiv
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec using (tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open import Data.Product using (_,_; proj₂)
open import Function using (_∘_)
open import FiniteFunctions

-- An Enumerated 'type' is an isomorphism between a
-- "set" A and Fin n.  Do note that it comes with a particular
-- isomorphism, so that for any given A, it has n! enumerations.
Enum : ∀ {ℓ} → (A : Set ℓ) → (n : ℕ) →  Set ℓ
Enum A n = A ≃ Fin n

-- Enumerated types are extensional, in a way
funext : {n : ℕ} {A B : Set} {f g : A → B} → (e : Enum A n) → 
  ((x : A) →  f x ≡ g x) → 
  tabulate (f ∘ qinv.g (proj₂ e))  ≡ tabulate (g ∘ qinv.g (proj₂ e))
funext {n} {A} {B} {f} {g} (f₁ , mkqinv g₁ α₁ β₁) fe = finext (λ i → fe (g₁ i))
