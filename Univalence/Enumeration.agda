{-# OPTIONS --without-K #-}

module Enumeration where

open import Equiv
open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ;_+_;_*_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_;_,_)
open import Function using (_∘_)
open import TypeEquivalences using (path⊎; path×)
open import FinEquiv

-- An Enumerated 'type' is an isomorphism between a
-- "set" A and Fin n.  Do note that it comes with a particular
-- isomorphism, so that for any given A, it has n! enumerations.
Enum : ∀ {ℓ} → (A : Set ℓ) → (n : ℕ) →  Set ℓ
Enum A n = A ≃ Fin n

-- from TypeEquivalences and VecOps, we can get operations on enumerations
-- (note: should generalize TypeEquivalences to using Level)
_⊕e_ : {A : Set} {B : Set} {n m : ℕ} →
  Enum A n → Enum B m → Enum (A ⊎ B) (n + m)
eA ⊕e eB = trans≃ (path⊎ eA eB) Plus.fwd-iso

_⊛e_ : {A B : Set} {n m : ℕ} → Enum A n → Enum B m → Enum (A × B) (n * m)
eA ⊛e eB = trans≃ (path× eA eB) Times.fwd-iso

0E : Enum ⊥ 0
0E = ⊥-elim , mkqinv Fin0-⊥ (λ { () }) {- (λ x → ⊥-elim (Fin0-⊥ x)) -} (λ { () })
