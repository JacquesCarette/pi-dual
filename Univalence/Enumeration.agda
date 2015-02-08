{-# OPTIONS --without-K #-}

module Enumeration where

open import Equiv
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

-- An Enumerated 'type' is an isomorphism between a
-- "set" A and Fin n.  Do note that it comes with a particular
-- isomorphism, so that for any given A, it has n! enumerations.
data Enum {ℓ} (A : Set ℓ) (n : ℕ): Set ℓ where
    enum : A ≃ Fin n → Enum A n
