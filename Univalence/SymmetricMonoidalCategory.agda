{-# OPTIONS --without-K #-}

module SymmetricMonoidalCategory where

open import Level

open import Categories.Category using (Category)
open import Categories.Monoidal using (Monoidal)
open import Categories.Monoidal.Braided using (Braided; module Braided) 
open import Categories.NaturalIsomorphism using (module NaturalIsomorphism) 
open import Categories.NaturalTransformation using (id; _∘₁_; _≡_)

------------------------------------------------------------------------------
-- Definition

record SymmetricMonoidalCategory {o ℓ e} {ℂ  : Category o ℓ e} {Mℂ : Monoidal ℂ}
  (BMℂ : Braided Mℂ) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Braided BMℂ using (braid)
  open NaturalIsomorphism braid using () renaming (F⇒G to x⊗y⇒y⊗x; F⇐G to y⊗x⇒x⊗y)
  field
    symmetry : y⊗x⇒x⊗y ∘₁ x⊗y⇒y⊗x ≡ id

------------------------------------------------------------------------------
