{-# OPTIONS --without-K #-}

-- Inspired by Thorsten Altenkirch's definition of Groupoids 
-- see his OmegaCats repo on github.

module Groupoid where

open import Relation.Binary.PropositionalEquality

-- 1-groupoids are those where the various laws hold up to ≡.
record 1Groupoid : Set₁ where
  field
    set : Set₀
    _↝_ : set → set → Set
    id : ∀ {x} → x ↝ x
    _∘_ : ∀ {x y z} → y ↝ z → x ↝ y → x ↝ z
    _⁻¹ : ∀ {x y} → x ↝ y → y ↝ x
    lneutr : ∀ {x y}(α : x ↝ y) → id ∘ α ≡ α
    rneutr : ∀ {x y}(α : x ↝ y) → α ∘ id ≡ α
    assoc : ∀ {w x y z}(α : y ↝ z)(β : x ↝ y)(δ : w ↝ x) → (α ∘ β) ∘ δ ≡ α ∘ (β ∘ δ)
    linv : ∀ {x y}(α : x ↝ y) → α ⁻¹ ∘ α ≡ id
    rinv : ∀ {x y}(α : x ↝ y) → α ∘ α ⁻¹ ≡ id

