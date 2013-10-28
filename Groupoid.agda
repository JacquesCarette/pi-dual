{-# OPTIONS --without-K #-}

-- Inspired by Thorsten Altenkirch's definition of Groupoids 
-- see his OmegaCats repo on github.  And copumpkin's definition of
-- Category (see his categories repo, also on github).

module Groupoid where

open import Data.Sum
open import Relation.Binary

-- 1-groupoids are those where the various laws hold up to ≈.
record 1Groupoid : Set₁ where
  infixr 9 _∘_
  infixr 5 _↝_
  infix  4 _≈_
  field
    set : Set₀
    _↝_ : set → set → Set
    _≈_ : ∀ {A B} → A ↝ B → A ↝ B → Set
    id : ∀ {x} → x ↝ x
    _∘_ : ∀ {x y z} → y ↝ z → x ↝ y → x ↝ z
    _⁻¹ : ∀ {x y} → x ↝ y → y ↝ x
    lneutr : ∀ {x y}(α : x ↝ y) → id ∘ α ≈ α
    rneutr : ∀ {x y}(α : x ↝ y) → α ∘ id ≈ α
    assoc : ∀ {w x y z}(α : y ↝ z)(β : x ↝ y)(δ : w ↝ x) → (α ∘ β) ∘ δ ≈ α ∘ (β ∘ δ)
    equiv : ∀ {x y} → IsEquivalence (_≈_ {x} {y})
    linv : ∀ {x y}(α : x ↝ y) → α ⁻¹ ∘ α ≈ id {x}
    rinv : ∀ {x y}(α : x ↝ y) → α ∘ α ⁻¹ ≈ id {y}
    ∘-resp-≈ : ∀ {x y z} {f h : y ↝ z} {g i : x ↝ y} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

_[_,_] : (C : 1Groupoid) → 1Groupoid.set C → 1Groupoid.set C → Set
_[_,_] = 1Groupoid._↝_

open 1Groupoid

_⊎G_ : 1Groupoid → 1Groupoid → 1Groupoid
A ⊎G B = record 
  { set = set A ⊎ set B
  ; _↝_ = {!!}
  ; _≈_ = {!!}
  ; id = {!!};
           _∘_ = {!!};
           _⁻¹ = {!!};
           lneutr = {!!};
           rneutr = {!!};
           assoc = {!!};
           equiv = {!!};
           linv = {!!};
           rinv = {!!};
           ∘-resp-≈ = {!!} }