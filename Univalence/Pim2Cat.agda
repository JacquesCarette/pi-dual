{-# OPTIONS --without-K #-}

module Pim2Cat where

open import Level using (zero)

import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; isEquivalence) 

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)

open import PiU using (U)
open import PiLevelm2 using (_⟷_; collapse)

-- We will define a rig category whose objects are Pi types and whose
-- morphisms are the trivial equivalence that identifies all Pi types;
-- and where the equivalence of morphisms is propositional equality ≡

------------------------------------------------------------------------------
-- First it is a category

triv : {A B : U} → (f : A ⟷ B) → (collapse P.≡ f)
triv collapse = P.refl 

Pim2Cat : Category zero zero zero
Pim2Cat = record
  { Obj = U
  ; _⇒_ = _⟷_
  ; _≡_ = P._≡_
  ; id = collapse
  ; _∘_ = λ _ _ → collapse
  ; assoc = P.refl 
  ; identityˡ = λ {A} {B} {f} → triv f
  ; identityʳ = λ {A} {B} {f} → triv f
  ; equiv = P.isEquivalence
  ; ∘-resp-≡ = λ _ _ → P.refl
  }

-- and a groupoid

Pim2Groupoid : Groupoid Pim2Cat
Pim2Groupoid = record 
  { _⁻¹ = λ _ → collapse
  ; iso = record { isoˡ = P.refl; isoʳ = P.refl }
  }

------------------------------------------------------------------------------
