{-# OPTIONS --without-K #-}

-- Note that this is properly named, but it does depend on our version of
-- Equiv and TypeEquiv for a number of things.

module Data.Sum.Properties where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)

import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong; trans)
open import Function as F using (id; _∘_)

open import Equiv using (_∼_)
open import TypeEquiv
  using (unite₊; uniti₊; unite₊′; uniti₊′;
    swap₊; assocl₊; assocr₊)

infix 8 _⊎→_
infix 12 _⊎∼_

_⊎→_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
_⊎→_ = map⊎

------------------------------------------------------------------------------
-- Note that all these lemmas are "simple" in the sense that they
-- are all about ⊎→ (i.e. map⊎) rather than [_,_]

abstract

  id⊎id∼id : {A B : Set} → (F.id {A = A} ⊎→ F.id {A = B}) ∼ F.id
  id⊎id∼id (inj₁ x) = P.refl
  id⊎id∼id (inj₂ y) = P.refl

  ⊎∘∼∘⊎ : {A B C D E F : Set} →
    {f : A → C} {g : B → D} {h : C → E} {i : D → F} →
    (h F.∘ f) ⊎→ (i F.∘ g) ∼ (h ⊎→ i) ∘ (f ⊎→ g)
  ⊎∘∼∘⊎ (inj₁ x) = P.refl
  ⊎∘∼∘⊎ (inj₂ y) = P.refl

  _⊎∼_ : {A B C D : Set} → {f₀ g₀ : A → B} {f₁ g₁ : C → D} →
    (e₁ : f₀ ∼ g₀) → (e₂ : f₁ ∼ g₁) →  
    f₀ ⊎→ f₁ ∼ g₀ ⊎→ g₁
  _⊎∼_ f₀~g₀ _ (inj₁ x) = P.cong inj₁ (f₀~g₀ x)
  _⊎∼_ _ f₁~g₁ (inj₂ y) = P.cong inj₂ (f₁~g₁ y)

  unite₊-coh : {A B : Set} {f : A → B} →
    unite₊ ∘ (id ⊎→ f) ∼ f ∘ unite₊
  unite₊-coh (inj₁ ())
  unite₊-coh (inj₂ y) = P.refl

  -- and the 'converse', of sorts; g is used here because
  -- this is usually applied with g = f⁻¹
  uniti₊-coh : {A B : Set} {f : A → B} → (id ⊎→ f) ∘ uniti₊ ∼ uniti₊ ∘ f
  uniti₊-coh x = P.refl

  unite₊′-coh : {A B : Set} {f : A → B} →
    unite₊′ ∘ (f ⊎→ id) ∼ f ∘ unite₊′
  unite₊′-coh (inj₁ x) = P.refl
  unite₊′-coh (inj₂ ())

  uniti₊′-coh : {A B : Set} {g : A → B} →
    (g ⊎→ id) ∘ uniti₊′ ∼ (uniti₊′ ∘ g)
  uniti₊′-coh x = P.refl

  assocr₊-wf : {A B C D E F : Set} →
    {f₀ : A → D} {f₁ : B → E} {f₂ : C → F} →
    assocr₊ ∘ ((f₀ ⊎→ f₁) ⊎→ f₂) ∼ (f₀ ⊎→ (f₁ ⊎→ f₂)) ∘ assocr₊
  assocr₊-wf (inj₁ (inj₁ x)) = P.refl
  assocr₊-wf (inj₁ (inj₂ y)) = P.refl
  assocr₊-wf (inj₂ y) = P.refl

  assocl₊-wf : {A B C D E F : Set} →
    {f₀ : A → D} {f₁ : B → E} {f₂ : C → F} →
    ((f₀ ⊎→ f₁) ⊎→ f₂) ∘ assocl₊ ∼ assocl₊ ∘ (f₀ ⊎→ (f₁ ⊎→ f₂))
  assocl₊-wf (inj₁ x) = P.refl
  assocl₊-wf (inj₂ (inj₁ x)) = P.refl
  assocl₊-wf (inj₂ (inj₂ y)) = P.refl

  triangle⊎-right : {A B : Set} →
    unite₊′ ⊎→ F.id {A = B} ∼ (F.id {A = A} ⊎→ unite₊) ∘ assocr₊
  triangle⊎-right (inj₁ (inj₁ x)) = P.refl
  triangle⊎-right (inj₁ (inj₂ ()))
  triangle⊎-right (inj₂ y) = P.refl

  triangle⊎-left : {A B : Set} →
    uniti₊′ ⊎→ F.id {A = B} ∼ assocl₊ ∘ (F.id {A = A} ⊎→ uniti₊)
  triangle⊎-left (inj₁ x) = P.refl
  triangle⊎-left (inj₂ y) = P.refl

  pentagon⊎-right : {A B C D : Set} →
    assocr₊ ∘ assocr₊ {A = A ⊎ B} {C} {D} ∼ (F.id ⊎→ assocr₊) ∘ assocr₊ ∘ (assocr₊ ⊎→ F.id)
  pentagon⊎-right (inj₁ (inj₁ (inj₁ x))) = P.refl
  pentagon⊎-right (inj₁ (inj₁ (inj₂ y))) = P.refl
  pentagon⊎-right (inj₁ (inj₂ y)) = P.refl
  pentagon⊎-right (inj₂ y) = P.refl

  pentagon⊎-left : {A B C D : Set} →
    assocl₊ ∘ assocl₊ {A = A} {B} {C ⊎ D} ∼ (assocl₊ ⊎→ F.id) ∘ assocl₊ ∘ (F.id ⊎→ assocl₊)
  pentagon⊎-left (inj₁ x) = P.refl
  pentagon⊎-left (inj₂ (inj₁ x)) = P.refl
  pentagon⊎-left (inj₂ (inj₂ (inj₁ x))) = P.refl
  pentagon⊎-left (inj₂ (inj₂ (inj₂ y))) = P.refl

  swap₊-coh : {A B C D : Set} {f : A → C} {g : B → D} →
    swap₊ ∘ (f ⊎→ g) ∼ (g ⊎→ f) ∘ swap₊
  swap₊-coh (inj₁ x) = P.refl
  swap₊-coh (inj₂ y) = P.refl

  hexagon⊎-right : {A B C : Set} →
    assocr₊ {A = B} {C} {A} ∘ swap₊ ∘ assocr₊ ∼ (F.id ⊎→ swap₊) ∘ assocr₊ ∘ (swap₊ ⊎→ F.id)
  hexagon⊎-right (inj₁ (inj₁ x)) = P.refl
  hexagon⊎-right (inj₁ (inj₂ y)) = P.refl
  hexagon⊎-right (inj₂ y) = P.refl

  hexagon⊎-left : {A B C : Set} →
    assocl₊ {A = A} {B} {C} ∘ swap₊ ∘ assocl₊ ∼ (swap₊ ⊎→ F.id) ∘ assocl₊ ∘ (F.id ⊎→ swap₊)
  hexagon⊎-left (inj₁ x) = P.refl
  hexagon⊎-left (inj₂ (inj₁ x)) = P.refl
  hexagon⊎-left (inj₂ (inj₂ y)) = P.refl

------------------------------------------------------------------------------
