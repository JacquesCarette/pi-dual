{-# OPTIONS --without-K #-}

module BimonoidalCategory where

open import Level
open import Relation.Binary using (Rel)
open import Algebra.FunctionProperties using (Op₂)

------------------------------------------------------------------------------
-- Definition

record BimonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  infixr 9 _∘_
  infixl 7 _+_ _⊕_
  infixl 6 _*_ _⊗_
  infix  4 _⇒_
  infix  1 _≈_
  field
    -- objects, morphisms, equality on morphisms
    Obj : Set o
    _⇒_ : Rel Obj ℓ
    _≈_ : ∀ {A B} → Rel (A ⇒ B) e
    -- plain category
    id  : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    -- additive monoid
    0#  : Obj
    _+_ : Op₂ Obj
    _⊕_ : ∀ {A B C D} → (A ⇒ C) → (B ⇒ D) → (A + B ⇒ C + D)
    -- multiplicative monoid
    1#  : Obj
    _*_ : Op₂ Obj
    _⊗_ : ∀ {A B C D} → (A ⇒ C) → (B ⇒ D) → (A * B ⇒ C * D)
    -- axioms
    -- plain category
    idleft  : {A B : Obj} {f : A ⇒ B} → id ∘ f ≈ f
    idright : {A B : Obj} {f : A ⇒ B} → f ∘ id ≈ f
    ∘assoc  : {A B C D : Obj} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
              (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
    -- additive monoid
    assocl+ : {A B C : Obj} → (A + B) + C ⇒ A + (B + C)
    assocr+ : {A B C : Obj} → A + (B + C) ⇒ (A + B) + C
    unitel+ : {A : Obj} → 0# + A ⇒ A
    uniter+ : {A : Obj} → A ⇒ 0# + A
    unitil+ : {A : Obj} → A + 0# ⇒ A
    unitir+ : {A : Obj} → A ⇒ A + 0#
    αassoc+≃ : {A B C : Obj} → assocl+ {A} {B} {C} ∘ assocr+ ≈ id
    βassoc+≃ : {A B C : Obj} → assocr+ {A} {B} {C} ∘ assocl+ ≈ id
    αunite+≃ : {A : Obj} → unitel+ {A} ∘ uniter+ ≈ id
    βunite+≃ : {A : Obj} → uniter+ {A} ∘ unitel+ ≈ id
    αuniti+≃ : {A : Obj} → unitil+ {A} ∘ unitir+ ≈ id
    βuniti+≃ : {A : Obj} → unitir+ {A} ∘ unitil+ ≈ id
    -- ⊕ is a bifunctor
    -- units and assoc are natural transformations
    -- pentangon and triangle axioms
    
    -- multiplicative monoid
    -- distributivity
    

------------------------------------------------------------------------------
