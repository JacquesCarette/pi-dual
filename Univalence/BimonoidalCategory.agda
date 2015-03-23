{-# OPTIONS --without-K #-}

module BimonoidalCategory where

open import Level
open import Relation.Binary using (Rel)
open import Algebra.FunctionProperties using (Op₂)

------------------------------------------------------------------------------
-- Definition

record IsCategory {o ℓ e} {Obj : Set o}
  (_⇒_ : Rel Obj ℓ)
  (_≈_ : ∀ {A B} → Rel (A ⇒ B) e)
  (id  : ∀ {A} → A ⇒ A)
  (_∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C))
  : Set (o ⊔ ℓ ⊔ e) where
  field
    idleft  : {A B : Obj} {f : A ⇒ B} → (id ∘ f) ≈ f
    idright : {A B : Obj} {f : A ⇒ B} → (f ∘ id) ≈ f
    ∘assoc  : {A B C D : Obj} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
              ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))

record Iso {o ℓ e} {Obj : Set o}
  (_⇒_ : Rel Obj ℓ)
  (_≈_ : ∀ {A B} → Rel (A ⇒ B) e)
  (id  : ∀ {A} → A ⇒ A)
  (_∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C))
  (A B : Obj)
  :  Set (o ⊔ ℓ ⊔ e) where
  field
    fwd     : A ⇒ B 
    bwd     : B ⇒ A
    fwd∘bwd : (_∘_ {B} {A} {B} fwd bwd) ≈ id {B}
    bwd∘fwd : (_∘_ {A} {B} {A} bwd fwd) ≈ id {A}

record IsMonoid {o ℓ e} {Obj : Set o}
  (_⇒_ : Rel Obj ℓ)
  (_≈_ : ∀ {A B} → Rel (A ⇒ B) e)
  (id  : ∀ {A} → A ⇒ A)
  (_∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C))
  (u : Obj)
  (_op_ : Op₂ Obj)
  (opf : ∀ {A B C D} → (A ⇒ C) → (B ⇒ D) → (_⇒_ (A op B) (C op D)))
  : Set (o ⊔ ℓ ⊔ e) where
  field 
    assoc : {A B C : Obj} → Iso _⇒_ _≈_ id _∘_ ((A op B) op C) (A op (B op C))
    unite : {A : Obj} → Iso _⇒_ _≈_ id _∘_ (u op A) A
    uniti : {A : Obj} → Iso _⇒_ _≈_ id _∘_ (A op u) A

record IsBimonoidalCategory {o ℓ e} {Obj : Set o}
  (_⇒_ : Rel Obj ℓ)
  (_≈_ : ∀ {A B} → Rel (A ⇒ B) e)
  (id  : ∀ {A} → A ⇒ A)
  (_∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C))
  (0#  : Obj)
  (_+_ : Op₂ Obj)
  (_⊕_ : ∀ {A B C D} → (A ⇒ C) → (B ⇒ D) → (_⇒_ (A + B) (C + D)))
  (1#  : Obj)
  (_*_ : Op₂ Obj)
  (_⊗_ : ∀ {A B C D} → (A ⇒ C) → (B ⇒ D) → (_⇒_ (A * B) (C * D)))
  : Set (o ⊔ ℓ ⊔ e) where
  field
    cat        : IsCategory _⇒_ _≈_ id _∘_
    +-isMonoid : IsMonoid _⇒_ _≈_ id _∘_ 0# _+_ _⊕_
    *-isMonoid : IsMonoid _⇒_ _≈_ id _∘_ 1# _*_ _⊗_
    -- ⊕ is a bifunctor
    -- units and assoc are natural transformations
    -- pentangon and triangle axioms
    -- multiplicative monoid
    -- distributivity

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
    isBimonoidalCategory : IsBimonoidalCategory _⇒_ _≈_ id _∘_ 0# _+_ _⊕_ 1# _*_ _⊗_

------------------------------------------------------------------------------
