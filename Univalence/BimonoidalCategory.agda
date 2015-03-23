{-# OPTIONS --without-K #-}

module BimonoidalCategory where

open import Level
open import Relation.Binary using (Rel)
open import Algebra.FunctionProperties using (Op₂)

------------------------------------------------------------------------------
-- Definition

record IsBimonoidalCategory : Set where
 -- to do

record BimonoidalCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  infixr 9 _∘_
  infixl 7 _⊗_
  infixl 6 _⊕_
  infix  4 _⇒_
  field
    Obj                   : Set o
    _⇒_                   : Rel Obj ℓ
    _∘_                   : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    _≈_                   : ∀ {A B} → Rel (A ⇒ B) e
    _⊕_                   : Op₂ Obj
    _⊗_                   : Op₂ Obj
    0#                    : Obj
    1#                    : Obj
    isBimonoidalCategory  : IsBimonoidalCategory 

------------------------------------------------------------------------------
