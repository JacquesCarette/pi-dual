{-# OPTIONS --without-K #-}

-- Borrowed from OldUnivalence/Equivalences.agda, without HoTT
-- and then upgraded to work on Setoid rather than just on ≡
module EquivSetoid where

open import Level
open import Relation.Binary using (Setoid; module Setoid)

open import Function.Equality
import Function as Fun

infix 4 _≃S_

open Setoid

record _≃S_ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (A : Setoid ℓ₁ ℓ₂) (B : Setoid ℓ₃ ℓ₄)  : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  constructor equiv

  A⇨A = A ⇨ A

  _∼₁_ = _≈_ (B ⇨ B)    
  _∼₂_ = _≈_ A⇨A

  field
    f : A ⟶ B
    g : B ⟶ A
    α : (f ∘ g) ∼₁ id
    β : (g ∘ f) ∼₂ id

private
  id≃ : ∀ {ℓ₁ ℓ₂} {A : Setoid ℓ₁ ℓ₂} → A ≃S A
  id≃ {A = A} = equiv id id Fun.id Fun.id 

  sym≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} → (A ≃S B) → B ≃S A
  sym≃ eq = equiv e.g e.f e.β e.α
    where module e = _≃S_ eq

  trans≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} {C : Setoid ℓ₅ ℓ₆} → A ≃S B → B ≃S C → A ≃S C
  trans≃ {A = A} {B} {C} A≃B B≃C = equiv f g α' β'
    where
      module fm = _≃S_ A≃B
      module gm = _≃S_ B≃C
      f : A ⟶ C
      f = gm.f ∘ fm.f
      g : C ⟶ A
      g = fm.g ∘ gm.g
      α' : _≈_ (C ⇨ C) (f ∘ g)  id
      α' = λ z → trans C (cong gm.f (fm.α (cong gm.g (refl C)))) (gm.α z) 
      β' : _≈_ (A ⇨ A) (g ∘ f) id
      β' = λ z → trans A (cong fm.g (gm.β (cong fm.f (refl A)))) (fm.β z)

≃-Setoid : ∀ {ℓ₁ ℓ₂} → Setoid (suc ℓ₁ ⊔ suc ℓ₂) (ℓ₁ ⊔ ℓ₂)
≃-Setoid {ℓ₁} {ℓ₂} = record 
  { Carrier = Setoid ℓ₁ ℓ₂ 
  ; _≈_ = _≃S_ 
  ; isEquivalence = record 
    { refl = id≃ 
    ; sym = sym≃ 
    ; trans = trans≃ 
    } 
  }

-- equivalences are injective

_✴_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} → (A ≃S B) → (x : Carrier A) → Carrier B
(equiv f _ _ _) ✴ x = f ⟨$⟩ x  

inj≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} → (eq : A ≃S B) → {x y : Carrier A} → 
  _≈_ B (eq ✴ x)  (eq ✴ y) → _≈_ A x y
inj≃ {A = A'} (equiv f g _ β) p = A.trans (A.sym (β A.refl)) (A.trans (cong g p) (β A.refl))
  where
    module A = Setoid A'
