{-# OPTIONS --without-K #-}

-- Borrowed from OldUnivalence/Equivalences.agda, without HoTT
-- and then upgraded to work on Setoid rather than just on ≡
module EquivSetoid where

open import Level
open import Relation.Binary using (Setoid; module Setoid)
open import Data.Product using (_×_; _,′_; _,_)

open import Equiv using (_≃_)

open import Function.Equality
import Function as Fun

infix 4 _≃S_

open Setoid

record _≃S_ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (A : Setoid ℓ₁ ℓ₂) (B : Setoid ℓ₃ ℓ₄)  : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  constructor equiv

  field
    f : A ⟶ B
    g : B ⟶ A
    α : ∀ {x y} → _≈_ B x y → _≈_ B ((f ∘ g) ⟨$⟩ x) y
    β : ∀ {x y} → _≈_ A x y → _≈_ A ((g ∘ f) ⟨$⟩ x) y

id≃S : ∀ {ℓ₁ ℓ₂} {A : Setoid ℓ₁ ℓ₂} → A ≃S A
id≃S {A = A} = equiv id id Fun.id Fun.id 

sym≃S : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} → (A ≃S B) → B ≃S A
sym≃S eq = equiv e.g e.f e.β e.α
  where module e = _≃S_ eq

trans≃S : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} {C : Setoid ℓ₅ ℓ₆} → A ≃S B → B ≃S C → A ≃S C
trans≃S {A = A} {B} {C} A≃B B≃C = equiv f g α' β'
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


_✴_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} → (A ≃S B) → (x : Carrier A) → Carrier B
(equiv f _ _ _) ✴ x = f ⟨$⟩ x  

≃-Setoid : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} → Setoid ℓ₁ ℓ₂ → Setoid ℓ₃ ℓ₄ → Setoid (ℓ₄ ⊔ (ℓ₃ ⊔ (ℓ₂ ⊔ ℓ₁))) (ℓ₄ ⊔ (ℓ₃ ⊔ (ℓ₂ ⊔ ℓ₁)))
≃-Setoid {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B = record 
  { Carrier = A ≃S B
  ; _≈_ = λ eq₁ eq₂ → ( (∀ {x y} → _≈_ A x y → _≈_ B (eq₁ ✴ x) (eq₂ ✴ y)) ×
                                    (∀ {x y} → _≈_ B x y → _≈_ A ((sym≃S eq₁) ✴ x) ((sym≃S eq₂) ✴ y) ) )
  ; isEquivalence = record 
    { refl = λ {eq} → ((λ {x} {y} x≈y → cong (f eq) x≈y) ,′ 
                                (λ {x} {y} x≈y → cong (g eq) x≈y))
    ; sym = λ { (cong_f , cong_g) → 
                   (λ {x} {y} x≈y → sym B (cong_f (sym A x≈y))) ,′ 
                   (λ {x} {y} x≈y  → sym A (cong_g (sym B x≈y))) }
    ; trans = λ { (cong_f₁ , cong_g₁) (cong_f₂ , cong_g₂) →
                   ( (λ {x} {y} x≈y → trans B (cong_f₁ (refl A)) (cong_f₂ x≈y)) ,′
                      (λ {x} {y} x≈y → trans A (cong_g₁ (refl B)) (cong_g₂ x≈y)) ) }
    } 
  }
  where open _≃S_

-- equivalences are injective


inj≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} → (eq : A ≃S B) → {x y : Carrier A} → 
  _≈_ B (eq ✴ x)  (eq ✴ y) → _≈_ A x y
inj≃ {A = A'} (equiv f g _ β) p = A.trans (A.sym (β A.refl)) (A.trans (cong g p) (β A.refl))
  where
    module A = Setoid A'
