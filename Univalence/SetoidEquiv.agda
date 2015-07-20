{-# OPTIONS --without-K #-}

module SetoidEquiv where

open import Level using (Level; _⊔_)
open import Function.Equality using (_∘_; _⟶_; _⟨$⟩_)
open import Relation.Binary using (Setoid; module Setoid)
open import Relation.Binary.PropositionalEquality as P using (setoid) 

open Setoid

infix 4 _≃S_

------------------------------------------------------------------------------
-- A setoid gives us a set and an equivalence relation on that set.
-- A common equivalence relation that is used on setoids is ≡

-- In general, two setoids are equivalent if:

record _≃S_ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (A : Setoid ℓ₁ ℓ₂) (B : Setoid ℓ₃ ℓ₄) : 
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  constructor equiv
  field
    f : A ⟶ B
    g : B ⟶ A
    α : ∀ {x y} → _≈_ B x y → _≈_ B ((f ∘ g) ⟨$⟩ x) y
    β : ∀ {x y} → _≈_ A x y → _≈_ A ((g ∘ f) ⟨$⟩ x) y

-- Abbreviation for the special case in which the equivalence relation
-- is just ≡:

_≃S≡_ : ∀ {ℓ₁} → (A B : Set ℓ₁) → Set ℓ₁
A ≃S≡ B = (P.setoid A) ≃S (P.setoid B)

-- Two equivalences between setoids are themselves equivalent if

record _≋_ {ℓ₁} {A B : Set ℓ₁} (eq₁ eq₂ : A ≃S≡ B) : Set ℓ₁ where
  constructor equivS
  field
    f≡ : ∀ (x : A) → P._≡_ (_≃S_.f eq₁ ⟨$⟩ x) (_≃S_.f eq₂ ⟨$⟩ x)
    g≡ : ∀ (x : B) → P._≡_ (_≃S_.g eq₁ ⟨$⟩ x) (_≃S_.g eq₂ ⟨$⟩ x)
    -- note that this appears to be redundant (especially when looking
    -- at the proofs), but having both f and g is needed for inference
    -- of other aspects to succeed.

id≋ : ∀ {ℓ} {A B : Set ℓ} {x : A ≃S≡ B} → x ≋ x
id≋ = record { f≡ = λ x → P.refl ; g≡ = λ x → P.refl }

sym≋ : ∀ {ℓ} {A B : Set ℓ} {x y : A ≃S≡ B} → x ≋ y → y ≋ x
sym≋ (equivS f≡ g≡) = equivS (λ a → P.sym (f≡ a)) (λ b → P.sym (g≡ b))

trans≋ : ∀ {ℓ} {A B : Set ℓ} {x y z : A ≃S≡ B} → x ≋ y → y ≋ z → x ≋ z
trans≋ (equivS f≡ g≡) (equivS h≡ i≡) =
   equivS (λ a → P.trans (f≡ a) (h≡ a)) (λ b → P.trans (g≡ b) (i≡ b))
  
-- The set of equivalences between setoids is itself is a setoid
-- WARNING: this is not generic, but specific to ≡-Setoids of functions.

≃S-Setoid : ∀ {ℓ₁} → (A B : Set ℓ₁) → Setoid ℓ₁ ℓ₁
≃S-Setoid {ℓ₁} A B = record 
  { Carrier = AS ≃S BS
  ; _≈_ = _≋_ 
  ; isEquivalence = record
    { refl = id≋
    ; sym = sym≋
    ; trans = trans≋
    }
  }
  where
    open _≃S_
    AS = P.setoid A
    BS = P.setoid B
    
------------------------------------------------------------------------------
