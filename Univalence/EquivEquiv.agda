{-# OPTIONS --without-K #-}

module EquivEquiv where

open import Level using (Level; _⊔_)
open import Data.Product using (_,_) 

open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; trans; cong)

open import Equiv using (mkqinv; _≃_; sym≃; _●_; _⋆_)

------------------------------------------------------------------------------
-- Extensional equivalence of equivalences

-- We need g to "pin down" the inverse, else we get lots of unsolved
-- metas.

record _≋_ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} (eq₁ eq₂ : A ≃ B) :
  Set (ℓ ⊔ ℓ') where
  constructor eq
  field
    f≡ : ∀ x → eq₁ ⋆ x P.≡ eq₂ ⋆ x
    g≡ : ∀ x → (sym≃ eq₁) ⋆ x P.≡ (sym≃ eq₂) ⋆ x
 
-- The equivalence of equivalences is an equivalence relation that
-- respects composition

id≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x : A ≃ B} → x ≋ x
id≋ = record { f≡ = λ x → P.refl ; g≡ = λ x → P.refl }

sym≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A ≃ B} → x ≋ y → y ≋ x
sym≋ (eq f≡ g≡) = eq (λ a → P.sym (f≡ a)) (λ b → P.sym (g≡ b))

flip≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A ≃ B} →
        x ≋ y → (sym≃ x) ≋ (sym≃ y)
flip≋ (eq f≡ g≡) = eq g≡ f≡

trans≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y z : A ≃ B} →
         x ≋ y → y ≋ z → x ≋ z
trans≋ (eq f≡ g≡) (eq h≡ i≡) =
   eq (λ a → P.trans (f≡ a) (h≡ a)) (λ b → P.trans (g≡ b) (i≡ b))

●-resp-≋ : {A B C : Set} {f h : B ≃ C} {g i : A ≃ B} → f ≋ h → g ≋ i →
  (f ● g) ≋ (h ● i)
●-resp-≋ {f = f , _} {_ , mkqinv h⁻¹ _ _} {_ , mkqinv g⁻¹ _ _} {i , _}
  (eq f≡ g≡) (eq h≡ i≡) =
  eq (λ x → P.trans (P.cong f (h≡ x)) (f≡ (i x)))
     (λ x → P.trans (P.cong g⁻¹ (g≡ x)) (i≡ (h⁻¹ x)))

-- underlying it all, it uses ∘ and ≡ 

●-assoc : {A B C D : Set} {f : A ≃ B} {g : B ≃ C} {h : C ≃ D} →
      ((h ● g) ● f) ≋ (h ● (g ● f))
●-assoc = eq (λ x → P.refl) (λ x → P.refl)

-- The setoid of equivalences under ≋

_S≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Setoid (ℓ ⊔ ℓ') (ℓ ⊔ ℓ')
_S≃_ A B = record
 { Carrier = A ≃ B
 ; _≈_ = _≋_
 ; isEquivalence = record
   { refl = id≋
   ; sym = sym≋
   ; trans = trans≋
   }
 }

------------------------------------------------------------------------------
-- Upon much reflexion, I think the proper definition of ≋ is

record _≋′_ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} (eq₁ eq₂ : A ≃ B) :
  Set (ℓ ⊔ ℓ') where
  constructor eq′
  field
    pA : A ≃ A -- automorphism of A
    pB : B ≃ B -- automorphism of B
    f≡ : ∀ x → eq₁ ⋆ x P.≡ (pB ● (eq₂ ● pA)) ⋆ x
    g≡ : ∀ x → (sym≃ eq₁) ⋆ x P.≡ (pA ● (sym≃ eq₂ ● pB)) ⋆ x

------------------------------------------------------------------------------
