{-# OPTIONS --without-K #-}

module EquivEquiv where

open import Level using (Level; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; trans; cong)

import Relation.Binary.EqReasoning as EqR

open import Equiv
 using (module isequiv; iseq; _≃_; id≃; sym≃; _●_; _∼_; g-left-inv;
   path⊎)

------------------------------------------------------------------------------
-- Extensional equivalence of equivalences

-- We need g to "pin down" the inverse, else we get lots of unsolved
-- metas.

record _≋_ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} (eq₁ eq₂ : A ≃ B) :
  Set (ℓ ⊔ ℓ') where
  constructor eq
  open isequiv
  field
    f≡ : proj₁ eq₁ ∼ proj₁ eq₂
    g≡ : g (proj₂ eq₁) ∼ g (proj₂ eq₂)
 
-- The equivalence of equivalences is an equivalence relation that
-- respects composition

id≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x : A ≃ B} → x ≋ x
id≋ = record { f≡ = λ _ → P.refl ; g≡ = λ _ → P.refl }

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
●-resp-≋ {f = f , _} {_ , iseq h⁻¹ _ _ _} {_ , iseq g⁻¹ _ _ _} {i , _}
  (eq f≡ g≡) (eq h≡ i≡) =
  eq (λ x → P.trans (P.cong f (h≡ x)) (f≡ (i x)))
     (λ x → P.trans (P.cong g⁻¹ (g≡ x)) (i≡ (h⁻¹ x)))

path⊎-resp-≋ : {A B C D : Set} {f h : A ≃ B} {g i : C ≃ D} → f ≋ h → g ≋ i →
  (path⊎ f g) ≋ (path⊎ h i)
path⊎-resp-≋ {f = f , fe} {h , he} {g , ge} {i , ie}
  (eq f≡ g≡) (eq h≡ i≡) = eq f⊎g~h⊎i flip
  where
    f⊎g~h⊎i : proj₁ (path⊎ (f , fe) (g , ge)) ∼ proj₁ (path⊎ (h , he) (i , ie))
    f⊎g~h⊎i (inj₁ x) = P.cong inj₁ (f≡ x)
    f⊎g~h⊎i (inj₂ y) = P.cong inj₂ (h≡ y)
    flip : isequiv.g (proj₂ (path⊎ (f , fe) (g , ge))) ∼
           isequiv.g (proj₂ (path⊎ (h , he) (i , ie)))
    flip (inj₁ x) = P.cong inj₁ (g≡ x)
    flip (inj₂ y) = P.cong inj₂ (i≡ y)

linv≋ : ∀ {ℓ} {A B : Set ℓ} (x : A ≃ B) →
  (x ● (sym≃ x)) ≋ id≃ {A = B}
linv≋ x = eq (λ z → isequiv.α (proj₂ x) z) (λ z → isequiv.α (proj₂ x) z)

rinv≋ : ∀ {ℓ} {A B : Set ℓ} (x : A ≃ B) → ((sym≃ x) ● x) ≋ id≃
rinv≋ x = eq (λ z → g-left-inv x z) (λ z → g-left-inv x z)

-- underlying it all, it uses ∘ and ≡, thus associativity is immediate

●-assoc : {A B C D : Set} (f : A ≃ B) (g : B ≃ C) (h : C ≃ D) →
      ((h ● g) ● f) ≋ (h ● (g ● f))
●-assoc _ _ _ = eq (λ x → P.refl) (λ x → P.refl)

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

module ≋-Reasoning where
  module _ {a b} {A : Set a} {B : Set b} where
    open EqR (A S≃ B) public
      hiding (_≡⟨_⟩_; _≡⟨⟩_) renaming (_≈⟨_⟩_ to _≋⟨_⟩_)
      
------------------------------------------------------------------------------
