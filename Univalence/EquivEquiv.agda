{-# OPTIONS --without-K #-}

module EquivEquiv where

open import Level using (Level; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

import Relation.Binary.EqReasoning as EqR

open import Function using (_∘_)

open import Equiv
 using (module isqinv; qinv; _≃_; id≃; sym≃; _●_; _∼_; sym∼; trans∼;
   _⊎≃_; β₁; β₂; gg; β⊎₁; β⊎₂)

------------------------------------------------------------------------------
-- Extensional equivalence of equivalences

-- We need g to "pin down" the inverse, else we get lots of unsolved
-- metas.

infix 4 _≋_

record _≋_ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} (eq₁ eq₂ : A ≃ B) :
  Set (ℓ ⊔ ℓ') where
  constructor eq
  open isqinv
  field
    .f≡ : proj₁ eq₁ ∼ proj₁ eq₂
    .g≡ : g (proj₂ eq₁) ∼ g (proj₂ eq₂)
 
-- The equivalence of equivalences is an equivalence relation that
-- respects composition

id≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x : A ≃ B} → x ≋ x
id≋ = record { f≡ = λ _ → P.refl ; g≡ = λ _ → P.refl }

sym≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A ≃ B} → x ≋ y → y ≋ x
sym≋ (eq f≡ g≡) = eq (λ a → P.sym (f≡ a)) (λ b → P.sym (g≡ b))

flip≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A ≃ B} →
        x ≋ y → (sym≃ x) ≋ (sym≃ y)
flip≋ (eq f≡ g≡) = eq g≡ f≡

flip-sym≋ :  ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A ≃ B}→
        x ≋ y → sym≃ y ≋ sym≃ x
flip-sym≋ (eq f≡ g≡) = eq (sym∼ g≡) (sym∼ f≡)

trans≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y z : A ≃ B} →
         x ≋ y → y ≋ z → x ≋ z
trans≋ (eq f≡ g≡) (eq h≡ i≡) =
   eq (λ a → P.trans (f≡ a) (h≡ a)) (λ b → P.trans (g≡ b) (i≡ b))


_◎_ : {A B C : Set} {f h : B ≃ C} {g i : A ≃ B} → f ≋ h → g ≋ i →
  (f ● g) ≋ (h ● i)
_◎_ {f = f} {h} {g} {i}
  (eq f≡ g≡) (eq h≡ i≡) = eq fwd bwd
  -- eq (λ x → {!!} ) -- P.trans (P.cong f (h≡ x)) (f≡ (i x)))
  --   (λ x → {!!} ) -- P.trans (P.cong g⁻¹ (g≡ x)) (i≡ (h⁻¹ x)))
  where
    open P.≡-Reasoning
    .fwd : proj₁  (f ● g) ∼ proj₁ (h ● i)
    fwd x =  begin (
      proj₁ (f ● g) x
        ≡⟨ β₁ x ⟩
      proj₁ f (proj₁ g x)
        ≡⟨ f≡ (proj₁ g x) ⟩
      proj₁ h (proj₁ g x)
        ≡⟨ P.cong (proj₁ h) (h≡ x) ⟩
      proj₁ h (proj₁ i x)
        ≡⟨ P.sym (β₁ x) ⟩
      proj₁ (h ● i) x ∎)
    .bwd :  gg (f ● g) ∼ gg (h ● i)
    bwd x = 
      begin (
        gg (f ● g) x
          ≡⟨ β₂ x ⟩
        gg g (gg f x)
          ≡⟨ i≡ (gg f x) ⟩
        gg i (gg f x)
          ≡⟨ P.cong (gg i) (g≡ x) ⟩
        gg i (gg h x)
          ≡⟨ P.sym (β₂ x) ⟩
        gg (h ● i) x ∎)

⊎≃-resp-≋ : {A B C D : Set} {f h : A ≃ B} {g i : C ≃ D} → f ≋ h → g ≋ i →
  f ⊎≃ g ≋ h ⊎≃ i
⊎≃-resp-≋ {f = f} {h} {g} {i}
  (eq f≡ g≡) (eq h≡ i≡) = eq f⊎g~h⊎i flip
  where
    .f⊎g~h⊎i : proj₁ (f ⊎≃ g) ∼ proj₁ (h ⊎≃ i)
    f⊎g~h⊎i (inj₁ x) = {!P.trans (β⊎₁ (inj₁ x)) (P.cong inj₁ (f≡ x))!} -- P.cong inj₁ (f≡ x)
    f⊎g~h⊎i (inj₂ y) = {!!} -- P.cong inj₂ (h≡ y)
    .flip : isqinv.g (proj₂ (f ⊎≃ g)) ∼
           isqinv.g (proj₂ (h ⊎≃ i))
    flip (inj₁ x) = {!!} -- P.cong inj₁ (g≡ x)
    flip (inj₂ y) = {!!} -- P.cong inj₂ (i≡ y)

rinv≋ : ∀ {ℓ} {A B : Set ℓ} (x : A ≃ B) →
  (x ● (sym≃ x)) ≋ id≃ {A = B}
rinv≋ (_ , qinv _ α _) = eq (trans∼ β₁ α) (trans∼ β₂ α)

linv≋ : ∀ {ℓ} {A B : Set ℓ} (e : A ≃ B) → ((sym≃ e) ● e) ≋ id≃
linv≋ (_ , qinv _ _ β) = eq (trans∼ β₁ β) (trans∼ β₂ β) 

lid≋ : ∀ {ℓ} {A B : Set ℓ} {f : A ≃ B} → (id≃ ● f) ≋ f
lid≋ = eq β₁ β₂

rid≋ : ∀ {ℓ} {A B : Set ℓ} {f : A ≃ B} → (f ● id≃) ≋ f
rid≋ = eq β₁ β₂

--

{--
not needed: equivalent to id≋ 

symsym : ∀ {A B : Set} {f : A ≃ B} → sym≃ (sym≃ f) ≋ f
symsym = eq (λ _ → P.refl) (λ _ → P.refl)  

sym≃● : ∀ {A B C : Set} {g : B ≃ C} {f : A ≃ B} →
        sym≃ (g ● f) ≋ sym≃ f ● sym≃ g
sym≃● = eq (λ _ → P.refl) (λ _ → P.refl) 
--}

-- underlying it all, it uses ∘ and ≡, thus associativity is immediate

●-assoc : {A B C D : Set} {f : A ≃ B} {g : B ≃ C} {h : C ≃ D} →
      ((h ● g) ● f) ≋ (h ● (g ● f))
●-assoc {f = f} {g} {h} = eq fwd bwd
  where
    open P.≡-Reasoning
    fwd : proj₁ ((h ● g) ● f) ∼ proj₁ (h ● (g ● f))
    fwd x = begin (
       proj₁ ((h ● g) ● f) x
         ≡⟨ β₁ x ⟩
      proj₁ (h ● g) (proj₁ f x)
         ≡⟨ β₁ (proj₁ f x) ⟩
      proj₁ h (proj₁ g (proj₁ f x))
         ≡⟨ P.cong (proj₁ h) (P.sym (β₁ x)) ⟩
      proj₁ h (proj₁ (g ● f) x)
         ≡⟨ P.sym (β₁ x) ⟩
       proj₁ (h ● (g ● f)) x ∎)
    bwd : gg ((h ● g) ● f) ∼ gg (h ● (g ● f))
    bwd x = begin (
      gg ((h ● g) ● f) x
         ≡⟨ β₂ x ⟩
      gg f (gg (h ● g) x)
         ≡⟨ P.cong (gg f) (β₂ x) ⟩
      gg f (gg g (gg h x))
         ≡⟨ P.sym (β₂ (gg h x)) ⟩
      gg (g ● f) (gg h x)
         ≡⟨ P.sym (β₂ x) ⟩
      gg (h ● (g ● f)) x ∎)

●-assocl : {A B C D : Set} {f : A ≃ B} {g : B ≃ C} {h : C ≃ D} →
       h ● (g ● f) ≋ (h ● g) ● f
●-assocl {f = f} {g} {h} = sym≋ (●-assoc {f = f} {g} {h})

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
