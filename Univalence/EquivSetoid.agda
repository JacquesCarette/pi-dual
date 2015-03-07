{-# OPTIONS --without-K #-}

-- Borrowed from OldUnivalence/Equivalences.agda, without HoTT
-- and then upgraded to work on Setoid rather than just on ≡
module EquivSetoid where

open import Level
open import Relation.Binary using (Setoid; module Setoid)
open import Data.Product using (_×_; _,′_; _,_)
open import Relation.Binary.PropositionalEquality as P using ()
open import Data.Empty 

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

-- any type can be made into a setoid over ≡
≡-Setoid : ∀ {ℓ} → (A : Set ℓ) → Setoid ℓ ℓ
≡-Setoid A = record 
  { Carrier = A 
  ; _≈_ = P._≡_ 
  ; isEquivalence = record 
    { refl = P.refl 
    ; sym = P.sym 
    ; trans = P.trans 
    } 
  }

0S : Setoid zero zero
0S = ≡-Setoid ⊥

-- can't use id because it is not sufficiently dependently typed!
0≃S : 0S ≃S 0S
0≃S = equiv id id (λ x → x) (λ x → x) 

-- just to make things prettier
_≃S≡_ : ∀ {ℓ₁} → (A B : Set ℓ₁) → Set ℓ₁
A ≃S≡ B = (≡-Setoid A) ≃S (≡-Setoid B)

record _≋_ {ℓ₁} {A B : Set ℓ₁} (eq₁ eq₂ : A ≃S≡ B) : Set ℓ₁ where
  constructor equivS
  field
    f≡ : ∀ (x : A) → P._≡_ (_≃S_.f eq₁ ⟨$⟩ x) (_≃S_.f eq₂ ⟨$⟩ x)
    g≡ : ∀ (x : B) → P._≡_ (_≃S_.g eq₁ ⟨$⟩ x) (_≃S_.g eq₂ ⟨$⟩ x)

id≋ : ∀ {ℓ} {A B : Set ℓ} {x : A ≃S≡ B} → x ≋ x
id≋ = record { f≡ = λ x → P.refl ; g≡ = λ x → P.refl }

sym≋ : ∀ {ℓ} {A B : Set ℓ} {x y : A ≃S≡ B} → x ≋ y → y ≋ x
sym≋ (equivS f≡ g≡) = equivS (λ a → P.sym (f≡ a)) (λ b → P.sym (g≡ b))

trans≋ : ∀ {ℓ} {A B : Set ℓ} {x y z : A ≃S≡ B} → x ≋ y → y ≋ z → x ≋ z
trans≋ (equivS f≡ g≡) (equivS h≡ i≡) =
   equivS (λ a → P.trans (f≡ a) (h≡ a)) (λ b → P.trans (g≡ b) (i≡ b))
  
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
    AS = ≡-Setoid A
    BS = ≡-Setoid B
    
-- equivalences are injective
inj≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} → (eq : A ≃S B) → {x y : Carrier A} → 
  _≈_ B (eq ✴ x)  (eq ✴ y) → _≈_ A x y
inj≃ {A = A'} (equiv f g _ β) p = A.trans (A.sym (β A.refl)) (A.trans (cong g p) (β A.refl))
  where
    module A = Setoid A'
