{-# OPTIONS --without-K #-}

module FiniteTypeEquiv where
open import Level 
open import Data.Nat using (ℕ) 
open import Data.Fin using (Fin)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function.Equality using (_∘_; _⟶_; _⟨$⟩_)
open ≡-Reasoning
open import Function renaming (_∘_ to _○_)
open import FinVec

------------------------------------------------------------------------------
-- Permutations

record CPerm {ℓ : Level} (values : ℕ) (size : ℕ) : Set ℓ where
  constructor cp
  field
    π  : FinVec values size
    πᵒ : FinVec size values
    αp : π ∘̂ πᵒ ≡ 1C
    βp : πᵒ ∘̂ π ≡ 1C

-- Permutations are compared by ≡

-- The setoid of permutations under ≡ 

SCPerm : ∀ {ℓ} → ℕ → ℕ → Setoid ℓ ℓ
SCPerm m n = setoid (CPerm m n)

------------------------------------------------------------------------------
-- Equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) qinv 

sym≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A ≃ B) → (B ≃ A)
sym≃ (A→B , equiv) = e.g , mkqinv A→B e.β e.α
  where module e = qinv equiv

-- Equivalences are compared by ≋ which reduces to extensional
-- equality of the underlying back and forth functions

_⋆_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A ≃ B) → (x : A) → B
(f , _) ⋆ x = f x 

record _≋_ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} (eq₁ eq₂ : A ≃ B) :
  Set (ℓ ⊔ ℓ') where
  constructor eq
  field
    f≡ : ∀ x → eq₁ ⋆ x ≡ eq₂ ⋆ x
    g≡ : ∀ x → (sym≃ eq₁) ⋆ x ≡ (sym≃ eq₂) ⋆ x

id≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x : A ≃ B} → x ≋ x
id≋ = record { f≡ = λ x → refl ; g≡ = λ x → refl }

sym≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A ≃ B} → x ≋ y → y ≋ x
sym≋ (eq f≡ g≡) = eq (λ a → sym (f≡ a)) (λ b → sym (g≡ b))

trans≋ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y z : A ≃ B} → x ≋ y → y ≋ z → x ≋ z
trans≋ (eq f≡ g≡) (eq h≡ i≡) =
   eq (λ a → trans (f≡ a) (h≡ a)) (λ b → trans (g≡ b) (i≡ b))

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
-- Univalence...

-- On one side we have permutations under ≡
-- On the other we have equivalences under ≋
-- 
-- The equivalence of these two sides uses a version of ≃ (called ≃S)
-- that relates setoids each with its own equivalence relation

infix 4 _≃S_

record _≃S_ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (A : Setoid ℓ₁ ℓ₂) (B : Setoid ℓ₃ ℓ₄) : 
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  constructor equiv
  field
    f : A ⟶ B
    g : B ⟶ A
    α : ∀ {x y} → Setoid._≈_ B x y → Setoid._≈_ B ((f ∘ g) ⟨$⟩ x) y
    β : ∀ {x y} → Setoid._≈_ A x y → Setoid._≈_ A ((g ∘ f) ⟨$⟩ x) y

univalence : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {m n : ℕ} →
  (A ≃ Fin m) → (B ≃ Fin n) → _≃S_ {ℓ} {ℓ} {ℓ ⊔ ℓ'} {ℓ ⊔ ℓ'} (SCPerm m n) (A S≃ B)
univalence {A} {B} {m} {n} A≃Fm B≃Fn =
  equiv {!!} {!!} {!!} {!!}

------------------------------------------------------------------------------
