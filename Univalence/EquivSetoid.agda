{-# OPTIONS --without-K #-}

-- Borrowed from OldUnivalence/Equivalences.agda, without HoTT
module EquivSetoid where

open import Level
open import Function
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
-- open import Relation.Binary.PropositionalEquality
open import Relation.Binary

open import Function.Equality renaming (_∘_ to _⊚_; id to id⊚)
-- infix 4 _≃_

open Setoid

record _≃_ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (A : Setoid ℓ₁ ℓ₂) (B : Setoid ℓ₃ ℓ₄)  : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  constructor equiv

  A⇨A : Setoid (ℓ₂ ⊔ ℓ₁) (ℓ₂ ⊔ ℓ₁)
  A⇨A = A ⇨ A

  _∼₁_ = _≈_ (B ⇨ B)    
  _∼₂_ = _≈_ A⇨A

  field
    f : A ⟶ B
    g : B ⟶ A
    α : (f ⊚ g) ∼₁ id⊚
    β : (g ⊚ f) ∼₂ id⊚

id≃ : ∀ {ℓ₁ ℓ₂} {A : Setoid ℓ₁ ℓ₂} → A ≃ A
id≃ {A = A} = equiv id⊚ id⊚ id id 

sym≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} → (A ≃ B) → B ≃ A
sym≃ eq = equiv e.g e.f e.β e.α
  where module e = _≃_ eq

{-
trans≃ : {A : Setoid _ _} {B : Setoid _ _} {C : Setoid _ _} → A ≃ B → B ≃ C → A ≃ C
trans≃ (f , feq) (g , geq) = (g ∘ f) , (mkqinv inv α' β')
  where
    module fm = qinv feq
    module gm = qinv geq
    inv = fm.g ∘ gm.g
    α' = λ x → trans (cong g (fm.α (gm.g x))) (gm.α x)
    β' = λ x → trans (cong fm.g (gm.β (f x))) (fm.β x)

-- equivalences are injective

_⋆_ : {A B : Set} → (A ≃ B) → (x : A) → B
(f , _) ⋆ x = f x 

inj≃ : {A B : Set} → (eq : A ≃ B) → (x y : A) → (eq ⋆ x ≡ eq ⋆ y → x ≡ y)
inj≃ (f , mkqinv g α β) x y p = trans (sym (β x)) (trans (cong g p) (β y))

bad-path : {A B : Set} → (a : A) → (b : B) → inj₁ a ≡ inj₂ b → ⊥
bad-path x y ()

-- ⊎ injective too
inj₁≡ : {A B : Set} → {a b : A} → inj₁ {A = A} {B} a ≡ inj₁ b → a ≡ b
inj₁≡ refl = refl

inj₂≡ : {A B : Set} → {a b : B} → inj₂ {A = A} {B} a ≡ inj₂ b → a ≡ b
inj₂≡ refl = refl

-- when are two equivalences actually equal? We need funext for that, but we do
-- have it when it matters!
≃≡ : {A B : Set} → (funextA : {D : A → Set} {f g : (y : A) → D y} → (∀ x → f x ≡ g x) → f ≡ g) →
                               (funextB : {D : B → Set} {f g : (y : B) → D y} → (∀ x → f x ≡ g x) → f ≡ g) → 
  (eq₁ eq₂ : A ≃ B) → 
  (∀ x → eq₁ ⋆ x ≡ eq₂ ⋆ x) → (∀ x → (sym≃ eq₁) ⋆ x ≡ (sym≃ eq₂) ⋆ x) → eq₁ ≡ eq₂
≃≡ feA feB (f₀ , mkqinv g₀ α₀ β₀) (f₁ , mkqinv g₁ α₁ β₁) f-ext g-ext with feA f-ext | feB g-ext 
≃≡ {A} {B} feA feB (f₀ , mkqinv g₀ α₀ β₀) (.f₀ , mkqinv .g₀ α₁ β₁) f-ext g-ext | refl | refl with feB (λ x → proof-irrelevance (α₀ x) (α₁ x)) | feA (λ x → proof-irrelevance (β₀ x) (β₁ x))
≃≡ feA feB (f₀ , mkqinv g₀ α₀ β₀) (.f₀ , mkqinv .g₀ .α₀ .β₀) f-ext g-ext | refl | refl | refl | refl = refl

-}
