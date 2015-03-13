{-# OPTIONS --without-K #-}

-- Borrowed from OldUnivalence/Equivalences.agda, without HoTT
module Equiv where

open import Level
open import Function
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality

infix 4 _∼_
infix 4 _≃_

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

refl∼ : {A B : Set} {f : A → B} → (f ∼ f)
refl∼ {A} {B} {f} x = refl

sym∼ : {A B : Set} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = sym (H x) 

trans∼ : {A B : Set} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = trans (H x)  (G x)

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {A = A} id
idqinv = record {
           g = id ;
           α = λ b → refl ; 
           β = λ a → refl
         }
         
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) qinv

id≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
id≃ = (id , idqinv)

sym≃ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A ≃ B) → B ≃ A
sym≃ (A→B , equiv) = e.g , mkqinv A→B e.β e.α
  where module e = qinv equiv

trans≃ : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
trans≃ (f , feq) (g , geq) = (g ∘ f) , (mkqinv inv α' β')
  where
    module fm = qinv feq
    module gm = qinv geq
    inv = fm.g ∘ gm.g
    α' = λ x → trans (cong g (fm.α (gm.g x))) (gm.α x)
    β' = λ x → trans (cong fm.g (gm.β (f x))) (fm.β x)

_⋆_ : {A B : Set} → (A ≃ B) → (x : A) → B
(f , _) ⋆ x = f x 

-- there-and-back is identity
p∘!p≡id : {A B : Set} {p : A ≃ B} → (_⋆_ (trans≃ p (sym≃ p))) ∼ (_⋆_ id≃)
p∘!p≡id {p = f , mkqinv q _ β} = β

-- equivalences are injective

inj≃ : {A B : Set} → (eq : A ≃ B) → (x y : A) → (eq ⋆ x ≡ eq ⋆ y → x ≡ y)
inj≃ (f , mkqinv g α β) x y p = trans (sym (β x)) (trans (cong g p) (β y))

bad-path : {A B : Set} → (a : A) → (b : B) → inj₁ a ≡ inj₂ b → ⊥
bad-path x y ()

-- ⊎ injective too
inj₁≡ : {A B : Set} → {a b : A} → inj₁ {A = A} {B} a ≡ inj₁ b → a ≡ b
inj₁≡ refl = refl

inj₂≡ : {A B : Set} → {a b : B} → inj₂ {A = A} {B} a ≡ inj₂ b → a ≡ b
inj₂≡ refl = refl
