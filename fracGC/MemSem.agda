{-# OPTIONS --without-K --safe #-}

module MemSem where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject+; raise)
open import Data.Vec
open import Data.Vec.Properties
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_

data 𝕌 : Set where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌

⟦_⟧ : (A : 𝕌) → Set
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

data _⟷_ : 𝕌 → 𝕌 → Set where
  unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ⟷ t
  uniti₊l : {t : 𝕌} → t ⟷ 𝟘 +ᵤ t
  unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ⟷ t
  uniti₊r : {t : 𝕌} → t ⟷ t +ᵤ 𝟘
  swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ⟷ t₂ +ᵤ t₁
  assocl₊ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ +ᵤ t₂) +ᵤ t₃
  assocr₊ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ⟷ t₁ +ᵤ (t₂ +ᵤ t₃)
  unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ⟷ t
  uniti⋆l : {t : 𝕌} → t ⟷ 𝟙 ×ᵤ t
  unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ⟷ t
  uniti⋆r : {t : 𝕌} → t ⟷ t ×ᵤ 𝟙
  swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ⟷ t₂ ×ᵤ t₁
  assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  absorbr : {t : 𝕌} → 𝟘 ×ᵤ t ⟷ 𝟘
  absorbl : {t : 𝕌} → t ×ᵤ 𝟘 ⟷ 𝟘
  factorzr : {t : 𝕌} → 𝟘 ⟷ t ×ᵤ 𝟘
  factorzl : {t : 𝕌} → 𝟘 ⟷ 𝟘 ×ᵤ t
  dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
  factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤ t₃)
  id⟷     : {t : 𝕌} → t ⟷ t
  _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)

∣_∣ : (A : 𝕌) → ℕ
∣ 𝟘 ∣ = 0
∣ 𝟙 ∣ = 1
∣ A₁ +ᵤ A₂ ∣ = ∣ A₁ ∣ + ∣ A₂ ∣
∣ A₁ ×ᵤ A₂ ∣ = ∣ A₁ ∣ * ∣ A₂ ∣

Enum : (A : 𝕌) → Vec ⟦ A ⟧ ∣ A ∣
Enum 𝟘 = []
Enum 𝟙 = tt ∷ []
Enum (A₁ +ᵤ A₂) = map inj₁ (Enum A₁) ++ map inj₂ (Enum A₂)
Enum (A₁ ×ᵤ A₂) = concat (map (λ a₁ → map (a₁ ,_) (Enum A₂)) (Enum A₁))

Find : {A : 𝕌} (x : ⟦ A ⟧) → Σ[ i ∈ Fin ∣ A ∣ ] (x ≡ lookup (Enum A) i)
Find {𝟘} ()
Find {𝟙} tt = zero , refl
Find {A₁ +ᵤ A₂} (inj₁ x) with Find x
Find {A₁ +ᵤ A₂} (inj₁ .(lookup (Enum A₁) i)) | i , refl = inject+ ∣ A₂ ∣ i
                                                        , sym (trans (lookup-++ˡ (map inj₁ (Enum A₁)) (map inj₂ (Enum A₂)) i)
                                                                     (lookup-map i inj₁ (Enum A₁)))
Find {A₁ +ᵤ A₂} (inj₂ y) with Find y
Find {A₁ +ᵤ A₂} (inj₂ .(lookup (Enum A₂) i)) | i , refl = raise ∣ A₁ ∣ i
                                                        , sym (trans (lookup-++ʳ (map inj₁ (Enum A₁)) (map inj₂ (Enum A₂)) i)
                                                                     (lookup-map i inj₂ (Enum A₂)))
Find {A₁ ×ᵤ A₂} (x , y) with Find x
... | i , p = {!!}

data State : Set where
  _∥_∥_ : {A B : 𝕌} → A ⟷ B → Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State

data _⤇_ : State → State → Set where
  unite₊l⤇ : {t : 𝕌} {i : Fin ∣ 𝟘 +ᵤ t ∣}
           → (unite₊l ∥ Enum (𝟘 +ᵤ t) ∥ i) ⤇ (id⟷ ∥ Enum t ∥ i)
  uniti₊l⤇ : {t : 𝕌} {i : Fin ∣ t ∣}
           → (uniti₊l ∥ Enum t ∥ i) ⤇ (id⟷ ∥ Enum (𝟘 +ᵤ t) ∥ i)
  unite₊r⤇ : {t : 𝕌} {i : Fin ∣ t +ᵤ 𝟘 ∣}
           → (unite₊r ∥ Enum (t +ᵤ 𝟘) ∥ i) ⤇ (id⟷ ∥ Enum t ∥ {!!})
