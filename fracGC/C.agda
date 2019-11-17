{-# OPTIONS --without-K --safe #-}

module C where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Singleton

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_

------------------------------------------------------------------------------
-- Pi

data 𝕌 : Set
⟦_⟧ : 𝕌 → Σ[ A ∈ Set ] A
data _⟷_ : 𝕌 → 𝕌 → Set

data 𝕌 where
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌
  Singᵤ : 𝕌 → 𝕌
  Recipᵤ : 𝕌 → 𝕌

⟦ 𝟙 ⟧ = ⊤ , tt
⟦ T₁ ×ᵤ T₂ ⟧ = zip _×_ _,_ ⟦ T₁ ⟧ ⟦ T₂ ⟧
⟦ T₁ +ᵤ T₂ ⟧ = zip _⊎_ (λ x _ → inj₁ x) ⟦ T₁ ⟧ ⟦ T₂ ⟧
⟦ Singᵤ T ⟧ = < uncurry Singleton , (λ y → proj₂ y , refl) > ⟦ T ⟧
⟦ Recipᵤ T ⟧ = < uncurry Recip , (λ _ _ → tt) > ⟦ T ⟧

data _⟷_ where
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
  dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
  factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤ t₃)
  id⟷     : {t : 𝕌} → t ⟷ t
  _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)
  -- monad
  return : (T : 𝕌) → T ⟷ Singᵤ T
  join : (T : 𝕌) → Singᵤ (Singᵤ T) ⟷ Singᵤ T
  unjoin : (T : 𝕌) → Singᵤ T ⟷ Singᵤ (Singᵤ T)
  tensorl : (T₁ T₂ : 𝕌) → (Singᵤ T₁ ×ᵤ T₂) ⟷ Singᵤ (T₁ ×ᵤ T₂)
  tensorr : (T₁ T₂ : 𝕌) → (T₁ ×ᵤ Singᵤ T₂) ⟷ Singᵤ (T₁ ×ᵤ T₂)
  tensor : (T₁ T₂ : 𝕌) → (Singᵤ T₁ ×ᵤ Singᵤ T₂) ⟷ Singᵤ (T₁ ×ᵤ T₂)
  untensor : (T₁ T₂ : 𝕌) → Singᵤ (T₁ ×ᵤ T₂) ⟷ (Singᵤ T₁ ×ᵤ Singᵤ T₂)
  plusl : (T₁ T₂ : 𝕌) → (Singᵤ T₁ +ᵤ T₂) ⟷ Singᵤ (T₁ +ᵤ T₂)
  -- comonad
  extract : (T : 𝕌) → Singᵤ T ⟷ T
  cojoin : (T : 𝕌) → Singᵤ T ⟷ Singᵤ (Singᵤ T)
  counjoin : (T : 𝕌) → Singᵤ (Singᵤ T) ⟷ Singᵤ T
  cotensorl : (T₁ T₂ : 𝕌) → Singᵤ (T₁ ×ᵤ T₂) ⟷ (Singᵤ T₁ ×ᵤ T₂)
  cotensorr : (T₁ T₂ : 𝕌) → Singᵤ (T₁ ×ᵤ T₂) ⟷ (T₁ ×ᵤ Singᵤ T₂)
  coplusl : (T₁ T₂ : 𝕌) → Singᵤ (T₁ +ᵤ T₂) ⟷ (Singᵤ T₁ +ᵤ T₂)
  -- both?
  Singᵤ : (T₁ T₂ : 𝕌) → (T₁ ⟷ T₂) → (Singᵤ T₁ ⟷ Singᵤ T₂)
  -- eta/epsilon
  η : (T : 𝕌) → 𝟙 ⟷ (Singᵤ T ×ᵤ Recipᵤ T)
  ε : (T : 𝕌) → (Singᵤ T ×ᵤ Recipᵤ T) ⟷ 𝟙

