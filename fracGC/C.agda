{-# OPTIONS --without-K --safe #-}

module C where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Singleton

infixr 70 _×ᵤ_
infixr 60 _+ᵤₗ_
infixr 60 _+ᵤᵣ_
infixr 50 _⊚_

------------------------------------------------------------------------------
-- Pi

data 𝕌 : Set
⟦_⟧ : 𝕌 → Σ[ A ∈ Set ] A
data _⟷_ : 𝕌 → 𝕌 → Set

data 𝕌 where
  𝟙       : 𝕌
  _+ᵤₗ_    : 𝕌 → 𝕌 → 𝕌
  _+ᵤᵣ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌
  Singᵤ : 𝕌 → 𝕌
  Recipᵤ : 𝕌 → 𝕌

⟦ 𝟙 ⟧ = ⊤ , tt
⟦ T₁ ×ᵤ T₂ ⟧ = zip _×_ _,_ ⟦ T₁ ⟧ ⟦ T₂ ⟧
⟦ T₁ +ᵤₗ T₂ ⟧ = zip _⊎_ (λ x _ → inj₁ x) ⟦ T₁ ⟧ ⟦ T₂ ⟧
⟦ T₁ +ᵤᵣ T₂ ⟧ = zip _⊎_ (λ _ y → inj₂ y) ⟦ T₁ ⟧ ⟦ T₂ ⟧
⟦ Singᵤ T ⟧ = < uncurry Singleton , (λ y → proj₂ y , refl) > ⟦ T ⟧
⟦ Recipᵤ T ⟧ = < uncurry Recip , (λ _ _ → tt) > ⟦ T ⟧

data _⟷_ where
  swap₊₁   : {t₁ t₂ : 𝕌} → t₁ +ᵤₗ t₂ ⟷ t₂ +ᵤᵣ t₁
  swap₊₂   : {t₁ t₂ : 𝕌} → t₁ +ᵤᵣ t₂ ⟷ t₂ +ᵤₗ t₁
  assocl₊₁ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤₗ (t₂ +ᵤₗ t₃) ⟷ (t₁ +ᵤₗ t₂) +ᵤₗ t₃
  assocl₊₂ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤₗ (t₂ +ᵤᵣ t₃) ⟷ (t₁ +ᵤₗ t₂) +ᵤₗ t₃
  assocl₊₃ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤᵣ (t₂ +ᵤₗ t₃) ⟷ (t₁ +ᵤᵣ t₂) +ᵤₗ t₃
  assocl₊₄ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤᵣ (t₂ +ᵤᵣ t₃) ⟷ (t₁ +ᵤₗ t₂) +ᵤᵣ t₃
  assocl₊₅ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤᵣ (t₂ +ᵤᵣ t₃) ⟷ (t₁ +ᵤᵣ t₂) +ᵤᵣ t₃
  assocr₊₁ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤₗ t₂) +ᵤₗ t₃ ⟷ t₁ +ᵤₗ (t₂ +ᵤᵣ t₃)
  assocr₊₂ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤₗ t₂) +ᵤₗ t₃ ⟷ t₁ +ᵤₗ (t₂ +ᵤₗ t₃)
  assocr₊₃ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤᵣ t₂) +ᵤₗ t₃ ⟷ t₁ +ᵤᵣ (t₂ +ᵤₗ t₃)
  assocr₊₄ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤₗ t₂) +ᵤᵣ t₃ ⟷ t₁ +ᵤᵣ (t₂ +ᵤᵣ t₃)
  assocr₊₅ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤᵣ t₂) +ᵤᵣ t₃ ⟷ t₁ +ᵤᵣ (t₂ +ᵤᵣ t₃)
  unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ⟷ t
  uniti⋆l : {t : 𝕌} → t ⟷ 𝟙 ×ᵤ t
  unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ⟷ t
  uniti⋆r : {t : 𝕌} → t ⟷ t ×ᵤ 𝟙
  swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ⟷ t₂ ×ᵤ t₁
  assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  dist₁    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤₗ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤₗ (t₂ ×ᵤ t₃)
  dist₂    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤᵣ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤᵣ (t₂ ×ᵤ t₃)
  factor₁  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤₗ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤₗ t₂) ×ᵤ t₃
  factor₂  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤᵣ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤᵣ t₂) ×ᵤ t₃
  distl₁   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤₗ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤₗ (t₁ ×ᵤ t₃)
  distl₂   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤᵣ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤᵣ (t₁ ×ᵤ t₃)
  factorl₁ : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤₗ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤₗ t₃)
  factorl₂ : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤᵣ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤᵣ t₃)
  id⟷     : {t : 𝕌} → t ⟷ t
  _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕₁_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤₗ t₂ ⟷ t₃ +ᵤₗ t₄)
  _⊕₂_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤᵣ t₂ ⟷ t₃ +ᵤᵣ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)
  -- monad
  return : (T : 𝕌) → T ⟷ Singᵤ T
  join : (T : 𝕌) → Singᵤ (Singᵤ T) ⟷ Singᵤ T
  unjoin : (T : 𝕌) → Singᵤ T ⟷ Singᵤ (Singᵤ T)
  tensorl : (T₁ T₂ : 𝕌) → (Singᵤ T₁ ×ᵤ T₂) ⟷ Singᵤ (T₁ ×ᵤ T₂)
  tensorr : (T₁ T₂ : 𝕌) → (T₁ ×ᵤ Singᵤ T₂) ⟷ Singᵤ (T₁ ×ᵤ T₂)
  tensor : (T₁ T₂ : 𝕌) → (Singᵤ T₁ ×ᵤ Singᵤ T₂) ⟷ Singᵤ (T₁ ×ᵤ T₂)
  untensor : (T₁ T₂ : 𝕌) → Singᵤ (T₁ ×ᵤ T₂) ⟷ (Singᵤ T₁ ×ᵤ Singᵤ T₂)
  plusl : (T₁ T₂ : 𝕌) → (Singᵤ T₁ +ᵤₗ T₂) ⟷ Singᵤ (T₁ +ᵤₗ T₂)
  plusr : (T₁ T₂ : 𝕌) → (T₁ +ᵤᵣ Singᵤ T₂) ⟷ Singᵤ (T₁ +ᵤᵣ T₂)
  -- comonad
  extract : (T : 𝕌) → Singᵤ T ⟷ T
  cojoin : (T : 𝕌) → Singᵤ T ⟷ Singᵤ (Singᵤ T)
  counjoin : (T : 𝕌) → Singᵤ (Singᵤ T) ⟷ Singᵤ T
  cotensorl : (T₁ T₂ : 𝕌) → Singᵤ (T₁ ×ᵤ T₂) ⟷ (Singᵤ T₁ ×ᵤ T₂)
  cotensorr : (T₁ T₂ : 𝕌) → Singᵤ (T₁ ×ᵤ T₂) ⟷ (T₁ ×ᵤ Singᵤ T₂)
  coplusl : (T₁ T₂ : 𝕌) → Singᵤ (T₁ +ᵤₗ T₂) ⟷ (Singᵤ T₁ +ᵤₗ T₂)
  coplusr : (T₁ T₂ : 𝕌) → Singᵤ (T₁ +ᵤᵣ T₂) ⟷ (T₁ +ᵤᵣ Singᵤ T₂)
  -- both?
  Singᵤ : (T₁ T₂ : 𝕌) → (T₁ ⟷ T₂) → (Singᵤ T₁ ⟷ Singᵤ T₂)
  -- eta/epsilon
  η : (T : 𝕌) → 𝟙 ⟷ (Singᵤ T ×ᵤ Recipᵤ T)
  ε : (T : 𝕌) → (Singᵤ T ×ᵤ Recipᵤ T) ⟷ 𝟙

!_ : {t₁ t₂ : 𝕌} → t₁ ⟷ t₂ → t₂ ⟷ t₁
! swap₊₁ = swap₊₂
! swap₊₂ = swap₊₁
! assocl₊₁ = assocr₊₂
! assocl₊₂ = assocr₊₁
! assocl₊₃ = assocr₊₃
! assocl₊₄ = assocr₊₄
! assocl₊₅ = assocr₊₅
! assocr₊₁ = assocl₊₂
! assocr₊₂ = assocl₊₁
! assocr₊₃ = assocl₊₃
! assocr₊₄ = assocl₊₄
! assocr₊₅ = assocl₊₅
! unite⋆l = uniti⋆l
! uniti⋆l = unite⋆l
! unite⋆r = uniti⋆r
! uniti⋆r = unite⋆r
! swap⋆ = swap⋆
! assocl⋆ = assocr⋆
! assocr⋆ = assocl⋆
! dist₁ = factor₁
! dist₂ = factor₂
! factor₁ = dist₁
! factor₂ = dist₂
! distl₁ = factorl₁
! distl₂ = factorl₂
! factorl₁ = distl₁
! factorl₂ = distl₂
! id⟷ = id⟷
! (c ⊚ c₁) = (! c₁) ⊚ (! c)
! (c ⊕₁ c₁) = (! c) ⊕₁ (! c₁)
! (c ⊕₂ c₁) = (! c) ⊕₂ (! c₁)
! (c ⊗ c₁) = (! c) ⊗ (! c₁)
! return T = extract T
! join T = return (Singᵤ T)
! unjoin T = join T
! tensorl T₁ T₂ = cotensorl T₁ T₂
! tensorr T₁ T₂ = cotensorr T₁ T₂
! tensor T₁ T₂ = untensor T₁ T₂
! untensor T₁ T₂ = tensor T₁ T₂
! plusl T₁ T₂ = coplusl T₁ T₂
! plusr T₁ T₂ = coplusr T₁ T₂
! extract T = return T
! cojoin T = join T
! counjoin T = return (Singᵤ T)
! cotensorl T₁ T₂ = tensorl T₁ T₂
! cotensorr T₁ T₂ = tensorr T₁ T₂
! coplusl T₁ T₂ = plusl T₁ T₂
! coplusr T₁ T₂ = plusr T₁ T₂
! Singᵤ T₁ T₂ c = Singᵤ T₂ T₁ (! c)
! η T = ε T
! ε T = η T
