{-# OPTIONS --without-K --safe #-}

module PiPointed where

open import Data.Empty
open import Data.Unit
open import Data.Sum 
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Singleton

infixr 90 _#_
infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_

------------------------------------------------------------------------------
-- Pi 

data 𝕌 : Set
⟦_⟧ : (A : 𝕌) → Set
data _⟷_ : 𝕌 → 𝕌 → Set
eval : {A B : 𝕌} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧

data 𝕌 where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌

⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

data _⟷_ where
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

eval unite₊l (inj₂ v) = v
eval uniti₊l v  = inj₂ v
eval unite₊r (inj₁ v) = v
eval uniti₊r v  = inj₁ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆l (tt , v) = v
eval uniti⋆l v = (tt , v)
eval unite⋆r (v , tt) = v
eval uniti⋆r v = (v , tt)
eval swap⋆ (v₁ , v₂)          = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbl ()
eval absorbr ()
eval factorzl ()
eval factorzr ()
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval distl (v , inj₁ v₁) = inj₁ (v , v₁)
eval distl (v , inj₂ v₂) = inj₂ (v , v₂)
eval factorl (inj₁ (v , v₁)) = (v , inj₁ v₁)
eval factorl (inj₂ (v , v₂)) = (v , inj₂ v₂)
eval id⟷ v = v
eval (c₁ ⊚ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

------------------------------------------------------------------------------
-- Pointed types and singleton types

data ∙𝕌 : Set where
  _#_ : (t : 𝕌) → (v : ⟦ t ⟧) → ∙𝕌
  _∙⊗_ : ∙𝕌 → ∙𝕌 → ∙𝕌
  _∙⊕l_ : ∙𝕌 → ∙𝕌 → ∙𝕌
  _∙⊕r_ : ∙𝕌 → ∙𝕌 → ∙𝕌
  sing : ∙𝕌 → ∙𝕌

∙⟦_⟧ : ∙𝕌 → Σ[ A ∈ Set ] A 
∙⟦ t # v ⟧ = ⟦ t ⟧ , v
∙⟦ T₁ ∙⊗ T₂ ⟧ with ∙⟦ T₁ ⟧ | ∙⟦ T₂ ⟧ 
... | (t₁ , v₁) | (t₂ , v₂) = (t₁ × t₂) , (v₁ , v₂)
∙⟦ T₁ ∙⊕l T₂ ⟧ with ∙⟦ T₁ ⟧ | ∙⟦ T₂ ⟧ 
... | (t₁ , v₁) | (t₂ , v₂) = (t₁ ⊎ t₂) , inj₁ v₁
∙⟦ T₁ ∙⊕r T₂ ⟧ with ∙⟦ T₁ ⟧ | ∙⟦ T₂ ⟧ 
... | (t₁ , v₁) | (t₂ , v₂) = (t₁ ⊎ t₂) , inj₂ v₂
∙⟦ sing T ⟧ with ∙⟦ T ⟧
... | (t , v) = Singleton t v , (v , refl) 

data _∙⟶_ : ∙𝕌 → ∙𝕌 → Set where
  ∙c :  {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} → (c : t₁ ⟷ t₂) → 
        t₁ # v ∙⟶ t₂ # (eval c v)
  ∙id⟷ : {T : ∙𝕌} → T ∙⟶ T
  _∙⊚_ : {T₁ T₂ T₃ : ∙𝕌} → (T₁ ∙⟶ T₂) → (T₂ ∙⟶ T₃) → (T₁ ∙⟶ T₃)
  -- monad
  return : (T : ∙𝕌) → T ∙⟶ sing T
  join : (T : ∙𝕌) → sing (sing T) ∙⟶ sing T
  unjoin : (T : ∙𝕌) → sing T ∙⟶ sing (sing T)
  ∙sing : {T₁ T₂ : ∙𝕌} → (T₁ ∙⟶ T₂) → (sing T₁ ∙⟶ sing T₂)

∙eval : {T₁ T₂ : ∙𝕌} → (C : T₁ ∙⟶ T₂) →
  let (t₁ , v₁) = ∙⟦ T₁ ⟧
      (t₂ , v₂) = ∙⟦ T₂ ⟧
  in Σ (t₁ → t₂) (λ f → f v₁ ≡ v₂)
∙eval ∙id⟷ = (λ x → x) , refl
∙eval (∙c c) = eval c , refl
∙eval (C₁ ∙⊚ C₂) with ∙eval C₁ | ∙eval C₂
... | (f , p) | (g , q) = (λ x → g (f x)) , trans (cong g p) q
∙eval (return T) with ∙⟦ T ⟧
... | (t , v) = (λ _ → v , refl) , refl
∙eval (join T) with ∙⟦ T ⟧
... | (t , v) = (λ {((.v , refl) , refl) → v , refl}) , refl 
∙eval (unjoin T) with ∙⟦ T ⟧
... | (t , v) = (λ {(w , refl) → (w , refl) , refl}) , refl 
∙eval (∙sing {T₁} {T₂} C) with ∙⟦ T₁ ⟧ | ∙⟦ T₂ ⟧ | ∙eval C
... | t₁ , v₁ | t₂ , .(f v₁) | f , refl = (λ {(x , refl) → f x , refl}) , refl 



------------------------------------------------------------------------------
