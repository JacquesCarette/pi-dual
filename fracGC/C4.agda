{-# OPTIONS --without-K #-}

module C4 where
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Nullary

infix  70 _⊠_
infix  60 _⊞_
infix  40 _⬌_
infixr 50 _○_

-----------------------------------------------------------------------------

data 𝕌 : Set      -- types
data 𝕌● : Set     -- pointed types
⟦_⟧ : 𝕌 → Set
⟦_⟧● : 𝕌● → Σ[ A ∈ Set ] A

data 𝕌 where
    𝟘 : 𝕌
    𝟙 : 𝕌
    _+ᵤ_ : 𝕌 → 𝕌 → 𝕌
    _×ᵤ_ : 𝕌 → 𝕌 → 𝕌

data 𝕌● where
    _●_ : (t : 𝕌) → ⟦ t ⟧ → 𝕌●
    _⊞_ : 𝕌● → 𝕌● → 𝕌● 
    _⊠_ : 𝕌● → 𝕌● → 𝕌● 
    𝟙/_ : 𝕌● → 𝕌● 

⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

⟦ t ● v ⟧● = ⟦ t ⟧ , v
⟦ t₁ ⊞ t₂ ⟧● with ⟦ t₁ ⟧● | ⟦ t₂ ⟧●  -- wedge sum ? 
... | (S₁ , v₁) | (S₂ , v₂) = (S₁ ⊎ S₂) , {!!} 
⟦ t₁ ⊠ t₂ ⟧● with ⟦ t₁ ⟧● | ⟦ t₂ ⟧●  -- smash product ? 
... | (S₁ , v₁) | (S₂ , v₂) = (S₁ × S₂) , (v₁ , v₂)
⟦ 𝟙/ T ⟧● with ⟦ T ⟧●
... | S , v = (Σ[ x ∈ S ] x ≡ v → ⊤) , λ { (w , w≡v) → tt }

-----------------------------------------------------------------------------

data _⬌_ : 𝕌● → 𝕌● → Set where
  swap₊   : {T₁ T₂ : 𝕌●} → T₁ ⊞ T₂ ⬌ T₂ ⊞ T₁
  assocl₊ : {T₁ T₂ T₃ : 𝕌●} → T₁ ⊞ (T₂ ⊞ T₃) ⬌ (T₁ ⊞ T₂) ⊞ T₃
  assocr₊ : {T₁ T₂ T₃ : 𝕌●} → (T₁ ⊞ T₂) ⊞ T₃ ⬌ T₁ ⊞ (T₂ ⊞ T₃)
  unite⋆l : {T : 𝕌●} → (𝟙 ● tt) ⊠ T ⬌ T
  uniti⋆l : {T : 𝕌●} → T ⬌ (𝟙 ● tt) ⊠ T
  unite⋆r : {T : 𝕌●} → T ⊠ (𝟙 ● tt) ⬌ T
  uniti⋆r : {T : 𝕌●} → T ⬌ T ⊠ (𝟙 ● tt)
  swap⋆   : {T₁ T₂ : 𝕌●} → T₁ ⊠ T₂ ⬌ T₂ ⊠ T₁
  assocl⋆ : {T₁ T₂ T₃ : 𝕌●} → T₁ ⊠ (T₂ ⊠ T₃) ⬌ (T₁ ⊠ T₂) ⊠ T₃
  assocr⋆ : {T₁ T₂ T₃ : 𝕌●} → (T₁ ⊠ T₂) ⊠ T₃ ⬌ T₁ ⊠ (T₂ ⊠ T₃)
  dist    : {T₁ T₂ T₃ : 𝕌●} → (T₁ ⊞ T₂) ⊠ T₃ ⬌ (T₁ ⊠ T₃) ⊞ (T₂ ⊠ T₃)
  factor  : {T₁ T₂ T₃ : 𝕌●} → (T₁ ⊠ T₃) ⊞ (T₂ ⊠ T₃) ⬌ (T₁ ⊞ T₂) ⊠ T₃
  distl   : {T₁ T₂ T₃ : 𝕌●} → T₁ ⊠ (T₂ ⊞ T₃) ⬌ (T₁ ⊠ T₂) ⊞ (T₁ ⊠ T₃)
  factorl : {T₁ T₂ T₃ : 𝕌● } → (T₁ ⊠ T₂) ⊞ (T₁ ⊠ T₃) ⬌ T₁ ⊠ (T₂ ⊞ T₃)
  id⬌  : {T : 𝕌●} → T ⬌ T
  _○_ : {T₁ T₂ T₃ : 𝕌●} → (T₁ ⬌ T₂) → (T₂ ⬌ T₃) → (T₁ ⬌ T₃)
  _➕_ : {T₁ T₂ T₃ T₄ : 𝕌●} → (T₁ ⬌ T₃) → (T₂ ⬌ T₄) → (T₁ ⊞ T₂ ⬌ T₃ ⊞ T₄)
  _✖_ : {T₁ T₂ T₃ T₄ : 𝕌●} → (T₁ ⬌ T₃) → (T₂ ⬌ T₄) → (T₁ ⊠ T₂ ⬌ T₃ ⊠ T₄)
  -- new combinators
  η : {T : 𝕌●} → (𝟙 ● tt) ⬌ (T ⊠ (𝟙/ T))
  ε : {T : 𝕌●} → (T ⊠ (𝟙/ T)) ⬌ (𝟙 ● tt)

{--
interp : {T₁ T₂ : 𝕌●} → (T₁ ⬌ T₂) → ⟦ T₁ ⟧● → ⟦ T₂ ⟧● -- Σ[ A ∈ Set ] A
interp swap₊ (inj₁ v) = inj₂ v
interp swap₊ (inj₂ v) = inj₁ v
interp assocl₊ (inj₁ v) = inj₁ (inj₁ v)
interp assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
interp assocl₊ (inj₂ (inj₂ v)) = inj₂ v
interp assocr₊ (inj₁ (inj₁ v)) = inj₁ v
interp assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
interp assocr₊ (inj₂ v) = inj₂ (inj₂ v)
interp unite⋆l v = proj₂ v
interp uniti⋆l v = tt , v
interp unite⋆r v = proj₁ v
interp uniti⋆r v = v , tt
interp swap⋆ (v₁ , v₂) = v₂ , v₁
interp assocl⋆ (v₁ , v₂ , v₃) = (v₁ , v₂) , v₃
interp assocr⋆ ((v₁ , v₂) , v₃) = v₁ , v₂ , v₃
interp dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
interp dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
interp factor (inj₁ (v₁ , v₃)) = inj₁ v₁ , v₃
interp factor (inj₂ (v₂ , v₃)) = inj₂ v₂ , v₃
interp distl (v₁ , inj₁ v₂) = inj₁ (v₁ , v₂)
interp distl (v₁ , inj₂ v₃) = inj₂ (v₁ , v₃)
interp factorl (inj₁ (v₁ , v₂)) = v₁ , inj₁ v₂
interp factorl (inj₂ (v₁ , v₃)) = v₁ , inj₂ v₃
interp id↔ v = v
interp (c₁ ○ c₂) v = interp c₂ (interp c₁ v)
interp (c₁ ➕ c₂) (inj₁ v) = inj₁ (interp c₁ v)
interp (c₁ ➕ c₂) (inj₂ v) = inj₂ (interp c₂ v)
interp (c₁ ✖ c₂) (v₁ , v₂) = interp c₁ v₁ , interp c₂ v₂
interp (η {T}) tt = ? 
interp ε (v , rv) = ? 
--}
