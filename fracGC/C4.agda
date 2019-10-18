{-# OPTIONS --without-K #-}

module C4 where
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Universe
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Nullary
open import Level

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
⟦ t₁ ⊞ t₂ ⟧● with ⟦ t₁ ⟧● | ⟦ t₂ ⟧●  -- can't interp swap anymore; wedge sum ? 
... | (S₁ , v₁) | (S₂ , v₂) = (S₁ ⊎ S₂) , inj₁ v₁
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

interp : {T₁ T₂ : 𝕌●} → (T₁ ⬌ T₂) →
  let S₁ , v₁ = ⟦ T₁ ⟧●
      S₂ , v₂ = ⟦ T₂ ⟧●
  in Σ[ w₁ ∈ S₁ ] v₁ ≡ w₁ → Σ[ w₂ ∈ S₂ ] v₂ ≡ w₂
interp swap₊ (inj₁ v , refl) = {!!} 
interp swap₊ (inj₂ v , p) = inj₁ v , {!!}
interp assocl₊ V = {!!}
interp assocr₊ V = {!!}
interp unite⋆l V = {!!}
interp uniti⋆l V = {!!}
interp unite⋆r V = {!!}
interp uniti⋆r V = {!!}
interp swap⋆ V = {!!}
interp assocl⋆ V = {!!}
interp assocr⋆ V = {!!}
interp dist V = {!!}
interp factor V = {!!}
interp distl V = {!!}
interp factorl V = {!!}
interp id⬌ V = V
interp (c₁ ○ c₂) V = {!!}
interp (c₁ ➕ c₂) V = {!!}
interp (c₁ ✖ c₂) V = {!!}
interp (η {T}) (tt , refl) with ⟦ T ⟧●
... | (S , v) = (v , λ { ( w , w≡v ) → tt}), {!!} 
interp ε ((v , f) , p) = f (v , {!!}) , {!!} 

