{-# OPTIONS --without-K --safe #-}

module PiPointed where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality

open import Singleton
open import PlainPi

infixr 90 _#_

------------------------------------------------------------------------------
-- Pointed types and singleton types

data ∙𝕌 : Set where
  _#_ : (t : 𝕌) → (v : ⟦ t ⟧) → ∙𝕌
  _∙×ᵤ_ : ∙𝕌 → ∙𝕌 → ∙𝕌
  _∙+ᵤl_ : ∙𝕌 → ∙𝕌 → ∙𝕌
  _∙+ᵤr_ : ∙𝕌 → ∙𝕌 → ∙𝕌
  Singᵤ : ∙𝕌 → ∙𝕌

∙⟦_⟧ : ∙𝕌 → Σ[ A ∈ Set ] A
∙⟦ t # v ⟧ = ⟦ t ⟧ , v
∙⟦ T₁ ∙×ᵤ T₂ ⟧ = zip _×_ _,_ ∙⟦ T₁ ⟧ ∙⟦ T₂ ⟧
∙⟦ T₁ ∙+ᵤl T₂ ⟧ = zip _⊎_ (λ x _ → inj₁ x) ∙⟦ T₁ ⟧ ∙⟦ T₂ ⟧
∙⟦ T₁ ∙+ᵤr T₂ ⟧ = zip _⊎_ (λ _ y → inj₂ y) ∙⟦ T₁ ⟧ ∙⟦ T₂ ⟧
∙⟦ Singᵤ T ⟧ = < uncurry Singleton , (λ y → proj₂ y , refl) > ∙⟦ T ⟧

data _∙⟶_ : ∙𝕌 → ∙𝕌 → Set where
  ∙c :  {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} → (c : t₁ ⟷ t₂) →
        t₁ # v ∙⟶ t₂ # (eval c v)
  ∙id⟷ : {T : ∙𝕌} → T ∙⟶ T
  _∙⊚_ : {T₁ T₂ T₃ : ∙𝕌} → (T₁ ∙⟶ T₂) → (T₂ ∙⟶ T₃) → (T₁ ∙⟶ T₃)
  ∙Singᵤ : (T₁ T₂ : ∙𝕌) → (T₁ ∙⟶ T₂) → (Singᵤ T₁ ∙⟶ Singᵤ T₂)
  -- monad
  return : (T : ∙𝕌) → T ∙⟶ Singᵤ T
  join : (T : ∙𝕌) → Singᵤ (Singᵤ T) ∙⟶ Singᵤ T
  tensorl : (T₁ T₂ : ∙𝕌) → (Singᵤ T₁ ∙×ᵤ T₂) ∙⟶ Singᵤ (T₁ ∙×ᵤ T₂)
  tensorr : (T₁ T₂ : ∙𝕌) → (T₁ ∙×ᵤ Singᵤ T₂) ∙⟶ Singᵤ (T₁ ∙×ᵤ T₂)
  tensor : (T₁ T₂ : ∙𝕌) → (Singᵤ T₁ ∙×ᵤ Singᵤ T₂) ∙⟶ Singᵤ (T₁ ∙×ᵤ T₂)
  untensor : (T₁ T₂ : ∙𝕌) → Singᵤ (T₁ ∙×ᵤ T₂) ∙⟶ (Singᵤ T₁ ∙×ᵤ Singᵤ T₂)
  plusl : (T₁ T₂ : ∙𝕌) → (Singᵤ T₁ ∙+ᵤl T₂) ∙⟶ Singᵤ (T₁ ∙+ᵤl T₂)
  plusr : (T₁ T₂ : ∙𝕌) → (T₁ ∙+ᵤr Singᵤ T₂) ∙⟶ Singᵤ (T₁ ∙+ᵤr T₂)
  --    plus : (T₁ T₂ : ∙𝕌) → (Singᵤ T₁ ∙+ᵤl Singᵤ T₂) ∙⟶ Singᵤ (T₁ ∙+ᵤl T₂)  -- lobsided, feels wrong
  -- comonad
  extract : (T : ∙𝕌) → Singᵤ T ∙⟶ T
  duplicate : (T : ∙𝕌) → Singᵤ T ∙⟶ Singᵤ (Singᵤ T)
  cotensorl : (T₁ T₂ : ∙𝕌) → Singᵤ (T₁ ∙×ᵤ T₂) ∙⟶ (Singᵤ T₁ ∙×ᵤ T₂)
  cotensorr : (T₁ T₂ : ∙𝕌) → Singᵤ (T₁ ∙×ᵤ T₂) ∙⟶ (T₁ ∙×ᵤ Singᵤ T₂)
  coplusl : (T₁ T₂ : ∙𝕌) → Singᵤ (T₁ ∙+ᵤl T₂) ∙⟶ (Singᵤ T₁ ∙+ᵤl T₂)
  coplusr : (T₁ T₂ : ∙𝕌) → Singᵤ (T₁ ∙+ᵤr T₂) ∙⟶ (T₁ ∙+ᵤr Singᵤ T₂)

∙eval : {T₁ T₂ : ∙𝕌} → (C : T₁ ∙⟶ T₂) →
  let (t₁ , v₁) = ∙⟦ T₁ ⟧
      (t₂ , v₂) = ∙⟦ T₂ ⟧
  in Σ (t₁ → t₂) (λ f → f v₁ ≡ v₂)
∙eval ∙id⟷ = (λ x → x) , refl
∙eval (∙c c) = eval c , refl
∙eval (C₁ ∙⊚ C₂) with ∙eval C₁ | ∙eval C₂
... | (f , p) | (g , q) = (λ x → g (f x)) , trans (cong g p) q
∙eval (∙Singᵤ T₁ T₂ C) with ∙⟦ T₁ ⟧ | ∙⟦ T₂ ⟧ | ∙eval C
... | t₁ , v₁ | t₂ , .(f v₁) | f , refl = (λ {(x , refl) → f x , refl}) , refl
∙eval (return T) = (λ _ → proj₂ ∙⟦ T ⟧ , refl) , refl
∙eval (join T) = (λ { (._ , refl) → (proj₂ ∙⟦ T ⟧) , refl} ) , refl
∙eval (tensorl T₁ T₂) = (λ {_ → (proj₂ ∙⟦ T₁ ⟧ , proj₂ ∙⟦ T₂ ⟧) , refl}) , refl
∙eval (tensorr T₁ T₂) = (λ {_ → (proj₂ ∙⟦ T₁ ⟧ , proj₂ ∙⟦ T₂ ⟧) , refl}) , refl
∙eval (tensor T₁ T₂) = (λ {_ → (proj₂ ∙⟦ T₁ ⟧ , proj₂ ∙⟦ T₂ ⟧) , refl}) , refl
∙eval (untensor T₁ T₂) = (λ _ → ((proj₂ ∙⟦ T₁ ⟧ , refl) , (proj₂ ∙⟦ T₂ ⟧ , refl))) , refl
∙eval (plusl T₁ T₂) = (λ _ → inj₁ (proj₂ ∙⟦ T₁ ⟧) , refl) , refl
∙eval (plusr T₁ T₂) = (λ _ → inj₂ (proj₂ ∙⟦ T₂ ⟧) , refl) , refl
-- ∙eval (plus T₁ T₂) with ∙⟦ T₁ ⟧ | ∙⟦ T₂ ⟧
-- ... | t₁ , v₁ | t₂ , v₂ = (λ _ → inj₁ v₁ , refl) , refl
∙eval (extract T) = (λ {(w , refl) → w}) , refl
∙eval (duplicate T) = (λ {(w , refl) → (w , refl) , refl}) , refl
∙eval (cotensorl T₁ T₂) = (λ _ → ((proj₂ ∙⟦ T₁ ⟧ , refl) , proj₂ ∙⟦ T₂ ⟧)) , refl
∙eval (cotensorr T₁ T₂) = (λ _ → (proj₂ ∙⟦ T₁ ⟧ , (proj₂ ∙⟦ T₂ ⟧) , refl)) , refl
∙eval (coplusl T₁ T₂) = (λ _ → inj₁ (proj₂ ∙⟦ T₁ ⟧ , refl)) , refl
∙eval (coplusr T₁ T₂) = (λ _ → inj₂ (proj₂ ∙⟦ T₂ ⟧ , refl)) , refl

-----------------------------------------------------------------------------
