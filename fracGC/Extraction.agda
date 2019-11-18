{-# OPTIONS --without-K --safe #-}

module Extraction where
open import Data.Product
open import Data.Sum
open import PiPointedFrac as Pi/ hiding (𝕌; ⟦_⟧)
open import PiFracDyn

Inj𝕌 : Pi/.𝕌 → 𝕌
Inj𝕌 𝟘 = 𝟘
Inj𝕌 𝟙 = 𝟙
Inj𝕌 (t₁ +ᵤ t₂) = Inj𝕌 t₁ +ᵤ Inj𝕌 t₂
Inj𝕌 (t₁ ×ᵤ t₂) = Inj𝕌 t₁ ×ᵤ Inj𝕌 t₂

Inj⟦𝕌⟧ : {t : Pi/.𝕌} → Pi/.⟦ t ⟧ → ⟦ Inj𝕌 t ⟧
Inj⟦𝕌⟧ {𝟙} tt = tt
Inj⟦𝕌⟧ {t₁ +ᵤ t₂} (inj₁ x) = inj₁ (Inj⟦𝕌⟧ x)
Inj⟦𝕌⟧ {t₁ +ᵤ t₂} (inj₂ y) = inj₂ (Inj⟦𝕌⟧ y)
Inj⟦𝕌⟧ {t₁ ×ᵤ t₂} (x , y) = Inj⟦𝕌⟧ x , Inj⟦𝕌⟧ y

Inj⟷ : ∀ {t₁ t₂} → t₁ ⟷ t₂ → Inj𝕌 t₁ ↔ Inj𝕌 t₂
Inj⟷ unite₊l = unite₊l
Inj⟷ uniti₊l = uniti₊l
Inj⟷ unite₊r = unite₊r
Inj⟷ uniti₊r = uniti₊r
Inj⟷ swap₊ = swap₊
Inj⟷ assocl₊ = assocl₊
Inj⟷ assocr₊ = assocr₊
Inj⟷ unite⋆l = unite⋆l
Inj⟷ uniti⋆l = uniti⋆l
Inj⟷ unite⋆r = unite⋆r
Inj⟷ uniti⋆r = uniti⋆r
Inj⟷ swap⋆ = swap⋆
Inj⟷ assocl⋆ = assocl⋆
Inj⟷ assocr⋆ = assocr⋆
Inj⟷ absorbr = absorbr
Inj⟷ absorbl = absorbl
Inj⟷ factorzr = factorzr
Inj⟷ factorzl = factorzl
Inj⟷ dist = dist
Inj⟷ factor = factor
Inj⟷ distl = distl
Inj⟷ factorl = factorl
Inj⟷ id⟷ = id↔
Inj⟷ (c ⊚ c₁) = Inj⟷ c ⊚ Inj⟷ c₁
Inj⟷ (c ⊕ c₁) = Inj⟷ c ⊕ Inj⟷ c₁
Inj⟷ (c ⊗ c₁) = Inj⟷ c ⊗ Inj⟷ c₁

Ext𝕌 : ∙𝕌 → Σ[ t ∈ 𝕌 ] ⟦ t ⟧
Ext𝕌 (t # v) = (Inj𝕌 t , Inj⟦𝕌⟧ v)
Ext𝕌 (t₁ ∙×ᵤ t₂) with Ext𝕌 t₁ | Ext𝕌 t₂
... | (t₁' , v₁') | (t₂' , v₂') = t₁' ×ᵤ t₂' , v₁' , v₂'
Ext𝕌 (t₁ ∙+ᵤl t₂) with Ext𝕌 t₁ | Ext𝕌 t₂
... | (t₁' , v₁') | (t₂' , v₂') = t₁' +ᵤ t₂' , inj₁ v₁'
Ext𝕌 (t₁ ∙+ᵤr t₂) with Ext𝕌 t₁ | Ext𝕌 t₂
... | (t₁' , v₁') | (t₂' , v₂') = t₁' +ᵤ t₂' , inj₂ v₂'
Ext𝕌 (Singᵤ T) with Ext𝕌 T
... | (t , v) = t , v
Ext𝕌 (Recipᵤ T) with Ext𝕌 T
... | (t , v) = 𝟙/ v , ○

Ext∙⟶ : ∀ {t₁ t₂} → t₁ ∙⟶ t₂ → proj₁ (Ext𝕌 t₁) ↔ proj₁ (Ext𝕌 t₂)
Ext∙⟶ (∙c c) = Inj⟷ c
Ext∙⟶ ∙times# = id↔
Ext∙⟶ ∙#times = id↔
Ext∙⟶ ∙id⟷ = id↔
Ext∙⟶ (c₁ ∙⊚ c₂) = Ext∙⟶ c₁ ⊚ Ext∙⟶ c₂
Ext∙⟶ ∙swap⋆ = swap⋆
Ext∙⟶ ∙assocl⋆ = assocl⋆
Ext∙⟶ ∙assocr⋆ = assocr⋆
Ext∙⟶ (c₁ ∙⊗ c₂) = Ext∙⟶ c₁ ⊗ Ext∙⟶ c₂
Ext∙⟶ (return T) = id↔
Ext∙⟶ (join T) = id↔
Ext∙⟶ (unjoin T) = id↔
Ext∙⟶ (tensorl T₁ T₂) = id↔
Ext∙⟶ (tensorr T₁ T₂) = id↔
Ext∙⟶ (tensor T₁ T₂) = id↔
Ext∙⟶ (untensor T₁ T₂) = id↔
Ext∙⟶ (plusl T₁ T₂) = id↔
Ext∙⟶ (plusr T₁ T₂) = id↔
Ext∙⟶ (extract T) = id↔
Ext∙⟶ (cojoin T) = id↔
Ext∙⟶ (counjoin T) = id↔
Ext∙⟶ (cotensorl T₁ T₂) = id↔
Ext∙⟶ (cotensorr T₁ T₂) = id↔
Ext∙⟶ (coplusl T₁ T₂) = id↔
Ext∙⟶ (coplusr T₁ T₂) = id↔
Ext∙⟶ (∙Singᵤ T₁ T₂ c) = Ext∙⟶ c
Ext∙⟶ (η T) = η (proj₂ (Ext𝕌 T))
Ext∙⟶ (ε T) = ε (proj₂ (Ext𝕌 T))
