{-# OPTIONS --without-K --safe #-}

-- Pi combinators inspired by duals and traced monoidal categories

module PiPointedFracTrace where
open import PiPointedFrac

------------------------------------------------------------------

dual : {A B : ∙𝕌} → (f : A ∙⟶ B) →  (Recipᵤ B ∙⟶ Recipᵤ A)
dual {A} {B} f = ∙uniti⋆l ∙⊚ (η A ∙⊗ ∙id⟷) ∙⊚ ((∙Singᵤ _ _ f ∙⊗ ∙id⟷) ∙⊗ ∙id⟷) ∙⊚
                 ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ ∙swap⋆) ∙⊚ ∙assocl⋆ ∙⊚ (ε B ∙⊗ ∙id⟷) ∙⊚ ∙unite⋆l

-- name, coname
name : {A B : ∙𝕌} → (f : A ∙⟶ B) → ∙𝟙 ∙⟶ Singᵤ B ∙×ᵤ Recipᵤ A
name {A} {B} f = η A ∙⊚ (∙Singᵤ _ _ f ∙⊗ ∙id⟷)

coname : {A B : ∙𝕌} → (f : A ∙⟶ B) → Singᵤ A ∙×ᵤ Recipᵤ B ∙⟶ ∙𝟙
coname {A} {B} f = (∙Singᵤ _ _ f ∙⊗ ∙id⟷) ∙⊚ ε B

-- and 'trace' reveals something neat: we can't choose just any random 'a' and 'c'
-- to start with, but we need that make a coherence choice of a and c !!
trace : {A B C : ∙𝕌} → (f : A ∙×ᵤ C ∙⟶ B ∙×ᵤ C) → A ∙⟶ B
trace {A} {B} {C} f =
  ∙uniti⋆r ∙⊚                -- A ×ᵤ 1
  (return _ ∙⊗ η C) ∙⊚       -- A ×ᵤ (C ×ᵤ 1/C)
  ∙assocl⋆ ∙⊚                -- (A ×ᵤ C) ×ᵤ 1/C
  (tensor _ _ ∙⊗ ∙id⟷) ∙⊚    -- bring in the ●
  (∙Singᵤ _ _ f ∙⊗ ∙id⟷) ∙⊚  -- (B ×ᵤ C) ×ᵤ 1/C
  (untensor _ _ ∙⊗ ∙id⟷) ∙⊚  -- bring out the ●
  ∙assocr⋆ ∙⊚                -- B ×ᵤ (C ×ᵤ 1/C)
  (extract _ ∙⊗ ε C) ∙⊚
  ∙unite⋆r
