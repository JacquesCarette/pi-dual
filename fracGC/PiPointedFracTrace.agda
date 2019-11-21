{-# OPTIONS --without-K --safe #-}

-- Pi combinators inspired by duals and traced monoidal categories

module PiPointedFracTrace where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

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

-- Trace terminates!  The type C is pointed with point c; trace uses c
-- as the initial value for C. So f gets two values (a,c). It can do
-- whatever to produce (b',c'). But f is reversible so it is limited
-- to essentially either id or swap. Makes sense???

𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

zz1 : (A : 𝕌) (v : ⟦ A ⟧) → Σ (⟦ A ⟧ → ⟦ A ⟧) (λ f → f v ≡ v)
zz1 A v = ∙eval (trace {A # v} ∙swap⋆)

zz3 : (A : 𝕌) (v : ⟦ A ⟧) (T : ∙𝕌) → Σ (⟦ A ⟧ → ⟦ A ⟧) (λ f → f v ≡ v)
zz3 A v T = ∙eval (trace {A # v} {_} {T} ∙id⟷)

-- There are more thing you put in trace as long as c is the fixpoint
NOT : 𝔹 ⟷ 𝔹
NOT = swap₊

CONTROLLED : {A : 𝕌} → (A ⟷ A) → 𝔹 ×ᵤ A ⟷ 𝔹 ×ᵤ A
CONTROLLED c = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ c)) ⊚ factor

CNOT : 𝔹 ×ᵤ 𝔹 ⟷ 𝔹 ×ᵤ 𝔹
CNOT = CONTROLLED NOT

ex1 : ∀ {b} → 𝔹 # b ∙⟶ 𝔹 # b
ex1 = trace {C = 𝔹 # 𝔽} (∙swap⋆ ∙⊚ ∙#times ∙⊚ ∙c CNOT ∙⊚ ∙times# ∙⊚ ∙swap⋆)
