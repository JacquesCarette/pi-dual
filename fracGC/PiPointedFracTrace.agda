{-# OPTIONS --without-K --safe #-}

-- Pi combinators inspired by duals and traced monoidal categories

module PiPointedFracTrace where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst)

open import PiPointedFrac

------------------------------------------------------------------

dual : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) →
                   (Recipᵤ (B # eval f v) ∙⟶ Recipᵤ (A # v))
dual {A} {B} f v = ∙uniti⋆l ∙⊚ (η (A # v) ∙⊗ ∙id⟷) ∙⊚ ((∙Singᵤ _ _ (∙c f) ∙⊗ ∙id⟷) ∙⊗ ∙id⟷) ∙⊚ 
                   ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ ∙swap⋆) ∙⊚ ∙assocl⋆ ∙⊚ (ε (B # eval f v) ∙⊗ ∙id⟷) ∙⊚ ∙unite⋆l

-- name, coname
name : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) → ∙𝟙 ∙⟶ Singᵤ (B # eval f v) ∙×ᵤ Recipᵤ (A # v)
name {A} {B} f v = η (A # v) ∙⊚ (∙Singᵤ _ _ (∙c f) ∙⊗ ∙id⟷)

coname : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) → Singᵤ (A # v) ∙×ᵤ Recipᵤ (B # eval f v) ∙⟶ ∙𝟙
coname {A} {B} f v = (∙Singᵤ _ _ (∙c f) ∙⊗ ∙id⟷) ∙⊚ ε (B # eval f v)

-- and 'trace' reveals something neat: we can't choose just any random 'a' and 'c'
-- to start with, but we need that make a coherence choice of a and c !!
trace : {A B C : 𝕌} (a : ⟦ A ⟧ ) → (f : A ×ᵤ C ⟷ B ×ᵤ C) →
  (coh : Σ ⟦ C ⟧ (λ c → proj₂ (eval f (a , c)) ≡ c)) →
  A # a  ∙⟶ B # proj₁ (eval f (a , proj₁ coh))
trace {A} {B} {C} a f (c , choice) =
  ∙uniti⋆r ∙⊚                               -- A ×ᵤ 1
  (return _ ∙⊗ η (C # c)) ∙⊚                    -- A ×ᵤ (C ×ᵤ 1/C)
  ∙assocl⋆ ∙⊚                               -- (A ×ᵤ C) ×ᵤ 1/C
  (tensor _ _ ∙⊗ ∙id⟷) ∙⊚                  -- bring in the ●
  (∙Singᵤ _ _ (∙#times ∙⊚ ∙c f ∙⊚ ∙times#) ∙⊗ ∙id⟷) ∙⊚ -- (B ×ᵤ C) ×ᵤ 1/C
  (untensor _ _ ∙⊗ ∙id⟷) ∙⊚ -- bring out the ●
  ∙assocr⋆ ∙⊚          -- B ×ᵤ (C ×ᵤ 1/C)
  (extract _ ∙⊗ (subst fixer choice ∙id⟷ ∙⊚ ε (C # c))) ∙⊚
  ∙unite⋆r
  where
    fixer : ⟦ C ⟧ → Set
    fixer d = Singᵤ (C # proj₂ (eval f (a , c))) ∙×ᵤ Recipᵤ (C # d) ∙⟶ Singᵤ (C # d) ∙×ᵤ Recipᵤ (C # d)
