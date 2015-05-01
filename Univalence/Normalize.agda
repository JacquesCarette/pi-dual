module Normalize where

open import Data.List
open import Data.Product

open import PiLevel0

-- We are going to use all the coherence as follows; make the right
-- hand side canonical and rewrite the left hand side to the right
-- hand side. Brute force below cannot work! 

-- Use the same structure as
-- https://agda.github.io/agda-stdlib/Algebra.Monoid-solver.html ??

{-# NO_TERMINATION_CHECK #-}
normalize : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂)
normalize unite₊ = {!!}
normalize uniti₊ = {!!}
normalize swap₊ = {!!}
normalize assocl₊ = {!!}
normalize assocr₊ = {!!}
normalize unite⋆ = {!!}
normalize uniti⋆ = {!!}
normalize swap⋆ = {!!}
normalize assocl⋆ = {!!}
normalize assocr⋆ = {!!}
normalize absorbr = {!!}
normalize absorbl = {!!}
normalize factorzr = {!!}
normalize factorzl = {!!}
normalize dist = {!!}
normalize factor = {!!}
normalize id⟷ = {!!}
normalize (c ◎ id⟷) = normalize c
normalize (unite₊ ◎ c₁) = {!!}
normalize (uniti₊ ◎ c₁) = {!!}
normalize (swap₊ ◎ c₁) = {!!}
normalize (assocl₊ ◎ c₁) = {!!}
normalize (assocr₊ ◎ c₁) = {!!}
normalize (unite⋆ ◎ c₁) = {!!}
normalize (uniti⋆ ◎ c₁) = {!!}
normalize (swap⋆ ◎ c₁) = {!!}
normalize (assocl⋆ ◎ c₁) = {!!}
normalize (assocr⋆ ◎ c₁) = {!!}
normalize (absorbr ◎ c₁) = {!!}
normalize (absorbl ◎ c₁) = {!!}
normalize (factorzr ◎ c₁) = {!!}
normalize (factorzl ◎ c₁) = {!!}
normalize (dist ◎ c₁) = {!!}
normalize (factor ◎ c₁) = {!!}
normalize (id⟷ ◎ c₁) = normalize c₁
normalize ((c ◎ c₁) ◎ c₂) = normalize (c ◎ (c₁ ◎ c₂))
normalize ((c ⊕ c₁) ◎ c₂) = {!!}
normalize ((c ⊗ c₁) ◎ c₂) = {!!}
normalize (c ⊕ unite₊) = {!!}
normalize (c ⊕ uniti₊) = {!!}
normalize (c ⊕ swap₊) = {!!}
normalize (c ⊕ assocl₊) = {!!}
normalize (c ⊕ assocr₊) = {!!}
normalize (c ⊕ unite⋆) = {!!}
normalize (c ⊕ uniti⋆) = {!!}
normalize (c ⊕ swap⋆) = {!!}
normalize (c ⊕ assocl⋆) = {!!}
normalize (c ⊕ assocr⋆) = {!!}
normalize (c ⊕ absorbr) = {!!}
normalize (c ⊕ absorbl) = {!!}
normalize (c ⊕ factorzr) = {!!}
normalize (c ⊕ factorzl) = {!!}
normalize (c ⊕ dist) = {!!}
normalize (c ⊕ factor) = {!!}
normalize (c ⊕ id⟷) = {!!}
normalize (c ⊕ c₁ ◎ c₂) = {!!}
normalize (c ⊕ (c₁ ⊕ c₂)) = {!!}
normalize (c ⊕ (c₁ ⊗ c₂)) = {!!}
normalize (c ⊗ c₁) = {!!} 

