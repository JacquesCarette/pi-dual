{-# OPTIONS --without-K --safe #-}

-- Pi combinators inspired by duals and traced monoidal categories

module Trace where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst)

open import PiFrac

------------------------------------------------------------------

dual : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) →
                   (𝟙/● B [ eval f v ] ⟷ 𝟙/● A [ v ])
dual f v = uniti⋆l ⊚ (η v ⊗ id⟷) ⊚ ((lift f ⊗ id⟷) ⊗ id⟷) ⊚
  assocr⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚ assocl⋆ ⊚ (ε (eval f v) ⊗ id⟷) ⊚ unite⋆l

-- name, coname
name : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) → 𝟙 ⟷ ● B [ eval f v ] ×ᵤ 𝟙/● A [ v ]
name f v = η v ⊚ (lift f ⊗ id⟷)

coname : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) → ● A [ v ] ×ᵤ 𝟙/● B [ eval f v ] ⟷ 𝟙
coname f v = (lift f ⊗ id⟷) ⊚ ε (eval f v)

-- and 'trace' reveals something neat: we can't choose just any random 'a' and 'c'
-- to start with, but we need that make a coherence choice of a and c !!
trace : {A B C : 𝕌} (a : ⟦ A ⟧ ) → (f : A ×ᵤ C ⟷ B ×ᵤ C) →
  (coh : Σ ⟦ C ⟧ (λ c → proj₂ (eval f (a , c)) ≡ c)) →
  ● A [ a ] ⟷ ● B [ proj₁ (eval f (a , proj₁ coh)) ]
trace {A} {B} {C} a f (c , choice) =
  uniti⋆r ⊚        -- A ×ᵤ 1
  (id⟷ ⊗ η c) ⊚   -- A ×ᵤ (C ×ᵤ 1/C)
  assocl⋆ ⊚       -- (A ×ᵤ C) ×ᵤ 1/C
  (tensorr ⊗ id⟷) ⊚ -- bring in the ●
  (lift f ⊗ id⟷) ⊚ -- (B ×ᵤ C) ×ᵤ 1/C
  (tensorl ⊗ id⟷) ⊚ -- bring out the ●
  assocr⋆ ⊚          -- B ×ᵤ (C ×ᵤ 1/C)
  (id⟷ ⊗ (subst fixer choice id⟷ ⊚ ε c)) ⊚ -- B ×ᵤ 1
  unite⋆r
  where
    fixer : ⟦ C ⟧ → Set
    fixer d = (● C [ proj₂ (eval f (a , c)) ] ×ᵤ 𝟙/● C [ d ]) ⟷ (● C [ d ] ×ᵤ 𝟙/● C [ d ])
