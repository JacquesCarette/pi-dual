{-# OPTIONS --without-K #-}

module Comonadic2 where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Pointed
open import PiFrac

open import Examples.BooleanCircuits

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

-- Example in Sec. 4.3 from Abramsky's paper
-- http://www.cs.ox.ac.uk/files/341/calco05.pdf

p : ∀ {A1 A2 A3 A4 : 𝕌} →
    (A1 ×ᵤ A2) ×ᵤ (A3 ×ᵤ A4) ⟷ (A2 ×ᵤ A4) ×ᵤ (A3 ×ᵤ A1)
p = (swap⋆ ⊗ swap⋆) ⊚
       assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⊚ (id⟷ ⊗ (swap⋆ ⊗ id⟷)) ⊚
       (id⟷ ⊗ assocr⋆) ⊚ assocl⋆ ⊚ (id⟷ ⊗ swap⋆)

p' : ∀ {A1 A2 A3 A4 : 𝕌} →
    ((A1 ×ᵤ A2) ×ᵤ A4) ×ᵤ A3 ⟷ ((A2 ×ᵤ A4) ×ᵤ A1) ×ᵤ A3
p' = assocr⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚ p ⊚ (id⟷ ⊗ swap⋆) ⊚ assocl⋆

tracedp : (v : ⟦ ((𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) ⟧) →
          let ((v1 , v2) , v4) = v in
          ● ((𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ v ] ⟷ ● ((𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (v2 , v4) , v1 ]
tracedp v = trace v p' (v , refl)

p2 : 𝔹 ×ᵤ (𝔹 ×ᵤ (𝔹 ×ᵤ 𝔹)) ⟷ 𝔹 ×ᵤ (𝔹 ×ᵤ (𝔹 ×ᵤ 𝔹))
p2 = assocl⋆ ⊚ (swap⋆ ⊗ swap⋆) ⊚
       assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⊚ (id⟷ ⊗ (swap⋆ ⊗ id⟷)) ⊚
       (id⟷ ⊗ assocr⋆) ⊚ assocl⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚ assocr⋆

p2' : (v : ⟦ 𝔹 ⟧) →
      ● 𝔹 [ v ] ⟷ ● 𝔹 [ proj₁ (proj₁ (eval p ((v , v) , (v , v)))) ]
p2' v = trace v p2 ((v , (v , v)) , refl)

-- Examples to build

-- A <-> 1 / (1/A)
-- 1 / (A x B) <-> 1/A x 1/B
-- (A <-> B) -> (1/A <-> 1/B)
-- 1/A x B is a space transformer; takes A space and returns B space
-- denote space transformers as A -o B
-- They can be applied (A -o B) x A <-> B
-- They compose (A -o B) -> (B -o C) -> (A -o C)
-- A/B x C/D <-> (A x C) / (B x D)
-- A/C + B/C <-> (A + B) / C
-- A/B + C/D <-> (A x D + B x C) / (B x D)

-- SAT solver Sec. 5 from https://www.cs.indiana.edu/~sabry/papers/rational.pdf
