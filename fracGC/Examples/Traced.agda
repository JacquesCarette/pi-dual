{-# OPTIONS --without-K #-}

module Examples.Traced where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Pointed
open import PiFrac
open import Trace

open import Examples.BooleanCircuits

------------------------------------------------------------------

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
