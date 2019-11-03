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
open import Reasoning

open import Examples.BooleanCircuits

------------------------------------------------------------------

-- Example in Sec. 4.3 from Abramsky's paper
-- http://www.cs.ox.ac.uk/files/341/calco05.pdf

q : {A1 A2 A3 A4 B1 B2 B3 B4 : 𝕌} →
  (f1 : A1 ⟷ B2) →
  (f2 : A2 ⟷ B4) →
  (f3 : A3 ⟷ B3) →
  (f4 : A4 ⟷ B1) →
  A1 ×ᵤ (A2 ×ᵤ (A3 ×ᵤ A4)) ⟷ B1 ×ᵤ (B2 ×ᵤ (B3 ×ᵤ B4))
q {A1} {A2} {A3} {A4} {B1} {B2} {B3} {B4} f1 f2 f3 f4 =
  (A1 ×ᵤ A2 ×ᵤ A3 ×ᵤ A4)     ⟷⟨ f1 ⊗ (f2 ⊗ (f3 ⊗ f4)) ⟩
  (B2 ×ᵤ B4 ×ᵤ B3 ×ᵤ B1)     ⟷⟨ assocl⋆ ⟩
  (B2 ×ᵤ B4) ×ᵤ (B3 ×ᵤ B1)   ⟷⟨ swap⋆ ⟩
  (B3 ×ᵤ B1) ×ᵤ (B2 ×ᵤ B4)   ⟷⟨ swap⋆ ⊗ id⟷ ⟩
  (B1 ×ᵤ B3) ×ᵤ (B2 ×ᵤ B4)   ⟷⟨ assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⟩
  B1 ×ᵤ ((B3 ×ᵤ B2) ×ᵤ B4)   ⟷⟨ id⟷ ⊗ ((swap⋆ ⊗ id⟷) ⊚ assocr⋆) ⟩
  B1 ×ᵤ (B2 ×ᵤ (B3 ×ᵤ B4)) □

q' : {A1 U2 U3 U4 B1 : 𝕌} →
  (f1 : A1 ⟷ U2) →
  (f2 : U2 ⟷ U4) →
  (f3 : U3 ⟷ U3) →
  (f4 : U4 ⟷ B1) → (v : ⟦ A1 ⟧) (u3 : ⟦ U3 ⟧)  → (u3-fix : eval f3 u3 ≡ u3) →
  let u2 = eval f1 v in
  let u4 = eval f2 u2 in
  ● A1 [ v ] ⟷ ● B1 [ proj₁ (eval (q f1 f2 f3 f4) (v , u2 , u3 , u4)) ]
q' f1 f2 f3 f4 v u3 u3fix =
  trace v (q f1 f2 f3 f4) (( u2 , ( u3 , u4 ) ), cong₂ _,_ refl (cong₂ _,_ u3fix refl))
  where
    u2 = eval f1 v
    u3′ = eval f3 u3
    u4 = eval f2 u2

p : {A1 A2 A3 A4 : 𝕌} →
    (A1 ×ᵤ A2) ×ᵤ (A3 ×ᵤ A4) ⟷ (A2 ×ᵤ A4) ×ᵤ (A3 ×ᵤ A1)
p = (swap⋆ ⊗ swap⋆) ⊚
       assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⊚ (id⟷ ⊗ (swap⋆ ⊗ id⟷)) ⊚
       (id⟷ ⊗ assocr⋆) ⊚ assocl⋆ ⊚ (id⟷ ⊗ swap⋆)

p' : {A1 A2 A3 A4 : 𝕌} →
    ((A1 ×ᵤ A2) ×ᵤ A4) ×ᵤ A3 ⟷ ((A2 ×ᵤ A4) ×ᵤ A1) ×ᵤ A3
p' = assocr⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚ p ⊚ (id⟷ ⊗ swap⋆) ⊚ assocl⋆

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
