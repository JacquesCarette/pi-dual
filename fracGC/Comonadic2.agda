{-# OPTIONS --without-K #-}

module Comonadic2 where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Comonadic

bwd : {A B : 𝕌} → (A ⟷ B) → ⟦ B ⟧ → ⟦ A ⟧
bwd-eval : {A B : 𝕌} → (c : A ⟷ B) → (v : ⟦ A ⟧) → bwd c (eval c v) ≡ v

bwd unite₊l v = inj₂ v
bwd uniti₊l (inj₂ v) = v
bwd unite₊r v = inj₁ v
bwd uniti₊r (inj₁ v) = v
bwd swap₊ (inj₁ v) = inj₂ v
bwd swap₊ (inj₂ v) = inj₁ v
bwd assocl₊ (inj₁ (inj₁ v)) = inj₁ v
bwd assocl₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
bwd assocl₊ (inj₂ v) = inj₂ (inj₂ v)
bwd assocr₊ (inj₁ v) = inj₁ (inj₁ v)
bwd assocr₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
bwd assocr₊ (inj₂ (inj₂ v)) = inj₂ v
bwd unite⋆l v = (tt , v)
bwd uniti⋆l (tt , v) = v
bwd unite⋆r v = (v , tt)
bwd uniti⋆r (v , tt) = v
bwd swap⋆ (v₁ , v₂) = (v₂ , v₁)
bwd assocl⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
bwd assocr⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
bwd dist (inj₁ (v₁ , v₂)) = (inj₁ v₁ , v₂)
bwd dist (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
bwd factor (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
bwd factor (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
bwd distl (inj₁ (v₁ , v₂)) = (v₁ , inj₁ v₂)
bwd distl (inj₂ (v₁ , v₃)) = (v₁ , inj₂ v₃)
bwd factorl (v₁ , inj₁ v₂) = inj₁ (v₁ , v₂)
bwd factorl (v₁ , inj₂ v₃) = inj₂ (v₁ , v₃)
bwd id⟷ v = v
bwd (c₁ ⊚ c₂) v = bwd c₁ (bwd c₂ v)
bwd (c₁ ⊕ c₂) (inj₁ v) = inj₁ (bwd c₁ v)
bwd (c₁ ⊕ c₂) (inj₂ v) = inj₂ (bwd c₂ v)
bwd (c₁ ⊗ c₂) (v₁ , v₂) = (bwd c₁ v₁ , bwd c₂ v₂)
bwd (canonical {v}) tt = ⇑ v refl
bwd canonical⁻¹ x = tt
bwd (lift {_} {_} {v₁} c) (⇑ ●₁ v≡●₁) = ⇑ (bwd c ●₁) (trans (sym (bwd-eval c v₁)) (cong (bwd c) v≡●₁))
bwd tensorl (p₁ , p₂) = ⇑ (● p₁ , ● p₂) (cong₂ _,_ (v≡● p₁) (v≡● p₂))
bwd tensorr (⇑ (v₁ , v₂) p) = ⇑ v₁ (cong proj₁ p) , ⇑ v₂ (cong proj₂ p)
bwd plusl p = ⇑ (inj₁ (● p)) (cong inj₁ (v≡● p))
bwd plusr p = ⇑ (inj₂ (● p)) (cong inj₂ (v≡● p))
bwd (η v) p = tt
bwd (ε v) tt = (⇑ v refl) , λ w x → tt
bwd (== c eq) v = bwd c (subst (Pointed ⟦ _ ⟧) (sym eq) v)

bwd-eval unite₊l (inj₂ v) = refl
bwd-eval uniti₊l v = refl
bwd-eval unite₊r (inj₁ v) = refl
bwd-eval uniti₊r v = refl
bwd-eval swap₊ (inj₁ v) = refl
bwd-eval swap₊ (inj₂ v) = refl
bwd-eval assocl₊ (inj₁ v) = refl
bwd-eval assocl₊ (inj₂ (inj₁ v)) = refl
bwd-eval assocl₊ (inj₂ (inj₂ v)) = refl
bwd-eval assocr₊ (inj₁ (inj₁ v)) = refl
bwd-eval assocr₊ (inj₁ (inj₂ v)) = refl
bwd-eval assocr₊ (inj₂ v) = refl
bwd-eval unite⋆l (tt , v) = refl
bwd-eval uniti⋆l v = refl
bwd-eval unite⋆r (v , tt) = refl
bwd-eval uniti⋆r v = refl
bwd-eval swap⋆ (v₁ , v₂) = refl
bwd-eval assocl⋆ (v₁ , (v₂ , v₃)) = refl
bwd-eval assocr⋆ ((v₁ , v₂) , v₃) = refl
bwd-eval dist (inj₁ v₁ , v₃) = refl
bwd-eval dist (inj₂ v₂ , v₃) = refl
bwd-eval factor (inj₁ (v₁ , v₃)) = refl
bwd-eval factor (inj₂ (v₂ , v₃)) = refl
bwd-eval distl (v₁ , inj₁ v₂) = refl
bwd-eval distl (v₁ , inj₂ v₃) = refl
bwd-eval factorl (inj₁ (v₁ , v₂)) = refl
bwd-eval factorl (inj₂ (v₁ , v₃)) = refl
bwd-eval id⟷ v = refl
bwd-eval (c₁ ⊚ c₂) v = trans (cong (bwd c₁) (bwd-eval c₂ (eval c₁ v))) (bwd-eval c₁ v)
bwd-eval (c₁ ⊕ c₂) (inj₁ v₁) = cong inj₁ (bwd-eval c₁ v₁)
bwd-eval (c₁ ⊕ c₂) (inj₂ v₂) = cong inj₂ (bwd-eval c₂ v₂)
bwd-eval (c₁ ⊗ c₂) (v₁ , v₂) = cong₂ _,_ (bwd-eval c₁ v₁) (bwd-eval c₂ v₂)
bwd-eval (canonical {v}) x = pointed-all-paths
bwd-eval canonical⁻¹ tt = refl
bwd-eval (lift c) v = pointed-all-paths
bwd-eval tensorl p = pointed-all-paths
bwd-eval tensorr (p₁ , p₂) = cong₂ _,_ pointed-all-paths pointed-all-paths
bwd-eval plusl p = pointed-all-paths
bwd-eval plusr p = pointed-all-paths
bwd-eval (η v) tt = refl
bwd-eval (ε v) (p , r) = cong₂ _,_ pointed-contr refl
bwd-eval (== c eq) p = pointed-all-paths

eval-bwd : {A B : 𝕌} → (c : A ⟷ B) → (v : ⟦ B ⟧) → eval c (bwd c v) ≡ v
eval-bwd unite₊l v = refl
eval-bwd uniti₊l (inj₂ v) = refl
eval-bwd unite₊r v = refl
eval-bwd uniti₊r (inj₁ v) = refl
eval-bwd swap₊ (inj₁ v) = refl
eval-bwd swap₊ (inj₂ v) = refl
eval-bwd assocl₊ (inj₁ (inj₁ v)) = refl
eval-bwd assocl₊ (inj₁ (inj₂ v)) = refl
eval-bwd assocl₊ (inj₂ v) = refl
eval-bwd assocr₊ (inj₁ v) = refl
eval-bwd assocr₊ (inj₂ (inj₁ v)) = refl
eval-bwd assocr₊ (inj₂ (inj₂ v)) = refl
eval-bwd unite⋆l v = refl
eval-bwd uniti⋆l (tt , v) = refl
eval-bwd unite⋆r v = refl
eval-bwd uniti⋆r (v , tt) = refl
eval-bwd swap⋆ (v₂ , v₁) = refl
eval-bwd assocl⋆ ((v₁ , v₂) , v₃) = refl
eval-bwd assocr⋆ (v₁ , (v₂ , v₃)) = refl
eval-bwd dist (inj₁ (v₁ , v₂)) = refl
eval-bwd dist (inj₂ (v₂ , v₃)) = refl
eval-bwd factor (inj₁ v₁ , v₃) = refl
eval-bwd factor (inj₂ v₂ , v₃) = refl
eval-bwd distl (inj₁ (v₁ , v₂)) = refl
eval-bwd distl (inj₂ (v₁ , v₃)) = refl
eval-bwd factorl (v₁ , inj₁ v₂) = refl
eval-bwd factorl (v₁ , inj₂ v₃) = refl
eval-bwd id⟷ v = refl
eval-bwd (c₁ ⊚ c₂) v = trans (cong (eval c₂) (eval-bwd c₁ (bwd c₂ v))) (eval-bwd c₂ v)
eval-bwd (c₁ ⊕ c₂) (inj₁ v) = cong inj₁ (eval-bwd c₁ v)
eval-bwd (c₁ ⊕ c₂) (inj₂ v) = cong inj₂ (eval-bwd c₂ v)
eval-bwd (c₁ ⊗ c₂) (v₃ , v₄) = cong₂ _,_ (eval-bwd c₁ v₃) (eval-bwd c₂ v₄)
eval-bwd (canonical {v}) tt = refl
eval-bwd (canonical⁻¹) x = pointed-all-paths
eval-bwd (lift c) x = pointed-all-paths
eval-bwd tensorl p = cong₂ _,_ pointed-all-paths pointed-all-paths
eval-bwd tensorr p = pointed-all-paths
eval-bwd plusl p = pointed-all-paths
eval-bwd plusr p = pointed-all-paths
eval-bwd (η v) (p , r) = cong₂ _,_ pointed-contr refl
eval-bwd (ε v) tt = refl
eval-bwd (== c eq) p = pointed-all-paths

------------------------------------------------------------------
-- note that 'dual' doesn't quite seem to work...

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
