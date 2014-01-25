{-# OPTIONS --without-K #-}
module Simplify where

open import FT
open import HoTT

-- just flip.  It is he caller's responsibility to do other things
flip : {b₁ b₂ : FT} → b₂ ⇛ b₁ → b₁ ⇛ b₂
flip unite₊⇛ = uniti₊⇛
flip uniti₊⇛ = unite₊⇛
flip swap₊⇛ = swap₊⇛
flip assocl₊⇛ = assocr₊⇛
flip assocr₊⇛ = assocl₊⇛
flip unite⋆⇛ = uniti⋆⇛
flip uniti⋆⇛ = unite⋆⇛
flip swap⋆⇛ = swap⋆⇛
flip assocl⋆⇛ = assocr⋆⇛
flip assocr⋆⇛ = assocl⋆⇛
flip distz⇛ = factorz⇛
flip factorz⇛ = distz⇛
flip dist⇛ = factor⇛
flip factor⇛ = dist⇛
flip id⇛ = id⇛
flip (sym⇛ p) = p
flip (p ◎ q) = flip q ◎ flip p
flip (p ⊕ q) = flip p ⊕ flip q
flip (p ⊗ q) = flip p ⊗ flip q

flip-id-lemma : ∀ {b} → flip {b} {b} id⇛ ≡ id⇛
flip-id-lemma = λ {b} → refl id⇛

-- we're going to be pretty brute-force about this, for now
-- All this is going to be one huge mutual definition.
mutual 
  simplify : {b₁ b₂ : FT} → b₁ ⇛ b₂ → b₁ ⇛ b₂
  -- all the basic (atomic) combinators simplify to themselves
  simplify unite₊⇛ = unite₊⇛
  simplify uniti₊⇛ = uniti₊⇛
  simplify swap₊⇛ = swap₊⇛
  simplify assocl₊⇛ = assocl₊⇛
  simplify assocr₊⇛ = assocr₊⇛
  simplify unite⋆⇛ = unite⋆⇛
  simplify uniti⋆⇛ = uniti⋆⇛
  simplify swap⋆⇛ = swap⋆⇛
  simplify assocl⋆⇛ = assocl⋆⇛
  simplify assocr⋆⇛ = assocr⋆⇛
  simplify distz⇛ = distz⇛
  simplify factorz⇛ = factorz⇛
  simplify dist⇛ = dist⇛
  simplify factor⇛ = factor⇛
  simplify id⇛ = id⇛
  simplify (sym⇛ p) = flip (simplify p)
  simplify (p ◎ q) = scomp (simplify p)  (simplify q)
  simplify (p ⊕ q) = simplify p ⊕ simplify q
  simplify (p ⊗ q) = simplify p ⊗ simplify q

  -- split on p, and then only on those q that we want to simplify
  scomp : {b₁ b₂ b₃ : FT} → b₁ ⇛ b₂ → b₂ ⇛ b₃ → b₁ ⇛ b₃
  scomp id⇛ p = p
  scomp unite₊⇛ id⇛ = unite₊⇛
  scomp unite₊⇛ uniti₊⇛ = id⇛
  scomp unite₊⇛ q = unite₊⇛ ◎ q -- more?
  scomp uniti₊⇛ unite₊⇛ = id⇛
  scomp uniti₊⇛ id⇛ = uniti₊⇛
  scomp uniti₊⇛ q = uniti₊⇛ ◎ q
  scomp swap₊⇛ swap₊⇛ = id⇛
  scomp swap₊⇛ id⇛ = swap₊⇛
  scomp swap₊⇛ (q ◎ q₁) = scomp swap₊⇛ q ◎ q₁
  scomp swap₊⇛ q = swap₊⇛ ◎ q
  scomp assocl₊⇛ assocr₊⇛ = id⇛
  scomp assocl₊⇛ id⇛ = assocl₊⇛
  scomp assocl₊⇛ q = assocl₊⇛ ◎ q
  scomp assocr₊⇛ assocl₊⇛ = id⇛
  scomp assocr₊⇛ id⇛ = assocr₊⇛
  scomp assocr₊⇛ q = assocr₊⇛ ◎ q
  scomp unite⋆⇛ uniti⋆⇛ = id⇛
  scomp unite⋆⇛ id⇛ = unite⋆⇛
  scomp unite⋆⇛ q = unite⋆⇛ ◎ q
  scomp uniti⋆⇛ unite⋆⇛ = id⇛
  scomp uniti⋆⇛ id⇛ = uniti⋆⇛
  scomp uniti⋆⇛ q = uniti⋆⇛ ◎ q
  scomp swap⋆⇛ swap⋆⇛ = id⇛
  scomp swap⋆⇛ id⇛ = swap⋆⇛
  scomp swap⋆⇛ q = swap⋆⇛ ◎ q
  scomp assocl⋆⇛ assocr⋆⇛ = id⇛
  scomp assocl⋆⇛ id⇛ = assocl⋆⇛
  scomp assocl⋆⇛ q = assocl⋆⇛ ◎ q
  scomp assocr⋆⇛ assocl⋆⇛ = id⇛
  scomp assocr⋆⇛ id⇛ = assocr⋆⇛
  scomp assocr⋆⇛ q = assocr⋆⇛ ◎ q
  scomp distz⇛ id⇛ = distz⇛
  scomp distz⇛ q = distz⇛ ◎ q
  scomp factorz⇛ distz⇛ = id⇛
  scomp factorz⇛ id⇛ = factorz⇛
  scomp factorz⇛ q = factorz⇛ ◎ q
  scomp dist⇛ q = dist⇛ ◎ q -- Can't simplify?
  scomp factor⇛ dist⇛ = id⇛
  scomp factor⇛ id⇛ = factor⇛
  scomp factor⇛ q = factor⇛ ◎ q
  scomp (sym⇛ p) q = (flip p) ◎ q -- won't happen from simplify
  scomp (p₁ ◎ p₂) id⇛ = scomp p₁ p₂
  scomp (p₁ ◎ p₂) q = scomp p₁ p₂ ◎ q
  scomp (p₁ ⊕ p₂) id⇛ = p₁ ⊕ p₂
  scomp (p₁ ⊕ p₂) (q₁ ⊕ q₂) = scomp p₁ q₁ ⊕ scomp p₂ q₂
  scomp (p₁ ⊕ p₂) q = (p₁ ⊕ p₂) ◎ q
  scomp (p₁ ⊗ p₂) id⇛ = p₁ ⊗ p₂
  scomp (p₁ ⊗ p₂) (q ◎ q₁) = scomp (p₁ ⊗ p₂) q ◎ q₁
  scomp (p₁ ⊗ p₂) (q ⊗ q₁) = scomp p₁ q ⊗ scomp p₂ q₁
  scomp (p₁ ⊗ p₂) q = (p₁ ⊗ p₂) ◎ q

-- testing
test1 : ∀ {b₁ : FT} → b₁ ⇛ b₁
test1 = simplify (id⇛ ◎ id⇛ ◎ id⇛) 

test2 : ∀ {b₁ : FT} → TIMES ONE b₁ ⇛ TIMES ONE b₁
test2 = simplify ((sym⇛ uniti⋆⇛) ◎ id⇛ ◎ uniti⋆⇛)