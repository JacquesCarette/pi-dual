{-# OPTIONS --without-K #-}
module FT-Nat where

open import Data.Empty
open import Data.Unit
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Function renaming (_∘_ to _○_)

open import FT
open import HoTT using (refl; pathInd; _≡_)
open import Equivalences
open import TypeEquivalences using (path⊎)
open import Path2Equiv

------------------------------------------------------------------
-- Finite Types and the natural numbers are intimately related.
--
-- Basically, this is because both of them are models of 
-- unital semirings, and the natural numbers are the initial object
-- in the category of unital semirings.  In this case, things are
-- deeper still, and so we record many of these facts here.
--
-- And, of course, as Pi records the proof-theory of semirings in
-- a fairly explicit manner, we can use all this to link up 
-- normalization of natural-numbers expressions and Pi-based paths.

toℕ : FT → ℕ
toℕ ZERO = zero
toℕ ONE = suc zero
toℕ (PLUS b₀ b₁) = (toℕ b₀) + (toℕ b₁) 
toℕ (TIMES b₀ b₁) = (toℕ b₀) * (toℕ b₁)

fromℕ : ℕ → FT
fromℕ zero = ZERO
fromℕ (suc n) = PLUS ONE (fromℕ n)

toℕ∘fromℕ : toℕ ○ fromℕ ∼ id
toℕ∘fromℕ zero = refl zero
toℕ∘fromℕ (suc n) =
  pathInd
    (λ {x} {y} _ → suc x ≡ suc y)
    (λ m → refl (suc m))
    (toℕ∘fromℕ n)

assocr : {m : ℕ} (n : ℕ) → (PLUS (fromℕ n) (fromℕ m)) ⇛ fromℕ (n + m)
assocr zero = unite₊⇛
assocr (suc n) = assocr₊⇛ ◎ (id⇛ ⊕ (assocr n))

distr : (n₀ : ℕ) {n₁ : ℕ} → TIMES (fromℕ n₀) (fromℕ n₁) ⇛ fromℕ (n₀ * n₁)
distr zero = distz⇛
distr (suc n) {m} = dist⇛ ◎ ((unite⋆⇛ ⊕ id⇛) ◎ ((id⇛ ⊕ distr n) ◎ assocr m))

-- normalize a finite type to (1 + (1 + (1 + ... + (1 + 0) ... )))
-- a bunch of ones ending with zero with left biased + in between

normalize : FT → FT
normalize = fromℕ ○ toℕ

normal : (b : FT) → b ⇛ normalize b
normal ZERO = id⇛
normal ONE = uniti₊⇛ ◎ swap₊⇛
normal (PLUS b₀ b₁) = (normal b₀ ⊕ normal b₁) ◎ assocr (toℕ b₀)
normal (TIMES b₀ b₁) = (normal b₀ ⊗ normal b₁) ◎ distr (toℕ b₀)

normalizeC : {B : FT} → ⟦ normalize B ⟧ ≃ ⟦ B ⟧
normalizeC {B} = path2equiv (sym⇛ (normal B))

mapNorm :  {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → ⟦ normalize B₁ ⟧ ≃ ⟦ normalize B₂ ⟧
mapNorm {B₁} {B₂} eq = trans≃ (trans≃ (normalizeC {B₁}) eq) (sym≃ (normalizeC {B₂}))

⟦_⟧ℕ : ℕ → Set
⟦ zero ⟧ℕ = ⊥
⟦ suc n ⟧ℕ = ⊤ ⊎ ⟦ n ⟧ℕ

ℕrespects⟦⟧ : {n : ℕ} → ⟦ fromℕ n ⟧ ≃ ⟦ n ⟧ℕ
ℕrespects⟦⟧ {zero} = id≃
ℕrespects⟦⟧ {suc n} = path⊎ id≃ (ℕrespects⟦⟧ {n})

------------------------------------------------------------------------------

{--

Not used

exf : ⊤ ⊎ ℕ → ℕ
exf (inj₁ tt) = 0 
exf (inj₂ n) = suc n

exg : ℕ → ⊤ ⊎ ℕ
exg 0 = inj₁ tt
exg (suc n) = inj₂ n

exα : exf ○ exg ∼ id
exα 0 = refl 0
exα (suc n) = refl (suc n)

exβ : exg ○ exf ∼ id
exβ (inj₁ tt) = refl (inj₁ tt)
exβ (inj₂ n) = refl (inj₂ n) 

ex : (⊤ ⊎ ℕ) ≃ ℕ
ex = (exf , equiv₁ (mkqinv exg exα exβ))

exf2 : (⊤ ⊎ (⊤ ⊎ ℕ)) → (⊤ ⊎ ℕ)
exf2 (inj₁ tt) = inj₂ 0
exf2 (inj₂ (inj₁ tt)) = inj₂ 1
exf2 (inj₂ (inj₂ 0)) = inj₁ tt
exf2 (inj₂ (inj₂ (suc n))) = inj₂ (suc (suc n))

exg2 : (⊤ ⊎ ℕ) → (⊤ ⊎ (⊤ ⊎ ℕ))
exg2 (inj₁ tt) = inj₂ (inj₂ 0)
exg2 (inj₂ 0) = inj₁ tt
exg2 (inj₂ 1) = inj₂ (inj₁ tt)
exg2 (inj₂ (suc (suc n))) = inj₂ (inj₂ (suc n))

exα2 : exf2 ○ exg2 ∼ id
exα2 (inj₁ tt) = refl (inj₁ tt)
exα2 (inj₂ 0) = refl (inj₂ 0) 
exα2 (inj₂ 1) = refl (inj₂ 1) 
exα2 (inj₂ (suc (suc n))) = refl (inj₂ (suc (suc n))) 

exβ2 : exg2 ○ exf2 ∼ id
exβ2 (inj₁ tt) = refl (inj₁ tt) 
exβ2 (inj₂ (inj₁ tt)) = refl (inj₂ (inj₁ tt)) 
exβ2 (inj₂ (inj₂ 0)) = refl (inj₂ (inj₂ 0)) 
exβ2 (inj₂ (inj₂ (suc n))) = refl (inj₂ (inj₂ (suc n))) 

ex2 : (⊤ ⊎ (⊤ ⊎ ℕ)) ≃ (⊤ ⊎ ℕ)
ex2 = (exf2 , equiv₁ (mkqinv exg2 exα2 exβ2)) 

--}
