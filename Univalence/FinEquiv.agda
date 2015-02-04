{-# OPTIONS --without-K #-}

module FinEquiv where

-- should restrict the imports (later)
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Fin renaming (_+_ to _+F_) hiding (_≤_)
open import Data.Fin.Properties
open import Data.Nat.Properties
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Data.Empty
open import Data.Nat 
open import Function

open import Equiv
open import LeqLemmas
open import FinNatLemmas
open import TypeEquivalences using (swap₊)

-- Divide into 2 modules
module  fwd : {m n : ℕ} → (Fin m ⊎ Fin n) → Fin (m + n)
  fwd {m} {n} (inj₁ x) = inject+ n x
  fwd {m} {n} (inj₂ y) = raise m y

  bwd : {m n : ℕ} → Fin (m + n) → (Fin m ⊎ Fin n)
  bwd {m} {n} i with toℕ i <? m
  ... | yes p = inj₁ (fromℕ≤ p)
  ... | no ¬p = inj₂ (reduce≥ i (≤-pred (≰⇒> ¬p)))

  fwd∘bwd~id : {m n : ℕ} → fwd {m} {n} ∘ bwd ∼ id
  fwd∘bwd~id {m} i with toℕ i <? m
  fwd∘bwd~id i | yes p = sym (inj₁-≡ i p)
  fwd∘bwd~id i | no ¬p = sym (inj₂-≡ i (≤-pred (≰⇒> ¬p)))

  bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
  bwd∘fwd~id {m} {n} (inj₁ x) with toℕ (inject+ n x) <? m 
  bwd∘fwd~id {n = n} (inj₁ x) | yes p = 
     cong inj₁ (inject+-injective (fromℕ≤ p) x (sym (inj₁-≡ (inject+ n x) p)))
  bwd∘fwd~id {m} {n} (inj₁ x) | no ¬p = ⊥-elim (1+n≰n pf)
   where
     open ≤-Reasoning
     pf : suc (toℕ x) ≤ toℕ x
     pf = let q =  (≤-pred (≰⇒> ¬p)) in 
            begin (
              suc (toℕ x)
                ≤⟨ bounded x ⟩
              m
                ≤⟨ q ⟩
              toℕ (inject+ n x)
                ≡⟨ sym (inject+-lemma n x) ⟩
              toℕ x ∎ )

  bwd∘fwd~id {m} {n} (inj₂ y) with toℕ (raise m y) <? m 
  bwd∘fwd~id {m} {n} (inj₂ y) | yes p = ⊥-elim (1+n≰n pf)
   where
     open ≤-Reasoning
     pf : suc m ≤ m
     pf = begin (
             suc m
                 ≤⟨ m≤m+n (suc m) (toℕ y) ⟩
             suc (m + toℕ y)
                 ≡⟨ cong suc (sym (toℕ-raise m y)) ⟩
             suc (toℕ (raise m y))
                 ≤⟨ p ⟩
             m ∎)
  bwd∘fwd~id {m} {n} (inj₂ y) | no ¬p = 
     cong inj₂ (raise-injective {m} (reduce≥ (raise m y) (≤-pred (≰⇒> ¬p))) 
                  y (sym (inj₂-≡ (raise m y) (≤-pred (≰⇒> ¬p)))))

  fwd-iso : {m n : ℕ} → (Fin m ⊎ Fin n) ≃ Fin (m + n)
  fwd-iso {m} {n} = fwd , mkqinv bwd (fwd∘bwd~id {m}) (bwd∘fwd~id {m})

  swapper : (m n : ℕ) → Fin (m + n) → Fin (n + m)
  swapper m n = fwd ∘ swap₊ ∘ bwd {m} {n} 
