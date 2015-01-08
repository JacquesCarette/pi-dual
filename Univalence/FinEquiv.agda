{-# OPTIONS --without-K #-}

module FinEquiv where

-- should restrict the imports (later)
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Fin renaming (_+_ to _+F_)
open import Data.Fin.Properties
open import Data.Nat.Properties
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Data.Nat 
open import Function

open import Equiv
open import LeqLemmas

private
  fwd : {m n : ℕ} → (Fin m ⊎ Fin n) → Fin (m + n)
  fwd {m} {n} (inj₁ x) = inject+ n x
  fwd {m} {n} (inj₂ y) = raise m y
 
  bwd : {m n : ℕ} → Fin (m + n) → (Fin m ⊎ Fin n)
  bwd {zero} i = inj₂ i
  bwd {suc m} zero = inj₁ zero
  bwd {suc m} (suc i) = f (bwd {m} i)
    where
      f : {p q : ℕ} → (Fin p ⊎ Fin q) → Fin (suc p) ⊎ Fin q
      f {p} {q} (inj₁ x) = inj₁ (suc x)
      f {p} {q} (inj₂ y) = inj₂ y

  bwd' : {m n : ℕ} → Fin (m + n) → (Fin m ⊎ Fin n)
  bwd' {m} {n} i with toℕ i <? m
  ... | yes p = inj₁ (fromℕ≤ p)
  ... | no ¬p = inj₂ (reduce≥ i (≤-pred (≰⇒> ¬p)))

  fwd∘bwd~id : {m n : ℕ} → fwd {m} {n} ∘ bwd ∼ id
  fwd∘bwd~id {zero} x = refl
  fwd∘bwd~id {suc m} zero = refl
  fwd∘bwd~id {suc m} (suc i) with bwd {m} i | inspect (bwd {m}) i
  fwd∘bwd~id {suc m} (suc i) | inj₁ x | [ eq ] = cong suc (trans (cong fwd (sym eq)) (fwd∘bwd~id {m} i))
  fwd∘bwd~id {suc m} (suc i) | inj₂ y | [ eq ] = cong suc (trans (cong fwd (sym eq)) (fwd∘bwd~id {m} i))

  bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
  bwd∘fwd~id {zero} (inj₁ ())
  bwd∘fwd~id {suc m} (inj₁ zero) = refl
  bwd∘fwd~id {suc m} {n} (inj₁ (suc x)) with (bwd {m} (inject+ n x)) | inspect (bwd {m}) (inject+ n x) 
  bwd∘fwd~id {suc m} {n} (inj₁ (suc x)) | inj₁ x₁ | [ eq ] = 
      cong (inj₁ ∘ suc) (toℕ-injective {!cong fwd (sym eq)!} )
  bwd∘fwd~id {suc m} (inj₁ (suc x)) | inj₂ y | [ eq ] = {!!}
  bwd∘fwd~id {zero} (inj₂ y) = refl
  bwd∘fwd~id {suc m} (inj₂ y) = {!!}

fwd-iso : {m n : ℕ} → (Fin m ⊎ Fin n) ≃ Fin (m + n)
fwd-iso {m} {n} = fwd , mkqinv bwd (fwd∘bwd~id {m}) (bwd∘fwd~id {m})
