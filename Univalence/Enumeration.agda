{-# OPTIONS --without-K #-}

module Enumeration where

open import Equiv
open import Proofs using (inj-injective)
open import Data.Empty
open import Data.Fin using (Fin; inject+; raise; toℕ; fromℕ≤; zero; suc;
  reduce≥)
open import Data.Fin.Properties using (inject+-lemma; bounded; fromℕ≤-toℕ;
  toℕ-raise; toℕ-injective)
open import Data.Nat using (ℕ;_+_;_*_; _≤?_; _≤_; _≥_;
  zero; suc; s≤s; z≤n; ≤-pred; module ≤-Reasoning)
open import Data.Nat.Properties using (¬i+1+j≤i; ≰⇒>)
open import Data.Nat.Properties.Simple using (+-suc)
open import Relation.Nullary using (yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_;_,_; proj₁; proj₂)
open import Function using (_∘_)
open import TypeEquivalences using (path⊎; path×)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans;
  subst; module ≡-Reasoning)
open import FinEquiv
open import LeqLemmas
open import FinNatLemmas

-- An Enumerated 'type' is an isomorphism between a
-- "set" A and Fin n.  Do note that it comes with a particular
-- isomorphism, so that for any given A, it has n! enumerations.
Enum : ∀ {ℓ} → (A : Set ℓ) → (n : ℕ) →  Set ℓ
Enum A n = A ≃ Fin n

-- from TypeEquivalences and VecOps, we can get operations on enumerations
-- (note: should generalize TypeEquivalences to using Level)
_⊕e_ : {A : Set} {B : Set} {n m : ℕ} →
  Enum A n → Enum B m → Enum (A ⊎ B) (n + m)
eA ⊕e eB = trans≃ (path⊎ eA eB) Plus.fwd-iso

_⊛e_ : {A B : Set} {n m : ℕ} → Enum A n → Enum B m → Enum (A × B) (n * m)
eA ⊛e eB = trans≃ (path× eA eB) Times.fwd-iso

0E : Enum ⊥ 0
0E = ⊥-elim , mkqinv Fin0-⊥ (λ { () }) (λ { () })

inj+-bounded : ∀ {m n} → (i : Fin m) → suc (toℕ (inject+ n i)) ≤ m
inj+-bounded {m} {n} i = 
  begin (
    suc (toℕ (inject+ n i))
      ≡⟨ cong suc (sym (inject+-lemma n i)) ⟩
    suc (toℕ i)
      ≤⟨ bounded i ⟩
    m ∎)
  where open ≤-Reasoning

raise≤m⇒⊥ : ∀ {m n} → (i : Fin n) → suc (toℕ (raise m i)) ≤ m → ⊥
raise≤m⇒⊥ {m} i p = ¬i+1+j≤i m (subst (λ x → x ≤ m) pf p)
  where
    pf : suc (toℕ (raise m i)) ≡ m + suc (toℕ i)
    pf = trans (cong suc (toℕ-raise m i)) (sym (+-suc m _) )

reduce-fromℕ≤ : (m : ℕ) {n : ℕ} (i : Fin m) → (p : suc (toℕ (inject+ n i)) ≤ m)
  → fromℕ≤ p ≡ i
reduce-fromℕ≤ 0 () p
reduce-fromℕ≤ (suc m) zero (s≤s z≤n) = refl
reduce-fromℕ≤ (suc (suc m)) {n} (suc i) (s≤s (s≤s p)) = 
  cong suc (reduce-fromℕ≤ (suc m) i (s≤s p))

reduce-reduce≥ : (m : ℕ) {n : ℕ} (i : Fin n) → (p : toℕ (raise m i) ≥ m)
  → reduce≥ (raise m i) p ≡ i
reduce-reduce≥ zero {n} i p = refl
reduce-reduce≥ (suc n) {zero} () _
reduce-reduce≥ (suc m) {suc n} i (s≤s p) = reduce-reduce≥ m i p

-- evaluating an ⊕e on the left component
eval-left : {A B : Set} {m n : ℕ} {eA : Enum A m} {eB : Enum B n} →
  (i : Fin m) → qinv.g (proj₂ (eA ⊕e eB)) (inject+ n i) ≡ inj₁ (qinv.g (proj₂ eA) i)
eval-left {m = m} {n} {eA} i with suc (toℕ (inject+ n i)) ≤? m
eval-left {m = m} {n} {_ , mkqinv g α β} i | yes p = cong (inj₁ ∘ g) extract
  where
    extract : fromℕ≤ p ≡ i
    extract = reduce-fromℕ≤ m i p
eval-left i | no ¬p = ⊥-elim (¬p (inj+-bounded i))

eval-right : {A B : Set} {m n : ℕ} {eA : Enum A m} {eB : Enum B n} →
  (i : Fin n) → qinv.g (proj₂ (eA ⊕e eB)) (raise m i) ≡ inj₂ (qinv.g (proj₂ eB) i)
eval-right {m = m} {n} {eA} {eB} i with  suc (toℕ (raise m i)) ≤? m
eval-right {m = m} {n} {_} {_} i | yes p = ⊥-elim (raise≤m⇒⊥ i p)
eval-right {m = m} {n} {_ } {_ , mkqinv g _ _} i | no ¬p = cong (inj₂ ∘ g) extract
  where
    extract : reduce≥ (raise m i) (≤-pred (≰⇒> ¬p)) ≡ i
    extract = reduce-reduce≥ m i (≤-pred (≰⇒> ¬p))
