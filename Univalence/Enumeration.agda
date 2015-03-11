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

-- evaluating an ⊕e on the left component
eval-left : {A B : Set} {m n : ℕ} {eA : Enum A m} {eB : Enum B n} →
  (i : Fin m) → qinv.g (proj₂ (eA ⊕e eB)) (inject+ n i) ≡ inj₁ (qinv.g (proj₂ eA) i)
eval-left {m = m} {n} {eA} {eB} i = 
  begin (
    qinv.g (proj₂ (eA ⊕e eB)) (inject+ n i)
      ≡⟨ refl ⟩ -- β reduce ⊕e, reverse-β Plus.fwd
    qinv.g (proj₂ (trans≃ (path⊎ eA eB) Plus.fwd-iso)) (Plus.fwd (inj₁ i))
      ≡⟨ refl ⟩ -- expand qinv.g and trans≃
    qinv.g (proj₂ (path⊎ eA eB)) (qinv.g (proj₂ Plus.fwd-iso) (Plus.fwd (inj₁ i)))
      ≡⟨ refl ⟩ -- expand rhs
    qinv.g (proj₂ (path⊎ eA eB)) ((Plus.bwd {m} ∘ Plus.fwd) (inj₁ i))
      ≡⟨ cong (qinv.g (proj₂ (path⊎ eA eB))) (Plus.bwd∘fwd~id (inj₁ i)) ⟩
    qinv.g (proj₂ (path⊎ eA eB)) (inj₁ i)
      ≡⟨ refl ⟩ -- by definition of path⊎
    inj₁ (qinv.g (proj₂ eA) i) ∎)
  where open ≡-Reasoning

eval-right : {A B : Set} {m n : ℕ} {eA : Enum A m} {eB : Enum B n} →
  (i : Fin n) → qinv.g (proj₂ (eA ⊕e eB)) (raise m i) ≡ inj₂ (qinv.g (proj₂ eB) i)
eval-right {eA = eA} {eB} i = cong (qinv.g (proj₂ (path⊎ eA eB))) (Plus.bwd∘fwd~id (inj₂ i))
