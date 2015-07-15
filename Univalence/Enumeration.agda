{-# OPTIONS --without-K #-}

module Enumeration where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin; inject+; raise)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl;  cong; module ≡-Reasoning)

open import Equiv using (_≃_; trans≃; path⊎; path×; mkqinv; module qinv)
open import FinEquiv using (module Plus; module Times; Fin0-⊥)

------------------------------------------------------------------------------

-- An Enumerated 'type' is an isomorphism between a
-- "set" A and Fin n.  Do note that it comes with a particular
-- isomorphism, so that for any given A, it has n! enumerations.

Enum : ∀ {ℓ} → (A : Set ℓ) → (n : ℕ) →  Set ℓ
Enum A n = A ≃ Fin n

-- from TypeEquiv and CauchyEquiv we can get operations on enumerations
-- (note: should generalize TypeEquiv to using Level)

_⊕e_ : {A : Set} {B : Set} {n m : ℕ} →
  Enum A n → Enum B m → Enum (A ⊎ B) (n + m)
eA ⊕e eB = trans≃ (path⊎ eA eB) Plus.fwd-iso

_⊛e_ : {A B : Set} {n m : ℕ} → Enum A n → Enum B m → Enum (A × B) (n * m)
eA ⊛e eB = trans≃ (path× eA eB) Times.fwd-iso

0E : Enum ⊥ 0
0E = ⊥-elim , mkqinv Fin0-⊥ (λ { () }) (λ { () })

-- evaluating an ⊕e on the left component

eval-left : {A B : Set} {m n : ℕ} {eA : Enum A m} {eB : Enum B n} →
  (i : Fin m) →
  qinv.g (proj₂ (eA ⊕e eB)) (inject+ n i) ≡ inj₁ (qinv.g (proj₂ eA) i)
eval-left {m = m} {n} {eA} {eB} i =
  let (fwd , mkqinv bwd _ bwd∘fwd~id) = Plus.fwd-iso {m} {n} in 
  begin (
    qinv.g (proj₂ (eA ⊕e eB)) (inject+ n i)
      ≡⟨ refl ⟩ -- β reduce ⊕e, reverse-β Plus.fwd
    qinv.g (proj₂ (trans≃ (path⊎ eA eB) Plus.fwd-iso)) (fwd (inj₁ i))
      ≡⟨ refl ⟩ -- expand qinv.g and trans≃
    qinv.g (proj₂ (path⊎ eA eB)) (qinv.g (proj₂ Plus.fwd-iso) (fwd (inj₁ i)))
      ≡⟨ refl ⟩ -- expand rhs
    qinv.g (proj₂ (path⊎ eA eB)) ((bwd ∘ fwd) (inj₁ i))
      ≡⟨ cong (qinv.g (proj₂ (path⊎ eA eB))) (bwd∘fwd~id (inj₁ i)) ⟩
    qinv.g (proj₂ (path⊎ eA eB)) (inj₁ i)
      ≡⟨ refl ⟩ -- by definition of path⊎
    inj₁ (qinv.g (proj₂ eA) i) ∎)
  where open ≡-Reasoning

eval-right : {A B : Set} {m n : ℕ} {eA : Enum A m} {eB : Enum B n} →
  (i : Fin n) →
  qinv.g (proj₂ (eA ⊕e eB)) (raise m i) ≡ inj₂ (qinv.g (proj₂ eB) i)
eval-right {eA = eA} {eB} i = 
  cong (qinv.g (proj₂ (path⊎ eA eB))) (qinv.β (proj₂ Plus.fwd-iso) (inj₂ i))

------------------------------------------------------------------------------
