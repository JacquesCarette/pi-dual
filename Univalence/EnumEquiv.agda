{-# OPTIONS --without-K #-}

module EnumEquiv where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_) 
open import Data.Fin using (Fin; inject+; raise)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂) 

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; module ≡-Reasoning)

open import Equiv using (_≃_; trans≃; path⊎; iseq; module isequiv) 
open import FinEquiv using (Fin0-⊥; module Plus) 

------------------------------------------------------------------------------
-- An equivalence between a set 'A' and a finite set 'Fin n' is an
-- enumeration of A.

Enum : ∀ {ℓ} → (A : Set ℓ) → (n : ℕ) →  Set ℓ
Enum A n = A ≃ Fin n

-- We only need some additive equivalences...

0E : Enum ⊥ 0
0E = ⊥-elim , iseq Fin0-⊥ (λ { () }) Fin0-⊥ (λ { () })

_⊕e_ : {A : Set} {B : Set} {n m : ℕ} →
       Enum A n → Enum B m → Enum (A ⊎ B) (n + m)
eA ⊕e eB = trans≃ (path⊎ eA eB) Plus.fwd-iso

-- shorthand to select the element indexed by i in the enumeration

select : {A B : Set} (eq : A ≃ B) → (B → A)
select (_ , iseq g _ _ _) = g

-- The enumeration of (A ⊎ B) is an enumeration of A followed by an
-- enumeration of B; in other words if we have an equivalence between
-- (A ⊎ B) and Fin (m + n) and we are given an index i < m then this
-- index selects an element of A.

-- evaluating an ⊕e on the left component

eval-left : {A B : Set} {m n : ℕ} {eA : Enum A m} {eB : Enum B n} (i : Fin m) →
  select (eA ⊕e eB) (inject+ n i) ≡ inj₁ (select eA i)
eval-left {m = m} {n} {eA} {eB} i =
  let (fwd , iseq bwd _ _ bwd∘fwd~id) = Plus.fwd-iso {m} {n} in 
  begin (
    select (eA ⊕e eB) (inject+ n i)
      ≡⟨ refl ⟩ -- β reduce ⊕e, reverse-β Plus.fwd
    select (trans≃ (path⊎ eA eB) Plus.fwd-iso) (fwd (inj₁ i))
      ≡⟨ refl ⟩ -- expand qinv.g and trans≃
    select (path⊎ eA eB) (select (Plus.fwd-iso) (fwd (inj₁ i)))
      ≡⟨ refl ⟩ -- expand rhs
    select (path⊎ eA eB) ((bwd ∘ fwd) (inj₁ i))
      ≡⟨ cong (select (path⊎ eA eB)) (bwd∘fwd~id (inj₁ i)) ⟩
    select (path⊎ eA eB) (inj₁ i)
      ≡⟨ refl ⟩ -- by definition of path⊎
    inj₁ (select eA i) ∎)
  where open ≡-Reasoning

eval-right : {A B : Set} {m n : ℕ} {eA : Enum A m} {eB : Enum B n} →
  (i : Fin n) → select (eA ⊕e eB) (raise m i) ≡ inj₂ (select eB i)
eval-right {eA = eA} {eB} i = 
  cong (select (path⊎ eA eB)) (isequiv.β (proj₂ Plus.fwd-iso) (inj₂ i))

------------------------------------------------------------------------------
-- We can also do the same for multiplication but it's not needed

-- _⊛e_ : {A B : Set} {n m : ℕ} → Enum A n → Enum B m → Enum (A × B) (n * m)
-- eA ⊛e eB = trans≃ (path× eA eB) Times.fwd-iso
-- 
-- etc.

------------------------------------------------------------------------------
