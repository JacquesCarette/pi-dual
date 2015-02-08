{-# OPTIONS --without-K #-}

module ConcretePermutation where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; tabulate)
open import VecHelpers using (_!!_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import VecOps
open import Function using (_∘_)
open import RepresPerm
open import Equiv
open import Enumeration
open import Data.Product using (_,_)

infix 4 _∼p_

_∼p_ : {n : ℕ} (p₁ p₂ : Vec (Fin n) n) → Set
_∼p_ {n} p₁ p₂ = (i : Fin n) → p₁ !! i ≡ p₂ !! i

_∘̂_ : {n : ℕ} → Vec (Fin n) n → Vec (Fin n) n → Vec (Fin n) n
_∘̂_ {n} = F.scompcauchy

-- a concrete permutation has 4 components:
-- - the permutation
-- - its inverse
-- - and 2 proofs that it is indeed inverse
record CPerm (size : ℕ) : Set where
  constructor cp
  field
    π : Vec (Fin size) size
    πᵒ : Vec (Fin size) size
    αp : (π ∘̂ πᵒ) ∼p (F.idcauchy size)
    βp : (πᵒ ∘̂ π) ∼p (F.idcauchy size)

idp : ∀ {n} → CPerm n
idp {n} = cp (F.idcauchy n) (F.idcauchy n) {!!} {!!}

symp : ∀ {n} → CPerm n → CPerm n
symp (cp p₁ p₂ α β) = cp p₂ p₁ β α

-- the big (semantic) theorem.
-- note how we do need separate numerations for A and B.  They are very important!
thm2 : ∀ {A B : Set} → (e : Enum A) → (Enum B) → RPerm A B ≃ CPerm (Enum.n e)
thm2 {A} {B} (enum n A≃Fn) (enum m B≃Fm) = fwd , (mkqinv bwd {!!} {!!})  
  where
    fwd : RPerm A B → CPerm n
    fwd (rp (enum n₀ iso) (enum n₁ iso₁) iso₂) = cp (tabulate {!!}) {!!} {!!} {!!}

    bwd : CPerm n → RPerm A B
    bwd (cp p₁ p₂ αp βp) = rp (enum n {!!}) (enum n {!!}) {!!}
