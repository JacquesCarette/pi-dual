{-# OPTIONS --without-K #-}

-- this is mostly reference for an unused intermediate step.
module Cauchy2 where

open import Data.Nat
open import Data.Vec renaming (map to mapV; _++_ to _++V_; concat to concatV)
open import Data.Fin using (Fin; inject+; raise; inject≤; fromℕ; toℕ)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import VectorLemmas
open import LeqLemmas
open import Cauchy using (id+)

Cauchy : ℕ → ℕ → Set
Cauchy n₁ n₂ = Vec (Fin n₁) n₂

------------------------------------------------------------------------------
-- Elementary permutations in the Cauchy representation

emptycauchy : Cauchy 0 0
emptycauchy = []

idcauchy : (n : ℕ) → Cauchy n n
idcauchy = allFin

-- Sequential composition

scompcauchy : ∀ {n₀ n₁ n₂} → Cauchy n₁ n₀ → Cauchy n₂ n₁ → Cauchy n₂ n₀
scompcauchy {n} perm₁ perm₂ =
 tabulate (λ i → lookup (lookup i perm₁) perm₂)

-- swap the first m elements with the last n elements
-- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
-- ==>
-- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

swap+cauchy : (m n : ℕ) → Cauchy (m + n) (n + m)
swap+cauchy m n = {!!} -- tabulate swapper

-- Parallel additive composition
-- append both permutations but adjust the indices in the second
-- permutation by the size of the first type so that it acts on the
-- second part of the vector

pcompcauchy : ∀ {m₁ n₁ m₂ n₂} → Cauchy m₁ m₂ → Cauchy n₁ n₂ → Cauchy (m₁ + n₁) (m₂ + n₂)
pcompcauchy {m} {n} α β = mapV (inject+ n) α ++V mapV (raise m) β

-- Tensor multiplicative composition
-- Transpositions in α correspond to swapping entire rows
-- Transpositions in β correspond to swapping entire columns
tcompcauchy : ∀ {m₁ n₁ m₂ n₂} → Cauchy m₁ m₂ → Cauchy n₁ n₂ → Cauchy (m₁ * n₁) (m₂ * n₂)
tcompcauchy {m} {n} α β =
 concatV
   (mapV
     (λ b →
        mapV (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)) β)
     α)

-- swap⋆
-- 
-- This is essentially the classical problem of in-place matrix transpose:
-- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
-- Given m and n, the desired permutation in Cauchy representation is:
-- P(i) = m*n-1 if i=m*n-1
--      = m*i mod m*n-1 otherwise

transposeIndex : (m n : ℕ) →
      (b : Fin m) → (d : Fin n) → Fin (n * m)
transposeIndex m n b d =
   inject≤ (fromℕ (toℕ d * m + toℕ b))
     (i*n+k≤m*n d b)
 {- inject≤
   (fromℕ (toℕ d * m + toℕ b))
   (trans≤ (i*n+k≤m*n d b) (refl′ (*-comm n m))) -}

swap⋆cauchy : (m₁ n₁ m₂ n₂ : ℕ) → (meq : m₂ ≡ m₁) → (neq : n₂ ≡ n₁) → Cauchy (n₁ * m₁) (n₂ * m₂)
swap⋆cauchy m₁ n₁ m₂ n₂ meq neq =
 concatV (mapV
           (λ d → mapV (λ b → transposeIndex m₁ n₁ (subst Fin meq b) (subst Fin neq d)) (allFin m₂))
           (allFin n₂))
