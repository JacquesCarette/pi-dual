{-# OPTIONS --without-K #-}

module Cauchy where

-- Definitions for permutations in the Cauchy representation

open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; suc; _+_; _*_) 
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; 
         raise; inject+; inject₁; inject≤; _≻toℕ_)
open import Data.Vec 
  using (Vec; tabulate; []; _∷_; lookup; allFin)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)

open import Proofs

------------------------------------------------------------------------------
-- Semantic representations of permutations

-- One possibility of course is to represent them as functions but
-- this is a poor representation and eventually requires function
-- extensionality. 

-- Representation III
-- This is the 2 line Cauchy representation. The first line is in
-- canonical order and implicit in the indices of the vector

Cauchy : ℕ → Set
Cauchy n = Vec (Fin n) n


------------------------------------------------------------------------------
-- Elementary permutations in the Cauchy representation 

emptycauchy : Cauchy 0
emptycauchy = []

idcauchy : (n : ℕ) → Cauchy n
idcauchy = allFin 

-- Sequential composition

scompcauchy : ∀ {n} → Cauchy n → Cauchy n → Cauchy n
scompcauchy {n} perm₁ perm₂ = 
  tabulate (λ i → lookup (lookup i perm₁) perm₂)

-- swap the first m elements with the last n elements
-- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
-- ==> 
-- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

swap+cauchy : (m n : ℕ) → Cauchy (m + n)
swap+cauchy m n = 
  subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
    (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))

-- Parallel additive composition 
-- append both permutations but adjust the indices in the second
-- permutation by the size of the first type so that it acts on the
-- second part of the vector

pcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m + n)
pcompcauchy {m} {n} α β = mapV (inject+ n) α ++V mapV (raise m) β

-- Tensor multiplicative composition
-- Transpositions in α correspond to swapping entire rows
-- Transpositions in β correspond to swapping entire columns

tcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m * n)
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
       (b : Fin m) → (d : Fin n) → Fin (m * n)
transposeIndex m n b d =
  inject≤
    (fromℕ (toℕ d * m + toℕ b))
    (trans≤ (i*n+k≤m*n d b) (refl′ (*-comm n m)))

swap⋆cauchy : (m n : ℕ) → Cauchy (m * n)
swap⋆cauchy m n =
  concatV (mapV
            (λ b → mapV (λ d → transposeIndex m n b d) (allFin n))
            (allFin m))

------------------------------------------------------------------------------
