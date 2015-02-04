-- Definition of the Operations on permutations, based on the Vector representation
-- There are 2 sets of definitions here:
-- 1. pure Vector, in which the contents are arbitrary sets
-- 2. specialized to Fin contents.

-- Some notes:
--   - There are operations (such as sequential composition) which 'lift' more
--     awkwardly.
--   - To avoid a proliferation of bad names, we use sub-modules

module VecOps where

open import Data.Nat
open import Data.Vec renaming (map to mapV; _++_ to _++V_; concat to concatV)
open import Data.Fin using (Fin; inject+; raise; inject≤; fromℕ; toℕ)
open import Function using (id; _∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import TypeEquivalences
open import VectorLemmas
open import LeqLemmas
open import FinEquiv using (module Plus)

------------------------------------------------------------------------------
module V where
  pcomp : ∀ {m n} {A B : Set} → Vec A m → Vec B n → Vec (A ⊎ B) (m + n)
  pcomp α β = tabulate (inj₁ ∘ _!!_ α) ++V tabulate (inj₂ ∘ _!!_ β)

  swap+ : {m n : ℕ} {A B : Set} → Vec (A ⊎ B) (m + n) → Vec (B ⊎ A) (m + n)
  swap+ v = tabulate (swap₊ ∘ _!!_ v)

------------------------------------------------------------------------------
-- Elementary permutations, Fin version

module F where
  -- convenient abbreviation
  Cauchy : ℕ → ℕ → Set
  Cauchy m n = Vec (Fin m) n
  
  idcauchy : (n : ℕ) → Cauchy n n
  idcauchy = allFin

  -- Sequential composition
  scompcauchy : ∀ {n₀ n₁ n₂} → Cauchy n₁ n₀ → Cauchy n₂ n₁ → Cauchy n₂ n₀
  scompcauchy π₁ π₂ = tabulate (_!!_ π₂ ∘ _!!_ π₁)
    -- tabulate (λ i → π₂ !! (π₁ !! i))

  -- swap the first m elements with the last n elements
  -- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
  -- ==>
  -- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

  swap+cauchy : (m n : ℕ) → Cauchy (n + m) (m + n)
  swap+cauchy m n = tabulate (Plus.swapper m n)

  -- Parallel additive composition
  -- append both permutations but adjust the indices in the second
  -- permutation by the size of the first type so that it acts on the
  -- second part of the vector

  pcompcauchy : ∀ {m₁ n₁ m₂ n₂} → Cauchy m₁ m₂ → Cauchy n₁ n₂ → Cauchy (m₁ + n₁) (m₂ + n₂)
  pcompcauchy α β = mapV Plus.fwd (V.pcomp α β)

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

  transposeIndex : (m n : ℕ) → (b : Fin m) → (d : Fin n) → Fin (n * m)
  transposeIndex m n b d =
     inject≤ (fromℕ (toℕ d * m + toℕ b))
       (i*n+k≤m*n d b)
 {- inject≤
   (fromℕ (toℕ d * m + toℕ b))
   (trans≤ (i*n+k≤m*n d b) (refl′ (*-comm n m))) -}

  swap⋆cauchy : (m₁ n₁ m₂ n₂ : ℕ) → (meq : m₂ ≡ m₁) → (neq : n₂ ≡ n₁) →
         Cauchy (n₁ * m₁) (n₂ * m₂)
  swap⋆cauchy m₁ n₁ m₂ n₂ meq neq =
   concatV (mapV
             (λ d → mapV (λ b → transposeIndex m₁ n₁ (subst Fin meq b) (subst Fin neq d)) (allFin m₂))
             (allFin n₂))
