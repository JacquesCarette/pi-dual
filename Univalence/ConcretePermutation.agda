{-# OPTIONS --without-K #-}

module ConcretePermutation where

open import Level renaming (zero to lzero) hiding (suc)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; inject+; fromℕ)
open import Data.Vec using (Vec; tabulate; allFin; []; _∷_)
open import Data.Vec.Properties using (tabulate∘lookup)

open import Function using (_∘_)
open import Relation.Binary using (Setoid) 
open import Relation.Binary.PropositionalEquality using (_≡_; setoid)

--

open import Proofs using (
  -- VectorLemmas
   _!!_
   )

------------------------------------------------------------------------------
-- A concrete permutation has 4 components:
-- - the one-line notation for a permutation
-- - the one-line notation for the inverse permutation
-- - and 2 proofs that these are indeed inverses

-- One-line notation for permutations with identity and composition

FinVec : ℕ → ℕ → Set
FinVec m n = Vec (Fin m) n

1C : {n : ℕ} → FinVec n n
1C {n} = allFin n

_∘̂_ : {n₀ n₁ n₂ : ℕ} → Vec (Fin n₁) n₀ → Vec (Fin n₂) n₁ → Vec (Fin n₂) n₀
π₁ ∘̂ π₂ = tabulate (_!!_ π₂ ∘ _!!_ π₁)

-- Actual permutation

record CPerm (values : ℕ) (size : ℕ) : Set where
  constructor cp
  field
    π  : FinVec values size
    πᵒ : FinVec size values
    αp : π ∘̂ πᵒ ≡ 1C
    βp : πᵒ ∘̂ π ≡ 1C

------------------------------------------------------------------------------
-- We can compare concrete permutations for equality using _≡_
-- It is actually sufficient to compare just the forward π using _≡_

-- The set of permutations under _≡_

SCPerm : ℕ → ℕ → Setoid lzero lzero
SCPerm m n = setoid (CPerm m n)

-- This is just tabulate∘lookup, but it hides the details; should this
-- be called 'join' or 'flatten' ?

cauchyext : {m n : ℕ} (π : FinVec m n) → tabulate (_!!_ π) ≡ π
cauchyext π = tabulate∘lookup π

------------------------------------------------------------------------------
-- I always mix up which way the permutation works. Here is a small
-- example to serve as a reminder:

-- values

0₅ 1₅ 2₅ 3₅ 4₅ : Fin 5
0₅ = zero
1₅ = inject+ 3 (fromℕ 1)
2₅ = inject+ 2 (fromℕ 2)
3₅ = inject+ 1 (fromℕ 3)
4₅ = fromℕ 4

-- indices

0₃ 1₃ 2₃ : Fin 3
0₃ = zero
1₃ = inject+ 1 (fromℕ 1)
2₃ = fromℕ 2

πex : FinVec 5 3
πex = 4₅ ∷ 3₅ ∷ 2₅ ∷ [] 

fex : Fin 3 → Fin 5
fex i = πex !! i

-- fex 0₃ => 4₅
-- fex 1₃ => 3₅
-- fex 2₃ => 2₅

------------------------------------------------------------------------------

