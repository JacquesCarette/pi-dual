{-# OPTIONS --without-K #-}

module PiLevel1Alternative where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Vec

open import FinVec
open F

open import ConcretePermutation

------------------------------------------------------------------------------
-- Equivalences between permutations
-- Objects are level 0 permutations ⟷
-- Morphisms are equivalences between these permutations

factorial : ℕ → ℕ
factorial 0 = 1
factorial (suc n) = n * factorial n

record EquivBetweenPerm {values : ℕ} {size : ℕ} (p₁ p₂ : CPerm  values size) : Set where
  constructor ebp
  module p₁ = CPerm p₁
  module p₂ = CPerm p₂
  field
    -- first we have a permutation on the underlying finite sets
    π  : FinVec values size
    πᵒ : FinVec size values
    αp : π ∘̂ πᵒ ≡ F.1C
    βp : πᵒ ∘̂ π ≡ F.1C
    -- then we have a permutation on these maps are consistent with p₁.π, p₂.π, etc.
    ππ : Vec (FinVec values size) (factorial size) -- ??? NO
    -- and so on
    -- and apply

{--
Ex: the two underlying permutations p₁ and p₂ are:
    values = {A,B,C}
    size = 3
    p₁.π = { A <=> C, B <=> A, C <=> B } represented as {C,A,B}
    p₂.π = { A <=> C, B <=> A, C <=> B } represented as {C,A,B}

    one equivalence between these permutations is 'id'; another has:
    π = { A <=> B, B <=> C, C <=> A }
    ππ = { (A <=> C) <=> (B <=> A), 
           (B <=> A) <=> (C <=> B), 
           (C <=> B) <=> (A <=> C) }
       represented as p₁.πᵒ ???
--}

------------------------------------------------------------------------------

