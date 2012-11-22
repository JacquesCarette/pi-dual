{-# OPTIONS --no-termination-check #-}

module Pi-reasoning where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat 
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

open import Pi-abstract-machine

------------------------------------------------------------------------------
-- Decidable equality

--
-- normalize a type to a natural number 

size : B → ℕ
size ZERO = 0
size ONE = 1
size (PLUS b₁ b₂) = size b₁ + size b₂
size (TIMES b₁ b₂) = size b₁ * size b₂

-- normalize a value to a number

normalize : {b : B} → VB b → ℕ
normalize {ZERO} () 
normalize {ONE} unitB = zero
normalize {PLUS b₁ b₂} (inlB v) = normalize {b₁} v
normalize {PLUS b₁ b₂} (inrB v) = size b₁ + normalize {b₂} v
normalize {TIMES b₁ b₂} (pairB v₁ v₂) = size b₂ * normalize {b₁} v₁ + normalize {b₂} v₂

{--
testT = PLUS ONE (PLUS ONE ONE)
test1 = normalize {testT} (inlB unitB)
test2 = normalize {testT} (inrB (inlB unitB))
test3 = normalize {testT} (inrB (inrB unitB))

testT = PLUS ZERO (PLUS ONE ONE)
test1 = normalize {testT} (inrB (inlB unitB))
test2 = normalize {testT} (inrB (inrB unitB))

testT = TIMES (PLUS ONE ONE) ZERO
test1 = size testT

testT = TIMES (PLUS ONE ONE) (PLUS ONE (PLUS ONE ONE))
test1 = normalize {testT} (pairB (inlB unitB) (inlB unitB))
test2 = normalize {testT} (pairB (inrB unitB) (inlB unitB))
test3 = normalize {testT} (pairB (inlB unitB) (inrB (inlB unitB)))
test4 = normalize {testT} (pairB (inrB unitB) (inrB (inlB unitB)))
test5 = normalize {testT} (pairB (inlB unitB) (inrB (inrB unitB)))
test6 = normalize {testT} (pairB (inrB unitB) (inrB (inrB unitB)))

--}

-- decidable equality of our values: normalize and compare the
-- underlying natural numbers

ℕ= : ℕ → ℕ → Bool
ℕ= zero zero = true
ℕ= zero _ = false
ℕ= _ zero = false
ℕ= (suc m) (suc n) = ℕ= m n 

b= : {b₁ b₂ : B} → (v₁ : VB b₁) → (v₂ : VB b₂) → Bool
b= {b₁} {b₂} v₁ v₂ = ℕ= (normalize {b₁} v₁) (normalize {b₂} v₂)

------------------------------------------------------------------------------
