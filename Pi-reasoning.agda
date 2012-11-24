{-# OPTIONS --no-termination-check #-}

module Pi-reasoning where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat 
open import Data.List
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Level hiding (suc)
open import Relation.Binary.Core
open import Algebra
import Algebra.FunctionProperties as FunctionProperties
open import Algebra.FunctionProperties.Core 
open import Algebra.Structures

open import Pi-abstract-machine

------------------------------------------------------------------------------
-- Decidable equality

-- normalize a type to a natural number 

size : B → ℕ
size ZERO = 0
size ONE = 1
size (PLUS b₁ b₂) = size b₁ + size b₂
size (TIMES b₁ b₂) = size b₁ * size b₂

-- normalize a value to a number

normalize : {b : B} → VB b → ℕ
normalize {ZERO} () 
normalize {ONE} unitB = 0
normalize {PLUS b₁ b₂} (inlB v) = normalize {b₁} v
normalize {PLUS b₁ b₂} (inrB v) = size b₁ + normalize {b₂} v
normalize {TIMES b₁ b₂} (pairB v₁ v₂) = size b₂ * normalize {b₁} v₁ + normalize {b₂} v₂

-- decidable equality of our values: normalize and compare the
-- underlying natural numbers. This is justified by the fact that the
-- natural numbers are a model of commutative semirings.

ℕ= : ℕ → ℕ → Bool
ℕ= 0 0 = true
ℕ= 0 _ = false
ℕ= _ 0 = false
ℕ= (suc m) (suc n) = ℕ= m n 

vb= : {b₁ b₂ : B} → (v₁ : VB b₁) → (v₂ : VB b₂) → Bool
vb= {b₁} {b₂} v₁ v₂ = ℕ= (normalize {b₁} v₁) (normalize {b₂} v₂)

-- generate all values of a type

values : (b : B) → List (VB b)
values ZERO = []
values ONE = [ unitB ]
values (PLUS b₁ b₂) = map inlB (values b₁) ++ map inrB (values b₂)
values (TIMES b₁ b₂) = concatMap (λ v₁ → map (pairB v₁) (values b₂)) (values b₁)

-- equality of combinators:
-- two combinators are equal if they map equal values to equal values

⟺=bool : {b₁ b₂ : B} → (b₁ ⟺ b₂) → (b₁ ⟺ b₂) → Bool
⟺=bool {b₁} {b₂} f g = 
  and (zipWith vb= (map (eval f) vs) (map (eval g) vs))
  where vs = values b₁

data _⟺=_ : {b₁ b₂ : B} → (b₁ ⟺ b₂) → (b₁ ⟺ b₂) → Set where
  id⟺= : {b₁ b₂ : B} → (f : b₁ ⟺ b₂) → (f ⟺= f) 
  check : {b₁ b₂ : B} → (f : b₁ ⟺ b₂) → (g : b₁ ⟺ b₂) → 
          T (⟺=bool f g) → (f ⟺= g) 

-- verifies that the given combinators relates the given values

data _s⟷_ : B → B → Set where
  sid⟷ : {b : B} {v₁ : VB b} {v₂ : VB b} {p : T (vb= (eval (iso id⟷) v₁) v₂)} → (b s⟷ b)

⟺=IsEquivalence : IsEquivalence _s⟷_
⟺=IsEquivalence = record { 
    refl = srefl ; 
    sym = {!!} ;
    trans = {!!} 
  } 
  where srefl : {b : B} {v : VB b} → b s⟷ b
        srefl {b} {v} = sid⟷ {b} {v} {v} {{!!}}

-- <-> : B -> B -> Set with constructors id : {b : B} -> (b <-> b)
-- IsEquivalence <->
--   refl = id

-- R= : B -> B -> Set with constructos 


------------------------------------------------------------------------------

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

BOOL = PLUS ONE ONE
test = ⟺= {BOOL} {BOOL} (iso swap₊ ◎ iso swap₊) (iso id⟷)

test1 : (iso swap₊) ⟺= (iso swap₊)
test1 = check
          {PLUS ONE ONE} {PLUS ONE ONE} 
          (iso swap₊) (iso swap₊)
          tt

The following does NOT typecheck which is good. Agda rejected my
nonsense claim that id is equivalent to swap+

test2 : (iso swap₊) ⟺= (iso id⟷)
test2 = check 
          {PLUS ONE ONE} {PLUS ONE ONE} 
          (iso swap₊) (iso id⟷)
          tt

--}
