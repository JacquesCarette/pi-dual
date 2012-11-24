{-# OPTIONS --no-termination-check #-}

module Pi-reasoning where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Nat 
open import Data.List
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Level hiding (suc)
open import Relation.Nullary
open import Relation.Binary
open import Algebra
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality as PropEq using(sym; trans)
import Algebra.FunctionProperties as FunctionProperties
-- open import Algebra.FunctionProperties
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
-- Note that we can't compare at different types so easily, they have
-- to have the same size, something not worth dealing with right now
vb= : {b : B} → (v₁ : VB b) → (v₂ : VB b) → Set
vb= {b} v₁ v₂ = (normalize {b} v₁) ≡ (normalize {b} v₂)

vb-Equivalence : {b : B} → IsEquivalence (vb= {b})
vb-Equivalence = record 
  { refl = refl
  ; sym = PropEq.sym
  ; trans = PropEq.trans }

vb== : {b : B} → Decidable {A = VB b} vb=
vb== {b} x y = (normalize {b} x) ≟ (normalize {b} y)

-- generate all normalized values of a type

values : (b : B) → List (VB b)
values ZERO = []
values ONE = [ unitB ]
values (PLUS b₁ b₂) = map inlB (values b₁) ++ map inrB (values b₂)
values (TIMES b₁ b₂) = concatMap (λ v₁ → map (pairB v₁) (values b₂)) (values b₁)

-- B is a Setoid

VB-is-Setoid : {b : B} → Setoid Level.zero Level.zero
VB-is-Setoid {b} = record 
  { Carrier = VB b
  ; _≈_ = vb=
  ; isEquivalence = vb-Equivalence
  }

-- equality of combinators:
-- two combinators are equal if they map equal values to equal values
-- best do this via proving that vb= generates a decidable equivalence
{-
⟺=bool : {b₁ b₂ : B} → (b₁ ⟺ b₂) → (b₁ ⟺ b₂) → Bool
⟺=bool {b₁} {b₂} f g = 
  and (zipWith vb= (map (eval f) vs) (map (eval g) vs))
  where vs = values b₁

data _⟺=_ : {b₁ b₂ : B} → (b₁ ⟺ b₂) → (b₁ ⟺ b₂) → Set where
  id⟺= : {b₁ b₂ : B} → (f : b₁ ⟺ b₂) → (f ⟺= f) 
  sym⟺= : {b₁ b₂ : B} → (f : b₁ ⟺ b₂) → (g : b₁ ⟺ b₂) → ( f ⟺= g ) → (g ⟺= f) 


⟺=IsEquivalence : {b₁ b₂ : B} → IsEquivalence (_⟺=_ {b₁} {b₂})
⟺=IsEquivalence {b₁} {b₂} = record {
    refl = λ {f : b₁ ⟺ b₂} → id⟺= {b₁} {b₂} f ;
    sym = λ {f : b₁ ⟺ b₂} {g : b₁ ⟺ b₂} h  → sym⟺= f g h ;
    trans = λ f g → {!!} 
  } 
-}
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
