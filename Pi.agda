module Pi where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Relation.Binary.HeterogeneousEquality.Core

-- First we define a universe of our value types

data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

bval : B → Set
bval ZERO          = ⊥
bval ONE           = ⊤
bval (PLUS b1 b2)  = bval b1 ⊎ bval b2
bval (TIMES b1 b2) = bval b1 × bval b2

-- Examples

unit_π : bval ONE
unit_π = tt

BOOL : B
BOOL = PLUS ONE ONE

true_π : bval BOOL
true_π = inj₁ tt

false_π : bval BOOL
false_π = inj₂ tt

-- Now we define our type of equivalences

infixr 1 _⟷_

data _⟷_ : B → B → Set where
  ZEROE : { b : B } → PLUS ZERO b ⟷ b

-- comb : { b₁ b₂ : B } → b₁ ⟷ b₂ → bval b₁ ≅ bval b₂
-- comb (ZEROE { b }) = {!!} 

