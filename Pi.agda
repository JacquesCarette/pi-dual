module Pi where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

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

-- Now we define another universe for our equivalences. First the codes for
-- equivalences.

infixr 1 _⟷_

data _⟷_ : B → B → Set where
  ZEROE : { b : B } → PLUS ZERO b ⟷ b

-- Now we define the semantic notion of equivalence

infixr 1 _⟺_

record _⟺_ (b₁ b₂ : B) : Set where 
 field
  f₁₂ : bval b₁ → bval b₂
  f₂₁ : bval b₂ → bval b₁
  p₁  : f₁₂ ∘ f₂₁ ≡ id
  p₂  : f₁₂ ∘ f₂₁ ≡ id


-- And finally we map each code to an actual equivalance

comb : { b₁ b₂ : B } → b₁ ⟷ b₂ → b₁ ⟺ b₂
comb (ZEROE { b }) = 
  record { 
    f₁₂ = left ;
    f₂₁ = right ; 
    p₁ = refl ;
    p₂ = refl 
  }
  where 
    left : { A : Set } → ⊥ ⊎ A → A
    left (inj₁ ())
    left (inj₂ v) = v

    right : { A : Set } → A → ⊥ ⊎ A
    right v = inj₂ v
