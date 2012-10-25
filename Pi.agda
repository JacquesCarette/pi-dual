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

⟦_⟧ : B → Set
⟦ ZERO ⟧         = ⊥
⟦ ONE ⟧          = ⊤
⟦ PLUS b1 b2 ⟧  = ⟦ b1 ⟧ ⊎ ⟦ b2 ⟧
⟦ TIMES b1 b2 ⟧ = ⟦ b1 ⟧ × ⟦ b2 ⟧

-- Examples

unit_π : ⟦ ONE ⟧
unit_π = tt

BOOL : B
BOOL = PLUS ONE ONE

true_π : ⟦ BOOL ⟧
true_π = inj₁ tt

false_π : ⟦ BOOL ⟧
false_π = inj₂ tt

-- Now we define another universe for our equivalences. First the codes for
-- equivalences.

infixr 1 _⟷_

data _⟷_ : B → B → Set where
  unit₊ : { b : B } → PLUS ZERO b ⟷ b
  swap₊ : { b₁ b₂ : B } → PLUS b₁ b₂ ⟷ PLUS b₂ b₁

-- Now we define the semantic notion of equivalence

infixr 1 _⟺_

record _⟺_ (b₁ b₂ : B) : Set where 
 field
  f₁₂ : ⟦ b₁ ⟧ → ⟦ b₂ ⟧
  f₂₁ : ⟦ b₂ ⟧ → ⟦ b₁ ⟧
  p₁  : { x : ⟦ b₁ ⟧ } → f₂₁ (f₁₂ x) ≡ x
  p₂  : { x : ⟦ b₂ ⟧ } → f₁₂ (f₂₁ x) ≡ x


-- And finally we map each code to an actual equivalance

iso : { b₁ b₂ : B } → b₁ ⟷ b₂ → b₁ ⟺ b₂

iso unit₊ = 
  record { 
    f₁₂ = zeroe ;
    f₂₁ = zeroi ; 
    p₁ = zeroeip ;
    p₂ = refl 
  }
  where 
    zeroe : {A : Set} → ⊥ ⊎ A → A
    zeroe (inj₁ ())
    zeroe (inj₂ v) = v
    zeroi : {A : Set} → A → ⊥ ⊎ A
    zeroi v = inj₂ v
    zeroeip : { A : Set } { x : ⊥ ⊎ A } → zeroi (zeroe x) ≡ x
    zeroeip { x = inj₁ () }
    zeroeip { x = inj₂ v } = refl

iso swap₊ = 
  record { 
    f₁₂ = sw ;
    f₂₁ = sw ;
    p₁ = swp ; 
    p₂ = swp 
  }
  where 
    sw : {A₁ A₂ : Set} → A₁ ⊎ A₂ → A₂ ⊎ A₁
    sw (inj₁ v) = inj₂ v
    sw (inj₂ v) = inj₁ v
    swp : { A₁ A₂ : Set } → { x : A₁ ⊎ A₂ } → sw (sw x) ≡ x
    swp { x = inj₁ v } = refl
    swp { x = inj₂ v } = refl

