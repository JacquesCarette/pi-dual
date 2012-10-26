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

-- Now we define another universe for our equivalences. First the codes for
-- equivalences.

infixr 30 _⟷_

data _⟷_ : B → B → Set where
  id⟷   : { b : B } → b ⟷ b
  unit₊ : { b : B } → PLUS ZERO b ⟷ b
  swap₊ : { b₁ b₂ : B } → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  _◎_ : { a b c : B } → a ⟷ b → b ⟷ c → a ⟷ c

-- NOW WE DEFINE THE SEMANTIC NOTION OF EQUIVALENCE

infixr 30 _⟺_

infixr 20 _⊙_
infixr 20 _◎_

record _⟺_ (b₁ b₂ : B) : Set where 
  constructor equiv
  field
    f₁₂ : ⟦ b₁ ⟧ → ⟦ b₂ ⟧
    f₂₁ : ⟦ b₂ ⟧ → ⟦ b₁ ⟧
    p₁  : ∀ { x : ⟦ b₁ ⟧ } → f₂₁ (f₁₂ x) ≡ x
    p₂  : ∀ { x : ⟦ b₂ ⟧ } → f₁₂ (f₂₁ x) ≡ x

open _⟺_ public

lem-⟺-inv : ∀{A B C : Set }(g₁₂ : A → B )(g₂₁ : B → A)
  (g₂₃ : B → C)(g₃₂ : C → B) →
     (∀ {x : B } → g₁₂ (g₂₁ x) ≡ x) → ({y : C } → g₂₃ (g₃₂ y) ≡ y ) →
     (∀ {z} → g₂₃ (g₁₂ (g₂₁ (g₃₂ z))) ≡ z)
lem-⟺-inv g₁₂ g₂₁ g₂₃ g₃₂ p₁ p₂ {z = z} = trans p p₂ 
  where w = g₁₂ (g₂₁ (g₃₂ z))
        p = cong g₂₃ {w} p₁
 
_⊙_ : {b₁ b₂ b₃ : B} → b₁ ⟺ b₂ → b₂ ⟺ b₃ → b₁ ⟺ b₃
r ⊙ s = equiv (λ x → f₁₂ s ( f₁₂ r x)) (λ x → f₂₁ r ( f₂₁ s x))
              (lem-⟺-inv (f₂₁ s) (f₁₂ s) (f₂₁ r) (f₁₂ r) (p₁ s) (p₁ r)) 
              (lem-⟺-inv (f₁₂ r) (f₂₁ r) (f₁₂ s) (f₂₁ s) (p₂ r) (p₂ s)) 

-- THESE ARE NEEDED MULTIPLE TIMES, FACTOR OUT
zeroe : {A : Set} → ⊥ ⊎ A → A
zeroe (inj₁ ())
zeroe (inj₂ V) = V

zeroi : {A : Set} → A → ⊥ ⊎ A
zeroi v = inj₂ v

zeroeip : { A : Set } { x : ⊥ ⊎ A } → zeroi (zeroe x) ≡ x
zeroeip { x = inj₁ () }
zeroeip { x = inj₂ v } = refl

sw : {A₁ A₂ : Set} → A₁ ⊎ A₂ → A₂ ⊎ A₁
sw (inj₁ v) = inj₂ v
sw (inj₂ v) = inj₁ v

swp : { A₁ A₂ : Set } → { x : A₁ ⊎ A₂ } → sw (sw x) ≡ x
swp { x = inj₁ v } = refl
swp { x = inj₂ v } = refl

-- And finally we map each code to an actual equivalence
iso : { b₁ b₂ : B } → b₁ ⟷ b₂ → b₁ ⟺ b₂

iso id⟷ = equiv id id refl refl
iso (f ◎ g) = (iso f) ⊙ (iso g)
iso unit₊ = equiv zeroe zeroi zeroeip refl 
iso swap₊ = equiv sw sw swp swp
 
-- Examples

unit_π : ⟦ ONE ⟧
unit_π = tt

BOOL : B
BOOL = PLUS ONE ONE

true_π : ⟦ BOOL ⟧
true_π = inj₁ tt

false_π : ⟦ BOOL ⟧
false_π = inj₂ tt

