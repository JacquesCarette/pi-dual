{-# OPTIONS --without-K #-}

module P where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

-- For now, a groupoid is just a set

Groupoid : Set₁
Groupoid = Set

mutual 

-- types
  data B : Set where
    ZERO : B 
    ONE : B
    _+_ : B → B → B
    _*_ : B → B → B
    _~_ : {b : B} → ⟦ b ⟧ → ⟦ b ⟧ → B

-- values
  ⟦_⟧ : B → Groupoid
  ⟦ ZERO ⟧ = ⊥
  ⟦ ONE ⟧ = ⊤
  ⟦ b₁ + b₂ ⟧ = ⟦ b₁ ⟧ ⊎ ⟦ b₂ ⟧
  ⟦ b₁ * b₂ ⟧ = ⟦ b₁ ⟧ × ⟦ b₂ ⟧
  ⟦ v₁ ~ v₂ ⟧ = v₁ ≡ v₂

-- pointed types
data PB : Set where
  POINTED : Σ B (λ b → ⟦ b ⟧) → PB
  RECIP : PB → PB 

-- lift B type constructors to pointed types

_++_ : PB → PB → PB
(POINTED (b₁ , v₁)) ++ (POINTED (b₂ , v₂)) = POINTED (b₁ + b₂ , inj₁ v₁)
_ ++ _ = {!!}

_**_ : PB → PB → PB
(POINTED (b₁ , v₁)) ** (POINTED (b₂ , v₂)) = POINTED (b₁ * b₂ , (v₁ , v₂))
_ ** _ = {!!}

-- All the pi combinators now work on pointed types

data _⟷_ : PB → PB → Set₁ where
  swap⋆ : {pb₁ pb₂ : PB} → (pb₁ ** pb₂) ⟷ (pb₂ ** pb₁)
  eta : {pb : PB} → POINTED (ONE , tt) ⟷ RECIP pb

-- induction principle to reason about identities; needed ???

ind : {b : B} → 
      (C : (v₁ v₂ : ⟦ b ⟧) → (p : ⟦ _~_ {b} v₁ v₂ ⟧) → Set) → 
      (c : (v : ⟦ b ⟧) → C v v refl) → 
      (v₁ v₂ : ⟦ b ⟧) → (p : ⟦ _~_ {b} v₁ v₂ ⟧) → C v₁ v₂ p
ind C c v .v refl = c v

-- Examples

Bool : B
Bool = ONE + ONE

false : ⟦ Bool ⟧
false = inj₁ tt

true : ⟦ Bool ⟧
true = inj₂ tt

pb1 : PB
pb1 = POINTED (Bool , false)

pb2 : PB
pb2 = POINTED (Bool , true)

FalseID : B
FalseID = _~_ {Bool} false false

pb3 : PB 
pb3 = POINTED (FalseID , refl)

FalseID^2 : B
FalseID^2 = _~_ {FalseID} refl refl

pb4 : PB
pb4 = POINTED (FalseID^2 , refl)

------------------------------------------------------------------------------


