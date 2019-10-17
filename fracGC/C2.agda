{-# OPTIONS --without-K #-}

module C2 where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Rational
  using (ℚ; _/_; _+_; _*_; _≢0)
  renaming (1/_ to recip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product -- using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Core using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; module ≡-Reasoning)
open import Category.Comonad

-- infix  30 _⟷_
-- infixr 50 _◎_

------------------------------------------------------------------------------
-- Level 1 of Pi extended with fractionals comonad

record Pointed (A : Set) : Set where
  constructor ⇑
  field
    ● : A

open Pointed

data U : Set
data U● : Set

data U where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U
  EXTRACT : U● → U

data U● where
  RETURN  : U → U● 
  RECIP   : U● → U●

⟦_⟧ : (A : U) → Set × ℚ
⟦_⟧● : (A : U●) → Set × (Σ[ p ∈  ℚ ] (∣ ℚ.numerator p ∣ ≢0))

⟦ ZERO ⟧ = ⊥ , + 0 / 1
⟦ ONE ⟧ = ⊤ , + 1 / 1
⟦ PLUS t₁ t₂ ⟧ with ⟦ t₁ ⟧ | ⟦ t₂ ⟧
... | S₁ , n₁ | S₂ , n₂ = (S₁ ⊎ S₂) , (n₁ + n₂)
⟦ TIMES t₁ t₂ ⟧ with ⟦ t₁ ⟧ | ⟦ t₂ ⟧
... | S₁ , n₁ | S₂ , n₂ = (S₁ × S₂) , (n₁ * n₂)
⟦ EXTRACT t ⟧ with ⟦ t ⟧●
... | S , n , _ = S , n

⟦ RETURN ZERO ⟧● = {!!}
⟦ RETURN ONE ⟧● = {!!}
⟦ RETURN (PLUS A A₁) ⟧● = {!!}
⟦ RETURN (TIMES A A₁) ⟧● = {!!}
⟦ RETURN (EXTRACT x) ⟧● = {!!} 
⟦ RECIP A ⟧● = {!!} 


------------------------------------------------------------------------------

{--
record Set• : Set₁ where
  constructor •[_,_]
  field
    ∣_∣ : Set
    • : ∣_∣

⊤• : Set• 
⊤• = •[ ⊤ , tt ]
--}

------------------------------------------------------------------------------
