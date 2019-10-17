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

------------------------------------------------------------------------------

{--
⟦_⟧ : (A : U) → Set
⟦ ZERO ⟧ = ⊥ 
⟦ ONE ⟧ = ⊤
⟦ PLUS t₁ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ U ⟧ = ? 

record Set• : Set₁ where
  constructor •[_,_]
  field
    ∣_∣ : Set
    • : ∣_∣

⊤• : Set• 
⊤• = •[ ⊤ , tt ]
--}

------------------------------------------------------------------------------
