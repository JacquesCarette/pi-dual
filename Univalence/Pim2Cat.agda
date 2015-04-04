{-# OPTIONS --without-K #-}

module Pim2Cat where

open import Level using () renaming (zero to lzero)
open import Data.Unit
open import Relation.Binary.Core using (IsEquivalence)
import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.PropositionalEquality.Core as PE

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric

------------------------------------------------------------------------------
-- Level -2 of Pi: we treat U as a singleton; there is at least one
-- type and all the types are equal; there is not even a notion of
-- equality of morphims other than identity

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

triv⟷ : (t₁ t₂ : U) → Set
triv⟷ _ _ = ⊤

triv⟷Equiv : {t₁ t₂ : U} → IsEquivalence triv⟷
triv⟷Equiv = record 
  { refl = tt
  ; sym = λ _ → tt
  ; trans = λ _ _ → tt
  }

-- It is a category...

PiCat : Category lzero lzero lzero
PiCat = record
  { Obj = U
  ; _⇒_ = triv⟷
  ; _≡_ = PE._≡_
  ; id = tt
  ; _∘_ = λ _ _ → tt
  ; assoc = PE.refl
  ; identityˡ = PE.refl
  ; identityʳ = PE.refl 
  ; equiv = PE.isEquivalence
  ; ∘-resp-≡ = λ _ _ → PE.refl
  }

------------------------------------------------------------------------------
