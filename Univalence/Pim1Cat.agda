{-# OPTIONS --without-K #-}

module Pim1Cat where

open import Level using () renaming (zero to lzero)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.Core using (Reflexive; IsEquivalence)

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric

------------------------------------------------------------------------------
-- Level -1 of Pi: We are treating U as a mere proposition: any two
-- elements of it are equal; in contrast to level -2, there is a
-- notion of equality of morphisms but it is trivial

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

triv≡ : {t₁ t₂ : U} → (f g : triv⟷ t₁ t₂) → Set
triv≡ _ _ = ⊤

triv≡Equiv : {t₁ t₂ : U} → IsEquivalence (triv≡ {t₁} {t₂})
triv≡Equiv = record 
  { refl = tt
  ; sym = λ _ → tt
  ; trans = λ _ _ → tt
  }

-- It is a category...

PiCat : Category lzero lzero lzero
PiCat = record
  { Obj = U
  ; _⇒_ = triv⟷
  ; _≡_ = λ {t₁} {t₂} → triv≡ {t₁} {t₂}
  ; id = tt
  ; _∘_ = λ _ _ → tt
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; equiv = λ {t₁} {t₂} → triv≡Equiv {t₁} {t₂}
  ; ∘-resp-≡ = λ _ _ → tt
  }

