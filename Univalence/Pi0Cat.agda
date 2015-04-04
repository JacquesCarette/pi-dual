{-# OPTIONS --without-K #-}

module Pi0Cat where

-- Proving that Pi with trivial 2 paths structure is a symmetric rig groupoid

open import Level using () renaming (zero to lzero)
open import Data.Unit
open import Relation.Binary.Core using (IsEquivalence)

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric

open import PiLevel0 using (U; _⟷_; id⟷; _◎_)

------------------------------------------------------------------------------
-- Trivial equivalence; equates all morphisms of the same type so for
-- example id and not : BOOL ⟷ BOOL are equated

triv≡ : {t₁ t₂ : U} → (f g : t₁ ⟷ t₂) → Set
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
  ; _⇒_ = _⟷_
  ; _≡_ = triv≡ 
  ; id = id⟷
  ; _∘_ = λ y⟷z x⟷y → x⟷y ◎ y⟷z 
  ; assoc = tt 
  ; identityˡ = tt 
  ; identityʳ = tt 
  ; equiv = triv≡Equiv 
  ; ∘-resp-≡ = λ _ _ → tt 
  }

------------------------------------------------------------------------------

