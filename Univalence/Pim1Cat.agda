{-# OPTIONS --without-K #-}

module Pim1Cat where

open import Level using () renaming (zero to lzero)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Nat
open import Relation.Nullary.Core using (yes; no)
open import Relation.Binary.Core using (Reflexive; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (refl; sym)

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric

------------------------------------------------------------------------------
-- Level -1 of Pi

-- U is a collection of types.
--
-- Between any two types, there is either no identification or exactly
-- one identification: the most sensible thing to do is to identify
-- all the empty types in one cluster; identify all the non-empty
-- types in another cluster; and have NO identifications between the
-- two clusters

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

toℕ : U → ℕ
toℕ ZERO = 0
toℕ ONE = 1
toℕ (PLUS t₁ t₂) = toℕ t₁ + toℕ t₂
toℕ (TIMES t₁ t₂) = toℕ t₁ * toℕ t₂ 

bool⟷ : (t₁ t₂ : U) → Set
bool⟷ t₁ t₂ with toℕ t₁ ≟ toℕ t₂
... | yes _ = ⊤ 
... | no _ = ⊥

refl⟷ : (t : U) → bool⟷ t t
refl⟷ t with toℕ t ≟ toℕ t
... | yes _ = tt
... | no p = p refl 

sym⟷ : (s t : U) → bool⟷ s t → bool⟷ t s
sym⟷ s t eq with toℕ s ≟ toℕ t | toℕ t ≟ toℕ s
... | yes x | yes y = eq
... | yes x | no y = y (sym x)
... | no x | yes y = tt -- weird!
... | no x | no y = eq

{- we don't actually need this
bool⟷Equiv : {t₁ t₂ : U} → IsEquivalence bool⟷
bool⟷Equiv = record 
  { refl = λ {t} → refl⟷ t
  ; sym = λ {i} {j} → sym⟷ i j 
  ; trans = {!!} 
  }
-}

triv≡ : {t₁ t₂ : U} → (f g : bool⟷ t₁ t₂) → Set
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
  ; _⇒_ = bool⟷
  ; _≡_ = λ {t₁} {t₂} → triv≡ {t₁} {t₂}
  ; id = λ {t} → refl⟷ t 
  ; _∘_ = λ bc ab → {!!}
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; equiv = λ {t₁} {t₂} → triv≡Equiv {t₁} {t₂}
  ; ∘-resp-≡ = λ _ _ → tt
  }


