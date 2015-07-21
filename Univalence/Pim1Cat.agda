{-# OPTIONS --without-K #-}

module Pim1Cat where

open import Level using () renaming (zero to lzero)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Nat
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Core using (Reflexive; IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; trans)

open import PiU

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

-- Between any two types, there is either no identification or exactly
-- one identification: the most sensible thing to do is to identify
-- all the empty types in one cluster; identify all the non-empty
-- types in another cluster; and have NO identifications between the
-- two clusters

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
sym⟷ s t () | no x | yes y
... | no x | no y = eq

triv≡ : {t₁ t₂ : U} → (f g : bool⟷ t₁ t₂) → Set
triv≡ _ _ = ⊤

triv≡Equiv : {t₁ t₂ : U} → IsEquivalence (triv≡ {t₁} {t₂})
triv≡Equiv = record 
  { refl = tt
  ; sym = λ a → a
  ; trans = λ _ _ → tt
  }

∘⟷ : {a b c : U} → bool⟷ b c → bool⟷ a b → bool⟷ a c
∘⟷ {a} {b} {c} bc ab with toℕ b ≟ toℕ c | toℕ a ≟ toℕ b | toℕ a ≟ toℕ c
∘⟷ bc ab | yes p | yes p₁ | yes p₂ = tt
∘⟷ bc ab | yes p | yes p₁ | no ¬p = ¬p (trans p₁ p)
∘⟷ bc () | yes p | no ¬p | yes p₁
∘⟷ bc () | yes p | no ¬p | no ¬p₁
∘⟷ () ab | no ¬p | yes p | yes p₁
∘⟷ () ab | no ¬p | yes p | no ¬p₁
∘⟷ () () | no ¬p | no ¬p₁ | yes p
∘⟷ () () | no ¬p | no ¬p₁ | no ¬p₂

-- It is a category...

PiCat : Category lzero lzero lzero
PiCat = record
  { Obj = U
  ; _⇒_ = bool⟷
  ; _≡_ = λ {t₁} {t₂} → triv≡ {t₁} {t₂}
  ; id = λ {t} → refl⟷ t 
  ; _∘_ = λ bc ab → ∘⟷ bc ab
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; equiv = λ {t₁} {t₂} → triv≡Equiv {t₁} {t₂}
  ; ∘-resp-≡ = λ _ _ → tt
  }


