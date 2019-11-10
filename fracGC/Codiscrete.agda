{-# OPTIONS --without-K --safe #-}

module Codiscrete where

open import Level using (Level; 0ℓ; lift; lower)
open import Data.Nat using (ℕ; suc)
open import Data.Fin hiding (lift)
open import Data.Unit
open import Function renaming (id to idf)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Categories.Category.Groupoid
open import Categories.Category.Instance.One
open import Categories.Category.Equivalence using (StrongEquivalence; WeakInverse)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category using (Category)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)

-- Codiscrete Groupoid on (n+1) points
CodiscreteGroupoid : (n : ℕ) → Groupoid 0ℓ 0ℓ 0ℓ
CodiscreteGroupoid n = record
  { category = record
    { Obj = Fin (suc n)
    ; _⇒_ = λ _ _ → ⊤
    ; _≈_ = _≡_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = trans }
    ; ∘-resp-≈ = λ _ _ → refl
    }
  ; isGroupoid = record
    { _⁻¹ = idf
    ; iso = record { isoˡ = refl ; isoʳ = refl }
    }
  }

open Groupoid

Contractible : (n : ℕ) → (k : Fin (suc n)) →
  StrongEquivalence (category (CodiscreteGroupoid n)) (One {0ℓ} {0ℓ} {0ℓ})
Contractible n k = record
  { F = F
  ; G = G
  ; weak-inverse = record
    { F∘G≈id = F∘G≃id
    ; G∘F≈id = G∘F≃id
    }
  }
  where
  C : Category _ _ _
  C = category (CodiscreteGroupoid n)
  O : Category 0ℓ 0ℓ 0ℓ
  O = One
  F : Functor C O
  F = record
    { F₀ = λ _ → lift tt -- This is our 'GC' function
    ; F₁ = lift
    ; identity = lift tt
    ; homomorphism = lift tt
    ; F-resp-≈ = λ _ → lift tt
    }
  -- This is where 'k' is used:
  G : Functor O C
  G = record
    { F₀ = λ _ → k
    ; F₁ = lower
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ _ → refl
    }
  F∘G≃id : F ∘F G ≃ idF
  F∘G≃id = record
    { F⇒G = record { η = idf ; commute = idf }
    ; F⇐G = record { η = idf ; commute = idf }
    }
  G∘F≃id : G ∘F F ≃ idF
  G∘F≃id = record
    { F⇒G = record { η = λ _ → tt ; commute = λ _ → refl }
    ; F⇐G = record { η = λ _ → tt ; commute = λ _ → refl }
    ; iso = λ X → record { isoˡ = refl ; isoʳ = refl }
    }
