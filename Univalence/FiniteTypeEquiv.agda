{-# OPTIONS --without-K #-}

module FiniteTypeEquiv where
import Level as L
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function renaming (_∘_ to _○_)
open import FinVec

record CPerm (values : ℕ) (size : ℕ) : Set where
  constructor cp
  field
    π  : FinVec values size
    πᵒ : FinVec size values
    αp : π ∘̂ πᵒ ≡ 1C
    βp : πᵒ ∘̂ π ≡ 1C

_∼_ : {A : Set} {P : A → Set} → (f g : (x : A) → P x) → Set 
_∼_ {A} {P} f g = (x : A) → f x ≡ g x

record qinv {A : Set} {B : Set} (f : A → B) : Set where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

_≃_ : ∀ (A : Set) (B : Set) → Set
A ≃ B = Σ (A → B) qinv 

univalence : {A B : Set} {m n : ℕ} →
  (A ≃ Fin m) → (B ≃ Fin n) → (CPerm m n) ≃ (A ≃ B)
univalence = {!!} 

