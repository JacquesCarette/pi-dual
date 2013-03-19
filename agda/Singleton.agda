module Singleton where

open import Level
open import Data.Unit
open import Data.Product
open import Function 
open import Relation.Binary
open import Function.Inverse
open import Relation.Binary.PropositionalEquality

data Singleton {c : Level} {A : Set c} : A → Set c where
  singleton : (x : A) -> Singleton x

B-to-Σ : {B : Set} → B → Σ B (λ _ → ⊤)
B-to-Σ v = (v , tt)

Σ-to-B : {B : Set} → Σ B (λ _ → ⊤) → B
Σ-to-B (v , _) = v


data _∼_ {c : Level} {A : Set c} {v : A} : Singleton v → Singleton v → Set c where
    uniq : {x : Singleton v} → x ∼ x


∼Equiv : {c : Level} {A : Set c} {v : A} → IsEquivalence {_} {_} {Singleton v}  _∼_
∼Equiv {v = v } = record { 
                    refl = uniq
                  ; sym = λ {i} {j} i∼j → {! i∼j!}
                  ; trans = {!!} }
 
SingSetoid : {c c : Level} → (A : Setoid c c) → (Setoid.Carrier A) → Setoid c c
SingSetoid A v = record { 
                   Carrier = Singleton v
                 ; _≈_ = _∼_ 
                 ; isEquivalence = record { refl = {!!}; sym = {!!}; trans = {!!} } }

