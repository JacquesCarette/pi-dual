module Singleton where

open import Level
open import Data.Unit
open import Data.Product
open import Function 
open import Relation.Binary
open import Function.Inverse
open import Function.Equality as FE
open import Relation.Binary.PropositionalEquality as P

open import Pi using (⟦_⟧; _⟷_ )

embed₁ : Set → Set
embed₁ b = Σ b (λ _ → ⊤)

B-to-Σ⊤ : {B : Set} → B → embed₁ B
B-to-Σ⊤ v = (v , tt)

Σ⊤-to-B : {B : Set} → embed₁ B → B
Σ⊤-to-B (v , _) = v

BΣ₁ : ∀ {b} → Inverse (P.setoid b) (P.setoid (embed₁ b))
BΣ₁ = record { 
        to = record { _⟨$⟩_ = B-to-Σ⊤; cong = P.cong B-to-Σ⊤  }
      ; from = record { _⟨$⟩_ = Σ⊤-to-B; cong = P.cong Σ⊤-to-B }
      ; inverse-of = record { left-inverse-of = λ _ → refl
                               ; right-inverse-of = λ x → refl } } 

data Singleton {c : Level} {A : Set c} : A → Set c where
  singleton : (x : A) -> Singleton x

-- That a Singleton type is a setoid is not needed, but here is the proof anyways.
data _∼_ {c : Level} {A : Set c} {v : A} (x : Singleton v) (y : Singleton v) : Set c where
    uniq : x ∼ y

∼Equiv : {c : Level} {A : Set c} {v : A} → IsEquivalence {_} {_} {Singleton v}  _∼_
∼Equiv {v = v } = record { 
                    refl = uniq
                  ; sym = λ _ →  uniq
                  ; trans = λ _ _ → uniq }
 
SingSetoid : {c c : Level} → (A : Setoid c c) → (Setoid.Carrier A) → Setoid c c
SingSetoid A v = record { 
                   Carrier = Singleton v
                 ; _≈_ = _∼_ 
                 ; isEquivalence = ∼Equiv }

-- We can map a type to its Σ of Singletons and back.
embed₂ : Set → Set
embed₂ b = Σ b Singleton

B-to-ΣS : {B : Set} → B → embed₂ B
B-to-ΣS v = (v , singleton v)

ΣS-to-B : {B : Set} → embed₂ B → B
ΣS-to-B x = proj₁ x

right-inverse : ∀ {c} {b : Set c} → (x : Σ b (Singleton {A = b})) → (proj₁ x , singleton (proj₁ x)) ≡ x
right-inverse (v , singleton .v) = refl

BΣ₂ : ∀ {b} → Inverse (P.setoid b) (P.setoid (embed₂ b))
BΣ₂ =  record { 
         to = record { _⟨$⟩_ = B-to-ΣS; cong = P.cong B-to-ΣS }
       ; from = record { _⟨$⟩_ = ΣS-to-B; cong = P.cong ΣS-to-B }
       ; inverse-of = record { left-inverse-of = λ x → refl
                             ; right-inverse-of = right-inverse } }

-- A generalized idea of a permutation: a bijection between any two types
Permutation : Set → Set -> Set
Permutation a b = Inverse (P.setoid a) (P.setoid b)

-- Now, what we really want is to interpret Pi combinators as
-- permutations.  We need a refined version of embed₂ which 
-- allows us to use a permutation to transport things.

embed₃ : {l : Level} → (S T : Setoid l l) → Inverse S T → Setoid l l
embed₃ S T f = record { 
                 Carrier = Σ A (λ b → Singleton (to f ⟨$⟩ b))
               ; _≈_ = _≡_
               ; isEquivalence = P.isEquivalence }
               where open Inverse {From = S} {T}
                     A = Setoid.Carrier S
