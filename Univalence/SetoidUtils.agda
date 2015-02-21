{-# OPTIONS --without-K #-}

module SetoidUtils where

open import Relation.Binary using (Setoid; module Setoid)
import Relation.Binary.PropositionalEquality as P
open import Data.Product using (_,_)
open import Function.Equality using (_⟶_)

open import Equiv
open import EquivSetoid

-- any type can be made into a setoid over ≡
≡-Setoid : ∀ {ℓ} → (A : Set ℓ) → Setoid ℓ ℓ
≡-Setoid A = record 
  { Carrier = A 
  ; _≈_ = P._≡_ 
  ; isEquivalence = record 
    { refl = P.refl 
    ; sym = P.sym 
    ; trans = P.trans 
    } 
  }

-- an ≃ equivalence of types can be lifted to a ≃S equivalence 
-- (over their ≡-Setoids)
lift≃ : ∀ {ℓ} → {A B : Set ℓ} → A ≃ B → (≡-Setoid A) ≃S (≡-Setoid B)
lift≃ {_} {A} {B} (f , mkqinv g α β) = equiv AS BS α' β'
  where
    module AA = Setoid (≡-Setoid A)
    module BB = Setoid (≡-Setoid B)
    AS : ≡-Setoid A ⟶ ≡-Setoid B
    AS = record { _⟨$⟩_ = f ; cong = λ { {i} {.i} P.refl → P.refl } }
    BS : ≡-Setoid B ⟶ ≡-Setoid A
    BS = record { _⟨$⟩_ = g ; cong = λ { {i} {.i} P.refl → P.refl} }
    α' : {x y : B} → P._≡_ x y → P._≡_ (f (g x)) y
    α' = λ {x} {y} p → BB.trans (α x) p
    β' : {x y : A} → P._≡_ x y → P._≡_ (g (f x)) y
    β' = λ {x} {y} p → AA.trans (β x) p
