{-# OPTIONS --without-K #-}

module PiG where

import Level as L
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Reasoning about paths

pathInd : ∀ {u u'} → {A : Set u} → 
  (C : (x y : A) → (x ≡ y) → Set u') → 
  (c : (x : A) → C x x refl) → 
  ((x y : A) (p : x ≡ y) → C x y p)
pathInd C c x .x refl = c x

trans' : {A : Set} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
trans' {A} {x} {y} {z} p q = 
  pathInd 
    (λ x y p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (pathInd (λ x z q → x ≡ z) (λ _ → refl))
    x y p z q

ap : {A B : Set} {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {A} {B} {x} {y} f p = 
  pathInd 
    (λ x y p → f x ≡ f y) 
    (λ x → refl) 
    x y p

ap× : {A B : Set} {x y : A} {z w : B} → (x ≡ y) → (z ≡ w) → 
      ((x , z) ≡ (y , w))
ap× {A} {B} {x} {y} {z} {w} p₁ p₂ = 
  pathInd 
    (λ x y p₁ → ((z : B) (w : B) (p₂ : z ≡ w) → ((x , z) ≡ (y , w))))
    (λ x → pathInd
             (λ z w p₂ → ((x , z) ≡ (x , w)))
             (λ z → refl))
    x y p₁ z w p₂

transport : {A : Set} {x y : A} {P : A → Set} → (p : x ≡ y) → P x → P y
transport {A} {x} {y} {P} p = 
  pathInd
    (λ x y p → (P x → P y))
    (λ x → id)
    x y p

------------------------------------------------------------------------------
-- Codes for our types

data B : Set where
  -- no zero because we map types to POINTED SETS
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B
  HALF  : B -- used to explore fractionals

{--

Now let's define groups/groupoids

The type 1/2 is modeled by the group { refl , loop } 
where loop is self-inverse, i.e., loop . loop = refl

We always get refl, inverses, and associativity for free. We need to
explicitly add the new element 'loop' and the new equation 
'loop . loop = refl'

--}

record Groupoid : Set (L.suc (L.suc L.zero)) where
  constructor •[_,_,_,_]
  field
    ∣_∣       : Set 
    •        : ∣_∣
    path     : • ≡ •        -- the additional path (loop)
    truncate : path ≡ path  -- the equivalence used to truncate

open Groupoid public

-- Example:

postulate iloop     : tt ≡ tt
          itruncate : iloop ≡ iloop -- (trans' iloop iloop) ≡ refl

half : Groupoid
half = •[ ⊤ , tt , iloop , itruncate ]

-- Interpretations of types

⟦_⟧ : B → Groupoid
⟦ ONE ⟧ = •[ ⊤ , tt , refl , refl ]
⟦ PLUS b₁ b₂ ⟧ with ⟦ b₁ ⟧ | ⟦ b₂ ⟧ 
... | •[ B₁ , x₁ , p₁ , t₁ ] | •[ B₂ , x₂ , p₂ , t₂ ] = 
  •[ B₁ ⊎ B₂ , inj₁ x₁ , ap inj₁ p₁ , ? ]
⟦ TIMES b₁ b₂ ⟧ with ⟦ b₁ ⟧ | ⟦ b₂ ⟧ 
... | •[ B₁ , x₁ , p₁ , t₁ ] | •[ B₂ , x₂ , p₂ , t₂ ] = 
  •[ B₁ × B₂ , (x₁ , x₂) , ap× p₁ p₂ , ? ]
⟦ HALF ⟧ = half

-- Combinators

data _⟷_ : B → B → Set₁ where
  swap× : {b₁ b₂ : B} → TIMES b₁ b₂ ⟷ TIMES b₂ b₁

record GFunctor (G₁ G₂ : Groupoid) : Set where
  field 
    fun : ∣ G₁ ∣ → ∣ G₂ ∣
    baseP : fun (• G₁) ≡ (• G₂)
    -- dependent paths??
    isoP : {x y : ∣ G₁ ∣} (p : x ≡ y) → (fun x ≡ fun y)

eval : {b₁ b₂ : B} → (b₁ ⟷ b₂) → GFunctor ⟦ b₁ ⟧ ⟦ b₂ ⟧
eval swap× = 
  record {
    fun = swap; 
    baseP = refl; 
    isoP = λ p → ap swap p
  }

------------------------------------------------------------------------------

