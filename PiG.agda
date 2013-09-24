{-# OPTIONS --without-K #-}

module PiG where

import Level as L
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Codes for our types

data B : Set where
--  no zero because we map types to POINTED SETS
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

-- Pointed sets with some paths on them (groupoids) 

PointedSet : ∀ {u} → Set (L.suc u)
PointedSet {u} = Σ (Set u) (λ A → A)

baseSet : PointedSet → Set
baseSet = proj₁

basePoint : (pt : PointedSet) → baseSet pt
basePoint = proj₂

Groupoid : Set₁
Groupoid = Σ PointedSet (λ pt → basePoint pt ≡ basePoint pt)

baseSetG : Groupoid → Set
baseSetG gp = proj₁ (proj₁ gp)

basePointG : (gp : Groupoid) → baseSetG gp
basePointG gp = proj₂ (proj₁ gp)

pathG : (gp : Groupoid) → (basePointG gp ≡ basePointG gp)
pathG = proj₂

-- Reasoning about paths

pathInd : ∀ {u} → {A : Set} → 
  (C : (x y : A) → (x ≡ y) → Set u) → 
  (c : (x : A) → C x x refl) → 
  ((x y : A) (p : x ≡ y) → C x y p)
pathInd C c x .x refl = c x

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

-- Interpretations of types

⟦_⟧ : B → Groupoid
⟦ ONE ⟧ = ((⊤ , tt) , refl)
⟦ PLUS b₁ b₂ ⟧ with ⟦ b₁ ⟧ | ⟦ b₂ ⟧ 
... | ((B₁ , x₁) , p₁) | ((B₂ , x₂) , p₂) = 
  (((B₁ ⊎ B₂) , inj₁ x₁) , ap inj₁ p₁)
⟦ TIMES b₁ b₂ ⟧ with ⟦ b₁ ⟧ | ⟦ b₂ ⟧ 
... | ((B₁ , x₁) , p₁) | ((B₂ , x₂) , p₂) = 
  (((B₁ × B₂) , (x₁ , x₂)) , ap× p₁ p₂)

-- Combinators

data _⟷_ : B → B → Set₁ where
  swap× : {b₁ b₂ : B} → TIMES b₁ b₂ ⟷ TIMES b₂ b₁

record GFunctor (G₁ G₂ : Groupoid) : Set where
  field 
    fun : baseSetG G₁ → baseSetG G₂
    baseP : fun (basePointG G₁) ≡ basePointG G₂
    isoP : {x y : baseSetG G₁} (p : x ≡ y) → (fun x ≡ fun y)

eval : {b₁ b₂ : B} → (b₁ ⟷ b₂) → GFunctor ⟦ b₁ ⟧ ⟦ b₂ ⟧
eval swap× = 
  record {
    fun = swap; 
    baseP = refl; 
    isoP = λ p → ap swap p
  }

------------------------------------------------------------------------------
