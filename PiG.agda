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
open import Relation.Binary

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

cut-path : {A : Set} → {x : A} → (f g : ( x ≡ x) → (x ≡ x)) → x ≡ x → Set
cut-path f g a = f a ≡ g a

record GroupoidVal : Set₁ where
  constructor •[_,_,_,_,_,_]
  field
    ∣_∣       : Set 
    •        : ∣_∣
    path     : • ≡ •        -- the additional path (loop)
    -- truncate : trans' path path ≡ refl  -- the equivalence used to truncate
    -- truncate : (f : • ≡ • → • ≡ •) → (b : • ≡ •) → f b ≡ refl
    path-rel₁ : • ≡ • → • ≡ •
    path-rel₂ : • ≡ • → • ≡ •  
    truncate : cut-path path-rel₁ path-rel₂ path

open GroupoidVal public

-- Example:

const-loop : {A : Set} {x : A} → (y : x ≡ x) → x ≡ x
const-loop _ = refl

postulate iloop     : tt ≡ tt
          itruncate : (f : tt ≡ tt → tt ≡ tt) → cut-path f const-loop iloop
              -- (trans' iloop iloop) ≡ refl

2loop : {A : Set} → {x : A} → x ≡ x → x ≡ x
2loop x = trans' x x

half : GroupoidVal
half = •[ ⊤ , tt , iloop , 2loop , const-loop , itruncate 2loop ]

-- Interpretations of types

⟦_⟧ : B → GroupoidVal
⟦ ONE ⟧ = •[ ⊤ , tt , refl , id , id , refl ]
⟦ PLUS b₁ b₂ ⟧ with ⟦ b₁ ⟧ | ⟦ b₂ ⟧ 
... | •[ B₁ , x₁ , p₁ , f₁ , g₁ , t₁ ] | •[ B₂ , x₂ , p₂ , f₂ , g₂ , t₂ ] = 
  •[ B₁ ⊎ B₂ , inj₁ x₁ , ap inj₁ p₁ , id , id ,  refl ]
⟦ TIMES b₁ b₂ ⟧ with ⟦ b₁ ⟧ | ⟦ b₂ ⟧ 
... | •[ B₁ , x₁ , p₁ , f₁ , g₁ , t₁ ] | •[ B₂ , x₂ , p₂ , f₂ , g₂ , t₂ ] = 
  •[ B₁ × B₂ , (x₁ , x₂) , ap× p₁ p₂ , id , id , refl ]
⟦ HALF ⟧ = half

-- Combinators

data _⟷_ : B → B → Set₁ where
  swap× : {b₁ b₂ : B} → TIMES b₁ b₂ ⟷ TIMES b₂ b₁

record GFunctor (G₁ G₂ : GroupoidVal) : Set where
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

{-
   Some old scribblings
A-2 : Set
A-2 = ⊤

postulate 
  S⁰ : Set
  S¹ : Set

record Trunc-1 (A : Set) : Set where
  field
    embed : A → Trunc-1 A
    hub : (r : S⁰ → Trunc-1 A) → Trunc-1 A
    spoke : (r : S⁰ → Trunc-1 A) → (x : S⁰) → r x ≡ hub r

-}

--------------------

record 2Groupoid : Set₁ where
  constructor ²[_,_,_]
  field
    obj      : Set 
    hom     : Rel obj L.zero        -- paths (loop)
    2path    : ∀ {a b} → hom a b → hom a b → Set  -- 2paths, i.e. path eqns

open 2Groupoid public

hom⊤ : Rel ⊤ L.zero
hom⊤ = _≡_

2path⊤ : Rel (hom⊤ tt tt) L.zero
2path⊤ = _≡_

half' : 2Groupoid
half' = ²[ ⊤ , hom⊤ , 2path⊤ ]
