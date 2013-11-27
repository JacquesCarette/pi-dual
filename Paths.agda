-- {-# OPTIONS --without-K #-}

module Paths where

open import Agda.Prim
open import Data.Unit
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Data.Sum 
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import PointedTypes

--infix  2  _∎      -- equational reasoning
--infixr 2  _≡⟨_⟩_  -- equational reasoning

------------------------------------------------------------------------------
-- Paths are pi-combinators

data _⇛_ {ℓ : Level} : 
  (A• : Set• ℓ) → (B• : Set• ℓ) → Set (lsuc (lsuc ℓ)) where
  -- additive structure
  swap₁₊⇛    : {A B : Set ℓ} {a : A} {b : B} → 
               •[ A ⊎ B , inj₁ a ] ⇛ •[ B ⊎ A , inj₂ a ]
  id⇛        : {A : Set ℓ} → (a : A) → •[ A , a ] ⇛ •[ A , a ]
  η⋆⇛        : {A : Set ℓ} {a : A} → •[ A , a ] ⇛ •[ (A → A) , id ]
  equiv⇛     : {A B : Set ℓ} {a : A} {b : B} → 
               (f : •[ A , a ] →• •[ B , b ]) → 
               (fequiv : isequiv• f) → 
               •[ A , a ] ⇛ •[ B , b ]

swap₊ : {ℓ : Level} {A B : Set ℓ} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

eval : {ℓ : Level} {A• B• : Set• ℓ} → A• ⇛ B• → (A• →• B•)
eval swap₁₊⇛ = record { fun = swap₊ ; resp• = refl } 
eval (id⇛ _) = id•
eval η⋆⇛ = {!!} 
eval (equiv⇛ _ _) = {!!}

pInversion : {ℓ : Level} {A• B• : Set• ℓ} → (c : A• ⇛ B•) → fun (eval c) (• A•) ≡ • B•
pInversion {ℓ} {A•} {B•} c = resp• (eval c) 

funext : {ℓ : Level} {A• B• : Set• ℓ} {f g : A• →• B•} → 
         (pt f ⇛ pt g) → (f ∼• g) 
funext = {!!} 

{--
  swap₂₊⇛    : {A• B• : Set• {ℓ}} → (A• ⊎•₂ B•) ⇛ (B• ⊎•₁ A•)
  assocl₁₊⇛  : {A• B• C• : Set• {ℓ}} → 
               (A• ⊎•₁ (B• ⊎•₁ C•)) ⇛ ((A• ⊎•₁ B•) ⊎•₁ C•)
  assocl₁₊⇛' : {A• B• C• : Set• {ℓ}} → 
               (A• ⊎•₁ (B• ⊎•₂ C•)) ⇛ ((A• ⊎•₁ B•) ⊎•₁ C•)
               •[ A ⊎ (B ⊎ C) , inj₁ a ] ⇛ •[ (A ⊎ B) ⊎ C , inj₁ (inj₁ a) ]
  assocl₂₁₊⇛ : {A B C : Set ℓ} → (b : B) → 
               •[ A ⊎ (B ⊎ C) , inj₂ (inj₁ b) ] ⇛ 
               •[ (A ⊎ B) ⊎ C , inj₁ (inj₂ b) ]
  assocl₂₂₊⇛ : {A B C : Set ℓ} → (c : C) → 
               •[ A ⊎ (B ⊎ C) , inj₂ (inj₂ c) ] ⇛ •[ (A ⊎ B) ⊎ C , inj₂ c ]
  assocr₁₁₊⇛ : {A B C : Set ℓ} → (a : A) → 
               •[ (A ⊎ B) ⊎ C , inj₁ (inj₁ a) ] ⇛ •[ A ⊎ (B ⊎ C) , inj₁ a ]
  assocr₁₂₊⇛ : {A B C : Set ℓ} → (b : B) → 
               •[ (A ⊎ B) ⊎ C , inj₁ (inj₂ b) ] ⇛ 
               •[ A ⊎ (B ⊎ C) , inj₂ (inj₁ b) ]
  assocr₂₊⇛  : {A B C : Set ℓ} → (c : C) → 
               •[ (A ⊎ B) ⊎ C , inj₂ c ] ⇛ •[ A ⊎ (B ⊎ C) , inj₂ (inj₂ c) ]
  -- multiplicative structure
  unite⋆⇛    : {A : Set ℓ} → (a : A) → •[ ⊤ × A , (tt , a) ] ⇛ •[ A , a ]
  uniti⋆⇛    : {A : Set ℓ} → (a : A) → •[ A , a ] ⇛ •[ ⊤ × A , (tt , a) ]
  swap⋆⇛     : {A B : Set ℓ} → (a : A) → (b : B) → 
               •[ A × B , (a , b) ] ⇛ •[ B × A , (b , a) ] 
  assocl⋆⇛   : {A B C : Set ℓ} → (a : A) → (b : B) → (c : C) → 
               •[ A × (B × C) , (a , (b , c)) ] ⇛ 
               •[ (A × B) × C , ((a , b) , c) ]
  assocr⋆⇛   : {A B C : Set ℓ} → (a : A) → (b : B) → (c : C) → 
               •[ (A × B) × C , ((a , b) , c) ] ⇛
               •[ A × (B × C) , (a , (b , c)) ]
  -- distributivity
  dist₁⇛     : {A B C : Set ℓ} → (a : A) → (c : C) → 
               •[ (A ⊎ B) × C , (inj₁ a , c) ] ⇛ 
               •[ (A × C) ⊎ (B × C) , inj₁ (a , c) ]
  dist₂⇛     : {A B C : Set ℓ} → (b : B) → (c : C) → 
               •[ (A ⊎ B) × C , (inj₂ b , c) ] ⇛
               •[ (A × C) ⊎ (B × C) , inj₂ (b , c) ]
  factor₁⇛   : {A B C : Set ℓ} → (a : A) → (c : C) → 
               •[ (A × C) ⊎ (B × C) , inj₁ (a , c) ] ⇛
               •[ (A ⊎ B) × C , (inj₁ a , c) ]
  factor₂⇛   : {A B C : Set ℓ} → (b : B) → (c : C) → 
               •[ (A × C) ⊎ (B × C) , inj₂ (b , c) ] ⇛
               •[ (A ⊎ B) × C , (inj₂ b , c) ]
  -- congruence but without sym which is provable
  id⇛        : {A : Set ℓ} → (a : A) → •[ A , a ] ⇛ •[ A , a ]
  trans⇛     : {A B C : Set ℓ} {a : A} {b : B} {c : C} → 
               (•[ A , a ] ⇛ •[ B , b ]) → 
               (•[ B , b ] ⇛ •[ C , c ]) → 
               (•[ A , a ] ⇛ •[ C , c ]) 
  plus₁⇛     : {A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
               (•[ A , a ] ⇛ •[ C , c ]) →
               (•[ B , b ] ⇛ •[ D , d ]) →
               (•[ A ⊎ B , inj₁ a ] ⇛ •[ C ⊎ D , inj₁ c ])
  plus₂⇛     : {A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
               (•[ A , a ] ⇛ •[ C , c ]) →
               (•[ B , b ] ⇛ •[ D , d ]) →
               (•[ A ⊎ B , inj₂ b ] ⇛ •[ C ⊎ D , inj₂ d ])
  times⇛     : {A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
               (•[ A , a ] ⇛ •[ C , c ]) → (•[ B , b ] ⇛ •[ D , d ]) →
               (•[ A × B , (a , b) ] ⇛ •[ C × D , (c , d) ])
--}

-- Abbreviations and small examples

{--
Path : {ℓ : Level} {A B : Set ℓ} → (a : A) → (b : B) → Set (lsuc ℓ)
Path {ℓ} {A} {B} a b = •[ A , a ] ⇛ •[ B , b ]

2Path : {ℓ : Level} {A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
  (p : Path a b) → (q : Path c d) → Set (lsuc (lsuc ℓ))
2Path {ℓ} {A} {B} {C} {D} {a} {b} {c} {d} p q = Path p q 
  --  •[ Path a b , p ] ⇛ •[ Path c d , q ]
--}
{--
_≡⟨_⟩_ : ∀ {ℓ} → {A B C : Set ℓ} (a : A) {b : B} {c : C} → 
         Path a b → Path b c → Path a c
_ ≡⟨ p ⟩ q = trans⇛ p q

_∎ : ∀ {ℓ} → {A : Set ℓ} (a : A) → Path a a
_∎ a = id⇛ a

test3 : {A : Set} {a : A} → Set•
test3 {A} {a} = •[ Path a a , id⇛ a ] 

test4 : Set•
test4 = •[ Path ℕ ℕ , id⇛ ℕ ]

test5 : Set• 
test5 = •[ Path (ℕ , Bool) (Bool , ℕ) , swap⋆⇛ ℕ Bool ]

test6 : Set• 
test6 = •[ Path (tt , ℕ) ℕ , unite⋆⇛ ℕ ] 

test7 : {A : Set} {a : A} → Set•
test7 {A} {a} = •[ 2Path (id⇛ a) (id⇛ a) , id⇛ (id⇛ a) ]

test8 : {A B C D : Set} {a : A} {b : B} {c : C} {d : D} → 
        (p : Path a b) → (q : Path c d) → Set•
test8 {A} {B} {C} {D} {a} {b} {c} {d} p q = 
  •[ Path (a , c) (b , d) , times⇛ p q ]

-- Propositional equality implies a path

≡Path : {ℓ : Level} {A : Set ℓ} {x y : A} → (x ≡ y) → Path x y
≡Path {ℓ} {A} {x} {.x} refl = id⇛ x
--}

------------------------------------------------------------------------------
-- Path induction

{--
pathInd : {ℓ ℓ' : Level} → 
  (P : {A• B• : Set• {ℓ}} → (A• ⇛ B•) → Set ℓ') → 
  ({A• B• : Set• {ℓ}} → P (swap₁₊⇛ {ℓ} {A•} {B•})) →
pathInd : {ℓ ℓ' : Level} → 
  (P : {A B : Set ℓ} {a : A} {b : B} → 
    (•[ A , a ] ⇛ •[ B , b ]) → Set ℓ') → 
  ({A B : Set ℓ} → (a : A) → P (swap₁₊⇛ {ℓ} {A} {B} a)) → 
  ({A B : Set ℓ} → (b : B) → P (swap₂₊⇛ {ℓ} {A} {B} b)) → 
  ({A B C : Set ℓ} → (a : A) → P (assocl₁₊⇛ {ℓ} {A} {B} {C} a)) → 
  ({A B C : Set ℓ} → (b : B) → P (assocl₂₁₊⇛ {ℓ} {A} {B} {C} b)) → 
  ({A B C : Set ℓ} → (c : C) → P (assocl₂₂₊⇛ {ℓ} {A} {B} {C} c)) → 
  ({A B C : Set ℓ} → (a : A) → P (assocr₁₁₊⇛ {ℓ} {A} {B} {C} a)) → 
  ({A B C : Set ℓ} → (b : B) → P (assocr₁₂₊⇛ {ℓ} {A} {B} {C} b)) → 
  ({A B C : Set ℓ} → (c : C) → P (assocr₂₊⇛ {ℓ} {A} {B} {C} c)) → 
  ({A : Set ℓ} → (a : A) → P (unite⋆⇛ {ℓ} {A} a)) → 
  ({A : Set ℓ} → (a : A) → P (uniti⋆⇛ {ℓ} {A} a)) → 
  ({A B : Set ℓ} → (a : A) → (b : B) → P (swap⋆⇛ {ℓ} {A} {B} a b)) → 
  ({A B C : Set ℓ} → (a : A) → (b : B) → (c : C) → 
    P (assocl⋆⇛ {ℓ} {A} {B} {C} a b c)) → 
  ({A B C : Set ℓ} → (a : A) → (b : B) → (c : C) → 
    P (assocr⋆⇛ {ℓ} {A} {B} {C} a b c)) → 
  ({A B C : Set ℓ} → (a : A) → (c : C) → P (dist₁⇛ {ℓ} {A} {B} {C} a c)) → 
  ({A B C : Set ℓ} → (b : B) → (c : C) → P (dist₂⇛ {ℓ} {A} {B} {C} b c)) → 
  ({A B C : Set ℓ} → (a : A) → (c : C) → P (factor₁⇛ {ℓ} {A} {B} {C} a c)) → 
  ({A B C : Set ℓ} → (b : B) → (c : C) → P (factor₂⇛ {ℓ} {A} {B} {C} b c)) → 
  ({A : Set ℓ} → (a : A) → P (id⇛ {ℓ} {A} a)) → 
  ({A B C : Set ℓ} {a : A} {b : B} {c : C} → 
    (p : (•[ A , a ] ⇛ •[ B , b ])) → 
    (q : (•[ B , b ] ⇛ •[ C , c ])) → 
    P p → P q → P (trans⇛ p q)) → 
  ({A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
    (p : (•[ A , a ] ⇛ •[ C , c ])) → 
    (q : (•[ B , b ] ⇛ •[ D , d ])) → 
    P p → P q → P (plus₁⇛ {ℓ} {A} {B} {C} {D} {a} {b} {c} {d} p q)) → 
  ({A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
    (p : (•[ A , a ] ⇛ •[ C , c ])) → 
    (q : (•[ B , b ] ⇛ •[ D , d ])) → 
    P p → P q → P (plus₂⇛ {ℓ} {A} {B} {C} {D} {a} {b} {c} {d} p q)) → 
  ({A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
    (p : (•[ A , a ] ⇛ •[ C , c ])) → 
    (q : (•[ B , b ] ⇛ •[ D , d ])) → 
    P p → P q → P (times⇛ p q)) → 
  {A B : Set ℓ} {a : A} {b : B} → (p : •[ A , a ] ⇛ •[ B , b ]) → P p
  {A• B• : Set• {ℓ}} → (p : A• ⇛ B•) → P p
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (swap₁₊⇛ a) = swap₁₊ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (swap₂₊⇛ b) = swap₂₊ b
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (assocl₁₊⇛ a) = assocl₁₊ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (assocl₂₁₊⇛ b) = assocl₂₁₊ b
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (assocl₂₂₊⇛ c) = assocl₂₂₊ c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (assocr₁₁₊⇛ a) = assocr₁₁₊ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (assocr₁₂₊⇛ b) = assocr₁₂₊ b
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (assocr₂₊⇛ c) = assocr₂₊ c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (unite⋆⇛ a) = unite⋆ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (uniti⋆⇛ a) = uniti⋆ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (swap⋆⇛ a b) = swap⋆ a b
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (assocl⋆⇛ a b c) = assocl⋆ a b c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (assocr⋆⇛ a b c) = assocr⋆ a b c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (dist₁⇛ a c) = dist₁ a c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (dist₂⇛ b c) = dist₂ b c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (factor₁⇛ a c) = factor₁ a c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (factor₂⇛ b c) = factor₂ b c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (id⇛ a) = cid a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (trans⇛ p q) = 
    ctrans p q  
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans plus₁ plus₂ times p)
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans plus₁ plus₂ times q)
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (plus₁⇛ p q) = 
    plus₁ p q
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans plus₁ plus₂ times p)
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans plus₁ plus₂ times q)
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (plus₂⇛ p q) = 
    plus₂ p q
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans plus₁ plus₂ times p)
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans plus₁ plus₂ times q)
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans plus₁ plus₂ times (times⇛ p q) = 
    times p q  
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans plus₁ plus₂ times p)
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans plus₁ plus₂ times q)
pathInd P swap₁₊ swap₁₊⇛ = swap₁₊
--}

------------------------------------------------------------------------------
-- Groupoid structure (emerging...)
{--
sym⇛ : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → Path a b → Path b a
sym⇛ {ℓ} {A} {B} {a} {b} p = 
  (pathInd 
    (λ {A} {B} {a} {b} p → Path b a)
    swap₂₊⇛ swap₁₊⇛ 
    assocr₁₁₊⇛ assocr₁₂₊⇛ assocr₂₊⇛ assocl₁₊⇛ assocl₂₁₊⇛ assocl₂₂₊⇛ 
    uniti⋆⇛ unite⋆⇛ (λ a b → swap⋆⇛ b a) 
    assocr⋆⇛ assocl⋆⇛ factor₁⇛ factor₂⇛ dist₁⇛ dist₂⇛ 
    id⇛ (λ _ _ p' q' → trans⇛ q' p'))
    (λ _ _ p' q' → plus₁⇛ p' q') (λ _ _ p' q' → plus₂⇛ p' q') 
    (λ _ _ p' q' → times⇛ p' q')
  {A} {B} {a} {b} p 

test9 : {A : Set} {a : A} → Path (a , (tt , a)) ((tt , a) , a)
test9 {A} {a} = sym⇛ (times⇛ (unite⋆⇛ a) (uniti⋆⇛ a)) 
             -- evaluates to (times⇛ (uniti⋆⇛ a) (unite⋆⇛ a) 
--}
{--
idright : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} {p : Path a b} →
          2Path (trans⇛ p (id⇛ b)) p
idright {ℓ} {A} {B} {a} {b} {p} = 
  (pathInd 
    (λ {A} {B} {a} {b} p → 2Path (trans⇛ p (id⇛ b)) p)
    (λ {A} {B} a₁ → {!!}) 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!}
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!})
  {A} {B} {a} {b} p

aptransL : {ℓ : Level} {A B C : Set ℓ} {a : A} {b : B} {c : C} → 
           (p q : Path a b) → (r : Path b c) → (α : 2Path p q) → 
           2Path (trans⇛ p r) (trans⇛ q r)
aptransL {ℓ} {A} {B} {C} {a} {b} {c} p q r α = 
  (pathInd 
    (λ {B} {C} {b} {c} r → (A : Set ℓ) → (a : A) → (p q : Path a b) → 
      (α : 2Path p q) → 2Path (trans⇛ p r) (trans⇛ q r))
    (λ a₁ A₂ a₂ p₁ q₁ α₁ → {!!}) 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!} 
    {!!})
  {B} {C} {b} {c} r A a p q α

symsym : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → (p : Path a b) → 
         2Path (sym⇛ (sym⇛ p)) p
symsym {ℓ} {A} {B} {a} {b} p = 
  (pathInd
    (λ {A} {B} {a} {b} p → 2Path (sym⇛ (sym⇛ p)) p)
    (λ a → id⇛ (swap₁₊⇛ a)) 
    (λ b → id⇛ (swap₂₊⇛ b)) 
    (λ a → id⇛ (assocl₁₊⇛ a)) 
    (λ b → id⇛ (assocl₂₁₊⇛ b)) 
    (λ c → id⇛ (assocl₂₂₊⇛ c)) 
    (λ a → id⇛ (assocr₁₁₊⇛ a)) 
    (λ b → id⇛ (assocr₁₂₊⇛ b)) 
    (λ c → id⇛ (assocr₂₊⇛ c)) 
    (λ a → id⇛ (unite⋆⇛ a)) 
    (λ a → id⇛ (uniti⋆⇛ a)) 
    (λ a b → id⇛ (swap⋆⇛ a b)) 
    (λ a b c → id⇛ (assocl⋆⇛ a b c)) 
    (λ a b c → id⇛ (assocr⋆⇛ a b c)) 
    (λ a c → id⇛ (dist₁⇛ a c)) 
    (λ b c → id⇛ (dist₂⇛ b c)) 
    (λ a c → id⇛ (factor₁⇛ a c)) 
    (λ b c → id⇛ (factor₂⇛ b c)) 
    (λ a → id⇛ (id⇛ a)) 
    (λ p q α β → {!!})
    (λ p q α β → {!!})
    (λ p q α β → {!!})
    (λ p q α β → {!!}))
  {A} {B} {a} {b} p
--}

------------------------------------------------------------------------------
{-- old stuff which we might need again

idright : {A B : Set} {a : A} {b : B} {p : •[ A , a ] ⇛ •[ B , b ]} →
          (trans⇛ p (id⇛ {B} {b})) 2⇛ p
idright = 2Path id⇛ id⇛ 
        
idleft : {A B : Set} {a : A} {b : B} {p : •[ A , a ] ⇛ •[ B , b ]} →
         (trans⇛ (id⇛ {A} {a}) p) 2⇛ p
idleft = 2Path id⇛ id⇛
        
assoc  : {A B C D : Set} {a : A} {b : B} {c : C} {d : D}
         {p : •[ A , a ] ⇛ •[ B , b ]}
         {q : •[ B , b ] ⇛ •[ C , c ]}
         {r : •[ C , c ] ⇛ •[ D , d ]} →
         (trans⇛ p (trans⇛ q r)) 2⇛ (trans⇛ (trans⇛ p q) r)
assoc = 2Path id⇛ id⇛

bifunctorid⋆ : {A B : Set} {a : A} {b : B} → 
  (times⇛ (id⇛ {A} {a}) (id⇛ {B} {b})) 2⇛ (id⇛ {A × B} {(a , b)})
bifunctorid⋆ = 2Path id⇛ id⇛

bifunctorid₊₁ : {A B : Set} {a : A} → 
  (plus₁⇛ {A} {B} {A} {B} (id⇛ {A} {a})) 2⇛ (id⇛ {A ⊎ B} {inj₁ a})
bifunctorid₊₁ = 2Path id⇛ id⇛

bifunctorid₊₂ : {A B : Set} {b : B} → 
  (plus₂⇛ {A} {B} {A} {B} (id⇛ {B} {b})) 2⇛ (id⇛ {A ⊎ B} {inj₂ b})
bifunctorid₊₂ = 2Path id⇛ id⇛

bifunctorC⋆ : {A B C D E F : Set} 
              {a : A} {b : B} {c : C} {d : D} {e : E} {f : F}
              {p : •[ A , a ] ⇛ •[ B , b ]}
              {q : •[ B , b ] ⇛ •[ C , c ]}
              {r : •[ D , d ] ⇛ •[ E , e ]} 
              {s : •[ E , e ] ⇛ •[ F , f ]} →
  (trans⇛ (times⇛ p r) (times⇛ q s)) 2⇛ (times⇛ (trans⇛ p q) (trans⇛ r s))
bifunctorC⋆ = 2Path id⇛ id⇛

bifunctorC₊₁₁ : {A B C D E F : Set} 
                {a : A} {b : B} {c : C}
                {p : •[ A , a ] ⇛ •[ B , b ]}
                {q : •[ B , b ] ⇛ •[ C , c ]} →
  (trans⇛ (plus₁⇛ {A} {D} {B} {E} p) (plus₁⇛ {B} {E} {C} {F} q)) 2⇛ 
  (plus₁⇛ {A} {D} {C} {F} (trans⇛ p q))
bifunctorC₊₁₁ = 2Path id⇛ id⇛

bifunctorC₊₂₂ : {A B C D E F : Set} 
                {d : D} {e : E} {f : F}
                {r : •[ D , d ] ⇛ •[ E , e ]} 
                {s : •[ E , e ] ⇛ •[ F , f ]} →
  (trans⇛ (plus₂⇛ {A} {D} {B} {E} r) (plus₂⇛ {B} {E} {C} {F} s)) 2⇛ 
  (plus₂⇛ {A} {D} {C} {F} (trans⇛ r s))
bifunctorC₊₂₂ = 2Path id⇛ id⇛

triangle : {A B : Set} {a : A} {b : B} → 
  (trans⇛ (assocr⋆⇛ {A} {⊤} {B} {a} {tt} {b}) (times⇛ id⇛ unite⋆⇛)) 2⇛
  (times⇛ (trans⇛ swap⋆⇛ unite⋆⇛) id⇛)
triangle = 2Path id⇛ id⇛

-- Now interpret a path (x ⇛ y) as a value of type (1/x , y)

Recip : {A : Set} → (x : • A) → Set₁
Recip {A} x = (x ⇛ x) 

η : {A : Set} {x : • A} → ⊤ → Recip x × • A 
η {A} {x} tt = (id⇛ x , x)

lower : {A : Set} {x : • A} → x ⇛ x -> ⊤
lower c = tt

-- The problem here is that we can't assert that y == x.
ε : {A : Set} {x : • A} → Recip x × • A → ⊤
ε {A} {x} (rx , y) = lower (id⇛ ( ↑ (fun (ap rx) (focus y)) )) -- makes insufficient sense

apr : {A B : Set} {x : • A} {y : • B} → (x ⇛ y) → Recip y → Recip x
apr {A} {B} {x} {y} q ry = trans⇛ q (trans⇛ ry (sym⇛ q))
  x 
    ≡⟨ q ⟩
  y
    ≡⟨ ry ⟩
  y
    ≡⟨ sym⇛ q ⟩
  x ∎

ε : {A B : Set} {x : A} {y : B} → Recip x → Singleton y → x ⇛ y
ε rx (singleton y) = rx y

pathV : {A B : Set} {x : A} {y : B} → (x ⇛ y) → Recip x × Singleton y
pathV unite₊⇛ = {!!}
pathV uniti₊⇛ = {!!}
--  swap₁₊⇛ : {A B : Set} {x : A} → _⇛_ {A ⊎ B} {B ⊎ A} (inj₁ x) (inj₂ x)
pathV (swap₁₊⇛ {A} {B} {x}) = ((λ x' → {!!}) , singleton (inj₂ x)) 
pathV swap₂₊⇛ = {!!}
pathV assocl₁₊⇛ = {!!}
pathV assocl₂₁₊⇛ = {!!}
pathV assocl₂₂₊⇛ = {!!}
pathV assocr₁₁₊⇛ = {!!}
pathV assocr₁₂₊⇛ = {!!}
pathV assocr₂₊⇛ = {!!}
pathV unite⋆⇛ = {!!}
pathV uniti⋆⇛ = {!!}
pathV swap⋆⇛ = {!!} 
pathV assocl⋆⇛ = {!!}
pathV assocr⋆⇛ = {!!}
pathV dist₁⇛ = {!!}
pathV dist₂⇛ = {!!}
pathV factor₁⇛ = {!!}
pathV factor₂⇛ = {!!}
pathV dist0⇛ = {!!}
pathV factor0⇛ = {!!}
pathV {A} {.A} {x} (id⇛ .x) = {!!}
pathV (sym⇛ p) = {!!}
pathV (trans⇛ p p₁) = {!!}
pathV (plus₁⇛ p) = {!!}
pathV (plus₂⇛ p) = {!!}
pathV (times⇛ p p₁) = {!!} 

-- these are individual paths so to speak
-- should we represent a path like swap+ as a family explicitly:
-- swap+ : (x : A) -> x ⇛ swapF x
-- I guess we can: swap+ : (x : A) -> case x of inj1 -> swap1 x else swap2 x

If A={x0,x1,x2}, 1/A has three values:
(x0<-x0, x0<-x1, x0<-x2)
(x1<-x0, x1<-x1, x1<-x2)
(x2<-x0, x2<-x1, x2<-x2)
It is a fake choice between x0, x1, and x2 (some negative information). You base
yourself at x0 for example and enforce that any other value can be mapped to x0.
So think of a value of type 1/A as an uncertainty about which value of A we 
have. It could be x0, x1, or x2 but at the end it makes no difference. There is
no choice.

You can manipulate a value of type 1/A (x0<-x0, x0<-x1, x0<-x2) by with a
path to some arbitrary path to b0 for example:

(b0<-x0<-x0, b0<-x0<-x1, b0<-x0<-x2)

eta_3 will give (x0<-x0, x0<-x1, x0<-x2, x0) for example but any other
combination is equivalent.

epsilon_3 will take (x0<-x0, x0<-x1, x0<-x2) and one actual xi which is now
certain; we can resolve our previous uncertainty by following the path from
xi to x0 thus eliminating the fake choice we seemed to have. 

Explain connection to negative information.

Knowing head or tails is 1 bits. Giving you a choice between heads and tails
and then cooking this so that heads=tails takes away your choice. 

-- transp⇛ : {A B : Set} {x y : • A} → 
-- (f : A → B) → x ⇛ y → ↑ (f (focus x)) ⇛ ↑ (f (focus y)) 

-- Morphism of pointed space: contains a path!
record _⟶_ {A B : Set} (pA : • A) (pB : • B) : Set₁ where
  field
    fun : A → B
    eq : ↑ (fun (focus pA)) ⇛ pB

open _⟶_

_○_ : {A B C : Set} {pA : • A} {pB : • B} {pC : • C} → pA ⟶ pB → pB ⟶ pC → pA ⟶ pC
f ○ g = record { fun = λ x → (fun g) ((fun f) x) ; eq = trans⇛ (transp⇛ (fun g) (eq f)) (eq g)}

mutual 

  ap : {A B : Set} {x : • A} {y : • B} → x ⇛ y → x ⟶ y
  ap {y = y} unite₊⇛ = record { fun = λ { (inj₁ ()) 
                                        ; (inj₂ x) → x } ; eq = id⇛ y }
  ap uniti₊⇛ (singleton x) = singleton (inj₂ x)
  ap (swap₁₊⇛ {A} {B} {x}) (singleton .(inj₁ x)) = singleton (inj₂ x)
  ap (swap₂₊⇛ {A} {B} {y}) (singleton .(inj₂ y)) = singleton (inj₁ y)
  ap (assocl₁₊⇛ {A} {B} {C} {x}) (singleton .(inj₁ x)) = 
    singleton (inj₁ (inj₁ x))
  ap (assocl₂₁₊⇛ {A} {B} {C} {y}) (singleton .(inj₂ (inj₁ y))) = 
    singleton (inj₁ (inj₂ y))
  ap (assocl₂₂₊⇛ {A} {B} {C} {z}) (singleton .(inj₂ (inj₂ z))) = 
    singleton (inj₂ z)
  ap (assocr₁₁₊⇛ {A} {B} {C} {x}) (singleton .(inj₁ (inj₁ x))) = 
    singleton (inj₁ x)
  ap (assocr₁₂₊⇛ {A} {B} {C} {y}) (singleton .(inj₁ (inj₂ y))) = 
    singleton (inj₂ (inj₁ y))
  ap (assocr₂₊⇛ {A} {B} {C} {z}) (singleton .(inj₂ z)) = 
    singleton (inj₂ (inj₂ z))
  ap {.(⊤ × A)} {A} {.(tt , x)} {x} unite⋆⇛ (singleton .(tt , x)) = 
    singleton x
  ap uniti⋆⇛ (singleton x) = singleton (tt , x)
  ap (swap⋆⇛ {A} {B} {x} {y}) (singleton .(x , y)) = singleton (y , x)
  ap (assocl⋆⇛ {A} {B} {C} {x} {y} {z}) (singleton .(x , (y , z))) = 
    singleton ((x , y) , z)
  ap (assocr⋆⇛ {A} {B} {C} {x} {y} {z}) (singleton .((x , y) , z)) = 
    singleton (x , (y , z))
  ap (dist₁⇛ {A} {B} {C} {x} {z}) (singleton .(inj₁ x , z)) = 
    singleton (inj₁ (x , z))
  ap (dist₂⇛ {A} {B} {C} {y} {z}) (singleton .(inj₂ y , z)) = 
    singleton (inj₂ (y , z))
  ap (factor₁⇛ {A} {B} {C} {x} {z}) (singleton .(inj₁ (x , z))) = 
    singleton (inj₁ x , z)
  ap (factor₂⇛ {A} {B} {C} {y} {z}) (singleton .(inj₂ (y , z))) = 
    singleton (inj₂ y , z)
  ap {.(⊥ × A)} {.⊥} {.(• , x)} {•} (dist0⇛ {A} {.•} {x}) (singleton .(• , x)) = 
    singleton • 
  ap factor0⇛ (singleton ()) 
  ap {x = x} (id⇛ .x) = record { fun = λ x → x; eq = id⇛ x }
  ap (sym⇛ c) = apI c
  ap (trans⇛ c₁ c₂) = (ap c₁) ○ (ap c₂)
  ap (transp⇛ f a) = record { fun = λ x → x; eq = transp⇛ f a }

  ap (plus₁⇛ {A} {B} {C} {D} {x} {z} c) (singleton .(inj₁ x)) 
    with ap c (singleton x)
  ... | singleton .z = singleton (inj₁ z)
  ap (plus₂⇛ {A} {B} {C} {D} {y} {w} c) (singleton .(inj₂ y)) 
    with ap c (singleton y)
  ... | singleton .w = singleton (inj₂ w)
  ap (times⇛ {A} {B} {C} {D} {x} {y} {z} {w} c₁ c₂) (singleton .(x , y)) 
    with ap c₁ (singleton x) | ap c₂ (singleton y) 
  ... | singleton .z | singleton .w = singleton (z , w)


  apI : {A B : Set} {x : • A} {y : • B} → x ⇛ y → y ⟶ x
  apI {y = y} unite₊⇛ = record { fun = inj₂; eq = id⇛ (↑ (inj₂ (focus y))) }

 
 apI {A} {.(⊥ ⊎ A)} {x} uniti₊⇛ (singleton .(inj₂ x)) = singleton x
  apI (swap₁₊⇛ {A} {B} {x}) (singleton .(inj₂ x)) = singleton (inj₁ x)
  apI (swap₂₊⇛ {A} {B} {y}) (singleton .(inj₁ y)) = singleton (inj₂ y)
  apI (assocl₁₊⇛ {A} {B} {C} {x}) (singleton .(inj₁ (inj₁ x))) = 
    singleton (inj₁ x)
  apI (assocl₂₁₊⇛ {A} {B} {C} {y}) (singleton .(inj₁ (inj₂ y))) = 
    singleton (inj₂ (inj₁ y))
  apI (assocl₂₂₊⇛ {A} {B} {C} {z}) (singleton .(inj₂ z)) = 
    singleton (inj₂ (inj₂ z))
  apI (assocr₁₁₊⇛ {A} {B} {C} {x}) (singleton .(inj₁ x)) = 
    singleton (inj₁ (inj₁ x))
  apI (assocr₁₂₊⇛ {A} {B} {C} {y}) (singleton .(inj₂ (inj₁ y))) = 
    singleton (inj₁ (inj₂ y))
  apI (assocr₂₊⇛ {A} {B} {C} {z}) (singleton .(inj₂ (inj₂ z))) = 
    singleton (inj₂ z)
  apI unite⋆⇛ (singleton x) = singleton (tt , x)
  apI {A} {.(⊤ × A)} {x} uniti⋆⇛ (singleton .(tt , x)) = singleton x
  apI (swap⋆⇛ {A} {B} {x} {y}) (singleton .(y , x)) = singleton (x , y)
  apI (assocl⋆⇛ {A} {B} {C} {x} {y} {z}) (singleton .((x , y) , z)) = 
    singleton (x , (y , z))
  apI (assocr⋆⇛ {A} {B} {C} {x} {y} {z}) (singleton .(x , (y , z))) = 
    singleton ((x , y) , z)
  apI (dist₁⇛ {A} {B} {C} {x} {z}) (singleton .(inj₁ (x , z))) = 
    singleton (inj₁ x , z)
  apI (dist₂⇛ {A} {B} {C} {y} {z}) (singleton .(inj₂ (y , z))) = 
    singleton (inj₂ y , z)
  apI (factor₁⇛ {A} {B} {C} {x} {z}) (singleton .(inj₁ x , z)) = 
    singleton (inj₁ (x , z))
  apI (factor₂⇛ {A} {B} {C} {y} {z}) (singleton .(inj₂ y , z)) = 
    singleton (inj₂ (y , z))
  apI dist0⇛ (singleton ()) 
  apI {.⊥} {.(⊥ × A)} {•} (factor0⇛ {A} {.•} {x}) (singleton .(• , x)) = 
    singleton •

  apI {x = x} (id⇛ .x) = record { fun = λ x → x; eq = id⇛ x }
  apI (sym⇛ c) = ap c
  apI (trans⇛ c₁ c₂) = (apI c₂) ○ (apI c₁)
  apI (transp⇛ f a) = record { fun = λ x → x; eq = transp⇛ f (sym⇛ a) }

  apI (plus₁⇛ {A} {B} {C} {D} {x} {z} c) (singleton .(inj₁ z)) 
    with apI c (singleton z)
  ... | singleton .x = singleton (inj₁ x)
  apI (plus₂⇛ {A} {B} {C} {D} {y} {w} c) (singleton .(inj₂ w)) 
    with apI c (singleton w) 
  ... | singleton .y = singleton (inj₂ y)
  apI (times⇛ {A} {B} {C} {D} {x} {y} {z} {w} c₁ c₂) (singleton .(z , w)) 
    with apI c₁ (singleton z) | apI c₂ (singleton w) 
  ... | singleton .x | singleton .y = singleton (x , y)

--}

--}
