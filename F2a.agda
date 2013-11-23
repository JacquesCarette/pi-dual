-- {-# OPTIONS --without-K #-}

module F2a where

open import Agda.Prim
open import Data.Unit
open import Data.Sum 
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

---------------------------------------------------------------------------
-- Pointed types

record Set• {ℓ : Level} : Set (lsuc ℓ) where
  constructor •[_,_]
  field
    ∣_∣ : Set ℓ
    • : ∣_∣

open Set• public

test0 : Set• {lzero}
test0 = •[ ℕ , 3 ]

test1 : Set• {lsuc lzero}
test1 = •[ Set , ℕ ]

test2 : ∀ {ℓ} → Set• {lsuc (lsuc ℓ)}
test2 {ℓ} = •[ Set (lsuc ℓ) , Set ℓ ]

-- functions between pointed types

record _→•_ {ℓ : Level} (A• B• : Set• {ℓ}) : Set ℓ where
  field 
    f : ∣ A• ∣ → ∣ B• ∣
    resp• : • B• ≡ f (• A•)

-- See:
-- http://homotopytypetheory.org/2012/11/21/on-heterogeneous-equality/

beta : {ℓ : Level} {A : Set ℓ} {a : A} → • •[ A , a ] ≡ a
beta {ℓ} {A} {a} = refl

eta : {ℓ : Level} → (A• : Set•) → •[ ∣ A• ∣ , • A• ] ≡ A•
eta {ℓ} A• = refl

---------------------------------------------------------------------------
-- Paths

-- Paths are pi-combinators

data _⇛_ {ℓ : Level} : Set• {ℓ} → Set• {ℓ} → Set (lsuc (lsuc ℓ)) where
  -- + 
  swap₁₊⇛    : {A B : Set ℓ} → (a : A) → 
               •[ A ⊎ B , inj₁ a ] ⇛ •[ B ⊎ A , inj₂ a ]
  swap₂₊⇛    : {A B : Set ℓ} → (b : B) → 
               •[ A ⊎ B , inj₂ b ] ⇛ •[ B ⊎ A , inj₁ b ]
  assocl₁₊⇛  : {A B C : Set ℓ} → (a : A) → 
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
  -- *
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
{--
  -- should we have something like that too?
  fun⇛     : {A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
               (•[ A , a ] ⇛ •[ C , c ]) → (•[ B , b ] ⇛ •[ D , d ]) →
               (•[ A → B , ??? ] ⇛ •[ C → D , ??? ])
  -- Jacques says: no!  That would build-in functions, and we want to show
  -- that we can do so 'by hand'.
--}

-- Abbreviations and small examples

Path : {ℓ : Level} {A B : Set ℓ} → (a : A) → (b : B) → Set (lsuc (lsuc ℓ))
Path {ℓ} {A} {B} a b = •[ A , a ] ⇛ •[ B , b ]

2Path : {ℓ : Level} {A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
  (p : Path a b) → (q : Path c d) → Set (lsuc (lsuc (lsuc (lsuc ℓ))))
2Path {ℓ} {A} {B} {C} {D} {a} {b} {c} {d} p q = 
  •[ Path a b , p ] ⇛ •[ Path c d , q ]

_≡⟨_⟩_ : ∀ {ℓ} → {A B C : Set ℓ} (a : A) {b : B} {c : C} → 
        Path a b → Path b c → Path a c
_ ≡⟨ p ⟩ q = trans⇛ p q

_∎ : ∀ {ℓ} → {A : Set ℓ} (a : A) → Path a a
_∎ a = id⇛ a

test3 : {A : Set} {a : A} → Set•
test3 {A} {a} = •[ Path a a , id⇛ a ] 

test4 : {A : Set} {a : A} → Set•
test4 {A} {a} = •[ 2Path (id⇛ a) (id⇛ a) , id⇛ (id⇛ a) ]

test5 : {A B C D : Set} {a : A} {b : B} {c : C} {d : D} → 
        (p : Path a b) → (q : Path c d) → Set•
test5 {A} {B} {C} {D} {a} {b} {c} {d} p q = 
  •[ Path (a , c) (b , d) , times⇛ p q ]
      
-- Propositional equality implies a path

≡Path : {ℓ : Level} {A : Set ℓ} {x y : A} → (x ≡ y) → Path x y
≡Path {ℓ} {A} {x} {.x} refl = id⇛ x

---------------------------------------------------------------------------
-- Path induction

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

---------------------------------------------------------------------------
-- Groupoid structure (emerging...)

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

test6 : {A : Set} {a : A} → Path (a , (tt , a)) ((tt , a) , a)
test6 {A} {a} = sym⇛ (times⇛ (unite⋆⇛ a) (uniti⋆⇛ a)) 
             -- evaluates to (times⇛ (uniti⋆⇛ a) (unite⋆⇛ a) 

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

---------------------------------------------------------------------------
-- Isomorphisms (or more accurately equivalences) between pointed types

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ lsuc (lsuc ℓ'))
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → Path (f x) (g x)

-- ∼ is an equivalence relation

refl∼ : {A B : Set} {f : A → B} → (f ∼ f)
refl∼ {A} {B} {f} x = id⇛ (f x)

sym∼ : {A B : Set} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = sym⇛ (H x) 

trans∼ : {A B : Set} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = trans⇛ (H x) (G x)

-- quasi-inverses

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (lsuc (lsuc ℓ) ⊔ lsuc (lsuc ℓ')) where
  constructor mkqinv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {ℓ} {ℓ} {A} {A} id
idqinv = record {
           g = id ;
           α = λ b → id⇛ b ; 
           β = λ a → id⇛ a
         } 

-- equivalences

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (lsuc (lsuc ℓ) ⊔ lsuc (lsuc ℓ')) where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    h : B → A
    β : (h ∘ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (lsuc (lsuc ℓ) ⊔ lsuc (lsuc ℓ'))
A ≃ B = Σ (A → B) isequiv

idequiv : ∀ {ℓ} {A : Set ℓ} → A ≃ A
idequiv = (id , equiv₁ idqinv)

------------------------------------------------------------------------------
-- We can extract a forward evaluator (i.e. paths really are functions)

swap₊ : {ℓ : Level} {A B : Set ℓ} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

assocl₊ : {ℓ : Level} {A B C : Set ℓ} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
assocl₊ (inj₁ a) = inj₁ (inj₁ a)
assocl₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b) 
assocl₊ (inj₂ (inj₂ c)) = inj₂ c

assocr₊ : {ℓ : Level} {A B C : Set ℓ} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C) 
assocr₊ (inj₁ (inj₁ a)) = inj₁ a
assocr₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
assocr₊ (inj₂ c) = inj₂ (inj₂ c)

eval• :  {ℓ : Level} {A• B• : Set•} → A• ⇛ B• → (A• →• B•)
eval• (swap₁₊⇛ a)    = record { f = swap₊   ; resp• = refl } 
eval• (swap₂₊⇛ b)    = record { f = swap₊   ; resp• = refl } 
eval• (assocl₁₊⇛ a)  = record { f = assocl₊ ; resp• = refl } 
eval• (assocl₂₁₊⇛ b) = record { f = assocl₊ ; resp• = refl } 
eval• (assocl₂₂₊⇛ c) = record { f = assocl₊ ; resp• = refl } 
eval• (assocr₁₁₊⇛ a) = record { f = assocr₊ ; resp• = refl } 
eval• (assocr₁₂₊⇛ b) = record { f = assocr₊ ; resp• = refl } 
eval• (assocr₂₊⇛ c)  = record { f = assocr₊ ; resp• = refl } 
eval• c = {!!} 

eval :  {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
    •[ A , a ] ⇛ •[ B , b ] → A → B
eval (swap₁₊⇛ a) (inj₁ x) = inj₂ x
eval (swap₁₊⇛ a) (inj₂ y) = inj₁ y
eval (swap₂₊⇛ b) (inj₁ x) = inj₂ x
eval (swap₂₊⇛ b) (inj₂ y) = inj₁ y
eval (assocl₁₊⇛ a) (inj₁ x) = inj₁ (inj₁ x)
eval (assocl₁₊⇛ a) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
eval (assocl₁₊⇛ a) (inj₂ (inj₂ y)) = inj₂ y
eval (assocl₂₁₊⇛ b) (inj₁ x) = inj₁ (inj₁ x)
eval (assocl₂₁₊⇛ b) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
eval (assocl₂₁₊⇛ b) (inj₂ (inj₂ y)) = inj₂ y
eval (assocl₂₂₊⇛ c) (inj₁ x) = inj₁ (inj₁ x)
eval (assocl₂₂₊⇛ c) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
eval (assocl₂₂₊⇛ c) (inj₂ (inj₂ y)) = inj₂ y
eval (assocr₁₁₊⇛ a) (inj₁ (inj₁ x)) = inj₁ x
eval (assocr₁₁₊⇛ a) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
eval (assocr₁₁₊⇛ a) (inj₂ y) = inj₂ (inj₂ y)
eval (assocr₁₂₊⇛ b) (inj₁ (inj₁ x)) = inj₁ x
eval (assocr₁₂₊⇛ b) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
eval (assocr₁₂₊⇛ b) (inj₂ y) = inj₂ (inj₂ y)
eval (assocr₂₊⇛ c) (inj₁ (inj₁ x)) = inj₁ x
eval (assocr₂₊⇛ c) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
eval (assocr₂₊⇛ c) (inj₂ y) = inj₂ (inj₂ y)
eval {b = b} (unite⋆⇛ .b) (tt , x) = x
eval {a = a} (uniti⋆⇛ .a) x = tt , x
eval (swap⋆⇛ a b) (x , y) = y , x
eval (assocl⋆⇛ a b c) (x , y , z) = (x , y) , z
eval (assocr⋆⇛ a b c) ((x , y) , z) = x , y , z
eval (dist₁⇛ a c) (inj₁ x , y) = inj₁ (x , y)
eval (dist₁⇛ a c) (inj₂ x , y) = inj₂ (x , y)
eval (dist₂⇛ b c) (inj₁ x , z) = inj₁ (x , z)
eval (dist₂⇛ b c) (inj₂ y , z) = inj₂ (y , z)
eval (factor₁⇛ a c) (inj₁ (x , y)) = inj₁ x , y
eval (factor₁⇛ a c) (inj₂ (x , y)) = inj₂ x , y
eval (factor₂⇛ b c) (inj₁ (x , y)) = inj₁ x , y
eval (factor₂⇛ b c) (inj₂ (x , y)) = inj₂ x , y
eval {a = a} (id⇛ .a) x = x
eval (trans⇛ c d) x = eval d (eval c x)
eval (plus₁⇛ c d) (inj₁ x) = inj₁ (eval c x)
eval (plus₁⇛ c d) (inj₂ x) = inj₂ (eval d x)
eval (plus₂⇛ c d) (inj₁ x) = inj₁ (eval c x)
eval (plus₂⇛ c d) (inj₂ x) = inj₂ (eval d x)
eval (times⇛ c d) (x , y) = (eval c x , eval d y)

-- and a backwards one too

evalB : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
        •[ A , a ] ⇛ •[ B , b ] → B → A
evalB (swap₂₊⇛ a) (inj₁ x) = inj₂ x
evalB (swap₂₊⇛ a) (inj₂ y) = inj₁ y
evalB (swap₁₊⇛ b) (inj₁ x) = inj₂ x
evalB (swap₁₊⇛ b) (inj₂ y) = inj₁ y
evalB (assocr₂₊⇛ a) (inj₁ x) = inj₁ (inj₁ x)
evalB (assocr₂₊⇛ a) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB (assocr₂₊⇛ a) (inj₂ (inj₂ y)) = inj₂ y
evalB (assocr₁₂₊⇛ b) (inj₁ x) = inj₁ (inj₁ x)
evalB (assocr₁₂₊⇛ b) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB (assocr₁₂₊⇛ b) (inj₂ (inj₂ y)) = inj₂ y
evalB (assocr₁₁₊⇛ c) (inj₁ x) = inj₁ (inj₁ x)
evalB (assocr₁₁₊⇛ c) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB (assocr₁₁₊⇛ c) (inj₂ (inj₂ y)) = inj₂ y
evalB (assocl₂₂₊⇛ a) (inj₁ (inj₁ x)) = inj₁ x
evalB (assocl₂₂₊⇛ a) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB (assocl₂₂₊⇛ a) (inj₂ y) = inj₂ (inj₂ y)
evalB (assocl₂₁₊⇛ b) (inj₁ (inj₁ x)) = inj₁ x
evalB (assocl₂₁₊⇛ b) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB (assocl₂₁₊⇛ b) (inj₂ y) = inj₂ (inj₂ y)
evalB (assocl₁₊⇛ c) (inj₁ (inj₁ x)) = inj₁ x
evalB (assocl₁₊⇛ c) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB (assocl₁₊⇛ c) (inj₂ y) = inj₂ (inj₂ y)
evalB {a = a} (uniti⋆⇛ .a) (tt , x) = x
evalB {b = b} (unite⋆⇛ .b) x = tt , x
evalB (swap⋆⇛ a b) (x , y) = y , x
evalB (assocr⋆⇛ a b c) (x , y , z) = (x , y) , z
evalB (assocl⋆⇛ a b c) ((x , y) , z) = x , y , z
evalB (dist₁⇛ a c) (inj₁ (x , y)) = inj₁ x , y
evalB (dist₁⇛ a c) (inj₂ (x , y)) = inj₂ x , y
evalB (dist₂⇛ b c) (inj₁ (x , z)) = inj₁ x , z
evalB (dist₂⇛ b c) (inj₂ (y , z)) = inj₂ y , z
evalB (factor₁⇛ a c) (inj₁ x , y) = inj₁ (x , y)
evalB (factor₁⇛ a c) (inj₂ x , y) = inj₂ (x , y)
evalB (factor₂⇛ b c) (inj₁ x , y) = inj₁ (x , y)
evalB (factor₂⇛ b c) (inj₂ x , y) = inj₂ (x , y)
evalB {a = a} (id⇛ .a) x = x
evalB (trans⇛ c d) x = evalB c (evalB d x)
evalB (plus₁⇛ c d) (inj₁ x) = inj₁ (evalB c x)
evalB (plus₁⇛ c d) (inj₂ x) = inj₂ (evalB d x)
evalB (plus₂⇛ c d) (inj₁ x) = inj₁ (evalB c x)
evalB (plus₂⇛ c d) (inj₂ x) = inj₂ (evalB d x)
evalB (times⇛ c d) (x , y) = (evalB c x , evalB d y)

eval-resp-• : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
              (c : •[ A , a ] ⇛ •[ B , b ]) → eval c a ≡ b
eval-resp-• (swap₁₊⇛ a) = refl
eval-resp-• (swap₂₊⇛ b) = refl
eval-resp-• (assocl₁₊⇛ a) = refl
eval-resp-• (assocl₂₁₊⇛ b) = refl
eval-resp-• (assocl₂₂₊⇛ c) = refl
eval-resp-• (assocr₁₁₊⇛ a) = refl
eval-resp-• (assocr₁₂₊⇛ b) = refl
eval-resp-• (assocr₂₊⇛ c) = refl
eval-resp-• {b = b} (unite⋆⇛ .b) = refl
eval-resp-• {a = a} (uniti⋆⇛ .a) = refl
eval-resp-• (swap⋆⇛ a b) = refl
eval-resp-• (assocl⋆⇛ a b c) = refl
eval-resp-• (assocr⋆⇛ a b c) = refl
eval-resp-• (dist₁⇛ a c) = refl
eval-resp-• (dist₂⇛ b c) = refl
eval-resp-• (factor₁⇛ a c) = refl
eval-resp-• (factor₂⇛ b c) = refl
eval-resp-• {a = a} (id⇛ .a) = refl
eval-resp-• {a = a} (trans⇛ c d) rewrite eval-resp-• c | eval-resp-• d = refl
eval-resp-• (plus₁⇛ c d) rewrite eval-resp-• c = refl 
eval-resp-• (plus₂⇛ c d) rewrite eval-resp-• d = refl 
eval-resp-• (times⇛ c d) rewrite eval-resp-• c | eval-resp-• d = refl 

eval-gives-id⇛ : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → 
  (c : •[ A , a ] ⇛ •[ B , b ]) → •[ B , eval c a ] ⇛ •[ B , b ]
eval-gives-id⇛ {b = b} c rewrite eval-resp-• c = id⇛ b

------------------------------------------------------------------------------
-- Univalence
-- 
-- as a postulate for now but hopefully we can actually prove it since
-- the pi-combinators are sound and complete for isomorphisms between
-- finite types

postulate 
  univalence : {ℓ : Level} {A B : Set ℓ} → (Path A B) ≃ (A ≃ B)

-- This is at the wrong level... We need to define equivalences ≃ between
-- pointed sets too...

path2iso : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → Path a b → A ≃ B
path2iso {ℓ} {A} {B} {a} {b} p = (eval p , {!!})

------------------------------------------------------------------------------
{--

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
