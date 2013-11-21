module F2a where

open import Agda.Prim
open import Data.Unit
open import Data.Sum 
open import Data.Nat hiding (_⊔_)
open import Data.Product
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

---------------------------------------------------------------------------
-- Paths

-- 1-paths are pi-combinators

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
  -- id and trans
  id⇛        : {A : Set ℓ} → (a : A) → •[ A , a ] ⇛ •[ A , a ]
  trans⇛     : {A B C : Set ℓ} {a : A} {b : B} {c : C} → 
               (•[ A , a ] ⇛ •[ B , b ]) → 
               (•[ B , b ] ⇛ •[ C , c ]) → 
               (•[ A , a ] ⇛ •[ C , c ]) 

trans~ : {ℓ : Level} {A B C : Set ℓ} {a : A} {b : B} {c : C} →
         •[ A , a ] ⇛ •[ B , b ] →
         •[ B , b ] ⇛ •[ C , c ] → 
         •[ A , a ] ⇛ •[ C , c ] 
trans~ (id⇛ a) q = q
trans~ (trans⇛ p₁ p₂) q = trans~ p₁ (trans~ p₂ q)
trans~ p q = trans⇛ p q

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
  {A B : Set ℓ} {a : A} {b : B} → (p : •[ A , a ] ⇛ •[ B , b ]) → P p
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (swap₁₊⇛ a) = swap₁₊ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (swap₂₊⇛ b) = swap₂₊ b
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (assocl₁₊⇛ a) = assocl₁₊ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (assocl₂₁₊⇛ b) = assocl₂₁₊ b
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (assocl₂₂₊⇛ c) = assocl₂₂₊ c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (assocr₁₁₊⇛ a) = assocr₁₁₊ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (assocr₁₂₊⇛ b) = assocr₁₂₊ b
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (assocr₂₊⇛ c) = assocr₂₊ c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (unite⋆⇛ a) = unite⋆ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (uniti⋆⇛ a) = uniti⋆ a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (swap⋆⇛ a b) = swap⋆ a b
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (assocl⋆⇛ a b c) = assocl⋆ a b c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (assocr⋆⇛ a b c) = assocr⋆ a b c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (dist₁⇛ a c) = dist₁ a c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (dist₂⇛ b c) = dist₂ b c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (factor₁⇛ a c) = factor₁ a c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (factor₂⇛ b c) = factor₂ b c
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (id⇛ a) = cid a
pathInd P swap₁₊ swap₂₊ 
  assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
  unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
  cid ctrans (trans⇛ p q) = 
    ctrans p q  
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans p)
      (pathInd P swap₁₊ swap₂₊ 
       assocl₁₊ assocl₂₁₊ assocl₂₂₊ assocr₁₁₊ assocr₁₂₊ assocr₂₊ 
       unite⋆ uniti⋆ swap⋆ assocl⋆ assocr⋆ dist₁ dist₂ factor₁ factor₂ 
       cid ctrans q)

-- Abbreviations and small examples

1Path : {ℓ : Level} {A B : Set ℓ} → (a : A) → (b : B) → Set (lsuc (lsuc ℓ))
1Path {ℓ} {A} {B} a b = •[ A , a ] ⇛ •[ B , b ]

2Path : {ℓ : Level} {A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
  (p : 1Path a b) → (q : 1Path c d) → Set (lsuc (lsuc (lsuc (lsuc ℓ))))
2Path {ℓ} {A} {B} {C} {D} {a} {b} {c} {d} p q = 
  •[ 1Path a b , p ] ⇛ •[ 1Path c d , q ]

_≡⟨_⟩_ : ∀ {ℓ} → {A B C : Set ℓ} (a : A) {b : B} {c : C} → 
        1Path a b → 1Path b c → 1Path a c
_ ≡⟨ p ⟩ q = trans⇛ p q

_∎ : ∀ {ℓ} → {A : Set ℓ} (a : A) → 1Path a a
_∎ a = id⇛ a

test3 : {A : Set} {a : A} → Set•
test3 {A} {a} = •[ 1Path a a , id⇛ a ] 

test4 : {A : Set} {a : A} → Set•
test4 {A} {a} = •[ 2Path (id⇛ a) (id⇛ a) , id⇛ (id⇛ a) ]

test5 : {A B C D : Set} {a : A} {b : B} {c : C} {d : D} → 
        (p : 1Path a b) → (q : 1Path c d) → Set•
test5 {A} {B} {C} {D} {a} {b} {c} {d} p q = 
  •[ 1Path a b × 1Path c d , (p , q) ]

-- The groupoid structure emerges...

sym⇛ : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → 1Path a b → 1Path b a
sym⇛ {ℓ} {A} {B} {a} {b} p = 
  (pathInd 
    (λ {A} {B} {a} {b} p → 1Path b a)
    swap₂₊⇛ swap₁₊⇛ 
    assocr₁₁₊⇛ assocr₁₂₊⇛ assocr₂₊⇛ assocl₁₊⇛ assocl₂₁₊⇛ assocl₂₂₊⇛ 
    uniti⋆⇛ unite⋆⇛ (λ a b → swap⋆⇛ b a) 
    assocr⋆⇛ assocl⋆⇛ factor₁⇛ factor₂⇛ dist₁⇛ dist₂⇛ 
    id⇛ (λ _ _ p' q' → trans⇛ q' p'))
  {A} {B} {a} {b} p 

test6 : {A : Set} {a : A} → 1Path a (tt , a)
test6 {A} {a} = sym⇛ (unite⋆⇛ a) -- evaluates to (uniti⋆⇛ a)

idright : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} {p : 1Path a b} →
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
    {!!})
  {A} {B} {a} {b} p

{--
?0 : {A₁ B₁ : Set ℓ} (a₁ : A₁) →
     2Path (trans⇛ (swap₁₊⇛ a₁) (id⇛ (inj₂ a₁))) (swap₁₊⇛ a₁)
?1 : {A₁ B₁ : Set ℓ} (b₁ : B₁) →
     2Path (trans⇛ (swap₂₊⇛ b₁) (id⇛ (inj₁ b₁))) (swap₂₊⇛ b₁)
?2 : {A₁ B₁ C : Set ℓ} (a₁ : A₁) →
     2Path (trans⇛ (assocl₁₊⇛ a₁) (id⇛ (inj₁ (inj₁ a₁)))) (assocl₁₊⇛ a₁)
?3 : {A₁ B₁ C : Set ℓ} (b₁ : B₁) →
     2Path (trans⇛ (assocl₂₁₊⇛ b₁) (id⇛ (inj₁ (inj₂ b₁))))
     (assocl₂₁₊⇛ b₁)
?4 : {A₁ B₁ C : Set ℓ} (c : C) →
     2Path (trans⇛ (assocl₂₂₊⇛ c) (id⇛ (inj₂ c))) (assocl₂₂₊⇛ c)
?5 : {A₁ B₁ C : Set ℓ} (a₁ : A₁) →
     2Path (trans⇛ (assocr₁₁₊⇛ a₁) (id⇛ (inj₁ a₁))) (assocr₁₁₊⇛ a₁)
?6 : {A₁ B₁ C : Set ℓ} (b₁ : B₁) →
     2Path (trans⇛ (assocr₁₂₊⇛ b₁) (id⇛ (inj₂ (inj₁ b₁))))
     (assocr₁₂₊⇛ b₁)
?7 : {A₁ B₁ C : Set ℓ} (c : C) →
     2Path (trans⇛ (assocr₂₊⇛ c) (id⇛ (inj₂ (inj₂ c)))) (assocr₂₊⇛ c)
?8 : {A₁ : Set ℓ} (a₁ : A₁) →
     2Path (trans⇛ (unite⋆⇛ a₁) (id⇛ a₁)) (unite⋆⇛ a₁)
?9 : {A₁ : Set ℓ} (a₁ : A₁) →
     2Path (trans⇛ (uniti⋆⇛ a₁) (id⇛ (tt , a₁))) (uniti⋆⇛ a₁)
?10 : {A₁ B₁ : Set ℓ} (a₁ : A₁) (b₁ : B₁) →
      2Path (trans⇛ (swap⋆⇛ a₁ b₁) (id⇛ (b₁ , a₁))) (swap⋆⇛ a₁ b₁)
?11 : {A₁ B₁ C : Set ℓ} (a₁ : A₁) (b₁ : B₁) (c : C) →
      2Path (trans⇛ (assocl⋆⇛ a₁ b₁ c) (id⇛ ((a₁ , b₁) , c)))
      (assocl⋆⇛ a₁ b₁ c)
?12 : {A₁ B₁ C : Set ℓ} (a₁ : A₁) (b₁ : B₁) (c : C) →
      2Path (trans⇛ (assocr⋆⇛ a₁ b₁ c) (id⇛ (a₁ , b₁ , c)))
      (assocr⋆⇛ a₁ b₁ c)
?13 : {A₁ B₁ C : Set ℓ} (a₁ : A₁) (c : C) →
      2Path (trans⇛ (dist₁⇛ a₁ c) (id⇛ (inj₁ (a₁ , c)))) (dist₁⇛ a₁ c)
?14 : {A₁ B₁ C : Set ℓ} (b₁ : B₁) (c : C) →
      2Path (trans⇛ (dist₂⇛ b₁ c) (id⇛ (inj₂ (b₁ , c)))) (dist₂⇛ b₁ c)
?15 : {A₁ B₁ C : Set ℓ} (a₁ : A₁) (c : C) →
      2Path (trans⇛ (factor₁⇛ a₁ c) (id⇛ (inj₁ a₁ , c))) (factor₁⇛ a₁ c)
?16 : {A₁ B₁ C : Set ℓ} (b₁ : B₁) (c : C) →
      2Path (trans⇛ (factor₂⇛ b₁ c) (id⇛ (inj₂ b₁ , c))) (factor₂⇛ b₁ c)
?17 : {A₁ : Set ℓ} (a₁ : A₁) → 2Path (trans⇛ (id⇛ a₁) (id⇛ a₁)) (id⇛ a₁)
?18 : {A₁ B₁ C : Set ℓ} {a₁ : A₁} {b₁ : B₁} {c : C}
      (p₁ : •[ A₁ , a₁ ] ⇛ •[ B₁ , b₁ ])
      (q : •[ B₁ , b₁ ] ⇛ •[ C , c ]) →
      2Path (trans⇛ p₁ (id⇛ b₁)) p₁ →
      2Path (trans⇛ q (id⇛ c)) q →
      2Path (trans⇛ (trans⇛ p₁ q) (id⇛ c)) (trans⇛ p₁ q)
--}

aptransL : {ℓ : Level} {A B C : Set ℓ} {a : A} {b : B} {c : C} → 
           (p q : 1Path a b) → (r : 1Path b c) → (α : 2Path p q) → 
           2Path (trans⇛ p r) (trans⇛ q r)
aptransL {ℓ} {A} {B} {C} {a} {b} {c} p q r α = 
  (pathInd 
    (λ {B} {C} {b} {c} r → (A : Set ℓ) → (a : A) → (p q : 1Path a b) → 
      (α : 2Path p q) → 2Path (trans⇛ p r) (trans⇛ q r))
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

{--
?19 : {A₁ B₁ : Set ℓ} (a₁ : A₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ (inj₁ a₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (swap₁₊⇛ a₁)) (trans⇛ q₁ (swap₁₊⇛ a₁))
?20 : {A₁ B₁ : Set ℓ} (b₁ : B₁) (A₂ : Set ℓ) (a₁ : A₂)
      (p₁ q₁ : 1Path a₁ (inj₂ b₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (swap₂₊⇛ b₁)) (trans⇛ q₁ (swap₂₊⇛ b₁))
?21 : {A₁ B₁ C₁ : Set ℓ} (a₁ : A₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ (inj₁ a₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (assocl₁₊⇛ a₁)) (trans⇛ q₁ (assocl₁₊⇛ a₁))
?22 : {A₁ B₁ C₁ : Set ℓ} (b₁ : B₁) (A₂ : Set ℓ) (a₁ : A₂)
      (p₁ q₁ : 1Path a₁ (inj₂ (inj₁ b₁))) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (assocl₂₁₊⇛ b₁)) (trans⇛ q₁ (assocl₂₁₊⇛ b₁))
?23 : {A₁ B₁ C₁ : Set ℓ} (c₁ : C₁) (A₂ : Set ℓ) (a₁ : A₂)
      (p₁ q₁ : 1Path a₁ (inj₂ (inj₂ c₁))) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (assocl₂₂₊⇛ c₁)) (trans⇛ q₁ (assocl₂₂₊⇛ c₁))
?24 : {A₁ B₁ C₁ : Set ℓ} (a₁ : A₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ (inj₁ (inj₁ a₁))) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (assocr₁₁₊⇛ a₁)) (trans⇛ q₁ (assocr₁₁₊⇛ a₁))
?25 : {A₁ B₁ C₁ : Set ℓ} (b₁ : B₁) (A₂ : Set ℓ) (a₁ : A₂)
      (p₁ q₁ : 1Path a₁ (inj₁ (inj₂ b₁))) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (assocr₁₂₊⇛ b₁)) (trans⇛ q₁ (assocr₁₂₊⇛ b₁))
?26 : {A₁ B₁ C₁ : Set ℓ} (c₁ : C₁) (A₂ : Set ℓ) (a₁ : A₂)
      (p₁ q₁ : 1Path a₁ (inj₂ c₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (assocr₂₊⇛ c₁)) (trans⇛ q₁ (assocr₂₊⇛ c₁))
?27 : {A₁ : Set ℓ} (a₁ : A₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ (tt , a₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (unite⋆⇛ a₁)) (trans⇛ q₁ (unite⋆⇛ a₁))
?28 : {A₁ : Set ℓ} (a₁ : A₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ a₁) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (uniti⋆⇛ a₁)) (trans⇛ q₁ (uniti⋆⇛ a₁))
?29 : {A₁ B₁ : Set ℓ} (a₁ : A₁) (b₁ : B₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ (a₁ , b₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (swap⋆⇛ a₁ b₁)) (trans⇛ q₁ (swap⋆⇛ a₁ b₁))
?30 : {A₁ B₁ C₁ : Set ℓ} (a₁ : A₁) (b₁ : B₁) (c₁ : C₁) (A₂ : Set ℓ)
      (a₂ : A₂) (p₁ q₁ : 1Path a₂ (a₁ , b₁ , c₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (assocl⋆⇛ a₁ b₁ c₁))
      (trans⇛ q₁ (assocl⋆⇛ a₁ b₁ c₁))
?31 : {A₁ B₁ C₁ : Set ℓ} (a₁ : A₁) (b₁ : B₁) (c₁ : C₁) (A₂ : Set ℓ)
      (a₂ : A₂) (p₁ q₁ : 1Path a₂ ((a₁ , b₁) , c₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (assocr⋆⇛ a₁ b₁ c₁))
      (trans⇛ q₁ (assocr⋆⇛ a₁ b₁ c₁))
?32 : {A₁ B₁ C₁ : Set ℓ} (a₁ : A₁) (c₁ : C₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ (inj₁ a₁ , c₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (dist₁⇛ a₁ c₁)) (trans⇛ q₁ (dist₁⇛ a₁ c₁))
?33 : {A₁ B₁ C₁ : Set ℓ} (b₁ : B₁) (c₁ : C₁) (A₂ : Set ℓ) (a₁ : A₂)
      (p₁ q₁ : 1Path a₁ (inj₂ b₁ , c₁)) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (dist₂⇛ b₁ c₁)) (trans⇛ q₁ (dist₂⇛ b₁ c₁))
?34 : {A₁ B₁ C₁ : Set ℓ} (a₁ : A₁) (c₁ : C₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ (inj₁ (a₁ , c₁))) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (factor₁⇛ a₁ c₁)) (trans⇛ q₁ (factor₁⇛ a₁ c₁))
?35 : {A₁ B₁ C₁ : Set ℓ} (b₁ : B₁) (c₁ : C₁) (A₂ : Set ℓ) (a₁ : A₂)
      (p₁ q₁ : 1Path a₁ (inj₂ (b₁ , c₁))) →
      2Path p₁ q₁ →
      2Path (trans⇛ p₁ (factor₂⇛ b₁ c₁)) (trans⇛ q₁ (factor₂⇛ b₁ c₁))
?36 : {A₁ : Set ℓ} (a₁ : A₁) (A₂ : Set ℓ) (a₂ : A₂)
      (p₁ q₁ : 1Path a₂ a₁) →
      2Path p₁ q₁ → 2Path (trans⇛ p₁ (id⇛ a₁)) (trans⇛ q₁ (id⇛ a₁))
?37 : {A₁ B₁ C₁ : Set ℓ} {a₁ : A₁} {b₁ : B₁} {c₁ : C₁}
      (p₁ : •[ A₁ , a₁ ] ⇛ •[ B₁ , b₁ ])
      (q₁ : •[ B₁ , b₁ ] ⇛ •[ C₁ , c₁ ]) →
      ((A₂ : Set ℓ) (a₂ : A₂) (p₂ q₂ : 1Path a₂ a₁) →
      2Path p₂ q₂ → 2Path (trans⇛ p₂ p₁) (trans⇛ q₂ p₁)) →
      ((A₂ : Set ℓ) (a₂ : A₂) (p₂ q₂ : 1Path a₂ b₁) →
      2Path p₂ q₂ → 2Path (trans⇛ p₂ q₁) (trans⇛ q₂ q₁)) →
      (A₂ : Set ℓ) (a₂ : A₂) (p₂ q₂ : 1Path a₂ a₁) →
      2Path p₂ q₂ →
      2Path (trans⇛ p₂ (trans⇛ p₁ q₁)) (trans⇛ q₂ (trans⇛ p₁ q₁))
--}

symsym : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → (p : 1Path a b) → 
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
    (λ p q α β → {!!}))
  {A} {B} {a} {b} p

{--
?38 : 2Path (sym⇛ (sym⇛ (trans⇛ p q))) (trans⇛ p q)
--}

-- Total cheat, but still shows the 'right' idea somehow
-- the code below was obtained by
-- ctrl-c ctrl-c on the argument of eval
-- for each line: ctr-c ctr-r, ctrl-c ctrl-a twice !
eval :  {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
    •[ A , a ] ⇛ •[ B , b ] → (Σ (A → B) (λ f → f a ≡ b ))
eval (swap₁₊⇛ a) = (λ _ → inj₂ a) , refl
eval (swap₂₊⇛ b) = (λ _ → inj₁ b) , refl
eval (assocl₁₊⇛ a) = (λ _ → inj₁ (inj₁ a)) , refl
eval (assocl₂₁₊⇛ b) = (λ _ → inj₁ (inj₂ b)) , refl
eval (assocl₂₂₊⇛ c) = (λ _ → inj₂ c) , refl
eval (assocr₁₁₊⇛ a) = (λ _ → inj₁ a) , refl
eval (assocr₁₂₊⇛ b) = (λ _ → inj₂ (inj₁ b)) , refl
eval (assocr₂₊⇛ c) = (λ _ → inj₂ (inj₂ c)) , refl
eval {b = b} (unite⋆⇛ .b) = (λ x → b) , refl
eval {a = a} (uniti⋆⇛ .a) = (λ x → tt , a) , refl
eval (swap⋆⇛ a b) = (λ x → b , proj₁ x) , refl
eval (assocl⋆⇛ a b c) = (λ z → (a , b) , proj₂ (proj₂ z)) , refl
eval (assocr⋆⇛ a b c) = (λ z → a , b , proj₂ z) , refl
eval (dist₁⇛ a c) = (λ z → inj₁ (a , proj₂ z)) , refl
eval (dist₂⇛ b c) = (λ z → inj₂ (b , proj₂ z)) , refl
eval (factor₁⇛ a c) = (λ _ → inj₁ a , c) , refl
eval (factor₂⇛ b c) = (λ _ → inj₂ b , c) , refl
eval {a = a} (id⇛ .a) = (λ z → z) , refl
eval {b = b} (trans⇛ c c₁) = (λ _ → b) , refl 

eval2 :  {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
    •[ A , a ] ⇛ •[ B , b ] → (A → B)
eval2 c = proj₁ (eval c)


------------------------------------------------------------------------------
{--

  trans⇛     : {A B C : Set ℓ} {a : A} {b : B} {c : C} → 
               (•[ A , a ] ⇛ •[ B , b ]) → (•[ B , b ] ⇛ •[ C , c ]) →
               (•[ A , a ] ⇛ •[ C , c ])
  plus₁⇛     : {A B C D : Set ℓ} {a : A} {c : C} → 
               (•[ A , a ] ⇛ •[ C , c ]) →
               (•[ A ⊎ B , inj₁ a ] ⇛ •[ C ⊎ D , inj₁ c ])
  plus₂⇛     : {A B C D : Set ℓ} {b : B} {d : D} → 
               (•[ B , b ] ⇛ •[ D , d ]) →
               (•[ A ⊎ B , inj₂ b ] ⇛ •[ C ⊎ D , inj₂ d ])
  times⇛     : {A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
               (•[ A , a ] ⇛ •[ C , c ]) → (•[ B , b ] ⇛ •[ D , d ]) →
               (•[ A × B , (a , b) ] ⇛ •[ C × D , (c , d) ])
  ({A B : Set ℓ} {a : A} {b : B} → 
    (p : (•[ A , a ] ⇛ •[ B , b ])) → P p → P (sym⇛ p)) →
  ({A B C : Set ℓ} {a : A} {b : B} {c : C} → 
    (p : (•[ A , a ] ⇛ •[ B , b ])) → 
    (q : (•[ B , b ] ⇛ •[ C , c ])) → 
    P p → P q → P (trans⇛ p q)) → 
  ({A B C D : Set ℓ} {a : A} {c : C} → (p : (•[ A , a ] ⇛ •[ C , c ])) → 
    P p → P (plus₁⇛ {ℓ} {A} {B} {C} {D} {a} {c} p)) → 
  ({A B C D : Set ℓ} {b : B} {d : D} → (q : (•[ B , b ] ⇛ •[ D , d ])) → 
    P q → P (plus₂⇛ {ℓ} {A} {B} {C} {D} {b} {d} q)) → 
  ({A B C D : Set ℓ} {a : A} {b : B} {c : C} {d : D} → 
    (p : (•[ A , a ] ⇛ •[ C , c ])) → 
    (q : (•[ B , b ] ⇛ •[ D , d ])) → 
    P p → P q → P (times⇛ p q)) → 


?17 : {A₁ : Set ℓ} (a₁ : A₁) → 
      2Path (trans⇛ (id⇛ a₁) (id⇛ a₁)) (id⇛ a₁)

?0 : {A₁ B₁ : Set ℓ} (a₁ : A₁) →
     2Path (trans⇛ (swap₁₊⇛ a₁) (id⇛ (inj₂ a₁))) (swap₁₊⇛ a₁)

--

     •[ 1Path (inj₁ a) (inj₂ a) , trans⇛ (swap₁₊⇛ a) (id⇛ (inj₂ a)) ]
   ⇛ •[ 1Path (inj₁ a) (inj₂ a) , swap₁₊⇛ a ]

--

     •[ •[ A ⊎ B , inj₁ a ] ⇛ •[ B ⊎ A , inj₂ a ] , 
        trans⇛ (swap₁₊⇛ a) (id⇛ (inj₂ a)) ]

   ⇛ •[ •[ A ⊎ B , inj₁ a ] ⇛ •[ B ⊎ A , inj₂ a ] , 
        swap₁₊⇛ a ]

-- use path induction to prove trans p id = p and so on

-- abbrev to path types Path A B instead of •[ A , a ] ⇛ • [ B , b ]
-- proof of idright: neat. provide a proof for each possible path that
   p could be...

-- 2-paths 

data _2⇛_ : {A B C D : Set} {a : A} {b : B} {c : C} {d : D} → 
            (•[ A , a ] ⇛ •[ B , b ]) → (•[ C , c ] ⇛ •[ D , d ]) → Set₂ where
  2Path : {A B C D : Set} 
          {a : A} {b : B} {c : C} {d : D}
          {p : •[ A , a ] ⇛ •[ B , b ]}
          {q : •[ C , c ] ⇛ •[ D , d ]} →
          (•[ C , c ] ⇛ •[ A , a ]) → (•[ B , b ] ⇛ •[ D , d ]) → 
          (p 2⇛ q)



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

--  id2⇛ : {A B : Set} {a : A} {b : B} {p : •[ A , a ] ⇛ •[ B , b ]} → p 2⇛ p

-- Paths as data

Path : ∀ {ℓ} {A B : Set ℓ} {a : • A} {b : • B} → (a ⇛ b) → • (a ⇛ b)
Path p = ↑ p

data _2⇛_ {ℓ : Level} : {A B : Set ℓ} → • A → • B → Set (lsuc ℓ) where

xη⇛ : ∀ {ℓ} {A : Set ℓ} {a : • A} → 
     One ⇛ (Times (Path (create⇛ {ℓ} {A} {a})) (Path (annihilate⇛ {ℓ} {A} {a})))
xη⇛ = {!!}

-- Introduce equational reasoning syntax to simplify proofs

_≡⟨_⟩_ : ∀ {ℓ} {A B C : Set ℓ} (a : • A) {b : • B} {c : • C} → 
        (a ⇛ b) → (b ⇛ c) → (a ⇛ c)
_ ≡⟨ p ⟩ q = trans⇛ p q

bydef : ∀ {ℓ} {A : Set ℓ} {a : • A} → (a ⇛ a)
bydef = id⇛ 

_∎ : ∀ {ℓ} {A : Set ℓ} {a : • A} → (a ⇛ a)
_∎ = id⇛ 

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
