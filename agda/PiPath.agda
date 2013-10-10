{-# OPTIONS --no-termination-check #-}

module PiPath where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Universe of types

-- The type < v > is the singleton type containing the one value v. We can
-- construct values of this type using (singleton v' proof) where the proof
-- asserts that v is propositionally equal to v.

data <_> {a : Level} {A : Set a} (x : A) : Set a where
  singleton : (y : A) → y ≡ x → < x > 

-- The types of Pi include 0, 1, +, * as usual but 

data B : Set where
  ZERO   : B 
  ONE    : B
  PLUS   : B → B → B
  TIMES  : B → B → B
  RECIP  : B → (B → B) → B

⟦_⟧ : B → Set
⟦ ZERO ⟧        = ⊥
⟦ ONE ⟧         = ⊤
⟦ PLUS b₁ b₂ ⟧  = ⟦ b₁ ⟧ ⊎ ⟦ b₂ ⟧
⟦ TIMES b₁ b₂ ⟧ = ⟦ b₁ ⟧ × ⟦ b₂ ⟧
⟦ RECIP b ⟧     = (v : ⟦ b ⟧) → ⊤

------------------------------------------------------------------------------
-- syntax and types of combinators ⟷ refers to eval
-- eval refers to evalB
-- evalB refers to eval and reverse
-- reverse refers to reverse'
-- reverse' refers to reverse

-- syntax and types of combinators

data _⟷_ : B → B → Set₁ where
  unite₊ : {b : B} → PLUS ZERO b ⟷ b
  uniti₊ : {b : B} → b ⟷ PLUS ZERO b
  swap₊ : {b₁ b₂ : B} → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
  unite⋆  : { b : B } → TIMES ONE b ⟷ b
  uniti⋆  : { b : B } → b ⟷ TIMES ONE b
  swap⋆ : {b₁ b₂ : B} → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
  id⟷ : {b : B } → b ⟷ b
  op    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)
  ε : {b₁ : B} → TIMES b₁ (TIMES b₁ (RECIP b₁)) ⟷ b₁

-- Semantics
mutual 
  eval : {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
  eval unite₊ (inj₁ ())
  eval unite₊ (inj₂ v) = v
  eval uniti₊ v = inj₂ v
  eval swap₊ (inj₁ x) = inj₂ x
  eval swap₊ (inj₂ y) = inj₁ y
  eval assocl₊ (inj₁ x) = inj₁ (inj₁ x)
  eval assocl₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  eval assocl₊ (inj₂ (inj₂ x)) = inj₂ x
  eval assocr₊ (inj₁ (inj₁ x)) = inj₁ x
  eval assocr₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  eval assocr₊ (inj₂ y) = inj₂ (inj₂ y)
  eval unite⋆ (tt , x) = x
  eval uniti⋆ v = ( tt , v)
  eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
  eval assocl⋆ (x , (y , z)) = ((x , y), z)
  eval assocr⋆ ((x , y), z) = (x , (y , z))
  eval id⟷ v = v
  eval (op c) v = evalB c v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (inj₁ x) = inj₁ (eval c₁ x)
  eval (c₁ ⊕ c₂) (inj₂ y) = inj₂ (eval c₂ y)
  eval (c₁ ⊗ c₂) (x , y) = (eval c₁ x , eval c₂ y)
  eval ε (x , y , z) = x

  evalB :  {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → ⟦ b₂ ⟧ → ⟦ b₁ ⟧
  evalB uniti₊ (inj₁ ())
  evalB uniti₊ (inj₂ v) = v
  evalB unite₊ v = inj₂ v
  evalB swap₊ (inj₁ x) = inj₂ x
  evalB swap₊ (inj₂ y) = inj₁ y
  evalB assocr₊ (inj₁ x) = inj₁ (inj₁ x)
  evalB assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalB assocr₊ (inj₂ (inj₂ x)) = inj₂ x
  evalB assocl₊ (inj₁ (inj₁ x)) = inj₁ x
  evalB assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalB assocl₊ (inj₂ y) = inj₂ (inj₂ y)
  evalB uniti⋆ (tt , x) = x
  evalB unite⋆ v = ( tt , v)
  evalB swap⋆ (v₁ , v₂) = (v₂ , v₁)
  evalB assocr⋆ (x , (y , z)) = ((x , y), z)
  evalB assocl⋆ ((x , y), z) = (x , (y , z))
  evalB id⟷ v = v
  evalB (op c) v = eval c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (inj₁ x) = inj₁ (evalB c₁ x)
  evalB (c₁ ⊕ c₂) (inj₂ y) = inj₂ (evalB c₂ y)
  evalB (c₁ ⊗ c₂) (x , y) = (evalB c₁ x , evalB c₂ y)
  evalB ε x = x , x , (λ _ → tt)

-- reversibility
mutual
  reverse : {b₁ b₂ : B} (c : b₁ ⟷ b₂) → (v : ⟦ b₁ ⟧) → v ≡ evalB c (eval c v)
  reverse unite₊ (inj₁ ())
  reverse unite₊ (inj₂ y) = refl
  reverse uniti₊ v = refl
  reverse swap₊ (inj₁ x) = refl
  reverse swap₊ (inj₂ y) = refl
  reverse assocl₊ (inj₁ x) = refl
  reverse assocl₊ (inj₂ (inj₁ x)) = refl
  reverse assocl₊ (inj₂ (inj₂ y)) = refl
  reverse assocr₊ (inj₁ (inj₁ x)) = refl
  reverse assocr₊ (inj₁ (inj₂ y)) = refl
  reverse assocr₊ (inj₂ y) = refl
  reverse unite⋆ v = refl
  reverse uniti⋆ v = refl
  reverse swap⋆ v = refl
  reverse assocl⋆ v = refl
  reverse assocr⋆ v = refl
  reverse id⟷ v = refl
  reverse (op c) v = reverse' c v
  reverse (c ◎ c₁) v = trans (reverse c v) 
                             (cong (evalB c) (reverse c₁ (eval c v)))
  reverse (c ⊕ _) (inj₁ x) = cong inj₁ (reverse c x)
  reverse (_ ⊕ c) (inj₂ y) = cong inj₂ (reverse c y)
  reverse (c₁ ⊗ c₂) (x , y) = cong₂ _,_ (reverse c₁ x) (reverse c₂ y)
  reverse ε (x , y , z) = {!!}

  reverse' : {b₁ b₂ : B} (c : b₁ ⟷ b₂) → (w : ⟦ b₂ ⟧) → w ≡ eval c (evalB c w)
  reverse' unite₊ w = refl
  reverse' uniti₊ (inj₁ ())
  reverse' uniti₊ (inj₂ y) = refl
  reverse' swap₊ (inj₁ x) = refl
  reverse' swap₊ (inj₂ y) = refl
  reverse' assocl₊ (inj₁ (inj₁ x)) = refl
  reverse' assocl₊ (inj₁ (inj₂ y)) = refl
  reverse' assocl₊ (inj₂ y) = refl
  reverse' assocr₊ (inj₁ x) = refl
  reverse' assocr₊ (inj₂ (inj₁ x)) = refl
  reverse' assocr₊ (inj₂ (inj₂ y)) = refl
  reverse' unite⋆ w = refl
  reverse' uniti⋆ w = refl
  reverse' swap⋆ w = refl
  reverse' assocl⋆ w = refl
  reverse' assocr⋆ w = refl
  reverse' id⟷ w = refl
  reverse' (op c) w = reverse c w
  reverse' (c ◎ c₁) w = trans (reverse' c₁ w) 
                              (cong (eval c₁) (reverse' c (evalB c₁ w)))
  reverse' (c ⊕ _) (inj₁ x) = cong inj₁ (reverse' c x)
  reverse' (_ ⊕ c) (inj₂ y) = cong inj₂ (reverse' c y)
  reverse' (c₁ ⊗ c₂) (x , y) = cong₂ _,_ (reverse' c₁ x) (reverse' c₂ y)
  reverse' ε _ = refl
------------------------------------------------------------------------------
-- Proofs of reversibility
{-
-- they are properly inverse of each other
-- easy direction
η∘ε : {b : B} (v : ⟦ b ⟧) → eval {b} (η ◎ ε) v ≡ v
η∘ε _ = refl

-- hard direction.
ε∘η : {b : B} (v : ⟦ b ⟧) → { w : Σ < v > (λ _ → < v > → ⊤) } 
      → (eval {DTIMES b (leftIdemp {b}) } {_} (ε ◎ η) (v , w)) ≡ (v , w)
ε∘η {b} v {(singleton .v refl , r )} = cong f {v , v , (singleton v refl)} refl
    where f : Σ ⟦ b ⟧ (λ x → Σ ⟦ b ⟧ (λ y → < v >)) → 
                Σ ⟦ b ⟧ (λ z → Σ < z > (λ x → < z > → ⊤ ))
          f (_ , (_ , j)) = (v , j , r)

------------------------------------------------------------------------------
-- Examples
-- Now need to write some actual programs...

makeFunc : {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → 
            b₁ ⟷ DTIMES b₁ (λ x → TIMES (SING (eval c x)) (RECIP x))
makeFunc c = η ◎ slide (λ {_} →  (lift c refl) ⊗ id⟷)

-}
------------------------------------------------------------------------------
------------------------------------------------------------------------------


