module VecS where

infixr 20 _◎_

open import Data.Product
open import Data.Vec
open import Data.Nat

------------------------------------------------------------------------------

data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

data BVAL : B → Set where
  UNIT : BVAL ONE
  LEFT : {b₁ b₂ : B} → BVAL b₁ → BVAL (PLUS b₁ b₂)
  RIGHT : {b₁ b₂ : B} → BVAL b₂ → BVAL (PLUS b₁ b₂)
  PAIR : {b₁ b₂ : B} → BVAL b₁ → BVAL b₂ → BVAL (TIMES b₁ b₂)

size : B → ℕ
size ZERO = 0
size ONE = 1
size (PLUS b₁ b₂) = size b₁ + size b₂
size (TIMES b₁ b₂) = size b₁ * size b₂

BVEC : B → Set
BVEC b = Vec (BVAL b) (size b)

------------------------------------------------------------------------------
 

{--
data Id_B : {b₁ b₂ : B} → (BVEC b₁ × BVEC b₂) → Set where
  unite₊  : { b : B } → Id_B (PLUS ZERO b , b) 
  uniti₊  : { b : B } → Id_B (b , PLUS ZERO b) 
  swap₊   : { b₁ b₂ : B } → Id_B (PLUS b₁ b₂ , PLUS b₂ b₁)
  assocl₊ : { b₁ b₂ b₃ : B } → Id_B (PLUS b₁ (PLUS b₂ b₃) , PLUS (PLUS b₁ b₂) b₃)
  assocr₊ : { b₁ b₂ b₃ : B } → Id_B (PLUS (PLUS b₁ b₂) b₃ , PLUS b₁ (PLUS b₂ b₃))
  unite⋆  : { b : B } → Id_B (TIMES ONE b , b)
  uniti⋆  : { b : B } → Id_B (b , TIMES ONE b)
  swap⋆   : { b₁ b₂ : B } → Id_B (TIMES b₁ b₂ , TIMES b₂ b₁)
  assocl⋆ : { b₁ b₂ b₃ : B } → 
            Id_B (TIMES b₁ (TIMES b₂ b₃) , TIMES (TIMES b₁ b₂) b₃)
  assocr⋆ : { b₁ b₂ b₃ : B } → 
            Id_B (TIMES (TIMES b₁ b₂) b₃ , TIMES b₁ (TIMES b₂ b₃))
  dist    : { b₁ b₂ b₃ : B } → 
            Id_B (TIMES (PLUS b₁ b₂) b₃ , PLUS (TIMES b₁ b₃) (TIMES b₂ b₃))
  factor  : { b₁ b₂ b₃ : B } → 
            Id_B (PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) , TIMES (PLUS b₁ b₂) b₃)
  id⟷   : { b : B } → Id_B (b , b)
  sym    : { b₁ b₂ : B } → Id_B (b₁ , b₂) → Id_B (b₂ , b₁)
  _◎_    : { b₁ b₂ b₃ : B } → Id_B (b₁ , b₂) → Id_B (b₂ , b₃) → Id_B (b₁ , b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           Id_B (b₁ , b₃) → Id_B (b₂ , b₄) → Id_B (PLUS b₁ b₂ , PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           Id_B (b₁ , b₃) → Id_B (b₂ , b₄) → Id_B (TIMES b₁ b₂ , TIMES b₃ b₄)


mutual

  eval : {b₁ b₂ : B} → Id_B (b₁ , b₂) → BVAL b₁ → BVAL b₂
  eval unite₊ (LEFT ())
  eval unite₊ (RIGHT v) = v
  eval uniti₊ v = RIGHT v
  eval swap₊ (LEFT v) = RIGHT v
  eval swap₊ (RIGHT v) = LEFT v
  eval assocl₊ (LEFT v) = LEFT (LEFT v)
  eval assocl₊ (RIGHT (LEFT v)) = LEFT (RIGHT v)
  eval assocl₊ (RIGHT (RIGHT v)) = RIGHT v
  eval assocr₊ (LEFT (LEFT v)) = LEFT v
  eval assocr₊ (LEFT (RIGHT v)) = RIGHT (LEFT v)
  eval assocr₊ (RIGHT v) = RIGHT (RIGHT v)
  eval unite⋆ (PAIR UNIT v) = v
  eval uniti⋆ v = PAIR UNIT v
  eval swap⋆ (PAIR v1 v2) = PAIR v2 v1
  eval assocl⋆ (PAIR v1 (PAIR v2 v3)) = PAIR (PAIR v1 v2) v3
  eval assocr⋆ (PAIR (PAIR v1 v2) v3) = PAIR v1 (PAIR v2 v3)
  eval dist (PAIR (LEFT v1) v3) = LEFT (PAIR v1 v3)
  eval dist (PAIR (RIGHT v2) v3) = RIGHT (PAIR v2 v3)
  eval factor (LEFT (PAIR v1 v3)) = PAIR (LEFT v1) v3
  eval factor (RIGHT (PAIR v2 v3)) = PAIR (RIGHT v2) v3
  eval id⟷ v = v
  eval (sym c) v = evalB c v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (LEFT v) = LEFT (eval c₁ v)
  eval (c₁ ⊕ c₂) (RIGHT v) = RIGHT (eval c₂ v)
  eval (c₁ ⊗ c₂) (PAIR v₁ v₂) = PAIR (eval c₁ v₁) (eval c₂ v₂)

  evalB : {b₁ b₂ : B} → Id_B (b₁ , b₂) → BVAL b₂ → BVAL b₁
  evalB unite₊ v = RIGHT v
  evalB uniti₊ (LEFT ())
  evalB uniti₊ (RIGHT v) = v
  evalB swap₊ (LEFT v) = RIGHT v
  evalB swap₊ (RIGHT v) = LEFT v
  evalB assocl₊ (LEFT (LEFT v)) = LEFT v
  evalB assocl₊ (LEFT (RIGHT v)) = RIGHT (LEFT v)
  evalB assocl₊ (RIGHT v) = RIGHT (RIGHT v)
  evalB assocr₊ (LEFT v) = LEFT (LEFT v)
  evalB assocr₊ (RIGHT (LEFT v)) = LEFT (RIGHT v)
  evalB assocr₊ (RIGHT (RIGHT v)) = RIGHT v
  evalB unite⋆ v = PAIR UNIT v
  evalB uniti⋆ (PAIR UNIT v) = v
  evalB swap⋆ (PAIR v1 v2) = PAIR v2 v1
  evalB assocl⋆ (PAIR (PAIR v1 v2) v3) = PAIR v1 (PAIR v2 v3)
  evalB assocr⋆ (PAIR v1 (PAIR v2 v3)) = PAIR (PAIR v1 v2) v3
  evalB dist (LEFT (PAIR v1 v3)) = PAIR (LEFT v1) v3
  evalB dist (RIGHT (PAIR v2 v3)) = PAIR (RIGHT v2) v3
  evalB factor (PAIR (LEFT v1) v3) = LEFT (PAIR v1 v3)
  evalB factor (PAIR (RIGHT v2) v3) = RIGHT (PAIR v2 v3)
  evalB id⟷ v = v
  evalB (sym c) v = eval c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (LEFT v) = LEFT (evalB c₁ v)
  evalB (c₁ ⊕ c₂) (RIGHT v) = RIGHT (evalB c₂ v)
  evalB (c₁ ⊗ c₂) (PAIR v₁ v₂) = PAIR (evalB c₁ v₁) (evalB c₂ v₂)
--}

------------------------------------------------------------------------------
