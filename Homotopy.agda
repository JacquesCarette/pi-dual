module Homotopy where

infixr 20 _◎_

open import Data.Product

------------------------------------------------------------------------------
-- Level 0
-- Start with this set and its elements

data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

------------------------------------------------------------------------------
-- Level 1
-- Now we introduce Id_B. Given b1 : B, b2 : B, we have the types
-- Id_B(b1,b2) of equivalences

data Id_B : B × B → Set where
  unite₊  : { b : B } → Id_B (PLUS ZERO b , b) 
  uniti₊  : { b : B } → Id_B (b , PLUS ZERO b) 
  swap₊   : { b₁ b₂ : B } → Id_B (PLUS b₁ b₂ , PLUS b₂ b₁)
  assocl₊ : { b₁ b₂ b₃ : B } → Id_B (PLUS b₁ (PLUS b₂ b₃) , PLUS (PLUS b₁ b₂) b₃)
  assocr₊ : { b₁ b₂ b₃ : B } → Id_B (PLUS (PLUS b₁ b₂) b₃ , PLUS b₁ (PLUS b₂ b₃))
  unite⋆  : { b : B } → Id_B (TIMES ONE b , b)
  uniti⋆  : { b : B } → Id_B (b , TIMES ONE b)
  swap⋆   : { b₁ b₂ : B } → Id_B (TIMES b₁ b₂ , TIMES b₂ b₁)
  assocl⋆ : { b₁ b₂ b₃ : B } → Id_B (TIMES b₁ (TIMES b₂ b₃) , TIMES (TIMES b₁ b₂) b₃)
  assocr⋆ : { b₁ b₂ b₃ : B } → Id_B (TIMES (TIMES b₁ b₂) b₃ , TIMES b₁ (TIMES b₂ b₃))
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

-- values

data BVAL : B → Set where
  UNIT : BVAL ONE
  LEFT : {b₁ b₂ : B} → BVAL b₁ → BVAL (PLUS b₁ b₂)
  RIGHT : {b₁ b₂ : B} → BVAL b₂ → BVAL (PLUS b₁ b₂)
  PAIR : {b₁ b₂ : B} → BVAL b₁ → BVAL b₂ → BVAL (TIMES b₁ b₂)

------------------------------------------------------------------------------
-- Level 2

-- Now we introduce Id_{Id_B}. Given c1 : Id_B(b1,b2) and c2 :
-- Id_B(b1,b2), we have the type of equivalences that show that c1 and
-- c2 are isomorphic.

data Id_Id_B : {b₁ b₂ : B} → Id_B (b₁ , b₂) × Id_B (b₁ , b₂) → Set where
