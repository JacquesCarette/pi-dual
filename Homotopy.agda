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

-- values

data BVAL : B → Set where
  UNIT : BVAL ONE
  LEFT : {b₁ b₂ : B} → BVAL b₁ → BVAL (PLUS b₁ b₂)
  RIGHT : {b₁ b₂ : B} → BVAL b₂ → BVAL (PLUS b₁ b₂)
  PAIR : {b₁ b₂ : B} → BVAL b₁ → BVAL b₂ → BVAL (TIMES b₁ b₂)

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

------------------------------------------------------------------------------
-- Level 2

-- Now we introduce Id_{Id_B}. Given c1 : Id_B(b1,b2) and c2 :
-- Id_B(b1,b2), we have the type of equivalences that show that c1 and
-- c2 are isomorphic.
--
-- We want:
--
-- data Id_Id_B : {b₁ b₂ : B} → Id_B (b₁ , b₂) × Id_B (b₁ , b₂) → Set where
--  ...
-- but before we do that we need to embed the combinators as values that can
-- be manipulated using combinators

-- define the category Int C whose objects are pairs (B,B) and which has an
-- inverse recip sending (B1,B2) to (B2,B1) and then the compact closed
-- eta/epsilon where eta : I -> (A+,A-) * (recip (A+,A-))

-- the embedding send B to (B,I)

-- INT B has as objects pairs of B objects

{--
data Id_BB : (B × B) × (B × B) → Set where
  intarr : { b₁ b₂ b₃ b₄ : B } → Id_BB ((b₁ , b₂) , (b₃ , b₄))

embedArr : { b₁ b₂ b₃ b₄ : B } → 
           Id_BB ((b₁ , b₂) , (b₃ , b₄)) → Id_B ((b₁ , b₄) , (b₂ , b₃))
embedArr x = ? 




  Iuniti₊  : { b : B } → Id_BB (b , PLUS ZERO b) 
  Iswap₊   : { b₁ b₂ : B } → Id_BB (PLUS b₁ b₂ , PLUS b₂ b₁)
  Iassocl₊ : { b₁ b₂ b₃ : B } → Id_BB (PLUS b₁ (PLUS b₂ b₃) , PLUS (PLUS b₁ b₂) b₃)
  Iassocr₊ : { b₁ b₂ b₃ : B } → Id_BB (PLUS (PLUS b₁ b₂) b₃ , PLUS b₁ (PLUS b₂ b₃))
  Iunite⋆  : { b : B } → Id_BB (TIMES ONE b , b)
  Iuniti⋆  : { b : B } → Id_BB (b , TIMES ONE b)
  Iswap⋆   : { b₁ b₂ : B } → Id_BB (TIMES b₁ b₂ , TIMES b₂ b₁)
  Iassocl⋆ : { b₁ b₂ b₃ : B } → 
            Id_BB (TIMES b₁ (TIMES b₂ b₃) , TIMES (TIMES b₁ b₂) b₃)
  Iassocr⋆ : { b₁ b₂ b₃ : B } → 
            Id_BB (TIMES (TIMES b₁ b₂) b₃ , TIMES b₁ (TIMES b₂ b₃))
  Idist    : { b₁ b₂ b₃ : B } → 
            Id_BB (TIMES (PLUS b₁ b₂) b₃ , PLUS (TIMES b₁ b₃) (TIMES b₂ b₃))
  Ifactor  : { b₁ b₂ b₃ : B } → 
            Id_BB (PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) , TIMES (PLUS b₁ b₂) b₃)
  Iid⟷   : { b : B } → Id_BB (b , b)
  Isym    : { b₁ b₂ : B } → Id_BB (b₁ , b₂) → Id_BB (b₂ , b₁)
  _I◎_    : { b₁ b₂ b₃ : B } → Id_BB (b₁ , b₂) → Id_BB (b₂ , b₃) → Id_BB (b₁ , b₃)
  _I⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           Id_BB (b₁ , b₃) → Id_BB (b₂ , b₄) → Id_BB (PLUS b₁ b₂ , PLUS b₃ b₄)
  _I⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           Id_BB (b₁ , b₃) → Id_BB (b₂ , b₄) → Id_BB (TIMES b₁ b₂ , TIMES b₃ b₄)

data BRVAL : BR → Set where
  UNITR : BRVAL ONER
  LEFTR : {b₁ b₂ : BR} → BRVAL b₁ → BRVAL (PLUSR b₁ b₂)
  RIGHTR : {b₁ b₂ : BR} → BRVAL b₂ → BRVAL (PLUSR b₁ b₂)
  PAIRR : {b₁ b₂ : BR} → BRVAL b₁ → BRVAL b₂ → BRVAL (TIMESR b₁ b₂)
  RECIPR : {b : BR} → BRVAL b → BRVAL (RECIP b)

embedT : B → BR
embedT ZERO = ZEROR
embedT ONE = ONER
embedT (PLUS b₁ b₂) = PLUSR (embedT b₁) (embedT b₂)
embedT (TIMES b₁ b₂) = TIMESR (embedT b₁) (embedT b₂)

embedV : {b : B} → BVAL b → BRVAL (embedT b)
embedV UNIT = UNITR
embedV (LEFT v) = LEFTR (embedV v)
embedV (RIGHT v) = RIGHTR (embedV v)
embedV (PAIR v₁ v₂) = PAIRR (embedV v₁) (embedV v₂)

embedC : {b₁ b₂ : B} → 
         Id_B (b₁ , b₂) → BRVAL (TIMESR (RECIP (embedT b₁)) (embedT b₂))
embedC unite₊ = ?
embedC uniti₊ = ? 
embedC swap₊ = ? 
embedC assocl₊ = ? 
embedC assocr₊ = ? 
embedC unite⋆ = ? 
embedC uniti⋆ = ? 
embedC swap⋆ = ? 
embedC assocl⋆ = ? 
embedC assocr⋆ = ? 
embedC dist = ? 
embedC factor = ? 
embedC id⟷ = ? 
embedC (sym c) = ? 
embedC (c₁ ◎ c₂) = ? 
embedC (c₁ ⊕ c₂) = ? 
embedC (c₁ ⊗ c₂) = ? 
--}
