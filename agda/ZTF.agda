module ZTF where

open import Data.Integer
open import Data.Product

------------------------------------------------------------------------------
-- Zero totalized fields 

data B : Set where
  ZERO   : B 
  ONE    : B
  PLUS   : B → B → B
  TIMES  : B → B → B
  RECIP  : B → B 
  NEG    : B → B 

normalizeB : B → (ℤ × ℤ)
normalizeB ZERO = (+ 0 , + 1)
normalizeB ONE = (+ 1 , + 1)
normalizeB (PLUS b₁ b₂) with normalizeB b₁ | normalizeB b₂
... | (n1 , d1) | (n2 , d2) = (n1 * d2 + n2 * d1 , d1 * d2)
normalizeB (TIMES b₁ b₂) with normalizeB b₁ | normalizeB b₂
... | (n1 , d1) | (n2 , d2) = (n1 * n2 , d1 * d2)
normalizeB (RECIP b) with normalizeB b
... | (n , d) = (d , n)
normalizeB (NEG b) with normalizeB b
... | (n , d) = (- n , d)

b1 : ℤ × ℤ
b1 = normalizeB (
       RECIP (PLUS 
               (TIMES (PLUS ONE ONE) (PLUS ONE (PLUS ONE ONE)))
               (NEG (TIMES (PLUS ONE ONE) (PLUS ONE (PLUS ONE ONE))))))

ztf : B → B
ztf b with normalizeB b
... | (_ , + 0) = ZERO
... | (+ 0 , _) = ZERO
... | _         = ONE

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
  dist    : { b₁ b₂ b₃ : B } → 
            TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor  : { b₁ b₂ b₃ : B } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
  distZ    : { b : B } → TIMES ZERO b ⟷ ZERO
  factorZ  : { b : B } → ZERO ⟷ TIMES ZERO b
  id⟷ : {b : B } → b ⟷ b
  op    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)
  η : {b : B} → ztf b ⟷ TIMES b (RECIP b)
  ε : {b : B} → TIMES b (RECIP b) ⟷ ztf b

------------------------------------------------------------------------------
