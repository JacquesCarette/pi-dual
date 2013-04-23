module ZTF where

infixr 40 _◎_

open import Data.Integer
open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Zero totalized fields 

data B : Set where
  ZERO   : B 
  ONE    : B
  PLUS   : B → B → B
  TIMES  : B → B → B
  RECIP  : B → B 
  NEG    : B → B 

normalizeB : B → ℤ × ℤ
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

helper : ℤ × ℤ → B
helper (+ 0 , _) = ZERO
helper (_ , + 0) = ZERO
helper _         = ONE

ztf : B → B
ztf b = helper (normalizeB b)

rlem : {b : B} → normalizeB b ≡ swap (normalizeB (RECIP b))
rlem = refl 

{--
helperlem : {z₁ z₂ : ℤ} → helper (z₁ , z₂) ≡ helper (z₂ , z₁)
helperlem {+ 0} {_} = refl
helperlem {_} {+ 0} = refl
helperlem {_} {_} = refl
--}

data X : Set where 
  P0 : X
  P1 : X 
  P2  : X

helperX : X × X → B
helperX (P0 , P0) = ZERO
helperX (_  ,  _) = ZERO
--helperX (P0 , _) = ZERO
--helperX (_ , P0) = ZERO
--helperX _        = ONE

helperlemX : {a b : X} → helperX (a , b) ≡ helperX (b , a)
helperlemX {P0} {P0} = refl 
helperlemX {P1} {P0} = refl 
helperlemX {P2} {P0} = refl 
helperlemX {_} {P1} = refl 
helperlemX {_} {P2} = refl 

blemX : {b : B} → b ≡ b
blemX = refl 


{--
helperlemX : ∀ a b → helperX (a , b) ≡ helperX (b , a)
helperlemX {P0} {P0} = refl
helperlemX {P0} {P1} = refl
helperlemX {P0} {P2} = refl
helperlemX {P1} {P0} = refl
helperlemX {P1} {P1} = refl
helperlemX {P1} {P2} = refl
helperlemX {P2} {P0} = refl
helperlemX {P2} {P1} = refl
helperlemX {P2} {P2} = refl


rlem2 : (b : B) → ztf b ≡ ztf (RECIP b)
rlem2 b = refl

with normalizeB b | normalizeB (RECIP b) 
... | (n , + 0) | .(+ 0 , n) = refl
... | (+ 0 , d) | .(d , + 0) = refl
... | (n  ,  d) | .(d , n)   = refl
--}

data _⟷_ : B → B → Set₁ where
  unite₊ : {b : B} → PLUS ZERO b ⟷ b
  uniti₊ : {b : B} → b ⟷ PLUS ZERO b
  swap₊ : {b₁ b₂ : B} → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
  unitez⋆  : { b : B } → TIMES (ztf b) b ⟷ b
  unitiz⋆  : { b : B } → b ⟷ TIMES (ztf b) b
-- subsumed by above
--  unite⋆  : { b : B } → TIMES ONE b ⟷ b
--  uniti⋆  : { b : B } → b ⟷ TIMES ONE b
--  distZ    : { b : B } → TIMES ZERO b ⟷ ZERO
--  factorZ  : { b : B } → ZERO ⟷ TIMES ZERO b
  swap⋆ : {b₁ b₂ : B} → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
  dist    : { b₁ b₂ b₃ : B } → 
            TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor  : { b₁ b₂ b₃ : B } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
  id⟷ : {b : B } → b ⟷ b
  op    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)
  η⋆ : {b : B} → ztf b ⟷ TIMES (RECIP b) b 
  ε⋆ : {b : B} → TIMES (RECIP b) b ⟷ ztf b
  η₊ : {b : B} → ZERO ⟷ PLUS (NEG b) b 
  ε₊ : {b : B} → PLUS (NEG b) b ⟷ ZERO

------------------------------------------------------------------------------
-- Examples

_⇒⋆_ : B → B → B
b₁ ⇒⋆ b₂ = TIMES (RECIP b₁) b₂

_⇒₊_ : B → B → B
b₁ ⇒₊ b₂ = PLUS (NEG b₁) b₂

name : {b₁ b₂ : B} → (b₁ ⟷ b₂) → (ztf b₁ ⟷ (b₁ ⇒⋆ b₂))
name c = η⋆ ◎ (id⟷ ⊗ c)

{--

doubleDiv : { b : B } → b ⟷ RECIP (RECIP b)
doubleDiv = unitiz⋆ ◎
            (η⋆ ⊗ id⟷) ◎
            assocr⋆ ◎
            (id⟷ ⊗ ε⋆) ◎
            swap⋆ ◎
            unitez⋆

--}

------------------------------------------------------------------------------
