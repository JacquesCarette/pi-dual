module PiNF-syntax where

open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

infixr 30 _⟷_
infixr 20 _◎_

------------------------------------------------------------------------------
-- First we define a universe of our value types

data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  NEG   : B → B
  TIMES : B → B → B
  RECIP : B → B

------------------------------------------------------------------------------
-- Now we define another universe for our equivalences. First the codes for
-- equivalences.

data _⟷_ : B → B → Set where
  unite₊  : { b : B } → PLUS ZERO b ⟷ b
  uniti₊  : { b : B } → b ⟷ PLUS ZERO b
  swap₊   : { b₁ b₂ : B } → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
  unite⋆  : { b : B } → TIMES ONE b ⟷ b
  uniti⋆  : { b : B } → b ⟷ TIMES ONE b
  swap⋆   : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
  dist    : { b₁ b₂ b₃ : B } → 
            TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor  : { b₁ b₂ b₃ : B } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
  η₊      : { b : B } → ZERO ⟷ PLUS (NEG b) b
  ε₊      : { b : B } → PLUS b (NEG b) ⟷ ZERO
  refe⋆   : { b : B } → RECIP (RECIP b) ⟷ b
  refi⋆   : { b : B } → b ⟷ RECIP (RECIP b) 
  rile⋆   : { b : B } → TIMES b (TIMES b (RECIP b)) ⟷ b
  rili⋆   : { b : B } → b ⟷ TIMES b (TIMES b (RECIP b)) 
  id⟷   : { b : B } → b ⟷ b
  sym    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)

--

adjoint : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
adjoint unite₊    = uniti₊
adjoint uniti₊    = unite₊
adjoint swap₊     = swap₊
adjoint assocl₊   = assocr₊
adjoint assocr₊   = assocl₊
adjoint unite⋆    = uniti⋆
adjoint uniti⋆    = unite⋆
adjoint swap⋆     = swap⋆
adjoint assocl⋆   = assocr⋆
adjoint assocr⋆   = assocl⋆
adjoint dist      = factor
adjoint factor    = dist
adjoint η₊        = swap₊ ◎ ε₊
adjoint ε₊        = η₊ ◎ swap₊
adjoint refe⋆     = refi⋆
adjoint refi⋆     = refe⋆
adjoint rile⋆     = rili⋆
adjoint rili⋆     = rile⋆
adjoint id⟷      = id⟷
adjoint (sym c)   = c
adjoint (c₁ ◎ c₂) = adjoint c₂ ◎ adjoint c₁
adjoint (c₁ ⊕ c₂) = adjoint c₁ ⊕ adjoint c₂
adjoint (c₁ ⊗ c₂) = adjoint c₁ ⊗ adjoint c₂

--

dist' : {b₁ b₂ b₃ : B} → TIMES b₁ (PLUS b₂ b₃) ⟷ PLUS (TIMES b₁ b₂) (TIMES b₁ b₃)
dist' = swap⋆ ◎ dist ◎ (swap⋆ ⊕ swap⋆) 

midtofront : {a b c : B} → TIMES a (TIMES b c) ⟷ TIMES b (TIMES a c)
midtofront = assocl⋆ ◎ (swap⋆ ⊗ id⟷) ◎ assocr⋆

neg : {b₁ b₂ : B} → (b₁ ⟷ b₂) → (NEG b₁ ⟷ NEG b₂) 
neg {b₁} {b₂} c =              -- -b1
  uniti₊ ◎                     -- 0 + (-b1)
  (η₊ {b₂} ⊕ id⟷) ◎           -- (-b2 + b2) + (-b1)
  ((id⟷ ⊕ sym c) ⊕ id⟷) ◎    -- (-b2 + b1) + (-b1)
  assocr₊ ◎                    -- (-b2) + (b1 + (-b1))
  (id⟷ ⊕ ε₊) ◎                -- (-b2) + 0
  swap₊ ◎                      -- 0 + (-b2)
  unite₊                       -- -b2

--

mul0 : {b : B} → TIMES ZERO b ⟷ ZERO
mul0 =                    -- 0*b
  uniti₊ ◎                  --  0 + 0*b
  (η₊ ⊕ id⟷) ◎        -- (-(0*b) + 0*b) + 0*b
  assocr₊ ◎              -- -(0*b) + (0*b + 0*b)
  (id⟷ ⊕ factor) ◎  -- -(0*b) + (0+0)*b
  (id⟷ ⊕ (unite₊ ⊗ id⟷)) ◎  -- -(0*b) + 0*b
  swap₊ ◎  ε₊ -- 0

inv0 : TIMES ZERO (RECIP ZERO) ⟷ ZERO
inv0 = mul0 

--

recip : {b₁ b₂ : B} → (b₁ ⟷ b₂) → (RECIP b₁ ⟷ RECIP b₂) 
recip {b₁} {b₂} c =          -- 1/a
  rili⋆ {RECIP b₁} ◎         -- 1/a * (1/a * 1/1/a)
  (id⟷ ⊗ (id⟷ ⊗ refe⋆)) ◎   -- 1/a * (1/a * a)
  assocl⋆ ◎                  -- (1/a * 1/a) * a
  (id⟷ ⊗ reciplem c) ◎     -- (1/a * 1/a) * (a * ((a * 1/b) * (b * 1/b)))
  assocl⋆ ◎                  -- (((1/a * 1/a) * a) * ((a * 1/b) * (b * 1/b)))
  ((id⟷ ⊗ refi⋆ ) ⊗ id⟷) ◎   -- (((1/a *1/a) * 1/(1/a)) * ((a * 1/b) * (b * 1/b))
  ((assocr⋆ ◎ rile⋆ ) ⊗ (id⟷ ⊗ ((sym c) ⊗ id⟷))) ◎ -- 1/a * ((a * 1/b) * (a * 1/b))
  (id⟷ ⊗ (assocr⋆ ◎ (id⟷ ⊗ midtofront))) ◎ -- 1/a * (a * (a * (1/b * 1/b)))
  (assocl⋆ ◎ assocl⋆) ◎                      -- ((1/a * a) * a) * (1/b * 1/b)
  (((swap⋆ ⊗ id⟷) ◎ swap⋆) ⊗ id⟷) ◎         -- ((a * (a * 1/a)) * (1/b * 1/b))
  (rile⋆ ⊗ id⟷ ) ◎                           -- a * (1/b * 1/b)
  ((c ◎ refi⋆ ) ⊗ id⟷) ◎ swap⋆ ◎             -- (1/b * 1/b) * 1/(1/b)
  assocr⋆ ◎ rile⋆                             -- 1/b
  where 
    reciplem : {b₁ b₂ : B} → (b₁ ⟷ b₂) → (b₁ ⟷ (TIMES b₁ (TIMES (TIMES b₁ (RECIP b₂)) (TIMES b₂ (RECIP b₂)))))
    reciplem {b₁} {b₂} c =  c ◎                       -- b
      rili⋆ ◎                                -- b * (b * 1/b)
      (rili⋆ ⊗ id⟷) ◎                        -- (b * (b * 1/b)) * (b * 1/b)
      (((sym c) ⊗ ((sym c) ⊗ id⟷)) ⊗ id⟷) ◎ -- ((a * (a * 1/b)) * (b * 1/b))  
      assocr⋆                                -- a * ((a * 1/b) * (b * 1/b))

------------------------------------------------------------------------------
-- Examples

BOOL : B
BOOL = PLUS ONE ONE

notπ : BOOL ⟷ BOOL
notπ = swap₊

BOOL² : B
BOOL² = TIMES BOOL BOOL

BOOL³ : B
BOOL³ = TIMES BOOL BOOL² 

ifc : { b : B } → (b ⟷ b) → (TIMES BOOL b ⟷ TIMES BOOL b)
ifc c = dist ◎ ((id⟷ ⊗ c) ⊕ id⟷) ◎ factor

cnot : BOOL² ⟷ BOOL²
cnot = ifc notπ

toffoli : BOOL³ ⟷ BOOL³
toffoli = ifc cnot

------------------------------------------------------------------------------

