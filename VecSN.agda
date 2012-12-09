module VecSN where

open import Data.Bool

infixr 20 _◎_

------------------------------------------------------------------------------
-- fix a field F_3 = {0, 1, -1} 
-- types B (ZERO,ONE,PLUS,TIMES) determine the DIMENSION of a vector space over F_3
-- values of type B are INDICES for B-dimensional vectors
-- we do not allow superpositions (we have AT MOST one entry in the
-- vector that is non-zero), so we can identify the INDICES with the vectors
--
-- in particular: 
--   - ZERO is not the empty type! it is like the 0-dimensional vector space
--     (i.e, the type containing one "annihilating value")
--   - ONE is like a 1-dimensional vector space; it is isomorphic to 
--     the scalars (0,+1,-1)
--   - PLUS gives the direct sum of vector spaces (dimension is the sum)
--   - TIMES gives the tensor product of vector spaces (dimension is the product)
--   - DUAL gives the dual space (functionals that map vectors to scalars; i.e.
--     that maps values to scalars)

data B : Set where
  ZERO   : B
  ONE    : B
  PLUS   : B → B → B  
  TIMES  : B → B → B  
  DUAL   : B → B

-- now we describe the vectors for each B-dimensional vector space
-- the zero vector is everywhere

data BVAL : B → Set where
  zero : {b : B} → BVAL b
  unit : BVAL ONE
  left : {b₁ b₂ : B} → BVAL b₁ → BVAL (PLUS b₁ b₂)
  right : {b₁ b₂ : B} → BVAL b₂ → BVAL (PLUS b₁ b₂)
  pair : {b₁ b₂ : B} → BVAL b₁ → BVAL b₂ → BVAL (TIMES b₁ b₂)
  dual : {b : B} → BVAL b → BVAL (DUAL b)

-- syntactic equality on vectors

b= : { b : B } → BVAL b → BVAL b → Bool
b= zero zero = true
b= unit unit = true
b= (left v₁) (left v₂) = b= v₁ v₂
b= (right v₁) (right v₂) = b= v₁ v₂
b= (pair v₁ v₂) (pair v₁' v₂') = b= v₁ v₁' ∧ b= v₂ v₂'
b= (dual v₁) (dual v₂) = b= v₁ v₂
b= _ _ = false

--HERE

data Iso : B → B → Set where
  -- (+,0) commutative monoid
  unite₊  : { b : B } → Iso (PLUS ZERO b) b
  uniti₊  : { b : B } → Iso b (PLUS ZERO b)
  swap₊   : { b₁ b₂ : B } → Iso (PLUS b₁ b₂) (PLUS b₂ b₁)
  assocl₊ : { b₁ b₂ b₃ : B } → Iso (PLUS b₁ (PLUS b₂ b₃)) (PLUS (PLUS b₁ b₂) b₃)
  assocr₊ : { b₁ b₂ b₃ : B } → Iso (PLUS (PLUS b₁ b₂) b₃) (PLUS b₁ (PLUS b₂ b₃))
  -- (*,1) commutative monoid
  unite⋆  : { b : B } → Iso (TIMES ONE b) b
  uniti⋆  : { b : B } → Iso b (TIMES ONE b)
  swap⋆   : { b₁ b₂ : B } → Iso (TIMES b₁ b₂) (TIMES b₂ b₁)
  assocl⋆ : { b₁ b₂ b₃ : B } → Iso (TIMES b₁ (TIMES b₂ b₃)) (TIMES (TIMES b₁ b₂) b₃)
  assocr⋆ : { b₁ b₂ b₃ : B } → Iso (TIMES (TIMES b₁ b₂) b₃) (TIMES b₁ (TIMES b₂ b₃))
  -- * distributes over + 
  dist    : { b₁ b₂ b₃ : B } → 
            Iso (TIMES (PLUS b₁ b₂) b₃) (PLUS (TIMES b₁ b₃) (TIMES b₂ b₃))
  factor  : { b₁ b₂ b₃ : B } → 
            Iso (PLUS (TIMES b₁ b₃) (TIMES b₂ b₃)) (TIMES (PLUS b₁ b₂) b₃)
  -- closure
  id⟷   : { b : B } → Iso b b
  sym    : { b₁ b₂ : B } → Iso b₁ b₂ → Iso b₂ b₁
  _◎_    : { b₁ b₂ b₃ : B } → Iso b₁ b₂ → Iso b₂ b₃ → Iso b₁ b₃
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           Iso b₁ b₃ → Iso b₂ b₄ → Iso (PLUS b₁ b₂) (PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           Iso b₁ b₃ → Iso b₂ b₄ → Iso (TIMES b₁ b₂) (TIMES b₃ b₄)
  -- multiplicative duality
  refe⋆   : { b : B } → Iso (DUAL (DUAL b)) b
  refi⋆   : { b : B } → Iso b (DUAL (DUAL b))
  rile⋆   : { b : B } → Iso (TIMES b (TIMES b (DUAL b))) b
  rili⋆   : { b : B } → Iso b (TIMES b (TIMES b (DUAL b)))

mutual 

  eval : {b₁ b₂ : B} → Iso b₁ b₂ → BVAL b₁ → BVAL b₂
  eval unite₊ (left _) = zero
  eval unite₊ (right v) = v
  eval uniti₊ v = right v
  eval swap₊ (left v) = right v
  eval swap₊ (right v) = left v
  eval assocl₊ (left v) = left (left v)
  eval assocl₊ (right (left v)) = left (right v)
  eval assocl₊ (right (right v)) = right v
  eval assocr₊ (left (left v)) = left v
  eval assocr₊ (left (right v)) = right (left v)
  eval assocr₊ (right v) = right (right v)
  eval unite⋆ (pair unit v) = v
  eval uniti⋆ v = pair unit v
  eval swap⋆ (pair v1 v2) = pair v2 v1
  eval assocl⋆ (pair v1 (pair v2 v3)) = pair (pair v1 v2) v3
  eval assocr⋆ (pair (pair v1 v2) v3) = pair v1 (pair v2 v3)
  eval dist (pair (left v1) v3) = left (pair v1 v3)
  eval dist (pair (right v2) v3) = right (pair v2 v3)
  eval factor (left (pair v1 v3)) = pair (left v1) v3
  eval factor (right (pair v2 v3)) = pair (right v2) v3
  eval id⟷ v = v
  eval (sym c) v = evalB c v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (left v) = left (eval c₁ v)
  eval (c₁ ⊕ c₂) (right v) = right (eval c₂ v)
  eval (c₁ ⊗ c₂) (pair v₁ v₂) = pair (eval c₁ v₁) (eval c₂ v₂)
  eval refe⋆ (dual (dual v)) = v
  eval refi⋆ v = dual (dual v)
  eval rile⋆ (pair v (pair v₁ (dual v₂))) with b= v₁ v₂
  eval rile⋆ (pair v (pair v₁ (dual v₂))) | true = v
  eval rile⋆ (pair v (pair v₁ (dual v₂))) | false = zero
  eval rili⋆ v = pair v (pair v (dual v))
  eval _ _ = zero

  evalB : {b₁ b₂ : B} → Iso b₁ b₂ → BVAL b₂ → BVAL b₁
  evalB unite₊ v = right v
  evalB uniti₊ (left _) = zero
  evalB uniti₊ (right v) = v
  evalB swap₊ (left v) = right v
  evalB swap₊ (right v) = left v
  evalB assocl₊ (left (left v)) = left v
  evalB assocl₊ (left (right v)) = right (left v)
  evalB assocl₊ (right v) = right (right v)
  evalB assocr₊ (left v) = left (left v)
  evalB assocr₊ (right (left v)) = left (right v)
  evalB assocr₊ (right (right v)) = right v
  evalB unite⋆ v = pair unit v
  evalB uniti⋆ (pair unit v) = v
  evalB swap⋆ (pair v1 v2) = pair v2 v1
  evalB assocl⋆ (pair (pair v1 v2) v3) = pair v1 (pair v2 v3)
  evalB assocr⋆ (pair v1 (pair v2 v3)) = pair (pair v1 v2) v3
  evalB dist (left (pair v1 v3)) = pair (left v1) v3
  evalB dist (right (pair v2 v3)) = pair (right v2) v3
  evalB factor (pair (left v1) v3) = left (pair v1 v3)
  evalB factor (pair (right v2) v3) = right (pair v2 v3)
  evalB id⟷ v = v
  evalB (sym c) v = eval c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (left v) = left (evalB c₁ v)
  evalB (c₁ ⊕ c₂) (right v) = right (evalB c₂ v)
  evalB (c₁ ⊗ c₂) (pair v₁ v₂) = pair (evalB c₁ v₁) (evalB c₂ v₂)
  evalB refe⋆ v = dual (dual v)
  evalB refi⋆ (dual (dual v)) = v
  evalB rile⋆ v = pair v (pair v (dual v))
  evalB rili⋆ (pair v (pair v₁ (dual v₂))) with b= v₁ v₂
  evalB rili⋆ (pair v (pair v₁ (dual v₂))) | true = v
  evalB rili⋆ (pair v (pair v₁ (dual v₂))) | false = zero
  evalB _ _ = zero

------------------------------------------------------------------------------
-- example with duals

pibool : B
pibool = PLUS ONE ONE

pitrue : BVAL pibool
pitrue = left unit

pifalse : BVAL pibool
pifalse = right unit

-- swap clause 1 = (T => F)
clause1 : BVAL (TIMES (DUAL pibool) pibool)
clause1 = pair (dual pitrue) pifalse

-- swap clause 2 = (F => T)
clause2 : BVAL (TIMES (DUAL pibool) pibool)
clause2 = pair (dual pifalse) pitrue

-- swap clause 1 applied to true
ex1 : BVAL (TIMES pibool (TIMES (DUAL pibool) pibool))
ex1 = pair pitrue clause1

-- swap clause 1 applied to false
ex2 : BVAL (TIMES pibool (TIMES (DUAL pibool) pibool))
ex2 = pair pifalse clause1

-- swap clause 1 applied to true
ex3 : BVAL (TIMES pibool (TIMES (DUAL pibool) pibool))
ex3 = pair pitrue clause2

-- swap clause 1 applied to false
ex4 : BVAL (TIMES pibool (TIMES (DUAL pibool) pibool))
ex4 = pair pifalse clause2

-- applies one of the clauses to a value 
c : Iso (TIMES pibool (TIMES (DUAL pibool) pibool)) pibool
c =         -- (v,(1/t,f))
  assocl⋆ ◎ -- ((v,1/t),f)
  swap⋆ ◎   -- (f,(v,1/t))
  rile⋆     -- f or zero

-- 
v1 = eval c ex1
v2 = eval c ex2
v3 = eval c ex3
v4 = eval c ex4

------------------------------------------------------------------------------
