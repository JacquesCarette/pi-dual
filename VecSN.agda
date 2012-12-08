module VecSN where

open import Data.Bool

------------------------------------------------------------------------------
-- types (dimension of a vector space)
-- values (indices for vectors which match the dimension)
--
-- next layer of types (vectors and duals assuming underlying field is F_3
-- and that we do not allow superpositions)

data BV : Set where
  ZEROV   : BV
  ONEV    : BV
  PLUSV   : BV → BV → BV
  TIMESV  : BV → BV → BV
--
  DUALV   : BV → BV
  IPV     : BV → BV → BV
--
  NEGV    : BV → BV
  CHOOSEV : BV → BV → BV

data BVEC : BV → Set where
  zero : {b : BV} → BVEC b
  unit : BVEC ONEV
  left : {b₁ b₂ : BV} → BVEC b₁ → BVEC (PLUSV b₁ b₂)
  right : {b₁ b₂ : BV} → BVEC b₂ → BVEC (PLUSV b₁ b₂)
  pair : {b₁ b₂ : BV} → BVEC b₁ → BVEC b₂ → BVEC (TIMESV b₁ b₂)
  dual : {b : BV} → BVEC b → BVEC (DUALV b)
  ip : {b₁ b₂ : BV} → BVEC b₁ → BVEC b₂ → BVEC (IPV b₁ b₂)
  neg : {b : BV} → BVEC b → BVEC (NEGV b)
  choose : {b₁ b₂ : BV} → BVEC b₁ → BVEC b₂ → BVEC (CHOOSEV b₁ b₂)

b= : { b : BV } → BVEC b → BVEC b → Bool
b= zero zero = true
b= unit unit = true
b= (left v₁) (left v₂) = b= v₁ v₂
b= (right v₁) (right v₂) = b= v₁ v₂
b= (pair v₁ v₂) (pair v₁' v₂') = b= v₁ v₁' ∧ b= v₂ v₂'
b= (dual v₁) (dual v₂) = b= v₁ v₂
b= (ip v₁ v₂) (ip v₁' v₂') = b= v₁ v₁' ∧ b= v₂ v₂'
b= (neg v₁) (neg v₂) = b= v₁ v₂
b= (choose v₁ v₂) (choose v₁' v₂') = b= v₁ v₁' ∧ b= v₂ v₂'
b= _ _ = false

data Iso : BV → BV → Set where
  -- (+,0) commutative monoid
  unite₊  : { b : BV } → Iso (PLUSV ZEROV b) b
  uniti₊  : { b : BV } → Iso b (PLUSV ZEROV b)
  swap₊   : { b₁ b₂ : BV } → Iso (PLUSV b₁ b₂) (PLUSV b₂ b₁)
  assocl₊ : { b₁ b₂ b₃ : BV } → Iso (PLUSV b₁ (PLUSV b₂ b₃)) (PLUSV (PLUSV b₁ b₂) b₃)
  assocr₊ : { b₁ b₂ b₃ : BV } → Iso (PLUSV (PLUSV b₁ b₂) b₃) (PLUSV b₁ (PLUSV b₂ b₃))
  -- (*,1) commutative monoid
  unite⋆  : { b : BV } → Iso (TIMESV ONEV b) b
  uniti⋆  : { b : BV } → Iso b (TIMESV ONEV b)
  swap⋆   : { b₁ b₂ : BV } → Iso (TIMESV b₁ b₂) (TIMESV b₂ b₁)
  assocl⋆ : { b₁ b₂ b₃ : BV } → Iso (TIMESV b₁ (TIMESV b₂ b₃)) (TIMESV (TIMESV b₁ b₂) b₃)
  assocr⋆ : { b₁ b₂ b₃ : BV } → Iso (TIMESV (TIMESV b₁ b₂) b₃) (TIMESV b₁ (TIMESV b₂ b₃))
  -- * distributes over + 
  dist    : { b₁ b₂ b₃ : BV } → 
            Iso (TIMESV (PLUSV b₁ b₂) b₃) (PLUSV (TIMESV b₁ b₃) (TIMESV b₂ b₃))
  factor  : { b₁ b₂ b₃ : BV } → 
            Iso (PLUSV (TIMESV b₁ b₃) (TIMESV b₂ b₃)) (TIMESV (PLUSV b₁ b₂) b₃)
  -- closure
  id⟷   : { b : BV } → Iso b b
  sym    : { b₁ b₂ : BV } → Iso b₁ b₂ → Iso b₂ b₁
  _◎_    : { b₁ b₂ b₃ : BV } → Iso b₁ b₂ → Iso b₂ b₃ → Iso b₁ b₃
  _⊕_    : { b₁ b₂ b₃ b₄ : BV } → 
           Iso b₁ b₃ → Iso b₂ b₄ → Iso (PLUSV b₁ b₂) (PLUSV b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : BV } → 
           Iso b₁ b₃ → Iso b₂ b₄ → Iso (TIMESV b₁ b₂) (TIMESV b₃ b₄)
  -- additive duality
  refe₊   : { b : BV } → Iso (NEGV (NEGV b)) b
  refi₊   : { b : BV } → Iso b (NEGV (NEGV b))
  rile₊   : { b : BV } → Iso (PLUSV b (CHOOSEV b (NEGV b))) b
  rili₊   : { b : BV } → Iso b (PLUSV b (CHOOSEV b (NEGV b)))
  -- multiplicative duality
  refe⋆   : { b : BV } → Iso (DUALV (DUALV b)) b
  refi⋆   : { b : BV } → Iso b (DUALV (DUALV b))
  rile⋆   : { b : BV } → Iso (TIMESV b (IPV b (DUALV b))) b
  rili⋆   : { b : BV } → Iso b (TIMESV b (IPV b (DUALV b)))

mutual 

  evalV : {b₁ b₂ : BV} → Iso b₁ b₂ → BVEC b₁ → BVEC b₂
  evalV unite₊ (left _) = zero
  evalV unite₊ (right v) = v
  evalV uniti₊ v = right v
  evalV swap₊ (left v) = right v
  evalV swap₊ (right v) = left v
  evalV assocl₊ (left v) = left (left v)
  evalV assocl₊ (right (left v)) = left (right v)
  evalV assocl₊ (right (right v)) = right v
  evalV assocr₊ (left (left v)) = left v
  evalV assocr₊ (left (right v)) = right (left v)
  evalV assocr₊ (right v) = right (right v)
  evalV unite⋆ (pair unit v) = v
  evalV uniti⋆ v = pair unit v
  evalV swap⋆ (pair v1 v2) = pair v2 v1
  evalV assocl⋆ (pair v1 (pair v2 v3)) = pair (pair v1 v2) v3
  evalV assocr⋆ (pair (pair v1 v2) v3) = pair v1 (pair v2 v3)
  evalV dist (pair (left v1) v3) = left (pair v1 v3)
  evalV dist (pair (right v2) v3) = right (pair v2 v3)
  evalV factor (left (pair v1 v3)) = pair (left v1) v3
  evalV factor (right (pair v2 v3)) = pair (right v2) v3
  evalV id⟷ v = v
  evalV (sym c) v = evalB c v
  evalV (c₁ ◎ c₂) v = evalV c₂ (evalV c₁ v)
  evalV (c₁ ⊕ c₂) (left v) = left (evalV c₁ v)
  evalV (c₁ ⊕ c₂) (right v) = right (evalV c₂ v)
  evalV (c₁ ⊗ c₂) (pair v₁ v₂) = pair (evalV c₁ v₁) (evalV c₂ v₂)
  evalV refe₊ (neg (neg v)) = v
  evalV refi₊ v = neg (neg v)
  evalV rile₊ (left v) = v
  evalV rile₊ (right (choose v₁ (neg v₂))) with b= v₁ v₂
  evalV rile₊ (right (choose v₁ (neg v₂))) | true = v₁
  evalV rile₊ (right (choose v₁ (neg v₂))) | false = zero
  evalV rili₊ v = left v
  evalV refe⋆ (dual (dual v)) = v
  evalV refi⋆ v = dual (dual v)
  evalV rile⋆ (pair v (ip v₁ (dual v₂))) with b= v₁ v₂
  evalV rile⋆ (pair v (ip v₁ (dual v₂))) | true = v₁
  evalV rile⋆ (pair v (ip v₁ (dual v₂))) | false = zero
  evalV rili⋆ v = pair v (ip v (dual v))
  evalV _ _ = zero

  evalB : {b₁ b₂ : BV} → Iso b₁ b₂ → BVEC b₂ → BVEC b₁
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
  evalB (sym c) v = evalV c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (left v) = left (evalB c₁ v)
  evalB (c₁ ⊕ c₂) (right v) = right (evalB c₂ v)
  evalB (c₁ ⊗ c₂) (pair v₁ v₂) = pair (evalB c₁ v₁) (evalB c₂ v₂)
  evalB refe₊ v = neg (neg v)
  evalB refi₊ (neg (neg v)) = v
  evalB rile₊ v = left v
  evalB rili₊ (left v) = v
  evalB rili₊ (right (choose v₁ (neg v₂))) with b= v₁ v₂
  evalB rili₊ (right (choose v₁ (neg v₂))) | true = v₁
  evalB rili₊ (right (choose v₁ (neg v₂))) | false = zero
  evalB refe⋆ v = dual (dual v)
  evalB refi⋆ (dual (dual v)) = v
  evalB rile⋆ v = pair v (ip v (dual v))
  evalB rili⋆ (pair v (ip v₁ (dual v₂))) with b= v₁ v₂
  evalB rili⋆ (pair v (ip v₁ (dual v₂))) | true = v₁
  evalB rili⋆ (pair v (ip v₁ (dual v₂))) | false = zero
  evalB _ _ = zero

------------------------------------------------------------------------------



