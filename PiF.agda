{-# OPTIONS --no-termination-check #-}

module PiF where

open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

infixr 30 _⟷_
infixr 30 _⟺_
infixr 20 _◎_

------------------------------------------------------------------------------
-- A universe of our value types

data BF : Set where
  ZEROF  : BF
  ONEF   : BF
  PLUSF  : BF → BF → BF
  TIMESF : BF → BF → BF
  RECIP  : BF → BF

-- fractional types are un-interpreted

data Recip (A : Set) : Set where
  recip : (a : A) → Recip A

⟦_⟧F : BF → Set
⟦ ZEROF ⟧F         = ⊥
⟦ ONEF ⟧F          = ⊤
⟦ PLUSF b1 b2 ⟧F   = ⟦ b1 ⟧F ⊎ ⟦ b2 ⟧F
⟦ TIMESF b1 b2 ⟧F  = ⟦ b1 ⟧F × ⟦ b2 ⟧F
⟦ RECIP b ⟧F  = Recip ⟦ b ⟧F

------------------------------------------------------------------------------
-- Primitive isomorphisms

data _⟷_ : BF → BF → Set where
  -- (+,0) commutative monoid
  unite₊  : { b : BF } → PLUSF ZEROF b ⟷ b
  uniti₊  : { b : BF } → b ⟷ PLUSF ZEROF b
  swap₊   : { b₁ b₂ : BF } → PLUSF b₁ b₂ ⟷ PLUSF b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : BF } → PLUSF b₁ (PLUSF b₂ b₃) ⟷ PLUSF (PLUSF b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : BF } → PLUSF (PLUSF b₁ b₂) b₃ ⟷ PLUSF b₁ (PLUSF b₂ b₃)
  -- (*,1) commutative monoid
  unite⋆  : { b : BF } → TIMESF ONEF b ⟷ b
  uniti⋆  : { b : BF } → b ⟷ TIMESF ONEF b
  swap⋆   : { b₁ b₂ : BF } → TIMESF b₁ b₂ ⟷ TIMESF b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : BF } → TIMESF b₁ (TIMESF b₂ b₃) ⟷ TIMESF (TIMESF b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : BF } → TIMESF (TIMESF b₁ b₂) b₃ ⟷ TIMESF b₁ (TIMESF b₂ b₃)
  -- * distributes over + 
  dist    : { b₁ b₂ b₃ : BF } → 
            TIMESF (PLUSF b₁ b₂) b₃ ⟷ PLUSF (TIMESF b₁ b₃) (TIMESF b₂ b₃) 
  factor  : { b₁ b₂ b₃ : BF } → 
            PLUSF (TIMESF b₁ b₃) (TIMESF b₂ b₃) ⟷ TIMESF (PLUSF b₁ b₂) b₃
  -- id
  id⟷    : { b : BF } → b ⟷ b

adjointP : { b₁ b₂ : BF } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
adjointP unite₊    = uniti₊
adjointP uniti₊    = unite₊
adjointP swap₊     = swap₊
adjointP assocl₊   = assocr₊
adjointP assocr₊   = assocl₊
adjointP unite⋆    = uniti⋆
adjointP uniti⋆    = unite⋆
adjointP swap⋆     = swap⋆
adjointP assocl⋆   = assocr⋆
adjointP assocr⋆   = assocl⋆
adjointP dist      = factor
adjointP factor    = dist
adjointP id⟷      = id⟷

evalP : { b₁ b₂ : BF } → (b₁ ⟷ b₂) → ⟦ b₁ ⟧F → ⟦ b₂ ⟧F
evalP unite₊ (inj₁ ())
evalP unite₊ (inj₂ v) = v
evalP uniti₊ v = inj₂ v
evalP swap₊ (inj₁ v) = inj₂ v
evalP swap₊ (inj₂ v) = inj₁ v
evalP assocl₊ (inj₁ v) = inj₁ (inj₁ v)
evalP assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
evalP assocl₊ (inj₂ (inj₂ v)) = inj₂ v
evalP assocr₊ (inj₁ (inj₁ v)) = inj₁ v
evalP assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
evalP assocr₊ (inj₂ v) = inj₂ (inj₂ v)
evalP unite⋆ (tt , v) = v
evalP uniti⋆ v = (tt , v)
evalP swap⋆ (v₁ , v₂) = (v₂ , v₁)
evalP assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
evalP assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
evalP dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
evalP dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
evalP factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
evalP factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
evalP id⟷ v = v

-- Backwards evaluator

bevalP : { b₁ b₂ : BF } → (b₁ ⟷ b₂) → ⟦ b₂ ⟧F → ⟦ b₁ ⟧F
bevalP c v = evalP (adjointP c) v

------------------------------------------------------------------------------
-- Closure combinators

data _⟺_ : BF → BF → Set where
  iso    : { b₁ b₂ : BF } → (b₁ ⟷ b₂) → (b₁ ⟺ b₂) 
  sym    : { b₁ b₂ : BF } → (b₁ ⟺ b₂) → (b₂ ⟺ b₁)
  _◎_    : { b₁ b₂ b₃ : BF } → (b₁ ⟺ b₂) → (b₂ ⟺ b₃) → (b₁ ⟺ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : BF } → 
           (b₁ ⟺ b₃) → (b₂ ⟺ b₄) → (PLUSF b₁ b₂ ⟺ PLUSF b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : BF } → 
           (b₁ ⟺ b₃) → (b₂ ⟺ b₄) → (TIMESF b₁ b₂ ⟺ TIMESF b₃ b₄)
  refe⋆  : { b : BF } → RECIP (RECIP b) ⟺ b
  refi⋆  : { b : BF } → b ⟺ RECIP (RECIP b) 
  rile⋆  : { b : BF } → TIMESF b (TIMESF b (RECIP b)) ⟺ b
  rili⋆  : { b : BF } → b ⟺ TIMESF b (TIMESF b (RECIP b)) 

-- 

adjoint : { b₁ b₂ : BF } → (b₁ ⟺ b₂) → (b₂ ⟺ b₁)
adjoint (iso c) = iso (adjointP c)
adjoint (sym c)   = c
adjoint (c₁ ◎ c₂) = adjoint c₂ ◎ adjoint c₁
adjoint (c₁ ⊕ c₂) = adjoint c₁ ⊕ adjoint c₂
adjoint (c₁ ⊗ c₂) = adjoint c₁ ⊗ adjoint c₂
adjoint refe⋆ = refi⋆
adjoint refi⋆ = refe⋆
adjoint rile⋆ = rili⋆
adjoint rili⋆ = rile⋆

--

-- (Context a b c d) represents a combinator (c <-> d) with a hole
-- requiring something of type (a <-> b). When we use these contexts,
-- it is always the case that the (c <-> a) part of the computation
-- has ALREADY been done and that we are about to evaluate (a <-> b)
-- using a given 'a'. The continuation takes the output 'b' and
-- produces a 'd'.

data Context : BF → BF → BF → BF → Set where
  emptyC : {a b : BF} → Context a b a b
  seqC₁ : {a b c i o : BF} → (b ⟺ c) → Context a c i o → Context a b i o
  seqC₂ : {a b c i o : BF} → (a ⟺ b) → Context a c i o → Context b c i o
  leftC : {a b c d i o : BF} → 
          (c ⟺ d) → Context (PLUSF a c) (PLUSF b d) i o → Context a b i o
  rightC : {a b c d i o : BF} → 
           (a ⟺ b) → Context (PLUSF a c) (PLUSF b d) i o → Context c d i o
  -- the (i <-> a) part of the computation is completely done; so we must store
  -- the value of type [[ c ]] as part of the context
  fstC : {a b c d i o : BF} → 
         ⟦ c ⟧F → (c ⟺ d) → Context (TIMESF a c) (TIMESF b d) i o → Context a b i o
  -- the (i <-> c) part of the computation and the (a <-> b) part of
  -- the computation are completely done; so we must store the value
  -- of type [[ b ]] as part of the context
  sndC : {a b c d i o : BF} → 
         (a ⟺ b) → ⟦ b ⟧F → Context (TIMESF a c) (TIMESF b d) i o → Context c d i o

-- Evaluation

mutual 

  -- The (c <-> a) part of the computation has been done. 
  -- We have an 'a' and we are about to do the (a <-> b) computation.
  -- We get a 'b' and examine the context to get the 'd'
  eval_c : { a b c : BF } → (a ⟺ b) → ⟦ a ⟧F → Context a b c c → ⟦ c ⟧F
  eval_c (iso f) v C = eval_k (iso f) (evalP f v) C
  eval_c (sym c) v C = eval_c (adjoint c) v C
  eval_c (f ◎ g) v C = eval_c f v (seqC₁ g C) 
  eval_c (f ⊕ g) (inj₁ v) C = eval_c f v (leftC g C)
  eval_c (f ⊕ g) (inj₂ v) C = eval_c g v (rightC f C)
  eval_c (f ⊗ g) (v₁ , v₂) C = eval_c f v₁ (fstC v₂ g C)
  eval_c refe⋆ (recip (recip v)) C = eval_k refe⋆ v C
  eval_c refi⋆ v C = eval_k refi⋆ (recip (recip v)) C
  eval_c rile⋆ (v₁ , (v₂ , recip v₃)) C = {!!} 
  eval_c rili⋆ v C = eval_k rili⋆ (v , (v , recip v)) C 

  -- The (c <-> a) part of the computation has been done.
  -- The (a <-> b) part of the computation has been done.
  -- We need to examine the context to get the 'd'.
  -- We rebuild the combinator on the way out.
  eval_k : { a b c : BF } → (a ⟺ b) → ⟦ b ⟧F → Context a b c c → ⟦ c ⟧F
  eval_k f v emptyC = v 
  eval_k f v (seqC₁ g C) = eval_c g v (seqC₂ f C) 
  eval_k g v (seqC₂ f C) = eval_k (f ◎ g) v C
  eval_k f v (leftC g C) = eval_k (f ⊕ g) (inj₁ v) C
  eval_k g v (rightC f C) = eval_k (f ⊕ g) (inj₂ v) C
  eval_k f v₁ (fstC v₂ g C) = eval_c g v₂ (sndC f v₁ C)
  eval_k g v₂ (sndC f v₁ C) = eval_k (f ⊗ g) (v₁ , v₂) C

  -- Backwards evaluator

  -- The (d <-> b) part of the computation has been done. 
  -- We have a 'b' and we are about to do the (a <-> b) computation backwards.
  -- We get an 'a' and examine the context to get the 'c'
  beval_c : { a b c : BF } → (a ⟺ b) → ⟦ b ⟧F → Context a b c c → ⟦ c ⟧F
  beval_c (iso f) v C = beval_k (iso f) (bevalP f v) C
  beval_c (sym c) v C = beval_c (adjoint c) v C
  beval_c (f ◎ g) v C = beval_c g v (seqC₂ f C) 
  beval_c (f ⊕ g) (inj₁ v) C = beval_c f v (leftC g C)
  beval_c (f ⊕ g) (inj₂ v) C = beval_c g v (rightC f C)
  beval_c (f ⊗ g) (v₁ , v₂) C = beval_c g v₂ (sndC f v₁ C)
  beval_c refe⋆ v C = beval_k refe⋆ (recip (recip v)) C
  beval_c refi⋆ (recip (recip v)) C = beval_k refi⋆ v C
  beval_c rile⋆ v C = beval_k rile⋆ (v , (v , (recip v))) C
  beval_c rili⋆ (v₁ , (v₂ , recip v₃)) C = {!!}

  -- The (d <-> b) part of the computation has been done. 
  -- The (a <-> b) backwards computation has been done. 
  -- We have an 'a' and examine the context to get the 'c'
  beval_k : { a b c : BF } → (a ⟺ b) → ⟦ a ⟧F → Context a b c c → ⟦ c ⟧F
  beval_k f v emptyC = v
  beval_k g v (seqC₂ f C) = beval_c f v (seqC₁ g C) 
  beval_k f v (seqC₁ g C) = beval_k (f ◎ g) v C
  beval_k f v (leftC g C) = beval_k (f ⊕ g) (inj₁ v) C
  beval_k g v (rightC f C) = beval_k (f ⊕ g) (inj₂ v) C
  beval_k g v₂ (sndC f v₁ C) = beval_c f v₁ (fstC v₂ g C)
  beval_k f v₁ (fstC v₂ g C) = beval_k (f ⊗ g) (v₁ , v₂) C

------------------------------------------------------------------------------
-- Top level eval

eval : { a : BF } → (a ⟺ a) → ⟦ a ⟧F → ⟦ a ⟧F
eval f v = eval_c f v emptyC

--

BOOL : BF
BOOL = PLUSF ONEF ONEF

test1 : ⟦ BOOL ⟧F
test1 = eval {BOOL} (iso swap₊) (inj₁ tt)
