{-# OPTIONS --no-termination-check #-}

module Pi-abstract-machine where

open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

infixr 30 _⟷_
infixr 30 _⟺_
infixr 20 _◎_

------------------------------------------------------------------------------
-- A universe of our value types

data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

data VB : (b : B) → Set where
  unitB : VB ONE
  inlB  : {b₁ b₂ : B} → VB b₁ → VB (PLUS b₁ b₂)
  inrB  : {b₁ b₂ : B} → VB b₂ → VB (PLUS b₁ b₂)
  pairB : {b₁ b₂ : B} → VB b₁ → VB b₂ → VB (TIMES b₁ b₂)

------------------------------------------------------------------------------
-- Primitive isomorphisms

data _⟷_ : B → B → Set where
  -- (+,0) commutative monoid
  unite₊  : { b : B } → PLUS ZERO b ⟷ b
  uniti₊  : { b : B } → b ⟷ PLUS ZERO b
  swap₊   : { b₁ b₂ : B } → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
  -- (*,1) commutative monoid
  unite⋆  : { b : B } → TIMES ONE b ⟷ b
  uniti⋆  : { b : B } → b ⟷ TIMES ONE b
  swap⋆   : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
  -- * distributes over + 
  dist    : { b₁ b₂ b₃ : B } → 
            TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor  : { b₁ b₂ b₃ : B } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
  -- id
  id⟷   : { b : B } → b ⟷ b

adjointP : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
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

evalP : { b₁ b₂ : B } → (b₁ ⟷ b₂) → VB b₁ → VB b₂
evalP unite₊ (inlB ())
evalP unite₊ (inrB v) = v
evalP uniti₊ v = inrB v
evalP swap₊ (inlB v) = inrB v
evalP swap₊ (inrB v) = inlB v
evalP assocl₊ (inlB v) = inlB (inlB v)
evalP assocl₊ (inrB (inlB v)) = inlB (inrB v)
evalP assocl₊ (inrB (inrB v)) = inrB v
evalP assocr₊ (inlB (inlB v)) = inlB v
evalP assocr₊ (inlB (inrB v)) = inrB (inlB v)
evalP assocr₊ (inrB v) = inrB (inrB v)
evalP unite⋆ (pairB unitB v) = v
evalP uniti⋆ v = (pairB unitB v)
evalP swap⋆ (pairB v₁ v₂) = pairB v₂ v₁
evalP assocl⋆ (pairB v₁ (pairB v₂ v₃)) = pairB (pairB v₁ v₂) v₃
evalP assocr⋆ (pairB (pairB v₁ v₂) v₃) = pairB v₁ (pairB v₂ v₃)
evalP dist (pairB (inlB v₁) v₃) = inlB (pairB v₁ v₃)
evalP dist (pairB (inrB v₂) v₃) = inrB (pairB v₂ v₃)
evalP factor (inlB (pairB v₁ v₃)) = pairB (inlB v₁) v₃
evalP factor (inrB (pairB v₂ v₃)) = pairB (inrB v₂) v₃
evalP id⟷ v = v

-- Backwards evaluator

bevalP : { b₁ b₂ : B } → (b₁ ⟷ b₂) → VB b₂ → VB b₁ 
bevalP c v = evalP (adjointP c) v

------------------------------------------------------------------------------
-- Closure combinators

data _⟺_ : B → B → Set where
  iso : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₁ ⟺ b₂) 
  sym : { b₁ b₂ : B } → (b₁ ⟺ b₂) → (b₂ ⟺ b₁)
  _◎_ : { b₁ b₂ b₃ : B } → (b₁ ⟺ b₂) → (b₂ ⟺ b₃) → (b₁ ⟺ b₃)
  _⊕_ : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟺ b₃) → (b₂ ⟺ b₄) → (PLUS b₁ b₂ ⟺ PLUS b₃ b₄)
  _⊗_ : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟺ b₃) → (b₂ ⟺ b₄) → (TIMES b₁ b₂ ⟺ TIMES b₃ b₄)

-- 

adjoint : { b₁ b₂ : B } → (b₁ ⟺ b₂) → (b₂ ⟺ b₁)
adjoint (iso c) = iso (adjointP c)
adjoint (sym c) = c
adjoint (c₁ ◎ c₂) = adjoint c₂ ◎ adjoint c₁
adjoint (c₁ ⊕ c₂) = adjoint c₁ ⊕ adjoint c₂
adjoint (c₁ ⊗ c₂) = adjoint c₁ ⊗ adjoint c₂

------------------------------------------------------------------------------
-- Operational semantics

-- (Context a b c d) represents a combinator (c <=> d) with a hole
-- requiring something of type (a <=> b). When we use these contexts,
-- it is always the case that the (c <=> a) part of the computation
-- has ALREADY been done and that we are about to evaluate (a <=> b)
-- using a given 'a'. The continuation takes the output 'b' and
-- produces a 'd'.

data Context : B → B → B → B → Set where
  emptyC : {a b : B} → Context a b a b
  seqC₁ : {a b c i o : B} → (b ⟺ c) → Context a c i o → Context a b i o
  seqC₂ : {a b c i o : B} → (a ⟺ b) → Context a c i o → Context b c i o
  leftC : {a b c d i o : B} → 
          (c ⟺ d) → Context (PLUS a c) (PLUS b d) i o → Context a b i o
  rightC : {a b c d i o : B} → 
           (a ⟺ b) → Context (PLUS a c) (PLUS b d) i o → Context c d i o
  -- the (i <-> a) part of the computation is completely done; so we must store
  -- the value of type [[ c ]] as part of the context
  fstC : {a b c d i o : B} → 
         VB c → (c ⟺ d) → Context (TIMES a c) (TIMES b d) i o → Context a b i o
  -- the (i <-> c) part of the computation and the (a <-> b) part of
  -- the computation are completely done; so we must store the value
  -- of type [[ b ]] as part of the context
  sndC : {a b c d i o : B} → 
         (a ⟺ b) → VB b → Context (TIMES a c) (TIMES b d) i o → Context c d i o

-- Small-step evaluation

-- A computation (c <=> d) is split into:
--   - a history (c <==> a)
--   - a current computation in focus (a <==> b)
--   - a future (b <==> d) 

record BState (a b c d : B) : Set where
  constructor <_!_!_>
  field
    comb : a ⟺ b 
    val : VB a 
    context :  Context a b c d 

record AState (a b c d : B) : Set where
  constructor [_!_!_]
  field
    comb : a ⟺ b 
    val : VB b 
    context : Context a b c d 

data State (d : B) : Set where
  before : {a b c : B} → BState a b c d → State d
  after : {a b c : B} → AState a b c d → State d
  final : VB d → State d

-- The (c <=> a) part of the computation has been done.
-- We are about to perform the (a <=> b) part of the computation.
beforeStep : {a b c d : B} → BState a b c d → State d
beforeStep < iso f ! v ! C > = after [ iso f ! (evalP f v) ! C ]
beforeStep < sym c ! v ! C > = before < adjoint c ! v ! C > 
beforeStep < _◎_ {b₂ = _} f g ! v ! C > = before < f ! v ! seqC₁ g C > 
beforeStep < _⊕_ {b₁} {b₂} {b₃} {b₄} f g ! inlB v ! C > = before < f ! v ! leftC g C >  
beforeStep < _⊕_ {b₁} {b₂} {b₃} {b₄} f g ! inrB v ! C > = before < g ! v ! rightC f C > 
beforeStep < _⊗_ f g ! (pairB v₁ v₂ ) ! C > = before < f ! v₁ ! fstC v₂ g C >  

-- The (c <=> a) part of the computation has been done.
-- The (a <=> b) part of the computation has been done.
-- We need to examine the context to get the 'd'.
-- We rebuild the combinator on the way out.
afterStep : {a b c d : B} → AState a b c d → State d
afterStep {d = d} [ f ! v ! emptyC ] = final v
afterStep [ f ! v ! seqC₁ g C ] = before <  g ! v ! seqC₂ f C >
afterStep [ g ! v ! seqC₂ f C ] = after [ f ◎ g ! v ! C ]
afterStep [ f ! v ! leftC g C ] = after [ f ⊕ g ! inlB v ! C ]
afterStep [ g ! v ! rightC f C ] = after [ f ⊕ g ! inrB v ! C ]
afterStep [ f ! v₁ ! fstC v₂ g C ] = before < g ! v₂ ! sndC f v₁ C >
afterStep [ g ! v₂ ! sndC f v₁ C ] = after [ f ⊗ g ! (pairB v₁ v₂) ! C ]

-- Backwards evaluator

record BStateb (a b c d : B) : Set where
  constructor <_!_!_>b
  field
    comb : a ⟺ b 
    val : VB b
    context :  Context a b c d 

record AStateb (a b c d : B) : Set where
  constructor [_!_!_]b
  field
    comb : a ⟺ b 
    val : VB a 
    context : Context a b c d 

data Stateb (c : B) : Set where
  before : {a b d : B} → BStateb a b c d → Stateb c
  after : {a b d : B} → AStateb a b c d → Stateb c
  final : VB c → Stateb c

-- The (d <=> b) part of the computation has been done. 
-- We have a 'b' and we are about to do the (a <=> b) computation backwards.
-- We get an 'a' and examine the context to get the 'c'

beforeStepb : { a b c d : B } → BStateb a b c d → Stateb c
beforeStepb < iso f ! v ! C >b = after [ iso f ! bevalP f v ! C ]b
beforeStepb < sym c ! v ! C >b = before < adjoint c ! v ! C >b
beforeStepb < f ◎ g ! v ! C >b = before < g ! v ! seqC₂ f C >b
beforeStepb < f ⊕ g ! inlB v ! C >b = before < f ! v ! leftC g C >b
beforeStepb < f ⊕ g ! inrB v ! C >b = before < g ! v ! rightC f C >b
beforeStepb < f ⊗ g ! pairB v₁ v₂ ! C >b = before < g ! v₂ ! sndC f v₁ C >b

-- The (d <-> b) part of the computation has been done. 
-- The (a <-> b) backwards computation has been done. 
-- We have an 'a' and examine the context to get the 'c'

afterStepb : { a b c d : B } → AStateb a b c d → Stateb c
afterStepb [ f ! v ! emptyC ]b = final v
afterStepb [ g ! v ! seqC₂ f C ]b = before < f ! v ! seqC₁ g C >b
afterStepb [ f ! v ! seqC₁ g C ]b = after [ f ◎ g ! v ! C ]b
afterStepb [ f ! v ! leftC g C ]b = after [ f ⊕ g ! inlB v ! C ]b
afterStepb [ g ! v ! rightC f C ]b = after [ f ⊕ g ! inrB v ! C ]b
afterStepb [ g ! v₂ ! sndC f v₁ C ]b = before < f ! v₁ ! fstC v₂ g C >b
afterStepb [ f ! v₁ ! fstC v₂ g C ]b = after [ f ⊗ g ! pairB v₁ v₂ ! C ]b

------------------------------------------------------------------------------
-- A single step of a machine

step : {d : B} → State d → State d
step (before st) = beforeStep st
step (after st) = afterStep st
step (final v) = final v

stepb : {c : B} → Stateb c → Stateb c
stepb (before st) = beforeStepb st
stepb (after st) = afterStepb st
stepb (final v) = final v

-- Forward and backwards evaluators loop until final state

eval : {a b : B} → (a ⟺ b) → VB a → VB b 
eval f v = loop (before < f ! v ! emptyC > )
  where
    loop : {b : B} → State b  → VB b
    loop (final v) = v
    loop st = loop (step st)

evalb : {a b : B} → (a ⟺ b) → VB b → VB a
evalb f v = loop (before < f ! v ! emptyC >b )
  where
    loop : {b : B} → Stateb b  → VB b
    loop (final v) = v
    loop st = loop (stepb st)

------------------------------------------------------------------------------
