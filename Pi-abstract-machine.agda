{-# OPTIONS --no-termination-check #-}

module Pi-abstract-machine where

open import Data.Empty
open import Data.Bool
open import Data.Fin hiding (_+_; zero; suc)
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Nat -- hiding (_+_; zero; suc)
open import Relation.Binary

open import Relation.Binary.PropositionalEquality hiding (sym; [_])

infixr 30 _⟷_
--infixr 30 _⟺_
--infixr 20 _◎_

------------------------------------------------------------------------------
-- A universe of our value types

-- un-normalized types
data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

-- un-normalized values
data VB : (b : B) → Set where
  unitB : VB ONE
  inlB : {b₁ b₂ : B} → VB b₁ → VB (PLUS b₁ b₂)
  inrB : {b₁ b₂ : B} → VB b₂ → VB (PLUS b₁ b₂)
  pairB : {b₁ b₂ : B} → VB b₁ → VB b₂ → VB (TIMES b₁ b₂)

-- normalize a type to a natural number (only thing that matters)
module Size where
  open Data.Nat using (_+_; _*_; zero; suc)

  size : B → ℕ
  size ZERO = 0
  size ONE = 1
  size (PLUS b₁ b₂) = size b₁ + size b₂
  size (TIMES b₁ b₂) = size b₁ * size b₂

open Size

-- normalize a value to a number
{--
 Example: 
    original type is PLUS ONE (PLUS ONE ONE)
    it has 3 values
      inlB unitB
      inrB (inlB unitB)
      inrB (inrB unitB)

    we map the type to the natural number 3
    we map the values to numbers
--}

module Norm where
  open Data.Nat using (_+_; _*_; zero; suc)

  normalize : (b : B) → VB b → ℕ
  normalize ZERO () 
  normalize ONE unitB = zero
  normalize (PLUS b₁ b₂) (inlB v) = normalize b₁ v
  normalize (PLUS b₁ b₂) (inrB v) = size b₁ + normalize b₂ v
  normalize (TIMES b₁ b₂) (pairB v₁ v₂) = size b₂ * normalize b₁ v₁ + normalize b₂ v₂

open Norm

{--
testT = PLUS ONE (PLUS ONE ONE)
test1 = normalize testT (inlB unitB)
test2 = normalize testT (inrB (inlB unitB))
test3 = normalize testT (inrB (inrB unitB))

testT = PLUS ZERO (PLUS ONE ONE)
test1 = normalize testT (inrB (inlB unitB))
test2 = normalize testT (inrB (inrB unitB))

testT = TIMES (PLUS ONE ONE) ZERO
test1 = size testT

testT = TIMES (PLUS ONE ONE) (PLUS ONE (PLUS ONE ONE))
test1 = normalize testT (pairB (inlB unitB) (inlB unitB))
test2 = normalize testT (pairB (inrB unitB) (inlB unitB))
test3 = normalize testT (pairB (inlB unitB) (inrB (inlB unitB)))
test4 = normalize testT (pairB (inrB unitB) (inrB (inlB unitB)))
test5 = normalize testT (pairB (inlB unitB) (inrB (inrB unitB)))
test6 = normalize testT (pairB (inrB unitB) (inrB (inrB unitB)))

--}

ℕ= : ℕ → ℕ → Bool
ℕ= zero zero = true
ℕ= zero _ = false
ℕ= _ zero = false
ℕ= (suc m) (suc n) = ℕ= m n 

b= : {b₁ b₂ : B} → (v₁ : VB b₁) → (v₂ : VB b₂) → Bool
b= {b₁} {b₂} v₁ v₂ = ℕ= (normalize b₁ v₁) (normalize b₂ v₂)

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
  iso    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₁ ⟺ b₂) 
  sym    : { b₁ b₂ : B } → (b₁ ⟺ b₂) → (b₂ ⟺ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟺ b₂) → (b₂ ⟺ b₃) → (b₁ ⟺ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟺ b₃) → (b₂ ⟺ b₄) → (PLUS b₁ b₂ ⟺ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟺ b₃) → (b₂ ⟺ b₄) → (TIMES b₁ b₂ ⟺ TIMES b₃ b₄)

-- 

adjoint : { b₁ b₂ : B } → (b₁ ⟺ b₂) → (b₂ ⟺ b₁)
adjoint (iso c) = iso (adjointP c)
adjoint (sym c)   = c
adjoint (c₁ ◎ c₂) = adjoint c₂ ◎ adjoint c₁
adjoint (c₁ ⊕ c₂) = adjoint c₁ ⊕ adjoint c₂
adjoint (c₁ ⊗ c₂) = adjoint c₁ ⊗ adjoint c₂

--

-- (Context a b c d) represents a combinator (c <-> d) with a hole
-- requiring something of type (a <-> b). When we use these contexts,
-- it is always the case that the (c <-> a) part of the computation
-- has ALREADY been done and that we are about to evaluate (a <-> b)
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

-- Evaluation

record BState { a b c d : B } : Set where
  constructor <_#_#_>
  field
    comb : a ⟺ b 
    val : VB a 
    context :  Context a b c d 

record AState { a b c d : B } : Set where
  constructor [_#_#_]
  field
    comb : a ⟺ b 
    val : VB b 
    context : Context a b c d 

data State (d : B) : Set where
  before : {a b c : B} → BState {a} {b} {c} {d} → State d
  after : {a b c : B} → AState {a} {b} {c} {d} → State d
  final : VB d → State d

beforeStep : {a b c d : B} → BState {a} {b} {c} {d} → State d
beforeStep < iso f # v # C > = after [ iso f # (evalP f v) # C ]
beforeStep < sym c # v # C > = before < adjoint c # v # C > 
beforeStep < _◎_ {b₂ = _} f g # v # C > = before < f # v # seqC₁ g C > 
beforeStep < _⊕_ {b₁} {b₂} {b₃} {b₄} f g # inlB v # C > = before < f # v # leftC g C >  
beforeStep < _⊕_ {b₁} {b₂} {b₃} {b₄} f g # inrB v # C > = before < g # v # rightC f C > 
beforeStep < _⊗_ f g # (pairB v₁ v₂ ) # C > = before < f # v₁ # fstC v₂ g C >  

afterStep : {a b c d : B} → AState {a} {b} {c} {d} → State d
afterStep {d = d} [ f # v # emptyC ] = final {d} v
afterStep [ f # v # seqC₁ g C ] = before <  g # v # seqC₂ f C >
afterStep [ g # v # seqC₂ f C ] = after [ f ◎ g # v # C ]
afterStep [ f # v # leftC g C ] = after [ f ⊕ g # inlB v # C ]
afterStep [ g # v # rightC f C ] = after [ f ⊕ g # inrB v # C ]
afterStep [ f # v₁ # fstC v₂ g C ] = before < g # v₂ # sndC f v₁ C >
afterStep [ g # v₂ # sndC f v₁ C ] = after [ f ⊗ g # (pairB v₁ v₂) # C ]
  -- The (c <-> a) part of the computation has been done.
  -- The (a <-> b) part of the computation has been done.
  -- We need to examine the context to get the 'd'.
  -- We rebuild the combinator on the way out.

eval : {a b : B} → (a ⟺ b) → VB a → VB b 
eval f v = loop (before < f # v # emptyC > )
  where
    loop : {b : B} → State b  → VB b
    loop (before y) = loop (beforeStep y)
    loop (after y) = loop (afterStep y)
    loop (final y) = y

step : {b : B} → State b → State b
step (before y) = beforeStep y
step (after y) = afterStep y
step (final y) = final y

mutual 

  -- The (c <-> a) part of the computation has been done. 
  -- We have an 'a' and we are about to do the (a <-> b) computation.
  -- We get a 'b' and examine the context to get the 'd'
  eval_c : { a b c d : B } → (a ⟺ b) → VB a → Context a b c d → VB d
  eval_c (iso f) v C = eval_k (iso f) (evalP f v) C
  eval_c (sym c) v C = eval_c (adjoint c) v C
  eval_c (f ◎ g) v C = eval_c f v (seqC₁ g C) 
  eval_c (f ⊕ g) (inlB v) C = eval_c f v (leftC g C)
  eval_c (f ⊕ g) (inrB v) C = eval_c g v (rightC f C)
  eval_c (f ⊗ g) (pairB v₁ v₂) C = eval_c f v₁ (fstC v₂ g C)

  -- The (c <-> a) part of the computation has been done.
  -- The (a <-> b) part of the computation has been done.
  -- We need to examine the context to get the 'd'.
  -- We rebuild the combinator on the way out.
  eval_k : { a b c d : B } → (a ⟺ b) → VB b → Context a b c d → VB d
  eval_k f v emptyC = v 
  eval_k f v (seqC₁ g C) = eval_c g v (seqC₂ f C) 
  eval_k g v (seqC₂ f C) = eval_k (f ◎ g) v C
  eval_k f v (leftC g C) = eval_k (f ⊕ g) (inlB v) C
  eval_k g v (rightC f C) = eval_k (f ⊕ g) (inrB v) C
  eval_k f v₁ (fstC v₂ g C) = eval_c g v₂ (sndC f v₁ C)
  eval_k g v₂ (sndC f v₁ C) = eval_k (f ⊗ g) (pairB v₁ v₂) C

-- Backwards evaluator

mutual 

  -- The (d <-> b) part of the computation has been done. 
  -- We have a 'b' and we are about to do the (a <-> b) computation backwards.
  -- We get an 'a' and examine the context to get the 'c'
  beval_c : { a b c d : B } → (a ⟺ b) → VB b → Context a b c d → VB c
  beval_c (iso f) v C = beval_k (iso f) (bevalP f v) C
  beval_c (sym c) v C = beval_c (adjoint c) v C
  beval_c (f ◎ g) v C = beval_c g v (seqC₂ f C) 
  beval_c (f ⊕ g) (inlB v) C = beval_c f v (leftC g C)
  beval_c (f ⊕ g) (inrB v) C = beval_c g v (rightC f C)
  beval_c (f ⊗ g) (pairB v₁ v₂) C = beval_c g v₂ (sndC f v₁ C)

  -- The (d <-> b) part of the computation has been done. 
  -- The (a <-> b) backwards computation has been done. 
  -- We have an 'a' and examine the context to get the 'c'
  beval_k : { a b c d : B } → (a ⟺ b) → VB a → Context a b c d → VB c 
  beval_k f v emptyC = v
  beval_k g v (seqC₂ f C) = beval_c f v (seqC₁ g C) 
  beval_k f v (seqC₁ g C) = beval_k (f ◎ g) v C
  beval_k f v (leftC g C) = beval_k (f ⊕ g) (inlB v) C
  beval_k g v (rightC f C) = beval_k (f ⊕ g) (inrB v) C
  beval_k g v₂ (sndC f v₁ C) = beval_c f v₁ (fstC v₂ g C)
  beval_k f v₁ (fstC v₂ g C) = beval_k (f ⊗ g) (pairB v₁ v₂) C

------------------------------------------------------------------------------
-- Proposition 'Reversible'

-- eval_c : { a b c d : B } → (a ⟺ b) → ⟦ a ⟧ → Context a b c d → ⟦ d ⟧
-- eval_k : { a b c d : B } → (a ⟺ b) → ⟦ b ⟧ → Context a b c d → ⟦ d ⟧
-- beval_c : { a b c d : B } → (a ⟺ b) → ⟦ b ⟧ → Context a b c d → ⟦ c ⟧
-- beval_k : { a b c d : B } → (a ⟺ b) → ⟦ a ⟧ → Context a b c d → ⟦ c ⟧

-- Prop. 2.2
{--
logical-reversibility : {a b : B} {f : a ⟺ b} {va : ⟦ a ⟧} {vb : ⟦ b ⟧} →
  eval_c f va emptyC ≡ eval_k f vb emptyC → 
  eval_c (adjoint f) vb emptyC ≡ eval_k (adjoint f) va emptyC
logical-reversibility = {!!} 
--}

------------------------------------------------------------------------------
