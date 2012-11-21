{-# OPTIONS --no-termination-check #-}

module Pi where

open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

open import Relation.Binary.PropositionalEquality hiding (sym; [_])

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

⟦_⟧ : B → Set
⟦ ZERO ⟧         = ⊥
⟦ ONE ⟧          = ⊤
⟦ PLUS b1 b2 ⟧   = ⟦ b1 ⟧ ⊎ ⟦ b2 ⟧
⟦ TIMES b1 b2 ⟧  = ⟦ b1 ⟧ × ⟦ b2 ⟧

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

evalP : { b₁ b₂ : B } → (b₁ ⟷ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
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

bevalP : { b₁ b₂ : B } → (b₁ ⟷ b₂) → ⟦ b₂ ⟧ → ⟦ b₁ ⟧
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
         ⟦ c ⟧ → (c ⟺ d) → Context (TIMES a c) (TIMES b d) i o → Context a b i o
  -- the (i <-> c) part of the computation and the (a <-> b) part of
  -- the computation are completely done; so we must store the value
  -- of type [[ b ]] as part of the context
  sndC : {a b c d i o : B} → 
         (a ⟺ b) → ⟦ b ⟧ → Context (TIMES a c) (TIMES b d) i o → Context c d i o

-- Evaluation

mutual 

  -- The (c <-> a) part of the computation has been done. 
  -- We have an 'a' and we are about to do the (a <-> b) computation.
  -- We get a 'b' and examine the context to get the 'd'
  eval_c : { a b c d : B } → (a ⟺ b) → ⟦ a ⟧ → Context a b c d → ⟦ d ⟧
  eval_c (iso f) v C = eval_k (iso f) (evalP f v) C
  eval_c (sym c) v C = eval_c (adjoint c) v C
  eval_c (f ◎ g) v C = eval_c f v (seqC₁ g C) 
  eval_c (f ⊕ g) (inj₁ v) C = eval_c f v (leftC g C)
  eval_c (f ⊕ g) (inj₂ v) C = eval_c g v (rightC f C)
  eval_c (f ⊗ g) (v₁ , v₂) C = eval_c f v₁ (fstC v₂ g C)

  -- The (c <-> a) part of the computation has been done.
  -- The (a <-> b) part of the computation has been done.
  -- We need to examine the context to get the 'd'.
  -- We rebuild the combinator on the way out.
  eval_k : { a b c d : B } → (a ⟺ b) → ⟦ b ⟧ → Context a b c d → ⟦ d ⟧
  eval_k f v emptyC = v 
  eval_k f v (seqC₁ g C) = eval_c g v (seqC₂ f C) 
  eval_k g v (seqC₂ f C) = eval_k (f ◎ g) v C
  eval_k f v (leftC g C) = eval_k (f ⊕ g) (inj₁ v) C
  eval_k g v (rightC f C) = eval_k (f ⊕ g) (inj₂ v) C
  eval_k f v₁ (fstC v₂ g C) = eval_c g v₂ (sndC f v₁ C)
  eval_k g v₂ (sndC f v₁ C) = eval_k (f ⊗ g) (v₁ , v₂) C

-- Backwards evaluator

mutual 

  -- The (d <-> b) part of the computation has been done. 
  -- We have a 'b' and we are about to do the (a <-> b) computation backwards.
  -- We get an 'a' and examine the context to get the 'c'
  beval_c : { a b c d : B } → (a ⟺ b) → ⟦ b ⟧ → Context a b c d → ⟦ c ⟧
  beval_c (iso f) v C = beval_k (iso f) (bevalP f v) C
  beval_c (sym c) v C = beval_c (adjoint c) v C
  beval_c (f ◎ g) v C = beval_c g v (seqC₂ f C) 
  beval_c (f ⊕ g) (inj₁ v) C = beval_c f v (leftC g C)
  beval_c (f ⊕ g) (inj₂ v) C = beval_c g v (rightC f C)
  beval_c (f ⊗ g) (v₁ , v₂) C = beval_c g v₂ (sndC f v₁ C)

  -- The (d <-> b) part of the computation has been done. 
  -- The (a <-> b) backwards computation has been done. 
  -- We have an 'a' and examine the context to get the 'c'
  beval_k : { a b c d : B } → (a ⟺ b) → ⟦ a ⟧ → Context a b c d → ⟦ c ⟧
  beval_k f v emptyC = v
  beval_k g v (seqC₂ f C) = beval_c f v (seqC₁ g C) 
  beval_k f v (seqC₁ g C) = beval_k (f ◎ g) v C
  beval_k f v (leftC g C) = beval_k (f ⊕ g) (inj₁ v) C
  beval_k g v (rightC f C) = beval_k (f ⊕ g) (inj₂ v) C
  beval_k g v₂ (sndC f v₁ C) = beval_c f v₁ (fstC v₂ g C)
  beval_k f v₁ (fstC v₂ g C) = beval_k (f ⊗ g) (v₁ , v₂) C

------------------------------------------------------------------------------
-- Proposition 'Reversible'

-- eval_c : { a b c d : B } → (a ⟺ b) → ⟦ a ⟧ → Context a b c d → ⟦ d ⟧
-- eval_k : { a b c d : B } → (a ⟺ b) → ⟦ b ⟧ → Context a b c d → ⟦ d ⟧
-- beval_c : { a b c d : B } → (a ⟺ b) → ⟦ b ⟧ → Context a b c d → ⟦ c ⟧
-- beval_k : { a b c d : B } → (a ⟺ b) → ⟦ a ⟧ → Context a b c d → ⟦ c ⟧

-- Prop. 2.2

logical-reversibility : {a b : B} {f : a ⟺ b} {va : ⟦ a ⟧} {vb : ⟦ b ⟧} →
  eval_c f va emptyC ≡ eval_k f vb emptyC → 
  eval_c (adjoint f) vb emptyC ≡ eval_k (adjoint f) va emptyC
logical-reversibility = {!!} 

------------------------------------------------------------------------------

  