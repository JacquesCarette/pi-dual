{-# OPTIONS --no-termination-check #-}

module PiN where

open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

infixr 30 _⟷_
infixr 30 _⟺_
infixr 20 _◎_

------------------------------------------------------------------------------
-- A universe of our value types

data BN : Set where
  ZERON  : BN
  ONEN   : BN
  PLUSN  : BN → BN → BN
  TIMESN : BN → BN → BN
  NEG    : BN → BN

-- negative types are un-interpreted

data Neg (A : Set) : Set where
  neg : (a : A) → Neg A

⟦_⟧N : BN → Set
⟦ ZERON ⟧N         = ⊥
⟦ ONEN ⟧N          = ⊤
⟦ PLUSN b1 b2 ⟧N   = ⟦ b1 ⟧N ⊎ ⟦ b2 ⟧N
⟦ TIMESN b1 b2 ⟧N  = ⟦ b1 ⟧N × ⟦ b2 ⟧N
⟦ NEG b ⟧N  = Neg ⟦ b ⟧N

------------------------------------------------------------------------------
-- Primitive isomorphisms

data _⟷_ : BN → BN → Set where
  -- (+,0) commutative monoid
  unite₊  : { b : BN } → PLUSN ZERON b ⟷ b
  uniti₊  : { b : BN } → b ⟷ PLUSN ZERON b
  swap₊   : { b₁ b₂ : BN } → PLUSN b₁ b₂ ⟷ PLUSN b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : BN } → PLUSN b₁ (PLUSN b₂ b₃) ⟷ PLUSN (PLUSN b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : BN } → PLUSN (PLUSN b₁ b₂) b₃ ⟷ PLUSN b₁ (PLUSN b₂ b₃)
  -- (*,1) commutative monoid
  unite⋆  : { b : BN } → TIMESN ONEN b ⟷ b
  uniti⋆  : { b : BN } → b ⟷ TIMESN ONEN b
  swap⋆   : { b₁ b₂ : BN } → TIMESN b₁ b₂ ⟷ TIMESN b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : BN } → TIMESN b₁ (TIMESN b₂ b₃) ⟷ TIMESN (TIMESN b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : BN } → TIMESN (TIMESN b₁ b₂) b₃ ⟷ TIMESN b₁ (TIMESN b₂ b₃)
  -- * distributes over + 
  dist    : { b₁ b₂ b₃ : BN } → 
            TIMESN (PLUSN b₁ b₂) b₃ ⟷ PLUSN (TIMESN b₁ b₃) (TIMESN b₂ b₃) 
  factor  : { b₁ b₂ b₃ : BN } → 
            PLUSN (TIMESN b₁ b₃) (TIMESN b₂ b₃) ⟷ TIMESN (PLUSN b₁ b₂) b₃
  -- id
  id⟷    : { b : BN } → b ⟷ b

adjointP : { b₁ b₂ : BN } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
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

evalP : { b₁ b₂ : BN } → (b₁ ⟷ b₂) → ⟦ b₁ ⟧N → ⟦ b₂ ⟧N
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

bevalP : { b₁ b₂ : BN } → (b₁ ⟷ b₂) → ⟦ b₂ ⟧N → ⟦ b₁ ⟧N
bevalP c v = evalP (adjointP c) v

------------------------------------------------------------------------------
-- Closure combinators

data _⟺_ : BN → BN → Set where
  iso    : { b₁ b₂ : BN } → (b₁ ⟷ b₂) → (b₁ ⟺ b₂) 
  sym    : { b₁ b₂ : BN } → (b₁ ⟺ b₂) → (b₂ ⟺ b₁)
  _◎_    : { b₁ b₂ b₃ : BN } → (b₁ ⟺ b₂) → (b₂ ⟺ b₃) → (b₁ ⟺ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : BN } → 
           (b₁ ⟺ b₃) → (b₂ ⟺ b₄) → (PLUSN b₁ b₂ ⟺ PLUSN b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : BN } → 
           (b₁ ⟺ b₃) → (b₂ ⟺ b₄) → (TIMESN b₁ b₂ ⟺ TIMESN b₃ b₄)
  η+     : { b : BN } →  ZERON ⟺ PLUSN (NEG b) b
  ε+     : { b : BN } → PLUSN (NEG b) b ⟺ ZERON

-- 

adjoint : { b₁ b₂ : BN } → (b₁ ⟺ b₂) → (b₂ ⟺ b₁)
adjoint (iso c) = iso (adjointP c)
adjoint (sym c)   = c
adjoint (c₁ ◎ c₂) = adjoint c₂ ◎ adjoint c₁
adjoint (c₁ ⊕ c₂) = adjoint c₁ ⊕ adjoint c₂
adjoint (c₁ ⊗ c₂) = adjoint c₁ ⊗ adjoint c₂
adjoint η+ = ε+
adjoint ε+ = η+

--

-- (Context a b c d) represents a combinator (c <-> d) with a hole
-- requiring something of type (a <-> b). When we use these contexts,
-- it is always the case that the (c <-> a) part of the computation
-- has ALREADY been done and that we are about to evaluate (a <-> b)
-- using a given 'a'. The continuation takes the output 'b' and
-- produces a 'd'.

data Context : BN → BN → BN → BN → Set where
  emptyC : {a b : BN} → Context a b a b
  seqC₁ : {a b c i o : BN} → (b ⟺ c) → Context a c i o → Context a b i o
  seqC₂ : {a b c i o : BN} → (a ⟺ b) → Context a c i o → Context b c i o
  leftC : {a b c d i o : BN} → 
          (c ⟺ d) → Context (PLUSN a c) (PLUSN b d) i o → Context a b i o
  rightC : {a b c d i o : BN} → 
           (a ⟺ b) → Context (PLUSN a c) (PLUSN b d) i o → Context c d i o
  -- the (i <-> a) part of the computation is completely done; so we must store
  -- the value of type [[ c ]] as part of the context
  fstC : {a b c d i o : BN} → 
         ⟦ c ⟧N → (c ⟺ d) → Context (TIMESN a c) (TIMESN b d) i o → Context a b i o
  -- the (i <-> c) part of the computation and the (a <-> b) part of
  -- the computation are completely done; so we must store the value
  -- of type [[ b ]] as part of the context
  sndC : {a b c d i o : BN} → 
         (a ⟺ b) → ⟦ b ⟧N → Context (TIMESN a c) (TIMESN b d) i o → Context c d i o

-- Evaluation

mutual 

  -- The (c <-> a) part of the computation has been done. 
  -- We have an 'a' and we are about to do the (a <-> b) computation.
  -- We get a 'b' and examine the context to get the 'd'
  eval_c : { a b c : BN } → (a ⟺ b) → ⟦ a ⟧N → Context a b c c → ⟦ c ⟧N
  eval_c (iso f) v C = eval_k (iso f) (evalP f v) C
  eval_c (sym c) v C = eval_c (adjoint c) v C
  eval_c (f ◎ g) v C = eval_c f v (seqC₁ g C) 
  eval_c (f ⊕ g) (inj₁ v) C = eval_c f v (leftC g C)
  eval_c (f ⊕ g) (inj₂ v) C = eval_c g v (rightC f C)
  eval_c (f ⊗ g) (v₁ , v₂) C = eval_c f v₁ (fstC v₂ g C)
  eval_c η+ () C 
  eval_c ε+ (inj₁ (neg v)) C = beval_k ε+ (inj₂ v) C
  eval_c ε+ (inj₂ v) C = beval_k ε+ (inj₁ (neg v)) C

  -- The (c <-> a) part of the computation has been done.
  -- The (a <-> b) part of the computation has been done.
  -- We need to examine the context to get the 'd'.
  -- We rebuild the combinator on the way out.
  eval_k : { a b c : BN } → (a ⟺ b) → ⟦ b ⟧N → Context a b c c → ⟦ c ⟧N
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
  beval_c : { a b c : BN } → (a ⟺ b) → ⟦ b ⟧N → Context a b c c → ⟦ c ⟧N
  beval_c (iso f) v C = beval_k (iso f) (bevalP f v) C
  beval_c (sym c) v C = beval_c (adjoint c) v C
  beval_c (f ◎ g) v C = beval_c g v (seqC₂ f C) 
  beval_c (f ⊕ g) (inj₁ v) C = beval_c f v (leftC g C)
  beval_c (f ⊕ g) (inj₂ v) C = beval_c g v (rightC f C)
  beval_c (f ⊗ g) (v₁ , v₂) C = beval_c g v₂ (sndC f v₁ C)
  beval_c η+ (inj₁ (neg v)) C = eval_k η+ (inj₂ v) C
  beval_c η+ (inj₂ v) C = eval_k η+ (inj₁ (neg v)) C
  beval_c ε+ () C 

  -- The (d <-> b) part of the computation has been done. 
  -- The (a <-> b) backwards computation has been done. 
  -- We have an 'a' and examine the context to get the 'c'
  beval_k : { a b c : BN } → (a ⟺ b) → ⟦ a ⟧N → Context a b c c → ⟦ c ⟧N
  beval_k f v emptyC = v
  beval_k g v (seqC₂ f C) = beval_c f v (seqC₁ g C) 
  beval_k f v (seqC₁ g C) = beval_k (f ◎ g) v C
  beval_k f v (leftC g C) = beval_k (f ⊕ g) (inj₁ v) C
  beval_k g v (rightC f C) = beval_k (f ⊕ g) (inj₂ v) C
  beval_k g v₂ (sndC f v₁ C) = beval_c f v₁ (fstC v₂ g C)
  beval_k f v₁ (fstC v₂ g C) = beval_k (f ⊗ g) (v₁ , v₂) C

------------------------------------------------------------------------------
-- Top level eval

eval : { a : BN } → (a ⟺ a) → ⟦ a ⟧N → ⟦ a ⟧N
eval f v = eval_c f v emptyC

BOOL : BN
BOOL = PLUSN ONEN ONEN

test1 : ⟦ BOOL ⟧N
test1 = eval {BOOL} (iso swap₊) (inj₁ tt)

-- 

teleport : {a : BN} → a ⟺ a
teleport = (iso uniti₊)        -- 0+a
         ◎ (η+ ⊕ (iso id⟷))   -- (-a+a)+a
         ◎ ((iso swap₊) ⊕ (iso id⟷)) -- (a+(-a))+a
         ◎ (iso assocr₊) -- a+((-a)+a)
         ◎ ((iso id⟷) ⊕ ε+) -- a+0
         ◎ (iso swap₊) -- 0+a
         ◎ (iso unite₊)

test2 : ⟦ BOOL ⟧N
test2 = eval {BOOL} teleport (inj₁ tt)

