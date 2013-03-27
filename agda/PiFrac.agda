module PiFrac where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

infixr 20 _◎_

data Singleton {A : Set} : A → Set where
  singleton : (x : A) -> Singleton x

mutual

  data B : Set where
    ZERO  : B 
    ONE   : B
    PLUS  : B → B → B
    TIMES : B → B → B
    RECIP : B → B
    DPAIR : { b : B } → (Σ ⟦ b ⟧ Singleton) → B

  ⟦_⟧ : B → Set
  ⟦ ZERO ⟧         = ⊥
  ⟦ ONE ⟧          = ⊤
  ⟦ PLUS b₁ b₂ ⟧   = ⟦ b₁ ⟧ ⊎ ⟦ b₂ ⟧
  ⟦ TIMES b₁ b₂ ⟧  = ⟦ b₁ ⟧ × ⟦ b₂ ⟧
  ⟦ RECIP b ⟧      = {v : ⟦ b ⟧} → Singleton v → ⊤
  ⟦ DPAIR {b} x ⟧ = Singleton x 

data _⟷_ : B → B → Set where
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
  id⟷ : {b : B } → b ⟷ b
  sym    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)
  η : {b₁ : B} {v : ⟦ b₁ ⟧} → (ONE ⟷ (DPAIR (v , singleton v)))

mutual
  eval : {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
  eval unite₊ (inj₁ ())
  eval unite₊ (inj₂ v) = v
  eval uniti₊ v = inj₂ v
  eval swap₊ (inj₁ x) = inj₂ x
  eval swap₊ (inj₂ y) = inj₁ y
  eval assocl₊ (inj₁ x) = inj₁ (inj₁ x)
  eval assocl₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  eval assocl₊ (inj₂ (inj₂ x)) = inj₂ x
  eval assocr₊ (inj₁ (inj₁ x)) = inj₁ x
  eval assocr₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  eval assocr₊ (inj₂ y) = inj₂ (inj₂ y)
  eval unite⋆ (tt , x) = x
  eval uniti⋆ v = ( tt , v)
  eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
  eval assocl⋆ (x , (y , z)) = ((x , y), z)
  eval assocr⋆ ((x , y), z) = (x , (y , z))
  eval id⟷ v = v
  eval (sym c) v = evalB c v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (inj₁ x) = inj₁ (eval c₁ x)
  eval (c₁ ⊕ c₂) (inj₂ y) = inj₂ (eval c₂ y)
  eval (c₁ ⊗ c₂) (x , y) = (eval c₁ x , eval c₂ y)
  eval (η {b₁} {v}) tt = singleton (v , (singleton v))

  evalB :  {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → ⟦ b₂ ⟧ → ⟦ b₁ ⟧
  evalB uniti₊ (inj₁ ())
  evalB uniti₊ (inj₂ v) = v
  evalB unite₊ v = inj₂ v
  evalB swap₊ (inj₁ x) = inj₂ x
  evalB swap₊ (inj₂ y) = inj₁ y
  evalB assocr₊ (inj₁ x) = inj₁ (inj₁ x)
  evalB assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalB assocr₊ (inj₂ (inj₂ x)) = inj₂ x
  evalB assocl₊ (inj₁ (inj₁ x)) = inj₁ x
  evalB assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalB assocl₊ (inj₂ y) = inj₂ (inj₂ y)
  evalB uniti⋆ (tt , x) = x
  evalB unite⋆ v = ( tt , v)
  evalB swap⋆ (v₁ , v₂) = (v₂ , v₁)
  evalB assocr⋆ (x , (y , z)) = ((x , y), z)
  evalB assocl⋆ ((x , y), z) = (x , (y , z))
  evalB id⟷ v = v
  evalB (sym c) v = eval c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (inj₁ x) = inj₁ (evalB c₁ x)
  evalB (c₁ ⊕ c₂) (inj₂ y) = inj₂ (evalB c₂ y)
  evalB (c₁ ⊗ c₂) (x , y) = (evalB c₁ x , evalB c₂ y)
  evalB (η {b₁} {v}) _ = tt

  -- This type checks, but it shouldn't :-(
test : ⊤
test = evalB (η {PLUS ONE ONE} {inj₁ tt}) (singleton ((inj₁ tt , singleton (inj₁ tt))))
{--

mutual
  data B : Set where
    ONE   : B
    PLUS  : B → B → B
    TIMES : B → B → B
    MATCH : {b : B} → Singleton b → B
    DPAIR : {b : B} → (Σ (BV b) Singleton) → B


mutual 
  eval : {b₁ b₂ : B} → b₁ ⟷ b₂ → BV b₁ → BV b₂
  eval swap₊ (LEFT v) = RIGHT v
  eval swap₊ (RIGHT v) = LEFT v
  eval (η {b₁} {v}) UNIT = NCPROD b₁ v
  eval assocl₊ (LEFT v) = LEFT (LEFT v)
  eval assocl₊ (RIGHT (LEFT v)) = LEFT (RIGHT v)
  eval assocl₊ (RIGHT (RIGHT v)) = RIGHT v
  eval assocr₊ (LEFT (LEFT v)) = LEFT v
  eval assocr₊ (LEFT (RIGHT v)) = RIGHT (LEFT v)
  eval assocr₊ (RIGHT v) = RIGHT (RIGHT v)
  eval unite⋆ (PAIR UNIT v) = v
  eval uniti⋆ v = PAIR UNIT v
  eval (ε {b₁} {v}) (NCPROD .b₁ .v) = UNIT
  eval id⟷ v = v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (LEFT v) = LEFT (eval c₁ v)
  eval (c₁ ⊕ c₂) (RIGHT v) = RIGHT (eval c₂ v)
  eval (c₁ ⊗ c₂) (PAIR v₁ v₂) = PAIR (eval c₁ v₁) (eval c₂ v₂)
  eval (lift {b₁} {b₂} {v} c) (NCPROD .b₁ .v) = NCPROD b₂ (eval c v)
 
-- name : {b₁ b₂ : B} {v : BV b₁} → (b₁ ⟷ b₂) → (ONE ⟷ DPAIR (v , singleton v))
-- name {b₁} {b₂} {v} c = η {b₁} {v} ◎ (lift (id⟷ ⊗ c))


--}

--------------------------------------------------------------------------------
-- Jacques's code

{--

data Singleton {A : Set} : A → Set where
  singleton : (x : A) -> Singleton x

mutual
  data B : Set where
    ONE   : B
    PLUS  : B → B → B
    TIMES : B → B → B
    MATCH : {b : B} → Singleton b → B
    DPAIR : {b : B} → (Σ (BV b) Singleton) → B

  data BV : B → Set where
    UNIT : BV ONE
    LEFT : {b₁ b₂ : B} → BV b₁ → BV (PLUS b₁ b₂)
    RIGHT : {b₁ b₂ : B} → BV b₂ → BV (PLUS b₁ b₂)
    PAIR : {b₁ b₂ : B} → BV b₁ → BV b₂ → BV (TIMES b₁ b₂)
    SINGLE : {b₁ : B} → BV b₁ → BV (MATCH {b₁} (singleton b₁)) 
    NCPROD : (b₁ : B) →  (v : BV b₁) → BV (DPAIR (v , (singleton v)))

mutual 
  data _⟷_ : B → B → Set where
    swap₊ : {b₁ b₂ : B} → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
    assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
    assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
    unite⋆  : { b : B } → TIMES ONE b ⟷ b
    uniti⋆  : { b : B } → b ⟷ TIMES ONE b
    η : {b₁ : B} {v : BV b₁} → ONE ⟷ DPAIR (v , (singleton v))
    ε : {b₁ : B} {v : BV b₁} → DPAIR (v , (singleton v)) ⟷ ONE
    id⟷ : {b : B } → b ⟷ b
-- closure combinators 
--   sym    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
    _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
    _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
             (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
    _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
             (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)
--   refe⋆  : { b : BF } → RECIP (RECIP b) ⟺ b
--   refi⋆  : { b : BF } → b ⟺ RECIP (RECIP b) 
--   rile⋆  : { b : BF } → TIMESF b (TIMESF b (RECIP b)) ⟺ b
--   rili⋆  : { b : BF } → b ⟺ TIMESF b (TIMESF b (RECIP b)) 
    lift : {b₁ b₂ : B} {v : BV b₁} → (c : b₁ ⟷ b₂) → 
      DPAIR (v , (singleton v)) ⟷ DPAIR (eval c v , (singleton (eval c v)))
 
  eval : {b₁ b₂ : B} → b₁ ⟷ b₂ → BV b₁ → BV b₂
  eval swap₊ (LEFT v) = RIGHT v
  eval swap₊ (RIGHT v) = LEFT v
  eval (η {b₁} {v}) UNIT = NCPROD b₁ v
  eval assocl₊ (LEFT v) = LEFT (LEFT v)
  eval assocl₊ (RIGHT (LEFT v)) = LEFT (RIGHT v)
  eval assocl₊ (RIGHT (RIGHT v)) = RIGHT v
  eval assocr₊ (LEFT (LEFT v)) = LEFT v
  eval assocr₊ (LEFT (RIGHT v)) = RIGHT (LEFT v)
  eval assocr₊ (RIGHT v) = RIGHT (RIGHT v)
  eval unite⋆ (PAIR UNIT v) = v
  eval uniti⋆ v = PAIR UNIT v
  eval (ε {b₁} {v}) (NCPROD .b₁ .v) = UNIT
  eval id⟷ v = v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (LEFT v) = LEFT (eval c₁ v)
  eval (c₁ ⊕ c₂) (RIGHT v) = RIGHT (eval c₂ v)
  eval (c₁ ⊗ c₂) (PAIR v₁ v₂) = PAIR (eval c₁ v₁) (eval c₂ v₂)
  eval (lift {b₁} {b₂} {v} c) (NCPROD .b₁ .v) = NCPROD b₂ (eval c v)
 
-- name : {b₁ b₂ : B} {v : BV b₁} → (b₁ ⟷ b₂) → (ONE ⟷ DPAIR (v , singleton v))
-- name {b₁} {b₂} {v} c = η {b₁} {v} ◎ (lift (id⟷ ⊗ c))

--}
