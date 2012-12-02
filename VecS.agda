module VecS where

open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum 
open import Data.Vec
open import Data.Nat
open import Data.Bool
open import Data.Nat.Properties

------------------------------------------------------------------------------

data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

data BVal : B → Set where
  UNIT   : BVal ONE
  LEFT   : {b₁ b₂ : B} → BVal b₁ → BVal (PLUS b₁ b₂)
  RIGHT  : {b₁ b₂ : B} → BVal b₂ → BVal (PLUS b₁ b₂)
  PAIR   : {b₁ b₂ : B} → BVal b₁ → BVal b₂ → BVal (TIMES b₁ b₂)
  UNITP  : BVal ONE
  LEFTP  : {b₁ b₂ : B} → BVal b₁ → BVal (PLUS b₁ b₂)
  RIGHTP : {b₁ b₂ : B} → BVal b₂ → BVal (PLUS b₁ b₂)
  PAIRP  : {b₁ b₂ : B} → BVal b₁ → BVal b₂ → BVal (TIMES b₁ b₂)
  DUAL   : {b : B} → BVal b → BVal b

data Iso : {b₁ b₂ : B} → BVal b₁ → BVal b₂ → Set where
  unite₊  : {b : B} {v : BVal b} → Iso (RIGHT {ZERO} {b} v) v
  uniti₊  : {b : B} {v : BVal b} → Iso v (RIGHT {ZERO} {b} v)
  swap₊1  : {b₁ b₂ : B} {v₁ : BVal b₁} → Iso (LEFT {b₁} {b₂} v₁) (RIGHT {b₂} {b₁} v₁)
  swap₊2  : {b₁ b₂ : B} {v₂ : BVal b₂} → Iso (RIGHT {b₁} {b₂} v₂) (LEFT {b₂} {b₁} v₂)
  assocl₊1 : {b₁ b₂ b₃ : B} {v₁ : BVal b₁} → 
             Iso (LEFT {b₁} {PLUS b₂ b₃} v₁) (LEFT {PLUS b₁ b₂} {b₃} (LEFT {b₁} {b₂} v₁))
  assocl₊2 : {b₁ b₂ b₃ : B} {v₂ : BVal b₂} → 
             Iso (RIGHT {b₁} {PLUS b₂ b₃} (LEFT {b₂} {b₃} v₂)) (LEFT {PLUS b₁ b₂} {b₃} (RIGHT {b₁} {b₂} v₂))
  assocl₊3 : {b₁ b₂ b₃ : B} {v₃ : BVal b₃} → 
             Iso (RIGHT {b₁} {PLUS b₂ b₃} (RIGHT {b₂} {b₃} v₃)) (RIGHT {PLUS b₁ b₂} {b₃} v₃)
  assocr₊1 : {b₁ b₂ b₃ : B} {v₁ : BVal b₁} → 
             Iso (LEFT {PLUS b₁ b₂} {b₃} (LEFT {b₁} {b₂} v₁)) (LEFT {b₁} {PLUS b₂ b₃} v₁) 
  assocr₊2 : {b₁ b₂ b₃ : B} {v₂ : BVal b₂} → 
             Iso (LEFT {PLUS b₁ b₂} {b₃} (RIGHT {b₁} {b₂} v₂)) (RIGHT {b₁} {PLUS b₂ b₃} (LEFT {b₂} {b₃} v₂)) 
  assocr₊3 : {b₁ b₂ b₃ : B} {v₃ : BVal b₃} → 
             Iso (RIGHT {PLUS b₁ b₂} {b₃} v₃) (RIGHT {b₁} {PLUS b₂ b₃} (RIGHT {b₂} {b₃} v₃)) 
  unite⋆  : {b : B} {v : BVal b} → Iso (PAIR UNIT v) v
  uniti⋆  : {b : B} {v : BVal b} → Iso v (PAIR UNIT v)
  swap⋆   : {b₁ b₂ : B} {v₁ : BVal b₁} {v₂ : BVal b₂} → Iso (PAIR v₁ v₂) (PAIR v₂ v₁)
  assocl⋆ : {b₁ b₂ b₃ : B} {v₁ : BVal b₁} {v₂ : BVal b₂} {v₃ : BVal b₃} → 
            Iso (PAIR v₁ (PAIR v₂ v₃)) (PAIR (PAIR v₁ v₂) v₃)
  assocr⋆ : {b₁ b₂ b₃ : B} {v₁ : BVal b₁} {v₂ : BVal b₂} {v₃ : BVal b₃} → 
            Iso (PAIR (PAIR v₁ v₂) v₃) (PAIR v₁ (PAIR v₂ v₃))
  dist1   : {b₁ b₂ b₃ : B} {v₁ : BVal b₁} {v₃ : BVal b₃} → 
            Iso (PAIR (LEFT {b₁} {b₂} v₁) v₃) (LEFT {TIMES b₁ b₃} {TIMES b₂ b₃} (PAIR v₁ v₃))
  dist2   : {b₁ b₂ b₃ : B} {v₂ : BVal b₂} {v₃ : BVal b₃} → 
            Iso (PAIR (RIGHT {b₁} {b₂} v₂) v₃) (RIGHT {TIMES b₁ b₃} {TIMES b₂ b₃} (PAIR v₂ v₃))
  factor1 : {b₁ b₂ b₃ : B} {v₁ : BVal b₁} {v₃ : BVal b₃} → 
            Iso (LEFT {TIMES b₁ b₃} {TIMES b₂ b₃} (PAIR v₁ v₃)) (PAIR (LEFT {b₁} {b₂} v₁) v₃)
  factor2 : {b₁ b₂ b₃ : B} {v₂ : BVal b₂} {v₃ : BVal b₃} → 
            Iso (RIGHT {TIMES b₁ b₃} {TIMES b₂ b₃} (PAIR v₂ v₃)) (PAIR (RIGHT {b₁} {b₂} v₂) v₃)
  id⟷   : {b : B} {v : BVal b} → Iso v v
  sym    : {b₁ b₂ : B} {v₁ : BVal b₁} {v₂ : BVal b₂} → Iso v₁ v₂ → Iso v₂ v₁
  VSEMI  : {b₁ b₂ b₃ : B} {v₁ : BVal b₁} {v₂ : BVal b₂} {v₃ : BVal b₃} → 
           Iso v₁ v₂ → Iso v₂ v₃ → Iso v₁ v₃
  VPLUS1  : {b₁ b₂ b₃ b₄ : B} {v₁ : BVal b₁} {v₂ : BVal b₂} {v₃ : BVal b₃} {v₄ : BVal b₄} → 
           Iso v₁ v₃ → Iso v₂ v₄ → Iso (LEFT {b₁} {b₂} v₁) (LEFT {b₃} {b₄} v₃)
  VPLUS2  : {b₁ b₂ b₃ b₄ : B} {v₁ : BVal b₁} {v₂ : BVal b₂} {v₃ : BVal b₃} {v₄ : BVal b₄} → 
           Iso v₁ v₃ → Iso v₂ v₄ → Iso (RIGHT {b₁} {b₂} v₂) (RIGHT {b₃} {b₄} v₄)
  VTIMES : {b₁ b₂ b₃ b₄ : B} {v₁ : BVal b₁} {v₂ : BVal b₂} {v₃ : BVal b₃} {v₄ : BVal b₄} → 
           Iso v₁ v₃ → Iso v₂ v₄ → Iso (PAIR v₁ v₂) (PAIR v₃ v₄)
  refe⋆   : {b : B} {v : BVal b} → Iso (DUAL (DUAL v)) v
  refi⋆   : {b : B} {v : BVal b} → Iso v (DUAL (DUAL v))
  rile⋆   : {b : B} {v : BVal b} → Iso (PAIR v (PAIR v (DUAL v))) v
  rili⋆   : {b : B} {v : BVal b} → Iso v (PAIR v (PAIR v (DUAL v)))

------------------------------------------------------------------------------

-- embed pi into this (values of type B go to a vector of dimension D
-- with a true at the entry indexed by the value and false everywhere
-- else; combinators go to matrices (outer product (dual v1 * v2)
