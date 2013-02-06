module VecS where

open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum 
open import Data.Vec
open import Data.Nat
open import Data.Bool
open import Data.Nat.Properties

import Homotopy as Pi

------------------------------------------------------------------------------

data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B
  DUAL  : B → B

data BVAL : B → Set where
  UNIT   : BVAL ONE
  LEFT   : {b₁ b₂ : B} → BVAL b₁ → BVAL (PLUS b₁ b₂)
  RIGHT  : {b₁ b₂ : B} → BVAL b₂ → BVAL (PLUS b₁ b₂)
  PAIR   : {b₁ b₂ : B} → BVAL b₁ → BVAL b₂ → BVAL (TIMES b₁ b₂)
  FLIP   : {b : B} → BVAL b → BVAL (DUAL b)

data Iso : {b₁ b₂ : B} → BVAL b₁ → BVAL b₂ → Set where
  unite₊  : {b : B} {v : BVAL b} → Iso (RIGHT {ZERO} {b} v) v
  uniti₊  : {b : B} {v : BVAL b} → Iso v (RIGHT {ZERO} {b} v)
  swap₊1  : {b₁ b₂ : B} {v₁ : BVAL b₁} → Iso (LEFT {b₁} {b₂} v₁) (RIGHT {b₂} {b₁} v₁)
  swap₊2  : {b₁ b₂ : B} {v₂ : BVAL b₂} → Iso (RIGHT {b₁} {b₂} v₂) (LEFT {b₂} {b₁} v₂)
  assocl₊1 : {b₁ b₂ b₃ : B} {v₁ : BVAL b₁} → 
             Iso (LEFT {b₁} {PLUS b₂ b₃} v₁) (LEFT {PLUS b₁ b₂} {b₃} (LEFT {b₁} {b₂} v₁))
  assocl₊2 : {b₁ b₂ b₃ : B} {v₂ : BVAL b₂} → 
             Iso (RIGHT {b₁} {PLUS b₂ b₃} (LEFT {b₂} {b₃} v₂)) (LEFT {PLUS b₁ b₂} {b₃} (RIGHT {b₁} {b₂} v₂))
  assocl₊3 : {b₁ b₂ b₃ : B} {v₃ : BVAL b₃} → 
             Iso (RIGHT {b₁} {PLUS b₂ b₃} (RIGHT {b₂} {b₃} v₃)) (RIGHT {PLUS b₁ b₂} {b₃} v₃)
  assocr₊1 : {b₁ b₂ b₃ : B} {v₁ : BVAL b₁} → 
             Iso (LEFT {PLUS b₁ b₂} {b₃} (LEFT {b₁} {b₂} v₁)) (LEFT {b₁} {PLUS b₂ b₃} v₁) 
  assocr₊2 : {b₁ b₂ b₃ : B} {v₂ : BVAL b₂} → 
             Iso (LEFT {PLUS b₁ b₂} {b₃} (RIGHT {b₁} {b₂} v₂)) (RIGHT {b₁} {PLUS b₂ b₃} (LEFT {b₂} {b₃} v₂)) 
  assocr₊3 : {b₁ b₂ b₃ : B} {v₃ : BVAL b₃} → 
             Iso (RIGHT {PLUS b₁ b₂} {b₃} v₃) (RIGHT {b₁} {PLUS b₂ b₃} (RIGHT {b₂} {b₃} v₃)) 
  unite⋆  : {b : B} {v : BVAL b} → Iso (PAIR UNIT v) v
  uniti⋆  : {b : B} {v : BVAL b} → Iso v (PAIR UNIT v)
  swap⋆   : {b₁ b₂ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} → Iso (PAIR v₁ v₂) (PAIR v₂ v₁)
  assocl⋆ : {b₁ b₂ b₃ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} {v₃ : BVAL b₃} → 
            Iso (PAIR v₁ (PAIR v₂ v₃)) (PAIR (PAIR v₁ v₂) v₃)
  assocr⋆ : {b₁ b₂ b₃ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} {v₃ : BVAL b₃} → 
            Iso (PAIR (PAIR v₁ v₂) v₃) (PAIR v₁ (PAIR v₂ v₃))
  dist1   : {b₁ b₂ b₃ : B} {v₁ : BVAL b₁} {v₃ : BVAL b₃} → 
            Iso (PAIR (LEFT {b₁} {b₂} v₁) v₃) (LEFT {TIMES b₁ b₃} {TIMES b₂ b₃} (PAIR v₁ v₃))
  dist2   : {b₁ b₂ b₃ : B} {v₂ : BVAL b₂} {v₃ : BVAL b₃} → 
            Iso (PAIR (RIGHT {b₁} {b₂} v₂) v₃) (RIGHT {TIMES b₁ b₃} {TIMES b₂ b₃} (PAIR v₂ v₃))
  factor1 : {b₁ b₂ b₃ : B} {v₁ : BVAL b₁} {v₃ : BVAL b₃} → 
            Iso (LEFT {TIMES b₁ b₃} {TIMES b₂ b₃} (PAIR v₁ v₃)) (PAIR (LEFT {b₁} {b₂} v₁) v₃)
  factor2 : {b₁ b₂ b₃ : B} {v₂ : BVAL b₂} {v₃ : BVAL b₃} → 
            Iso (RIGHT {TIMES b₁ b₃} {TIMES b₂ b₃} (PAIR v₂ v₃)) (PAIR (RIGHT {b₁} {b₂} v₂) v₃)
  id⟷   : {b : B} {v : BVAL b} → Iso v v
  sym    : {b₁ b₂ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} → Iso v₁ v₂ → Iso v₂ v₁
  VSEMI  : {b₁ b₂ b₃ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} {v₃ : BVAL b₃} → 
           Iso v₁ v₂ → Iso v₂ v₃ → Iso v₁ v₃
  VPLUS1  : {b₁ b₂ b₃ b₄ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} {v₃ : BVAL b₃} {v₄ : BVAL b₄} → 
           Iso v₁ v₃ → Iso v₂ v₄ → Iso (LEFT {b₁} {b₂} v₁) (LEFT {b₃} {b₄} v₃)
  VPLUS2  : {b₁ b₂ b₃ b₄ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} {v₃ : BVAL b₃} {v₄ : BVAL b₄} → 
           Iso v₁ v₃ → Iso v₂ v₄ → Iso (RIGHT {b₁} {b₂} v₂) (RIGHT {b₃} {b₄} v₄)
  VTIMES : {b₁ b₂ b₃ b₄ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} {v₃ : BVAL b₃} {v₄ : BVAL b₄} → 
           Iso v₁ v₃ → Iso v₂ v₄ → Iso (PAIR v₁ v₂) (PAIR v₃ v₄)
  refe⋆   : {b : B} {v : BVAL b} → Iso (FLIP (FLIP v)) v
  refi⋆   : {b : B} {v : BVAL b} → Iso v (FLIP (FLIP v))
  rile⋆   : {b : B} {v : BVAL b} → Iso (PAIR v (PAIR v (FLIP v))) v
  rili⋆   : {b : B} {v : BVAL b} → Iso v (PAIR v (PAIR v (FLIP v)))

------------------------------------------------------------------------------
-- Pi combinators

-- embed pi into the values with duals

liftT : Pi.B → B
liftT Pi.ZERO = ZERO
liftT Pi.ONE = ONE
liftT (Pi.PLUS b₁ b₂) = PLUS (liftT b₁) (liftT b₂)
liftT (Pi.TIMES b₁ b₂) = TIMES (liftT b₁) (liftT b₂)

lift : {b : Pi.B} → Pi.BVAL b → BVAL (liftT b)
lift Pi.UNIT = UNIT
lift (Pi.LEFT v) = LEFT (lift v)
lift (Pi.RIGHT v) = RIGHT (lift v)
lift (Pi.PAIR v₁ v₂) = PAIR (lift v₁) (lift v₂)

embed : {b₁ b₂ : Pi.B} → Pi.Id_B (b₁ , b₂) → Pi.BVAL b₁ → BVAL (TIMES (DUAL (liftT b₁)) (liftT b₂))
embed c v = PAIR (FLIP (lift v)) (lift (Pi.eval c v))

-- the idea would be that:
--   if   eval pi-combinator v = v'
-- then we would have a proof that 
--   (embed pi-combinator v , v) ~iso~ v'

pibool : Pi.B 
pibool = Pi.PLUS Pi.ONE Pi.ONE

pitrue : Pi.BVAL pibool
pitrue = Pi.LEFT Pi.UNIT

ex1 : BVAL (TIMES (DUAL (PLUS ONE ONE)) (PLUS ONE ONE))
ex1 = embed {pibool} {pibool} Pi.swap₊  pitrue
-- ex1 = PAIR (FLIP (LEFT UNIT)) (RIGHT UNIT)

-- Check: PAIR (PAIR (FLIP (LEFT UNIT)) (RIGHT UNIT)) (LEFT UNIT) ~ RIGHT UNIT