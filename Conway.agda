module Conway where

open import Data.Bool renaming (_≟_ to _B≟_)
open import Data.Nat renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≟_ to _ℕ≟_)
open import Data.Integer 
  renaming (_+_ to _ℤ+_ ; _*_ to _ℤ*_ ; -_ to ℤ-_ ; _≟_ to _ℤ≟_)
open import Data.Rational renaming (_≟_ to _ℚ≟_)
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

open import Rat -- operations on rationals

------------------------------------------------------------------------------
-- Universe of games

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U
  NEG   : U → U
  RECIP : U → U

-- Conversion from the rationals to the universe of games

n2U : ℕ → U
n2U 0       = ZERO
n2U (suc n) = PLUS ONE (n2U n) 

z2U : ℤ → U
z2U -[1+ n ] = NEG (n2U (ℕ.suc n))
z2U (+ n)    = n2U n

q2U : ℚ → U
q2U p = TIMES (z2U (ℚ.numerator p)) (RECIP (n2U (ℕ.suc (ℚ.denominator-1 p))))

-- Conversion from the universe of games to the rationals

-- use meadows?

mutual

  u2q : U → ℚ
  u2q ZERO        = 0ℚ
  u2q ONE         = 1ℚ
  u2q (PLUS g h)  = (u2q g) + (u2q h)
  u2q (TIMES g h) = (u2q g) * (u2q h)
  u2q (NEG g)     = - (u2q g)
  u2q (RECIP g)   = 1/_ (u2q g) {{!!}} 
-- need to know that | numerator (u2q g) | is not 0

  u2q≢0 : (u : U) → {u≢0 : False (u2q u ℚ≟ 0ℚ)} → ℚ
  u2q≢0 u {u≢0} with (u2q u ℚ≟ 0ℚ)
  u2q≢0 u {()} | yes _
  u2q≢0 u {_}  | no _ = u2q u

------------------------------------------------------------------------------
-- Small tests

private 

  test₁ = q2U (- (+ 1 ÷ 3))
  {--
    TIMES 
      (NEG (PLUS ONE ZERO))
      (RECIP (PLUS ONE (PLUS ONE (PLUS ONE ZERO))))
  --}

------------------------------------------------------------------------------
