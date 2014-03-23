module Conway where

open import Data.Bool
open import Data.Nat renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_)
open import Data.Integer renaming (_+_ to _ℤ+_ ; _*_ to _ℤ*_)
open import Data.Rational

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

u2q : U → ℚ
u2q ZERO        = 0ℚ
u2q ONE         = 1ℚ
u2q (PLUS g h)  = (u2q g) + (u2q h)
u2q (TIMES g h) = (u2q g) * (u2q h)
u2q (NEG g)     = neg (u2q g)
u2q (RECIP g)   = 1/ (u2q g) {{!!}} 
-- need to know that | numerator (u2q g) | is not 0

-- decidable syntactic equality of games
_≟U_ : U → U → Bool
ZERO ≟U ZERO = {!!}
ZERO ≟U ONE = {!!}
ZERO ≟U PLUS u₂ u₃ = {!!}
ZERO ≟U TIMES u₂ u₃ = {!!}
ZERO ≟U NEG u₂ = {!!}
ZERO ≟U RECIP u₂ = {!!}
ONE ≟U ZERO = {!!}
ONE ≟U ONE = {!!}
ONE ≟U PLUS u₂ u₃ = {!!}
ONE ≟U TIMES u₂ u₃ = {!!}
ONE ≟U NEG u₂ = {!!}
ONE ≟U RECIP u₂ = {!!}
PLUS u₁ u₂ ≟U ZERO = {!!}
PLUS u₁ u₂ ≟U ONE = {!!}
PLUS u₁ u₂ ≟U PLUS u₃ u₄ = {!!}
PLUS u₁ u₂ ≟U TIMES u₃ u₄ = {!!}
PLUS u₁ u₂ ≟U NEG u₃ = {!!}
PLUS u₁ u₂ ≟U RECIP u₃ = {!!}
TIMES u₁ u₂ ≟U ZERO = {!!}
TIMES u₁ u₂ ≟U ONE = {!!}
TIMES u₁ u₂ ≟U PLUS u₃ u₄ = {!!}
TIMES u₁ u₂ ≟U TIMES u₃ u₄ = {!!}
TIMES u₁ u₂ ≟U NEG u₃ = {!!}
TIMES u₁ u₂ ≟U RECIP u₃ = {!!}
NEG u₁ ≟U ZERO = {!!}
NEG u₁ ≟U ONE = {!!}
NEG u₁ ≟U PLUS u₂ u₃ = {!!}
NEG u₁ ≟U TIMES u₂ u₃ = {!!}
NEG u₁ ≟U NEG u₂ = {!!}
NEG u₁ ≟U RECIP u₂ = {!!}
RECIP u₁ ≟U ZERO = {!!}
RECIP u₁ ≟U ONE = {!!}
RECIP u₁ ≟U PLUS u₂ u₃ = {!!}
RECIP u₁ ≟U TIMES u₂ u₃ = {!!}
RECIP u₁ ≟U NEG u₂ = {!!}
RECIP u₁ ≟U RECIP u₂ = {!!} 

------------------------------------------------------------------------------
-- Small tests

private 

  test₁ = q2U (- + 1 ÷ 3) 
  {--
    TIMES 
      (NEG (PLUS ONE ZERO))
      (RECIP (PLUS ONE (PLUS ONE (PLUS ONE ZERO))))
  --}

------------------------------------------------------------------------------
