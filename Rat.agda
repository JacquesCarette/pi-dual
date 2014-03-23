module Rat where

open import Data.Unit
import Data.Sign as S
open import Data.String
open import Data.Nat renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≟_ to _ℕ≟_)
open import Data.Nat.Coprimality renaming (sym to symCoprime)
open import Data.Nat.GCD
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Nat.Divisibility
open import Data.Integer hiding (_-_ ; -_) 
  renaming (_+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _≟_ to _ℤ≟_ ; show to ℤshow)
open import Data.Integer.Properties
open import Data.Rational
open import Data.Product
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infix  8 -_ 1/_
infixl 7 _*_ _/_
infixl 6 _-_ _+_

------------------------------------------------------------------------------
-- Some lemmas to help with operations on rationals

-- normalize takes two natural numbers, say 6 and 21 and their gcd 3, and
-- returns them normalized as 2 and 7 and a proof that they are coprime

normalize : ∀ {m n g} → {n≢0 : False (n ℕ≟ 0)} → {g≢0 : False (g ℕ≟ 0)} →
            GCD m n g → Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] False (q ℕ≟ 0) × Coprime p q
normalize {m} {n} {0} {_} {()} _
normalize {m} {n} {ℕ.suc g} {_} {_} G with Bézout.identity G
normalize {m} {.0} {ℕ.suc g} {()} {_}
  (GCD.is (divides p m≡pg' , divides 0 refl) _) | _
normalize {m} {n} {ℕ.suc g} {_} {_}
  (GCD.is (divides p m≡pg' , divides (ℕ.suc q) n≡qg') _) | Bézout.+- x y eq =
    (p , ℕ.suc q , tt , Bézout-coprime {p} {ℕ.suc q} {g} (Bézout.+- x y
               (begin
                 ℕ.suc g ℕ+ y ℕ* (ℕ.suc q ℕ* ℕ.suc g)
               ≡⟨ cong (λ h → ℕ.suc g ℕ+ y ℕ* h) (sym n≡qg') ⟩
                 ℕ.suc g ℕ+ y ℕ* n
               ≡⟨ eq ⟩
                 x ℕ* m
               ≡⟨ cong (λ h → x ℕ* h) m≡pg' ⟩
                 x ℕ* (p ℕ* ℕ.suc g) ∎)))
normalize {m} {n} {ℕ.suc g} {_} {_}
  (GCD.is (divides p m≡pg' , divides (ℕ.suc q) n≡qg') _) | Bézout.-+ x y eq =
    (p , ℕ.suc q , tt , Bézout-coprime {p} {ℕ.suc q} {g} (Bézout.-+ x y
               (begin
                 ℕ.suc g ℕ+ x ℕ* (p ℕ* ℕ.suc g)
               ≡⟨ cong (λ h → ℕ.suc g ℕ+ x ℕ* h) (sym m≡pg') ⟩
                 ℕ.suc g ℕ+ x ℕ* m
               ≡⟨ eq ⟩
                 y ℕ* n
               ≡⟨ cong (λ h → y ℕ* h) n≡qg' ⟩
                 y ℕ* (ℕ.suc q ℕ* ℕ.suc g) ∎)))

-- a version of gcd that returns a proof that the result is non-zero given
-- that one of the inputs is non-zero

gcd≢0 : (m n : ℕ) → {m≢0 : False (m ℕ≟ 0)} → ∃ λ d → GCD m n d × False (d ℕ≟ 0)
gcd≢0 m  n {m≢0} with gcd m n
gcd≢0 m  n {m≢0} | (0 , GCD.is (0|m , _) _) with 0∣⇒≡0 0|m
gcd≢0 .0 n {()}  | (0 , GCD.is (0|m , _) _) | refl
gcd≢0 m  n {_}   | (ℕ.suc d , G) = (ℕ.suc d , G , tt)

------------------------------------------------------------------------------
-- Operations on rationals: unary -, reciprocal, multiplication, addition

-- unary negation
-- 
-- Andreas Abel says: Agda's type-checker is incomplete when it has to handle
-- types with leading hidden quantification, such as the ones of Coprime m n
-- and c.  A work around is to use hidden abstraction explicitly.  In your
-- case, giving λ {i} -> c works.  Not pretty, but unavoidable until we
-- improve on the current heuristics. I recorded this as a bug
-- http://code.google.com/p/agda/issues/detail?id=1079
--
-_ : ℚ → ℚ
-_ p with ℚ.numerator p | ℚ.denominator-1 p | toWitness (ℚ.isCoprime p)
... | -[1+ n ]  | d | c = (+ ℕ.suc n ÷ ℕ.suc d) {fromWitness (λ {i} → c)}
... | + 0       | d | _ = p
... | + ℕ.suc n | d | c = (-[1+ n ]  ÷ ℕ.suc d) {fromWitness (λ {i} → c)}

-- reciprocal: requires a proof that the numerator is not zero

1/_ : (p : ℚ) → {n≢0 : False (∣ ℚ.numerator p ∣ ℕ≟ 0)} → ℚ
1/_ p {n≢0} with ℚ.numerator p | ℚ.denominator-1 p | toWitness (ℚ.isCoprime p)
1/_ p {()} | + 0 | d | c
... | + (ℕ.suc n) | d | c =
  ((S.+ ◃ ℕ.suc d) ÷ ℕ.suc n)
  {fromWitness (λ {i} →
    subst (λ h → Coprime h (ℕ.suc n)) 
          (sym (abs-◃ S.+ (ℕ.suc d))) 
          (symCoprime c))}
... | -[1+ n ] | d | c =
  ((S.- ◃ ℕ.suc d) ÷ ℕ.suc n)
  {fromWitness (λ {i} →
    subst (λ h → Coprime h (ℕ.suc n)) 
          (sym (abs-◃ S.- (ℕ.suc d))) 
          (symCoprime c))}

-- multiplication

private 
  helper* : (n₁ : ℤ) → (d₁ : ℕ) → (n₂ : ℤ) → (d₂ : ℕ) →
            {n≢0 : False (∣ n₁ ℤ* n₂ ∣ ℕ≟ 0)} →
            {d≢0 : False (d₁ ℕ* d₂ ℕ≟ 0)} →
            ℚ
  helper* n₁ d₁ n₂ d₂ {n≢0} {d≢0} =
    let n = n₁ ℤ* n₂
        d = d₁ ℕ* d₂
        (g , G , g≢0) = gcd≢0 ∣ n ∣ d {n≢0}
        (nn , nd , nd≢0 , nc) = normalize {∣ n ∣} {d} {g} {d≢0} {g≢0} G
    in ((sign n ◃ nn) ÷ nd) 
       {fromWitness (λ {i} → 
          subst (λ h → Coprime h nd) (sym (abs-◃ (sign n) nn)) nc)}
       {nd≢0}

_*_ : ℚ → ℚ → ℚ
p₁ * p₂ with ℚ.numerator p₁ | ℚ.numerator p₂
... | + 0  | _    = + 0 ÷ 1
... | _    | + 0  = + 0 ÷ 1
... | + ℕ.suc n₁ | + ℕ.suc n₂ =
  helper* (+ ℕ.suc n₁) (ℕ.suc (ℚ.denominator-1 p₁))
          (+ ℕ.suc n₂) (ℕ.suc (ℚ.denominator-1 p₂))
... | + ℕ.suc n₁ | -[1+ n₂ ] =
  helper* (+ ℕ.suc n₁) (ℕ.suc (ℚ.denominator-1 p₁))
          -[1+ n₂ ] (ℕ.suc (ℚ.denominator-1 p₂))
... | -[1+ n₁ ] | + ℕ.suc n₂ =
  helper* -[1+ n₁ ] (ℕ.suc (ℚ.denominator-1 p₁))
          (+ ℕ.suc n₂) (ℕ.suc (ℚ.denominator-1 p₂))
... | -[1+ n₁ ] | -[1+ n₂ ] =
  helper* -[1+ n₁ ] (ℕ.suc (ℚ.denominator-1 p₁))
          -[1+ n₂ ] (ℕ.suc (ℚ.denominator-1 p₂))

-- addition

private 

  helper+ : (n : ℤ) → (d : ℕ) → {d≢0 : False (d ℕ≟ 0)} → ℚ
  helper+ (+ 0) d {d≢0} = + 0 ÷ 1
  helper+ (+ ℕ.suc n) d {d≢0} =
    let (g , G , g≢0) = gcd≢0 ∣ + ℕ.suc n ∣ d {tt}
        (nn , nd , nd≢0 , nc) = normalize {∣ + ℕ.suc n ∣} {d} {g} {d≢0} {g≢0} G
    in ((S.+ ◃ nn) ÷ nd) 
       {fromWitness (λ {i} → 
          subst (λ h → Coprime h nd) (sym (abs-◃ S.+ nn)) nc)}
       {nd≢0}
  helper+ -[1+ n ] d {d≢0} =
    let (g , G , g≢0) = gcd≢0 ∣ -[1+ n ] ∣ d {tt}
        (nn , nd , nd≢0 , nc) = normalize {∣ -[1+ n ] ∣} {d} {g} {d≢0} {g≢0} G
    in ((S.- ◃ nn) ÷ nd) 
       {fromWitness (λ {i} → 
          subst (λ h → Coprime h nd) (sym (abs-◃ S.- nn)) nc)}
       {nd≢0}

_+_ : ℚ → ℚ → ℚ
p₁ + p₂ =
  let n₁ = ℚ.numerator p₁
      d₁ = ℕ.suc (ℚ.denominator-1 p₁)
      n₂ = ℚ.numerator p₂
      d₂ = ℕ.suc (ℚ.denominator-1 p₂)
      n = (n₁ ℤ* + d₂) ℤ+ (n₂ ℤ* + d₁)
      d = d₁ ℕ* d₂
  in helper+ n d

-- subtraction and division

_-_ : ℚ → ℚ → ℚ
p₁ - p₂ = p₁ + (- p₂)

_/_ : (p₁ p₂ : ℚ) → {n≢0 : False (∣ ℚ.numerator p₂ ∣ ℕ≟ 0)} → ℚ
_/_ p₁ p₂ {n≢0} = p₁ * (1/_ p₂ {n≢0})

-- conventional representation

show : ℚ → String
show p = ℤshow (ℚ.numerator p) ++ "/" ++ ℕshow (ℕ.suc (ℚ.denominator-1 p))

------------------------------------------------------------------------------
-- A few constants and some small tests

0ℚ 1ℚ : ℚ
0ℚ = + 0 ÷ 1
1ℚ = + 1 ÷ 1

private

  p₀ p₁ p₂ p₃ : ℚ
  p₀ = + 1 ÷ 2
  p₁ = + 1 ÷ 3
  p₂ = -[1+ 2 ] ÷ 4
  p₃ = + 3 ÷ 4

  test₀ = show p₂
  test₁ = show (- p₂)
  test₂ = show (1/ p₂)
  test₃ = show (p₀ + p₀)
  test₄ = show (p₁ * p₂)

------------------------------------------------------------------------------
