module Rat where
           
open import Data.Unit
import Data.Sign as S
open import Data.Nat renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≟_ to _ℕ≟_)
open import Data.Nat.Coprimality renaming (sym to symCoprime)
open import Data.Nat.GCD
open import Data.Nat.Divisibility
open import Data.Integer renaming (_+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _≟_ to _ℤ≟_)
open import Data.Rational
open import Data.Product
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------------
-- Some lemmas to help with operations on rationals

-- normalize takes two natural numbers, say 6 and 21 and their gcd 3, and
-- returns them normalized as 2 and 7 and a proof that they are coprime

normalize : ∀ {m n g} → {n≢0 : False (n ℕ≟ 0)} → {g≢0 : False (g ℕ≟ 0)} → 
            GCD m n g → Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] Coprime p q × False (q ℕ≟ 0)
normalize {m} {n} {0} {_} {()} _
normalize {m} {n} {ℕ.suc g} {_} {_} G with Bézout.identity G 
normalize {m} {.0} {ℕ.suc g} {()} {_} 
  (GCD.is (divides p m≡pg' , divides 0 refl) _) | _ 
normalize {m} {n} {ℕ.suc g} {_} {_} 
  (GCD.is (divides p m≡pg' , divides (ℕ.suc q) n≡qg') _) | Bézout.+- x y eq = 
    (p , ℕ.suc q , Bézout-coprime {p} {ℕ.suc q} {g} (Bézout.+- x y
               (begin 
                 ℕ.suc g ℕ+ y ℕ* (ℕ.suc q ℕ* ℕ.suc g) 
               ≡⟨ cong (λ h → ℕ.suc g ℕ+ y ℕ* h) (sym n≡qg') ⟩
                 ℕ.suc g ℕ+ y ℕ* n
               ≡⟨ eq ⟩
                 x ℕ* m
               ≡⟨ cong (λ h → x ℕ* h) m≡pg' ⟩
                 x ℕ* (p ℕ* ℕ.suc g) ∎)) , 
             tt)
normalize {m} {n} {ℕ.suc g} {_} {_} 
  (GCD.is (divides p m≡pg' , divides (ℕ.suc q) n≡qg') _) | Bézout.-+ x y eq = 
    (p , ℕ.suc q , Bézout-coprime {p} {ℕ.suc q} {g} (Bézout.-+ x y
               (begin
                 ℕ.suc g ℕ+ x ℕ* (p ℕ* ℕ.suc g) 
               ≡⟨ cong (λ h → ℕ.suc g ℕ+ x ℕ* h) (sym m≡pg') ⟩ 
                 ℕ.suc g ℕ+ x ℕ* m
               ≡⟨ eq ⟩ 
                 y ℕ* n
               ≡⟨ cong (λ h → y ℕ* h) n≡qg' ⟩ 
                 y ℕ* (ℕ.suc q ℕ* ℕ.suc g) ∎)) , 
             tt)

-- a version of gcd that returns a proof that the result is non-zero given
-- that one of the inputs is non-zero

gcdz : (m n : ℕ) → {m≢0 : False (m ℕ≟ 0)} → 
       ∃ λ d → GCD m n d × False (d ℕ≟ 0)
gcdz m  n {m≢0} with gcd m n 
gcdz m  n {m≢0} | (0 , GCD.is (0|m , _) _) with 0∣⇒≡0 0|m
gcdz .0 n {()}  | (0 , GCD.is (0|m , _) _) | refl
gcdz m  n {_}   | (ℕ.suc d , G) = (ℕ.suc d , G , tt)

-- once we have a proof of coprimality for natural numbers we can get a proof
-- for absolute values of integers

sCoprime : ∀ {s n d} → Coprime n d → Coprime ∣ s ◃ n ∣ d
sCoprime {s} {n} {d} c {i} (divides q eq , i|d) = 
  c {i} 
    (divides q (begin
                  n
                ≡⟨ sym absSign ⟩
                  ∣ s ◃ n ∣
                ≡⟨ eq ⟩ 
                  q ℕ* i ∎) , 
     i|d)
  where absSign : ∀ {s n} → ∣ s ◃ n ∣ ≡ n 
        absSign {_}   {0}       = refl
        absSign {S.-} {ℕ.suc n} = refl
        absSign {S.+} {ℕ.suc n} = refl 

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
ℚN : ℚ → ℚ
ℚN p with ℚ.numerator p | ℚ.denominator-1 p | toWitness (ℚ.isCoprime p)
... | -[1+ n ]  | d | c = (+ ℕ.suc n ÷ ℕ.suc d) {fromWitness (λ {i} → c)}
... | + 0       | d | _ = p
... | + ℕ.suc n | d | c = (-[1+ n ]  ÷ ℕ.suc d) {fromWitness (λ {i} → c)}

-- reciprocal: requires a proof that the numerator is not zero

ℚR : (p : ℚ) → {n≢0 : False (∣ ℚ.numerator p ∣ ℕ≟ 0)} → ℚ
ℚR p {n≢0} with ℚ.numerator p | ℚ.denominator-1 p | toWitness (ℚ.isCoprime p)
ℚR p {()} | + 0 | d | c 
... | + (ℕ.suc n) | d | c = 
  ((S.+ ◃ ℕ.suc d) ÷ ℕ.suc n) 
  {fromWitness (λ {i} → 
     sCoprime {S.+} {ℕ.suc d} {ℕ.suc n} (symCoprime c))} 
... | -[1+ n ] | d | c = 
  ((S.- ◃ ℕ.suc d) ÷ ℕ.suc n) 
  {fromWitness (λ {i} → 
     sCoprime {S.-} {ℕ.suc d} {ℕ.suc n} (symCoprime c))} 

-- multiplication 

helper* : (n₁ : ℤ) → (d₁ : ℕ) → (n₂ : ℤ) → (d₂ : ℕ) → 
          {n≢0 : False (∣ n₁ ℤ* n₂ ∣ ℕ≟ 0)} → 
          {d≢0 : False (d₁ ℕ* d₂ ℕ≟ 0)} → 
          ℚ
helper* n₁ d₁ n₂ d₂ {n≢0} {d≢0} = 
  let n = n₁ ℤ* n₂
      d = d₁ ℕ* d₂
      (g , G , g≢0) = gcdz ∣ n ∣ d {n≢0}
      (nn , nd , nc , nd≢0) = normalize {∣ n ∣} {d} {g} {d≢0} {g≢0} G
  in ((sign n ◃ nn) ÷ nd) {fromWitness (λ {i} → sCoprime nc)} {nd≢0} 

_ℚ*_ : ℚ → ℚ → ℚ
p₁ ℚ* p₂ with ℚ.numerator p₁ | ℚ.numerator p₂
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

helper+ : (n : ℤ) → (d : ℕ) → {d≢0 : False (d ℕ≟ 0)} → ℚ
helper+ (+ 0) d {d≢0} = + 0 ÷ 1
helper+ (+ ℕ.suc n) d {d≢0} = 
  let (g , G , g≢0) = gcdz ∣ + ℕ.suc n ∣ d {tt}
      (nn , nd , nc , nd≢0) = normalize {∣ + ℕ.suc n ∣} {d} {g} {d≢0} {g≢0} G
  in ((S.+ ◃ nn) ÷ nd) {fromWitness (λ {i} → sCoprime nc)} {nd≢0}
helper+ -[1+ n ] d {d≢0} = 
  let (g , G , g≢0) = gcdz ∣ -[1+ n ] ∣ d {tt}
      (nn , nd , nc , nd≢0) = normalize {∣ -[1+ n ] ∣} {d} {g} {d≢0} {g≢0} G
  in ((S.- ◃ nn) ÷ nd) {fromWitness (λ {i} → sCoprime nc)} {nd≢0}

_ℚ+_ : ℚ → ℚ → ℚ
p₁ ℚ+ p₂ = 
  let n₁ = ℚ.numerator p₁
      d₁ = ℕ.suc (ℚ.denominator-1 p₁)
      n₂ = ℚ.numerator p₂
      d₂ = ℕ.suc (ℚ.denominator-1 p₂)
      n = (n₁ ℤ* + d₂) ℤ+ (n₂ ℤ* + d₁)
      d = d₁ ℕ* d₂
  in helper+ n d

-- subtraction and division

_ℚ-_ : ℚ → ℚ → ℚ
p₁ ℚ- p₂ = p₁ ℚ+ (ℚN p₂)

_ℚ/_ : (p₁ p₂ : ℚ) → {n≢0 : False (∣ ℚ.numerator p₂ ∣ ℕ≟ 0)} → ℚ
_ℚ/_ p₁ p₂ {pf} = p₁ ℚ* (ℚR p₂ {pf})

------------------------------------------------------------------------------
-- Testing

p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ : ℚ
p₀ = + 1 ÷ 2
p₁ = + 1 ÷ 3
p₂ = -[1+ 2 ] ÷ 4  -- -3/4
p₃ = + 3 ÷ 4
p₄ = + 1 ÷ 2
p₅ = + 1 ÷ 2
p₆ = + 1 ÷ 2
p₇ = + 1 ÷ 2
p₈ = + 1 ÷ 2
p₉ = + 1 ÷ 2

test₁ = ℚN p₂       -- 3/4
test₂ = ℚR p₂       -- -4/3
test₃ = p₀ ℚ+ p₀
test₄ = p₁ ℚ* p₂

------------------------------------------------------------------------------
