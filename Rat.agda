module Rat where
           
open import Data.Bool
open import Data.Unit
import Data.Sign as S
open import Data.Nat renaming (_+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≟_ to _ℕ≟_)
open import Data.Nat.Coprimality renaming (sym to symCoprime)
open import Data.Nat.GCD
open import Data.Nat.Divisibility
open import Data.Integer renaming (_+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _≟_ to _ℤ≟_)
open import Data.Integer.Properties
open import Data.Rational
open import Data.Product
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function
open import Algebra
import Data.Nat.Properties as NatProp
open NatProp.SemiringSolver
private module CS = CommutativeSemiring NatProp.commutativeSemiring
open ≡-Reasoning

------------------------------------------------------------------------------
-- Some lemmas to help with operations on rationals

-- normalize takes two natural numbers, say 6 and 21 and their gcd 3, and
-- returns them normalized as 2 and 7 and a proof that they are coprime

normalize : ∀ {m n g} → {g≢0 : False (g ℕ≟ 0)} → 
            GCD m n g → Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] Coprime p q
normalize {m} {n} {0} {()}
normalize {m} {n} {ℕ.suc g} {_} G with Bézout.identity G 
normalize {m} {n} {ℕ.suc g} {_} (GCD.is (divides p m≡pg' , divides q n≡qg') _)
  | Bézout.+- x y eq = 
    (p , q , Bézout-coprime {p} {q} {g} (Bézout.+- x y
               (begin 
                 ℕ.suc g ℕ+ y ℕ* (q ℕ* ℕ.suc g) 
               ≡⟨ cong (λ h → ℕ.suc g ℕ+ y ℕ* h) (sym n≡qg') ⟩
                 ℕ.suc g ℕ+ y ℕ* n
               ≡⟨ eq ⟩
                 x ℕ* m
               ≡⟨ cong (λ h → x ℕ* h) m≡pg' ⟩
                 x ℕ* (p ℕ* ℕ.suc g) ∎)))
normalize {m} {n} {ℕ.suc g} {_} (GCD.is (divides p m≡pg' , divides q n≡qg') _) 
  | Bézout.-+ x y eq = 
    (p , q , Bézout-coprime {p} {q} {g} (Bézout.-+ x y
               (begin
                 ℕ.suc g ℕ+ x ℕ* (p ℕ* ℕ.suc g) 
               ≡⟨ cong (λ h → ℕ.suc g ℕ+ x ℕ* h) (sym m≡pg') ⟩ 
                 ℕ.suc g ℕ+ x ℕ* m
               ≡⟨ eq ⟩ 
                 y ℕ* n
               ≡⟨ cong (λ h → y ℕ* h) n≡qg' ⟩ 
                 y ℕ* (q ℕ* ℕ.suc g) ∎)))

-- multiplying non-zero integers gives non-zero result

nzℤ* : (m n : ℤ) → {m≢0 : False (m ℤ≟ + 0)} → {n≢0 : False (n ℤ≟ + 0)} → 
       False (m ℤ* n ℤ≟ + 0)
nzℤ* (+ 0)       n           {()} {_}
nzℤ* m           (+ 0)       {_}  {()}
nzℤ* (+ ℕ.suc m) (+ ℕ.suc n) {_}  {_} = tt
nzℤ* (+ ℕ.suc m) -[1+ n ]    {_}  {_} = tt 
nzℤ* -[1+ m ]    (+ ℕ.suc n) {_}  {_} = tt
nzℤ* -[1+ m ]    -[1+ n ]    {_}  {_} = tt

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
ℚ- : ℚ → ℚ
ℚ- p with ℚ.numerator p | ℚ.denominator-1 p | toWitness (ℚ.isCoprime p)
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
          {n≢0 : False (∣ n₁ ℤ* n₂ ∣ ℕ≟ 0)} → ℚ
helper* n₁ d₁ n₂ d₂ {n≢0} = 
  let n = n₁ ℤ* n₂
      d = d₁ ℕ* d₂
      (g , G , g≢0) = gcdz ∣ n ∣ d {n≢0}
      (nn , nd , nc) = normalize {∣ n ∣} {d} {g} {g≢0} G
      nd≢0 : False (nd ℕ≟ 0)
      nd≢0 = {!!} 
  in ((sign n ◃ nn) ÷ nd) {fromWitness (λ {i} → sCoprime nc)} {nd≢0} 

_ℚ*_ : ℚ → ℚ → ℚ
p₁ ℚ* p₂ with ℚ.numerator p₁ | ℚ.numerator p₂
... | + 0  | _    = + 0 ÷ 1
... | _    | + 0  = + 0 ÷ 1
... | + ℕ.suc n₁ | + ℕ.suc n₂ = 
  helper* (+ ℕ.suc n₁) (ℕ.suc (ℚ.denominator-1 p₁))
          (+ ℕ.suc n₂) (ℕ.suc (ℚ.denominator-1 p₂))
          {nzℤ* (+ ℕ.suc n₁) (+ ℕ.suc n₂)}
... | + ℕ.suc n₁ | -[1+ n₂ ] = 
  helper* (+ ℕ.suc n₁) (ℕ.suc (ℚ.denominator-1 p₁))
          -[1+ n₂ ] (ℕ.suc (ℚ.denominator-1 p₂))
          {nzℤ* (+ ℕ.suc n₁) -[1+ n₂ ]}
... | -[1+ n₁ ] | + ℕ.suc n₂ = 
  helper* -[1+ n₁ ] (ℕ.suc (ℚ.denominator-1 p₁))
          (+ ℕ.suc n₂) (ℕ.suc (ℚ.denominator-1 p₂))
          {nzℤ* -[1+ n₁ ] (+ ℕ.suc n₂)}
... | -[1+ n₁ ] | -[1+ n₂ ] = 
  helper* -[1+ n₁ ] (ℕ.suc (ℚ.denominator-1 p₁))
          -[1+ n₂ ] (ℕ.suc (ℚ.denominator-1 p₂))
          {nzℤ* -[1+ n₁ ] -[1+ n₂ ]}

-- addition

helper+ : (n : ℤ) → (d : ℕ) → ℚ
helper+ (+ 0) d = + 0 ÷ 1
helper+ (+ ℕ.suc n) d = 
  let (g , G , g≢0) = gcdz ∣ + ℕ.suc n ∣ d {tt}
      (nn , nd , nc) = normalize {∣ + ℕ.suc n ∣} {d} {g} {g≢0} G
      nd≢0 : False (nd ℕ≟ 0)
      nd≢0 = {!!} 
  in ((S.+ ◃ nn) ÷ nd) {fromWitness (λ {i} → sCoprime nc)} {nd≢0}
helper+ -[1+ n ] d = 
  let (g , G , g≢0) = gcdz ∣ -[1+ n ] ∣ d {tt}
      (nn , nd , nc) = normalize {∣ -[1+ n ] ∣} {d} {g} {g≢0} G
      nd≢0 : False (nd ℕ≟ 0)
      nd≢0 = {!!} 
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

test₁ = ℚ- p₂       -- 3/4
test₂ = ℚR p₂       -- -4/3

------------------------------------------------------------------------------
{--
-- multiplying two non-zero numbers yields a non-zero number

-- if i|m then i|nm

div* : ∀ {i m n} → (i ∣ m) → (i ∣ n ℕ* m) 
div* {i} {m} {n} (divides q m≡qi) = 
  divides (n ℕ* q) (begin
    n ℕ* m 
  ≡⟨ cong (_ℕ*_ n) m≡qi ⟩ 
    n ℕ* (q ℕ* i) 
  ≡⟨ solve 3 (λ n q i → n :* (q :* i) := (n :* q) :* i) refl n q i ⟩ 
  -- in this case could have written  ≡⟨ sym (CS.*-assoc n q i) ⟩ 
    (n ℕ* q) ℕ* i ∎)

-- absolute value commutes with multiplication

divSign : ∀ {i m k} → (i ∣ ∣ m ℤ* k ∣) → (i ∣ ∣ m ∣ ℕ* ∣ k ∣)
divSign {i} {m} {k} (divides p mk≡pi) =  
  divides p (begin
    ∣ m ∣ ℕ* ∣ k ∣ 
  ≡⟨ sym (abs-*-commute m k) ⟩
    ∣ m ℤ* k ∣ 
  ≡⟨ mk≡pi ⟩ 
    p ℕ* i ∎) 

-- if i|kl then i|lk

divComm : ∀ {i k l} → (i ∣ k ℕ* l) → (i ∣ l ℕ* k)
divComm {i} {k} {l} (divides p kl≡pi) = 
  divides p (begin 
    l ℕ* k
  ≡⟨ CS.*-comm l k ⟩ 
    k ℕ* l
  ≡⟨ kl≡pi ⟩ 
    p ℕ* i ∎)

-- if i|mk and i|nl and Coprime m l then i|kn
-- if i|mk and i|nl and Coprime m n then i|kl 

coprimeL* : ∀ {m n k l i} →
    Coprime m l → (i ∣ m ℕ* k) → (i ∣ n ℕ* l) → (i ∣ k ℕ* n) 
coprimeL* {m} {n} {k} {l} {i} c (divides p mk≡pi) (divides q nl≡qi) =
  let i|mkn = divides (p ℕ* n) (begin 
                m ℕ* (k ℕ* n)
              ≡⟨ solve 3 (λ m k n → m :* (k :* n) := (m :* k) :* n) refl m k n ⟩ 
                (m ℕ* k) ℕ* n
              ≡⟨ cong (λ h → h ℕ* n) mk≡pi ⟩ 
                (p ℕ* i) ℕ* n
              ≡⟨ solve 3 (λ p i n → (p :* i) :* n := (p :* n) :* i) refl p i n ⟩ 
                (p ℕ* n) ℕ* i ∎)
      i|lkn = divides (q ℕ* k) (begin
                l ℕ* (k ℕ* n)
              ≡⟨ solve 3 (λ n k l → l :* (k :* n) := (n :* l) :* k) refl n k l ⟩
                (n ℕ* l) ℕ* k
              ≡⟨ cong (λ h → h ℕ* k) nl≡qi ⟩ 
                (q ℕ* i) ℕ* k
              ≡⟨ solve 3 (λ q i k → (q :* i) :* k := (q :* k) :* i) refl q i k ⟩
                (q ℕ* k) ℕ* i ∎)
  in coprime-factors c (i|mkn , i|lkn)

coprimeR* : ∀ {m n k l i} →
    Coprime m n → (i ∣ m ℕ* k) → (i ∣ n ℕ* l) → (i ∣ k ℕ* l) 
coprimeR* {m} {n} {k} {l} {i} c (divides p mk≡pi) (divides q nl≡qi) =
  let i|mkl = divides (p ℕ* l) (begin 
                m ℕ* (k ℕ* l)
              ≡⟨ solve 3 (λ m k l → m :* (k :* l) := (m :* k) :* l) refl m k l ⟩ 
                (m ℕ* k) ℕ* l
              ≡⟨ cong (λ h → h ℕ* l) mk≡pi ⟩ 
                (p ℕ* i) ℕ* l
              ≡⟨ solve 3 (λ p i l → (p :* i) :* l := (p :* l) :* i) refl p i l ⟩ 
                (p ℕ* l) ℕ* i ∎)
      i|nkl = divides (q ℕ* k) (begin
                n ℕ* (k ℕ* l)
              ≡⟨ solve 3 (λ n k l → n :* (k :* l) := (n :* l) :* k) refl n k l ⟩
                (n ℕ* l) ℕ* k
              ≡⟨ cong (λ h → h ℕ* k) nl≡qi ⟩ 
                (q ℕ* i) ℕ* k
              ≡⟨ solve 3 (λ q i k → (q :* i) :* k := (q :* k) :* i) refl q i k ⟩
                (q ℕ* k) ℕ* i ∎)
  in coprime-factors c (i|mkl , i|nkl)

_ℚ*_ : ℚ → ℚ → ℚ
p₁ ℚ* p₂ = 
  let num₁ = P₁.numerator
      den₁ = ℕ.suc P₁.denominator-1
      c₁ = toWitness P₁.isCoprime
      num₂ = P₂.numerator
      den₂ = ℕ.suc P₂.denominator-1
      c₂ = toWitness P₂.isCoprime
      G₁₂ = gcd ∣ num₁ ∣ den₂ 
      G₂₁ = gcd ∣ num₂ ∣ den₁
  in helper num₁ den₁ c₁ num₂ den₂ c₂ G₁₂ G₂₁ tt tt

  where 

    module P₁ = ℚ p₁; module P₂ = ℚ p₂

    helper2 : ∀ {m n k l} →
      Coprime ∣ m ∣ n → Coprime ∣ k ∣ l → Coprime ∣ m ∣ l → Coprime ∣ k ∣ n → 
      Coprime ∣ m ℤ* k ∣ (n ℕ* l)
    helper2 {m} {n} {k} {l} c₁ c₂ c₁₂ c₂₁ {i} (i|mk , i|nl) = 
      let i|kl = coprimeR* c₁ (divSign {i} {m} {k} i|mk) i|nl
          i|k  = coprime-factors c₁₂ 
                   (divSign {i} {m} {k} i|mk , divComm {i} {∣ k ∣} {l} i|kl)
          i|kn = coprimeL* {∣ m ∣} {n} {∣ k ∣} {l} {i} 
                   c₁₂ (divSign {i} {m} {k} i|mk) i|nl
          i|n  = coprime-factors c₂ (i|kn , divComm {i} {n} {l} i|nl)
      in c₂₁ (i|k , i|n)

    helper : (num₁ : ℤ) (den₁ : ℕ) (c₁ : Coprime ∣ num₁ ∣ den₁)
             (num₂ : ℤ) (den₂ : ℕ) (c₂ : Coprime ∣ num₂ ∣ den₂)
             (G₁₂ : ∃ (λ g₁₂ → GCD ∣ num₁ ∣ den₂ g₁₂))
             (G₂₁ : ∃ (λ g₂₁ → GCD ∣ num₂ ∣ den₁ g₂₁)) 
             (den₁≢0 : False (den₁ ℕ≟ 0)) (den₂≢0 : False (den₂ ℕ≟ 0)) → 
             ℚ
    helper num₁ den₁ c₁ num₂ den₂ c₂ (1 , gcd₁₂) (1 , gcd₂₁) den₁≢0 den₂≢0 = 
      let c₁₂ = gcd-coprime gcd₁₂ -- Coprime |num₁| den₂
          c₂₁ = gcd-coprime gcd₂₁ -- Coprime |num₂| den₁
      in ((num₁ ℤ* num₂) ÷ (den₁ ℕ* den₂))
         {fromWitness (λ {i} → helper2 {num₁} {den₁} {num₂} {den₂} 
                                 c₁ c₂ c₁₂ c₂₁)}
         {nz* den₁ den₂ den₁≢0 den₂≢0}
    helper num₁ den₁ c₁ num₂ den₂ c₂ (g₁₂ , gcd₁₂) (g₂₁ , gcd₂₁) den₁≢0 den₂≢0 =
      let (num₁' , den₂' , num₁'|num₁ , den₂'|den₂ , c₁₂') = 
            normalize {!!} gcd₁₂
          (num₂' , den₁' , num₂'|num₂ , den₁'|den₁ , c₂₁') = 
            normalize {!!} gcd₂₁
      in {!!} 

nzℕ* : (m n : ℕ) → {m≢0 : False (m ℕ≟ 0)} → {n≢0 : False (n ℕ≟ 0)} → 
       False (m ℕ* n ℕ≟ 0)
nzℕ* m 0 {_} {()}
nzℕ* 0 n {()} {_}
nzℕ* (ℕ.suc m) (ℕ.suc n) {_} {_} = tt 

--}
