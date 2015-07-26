{-# OPTIONS --without-K #-}

module ConcretePermutation where

import Level using (zero)

open import Data.Nat using (ℕ; _+_; _*_)

open import Algebra using (CommutativeSemiring)
open import Algebra.Structures using
  (IsSemigroup; IsCommutativeMonoid; IsCommutativeSemiring)

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

--

open import FinVec
  using (FinVec; 1C; _∘̂_; _⊎c_; _×c_; 
         unite+; uniti+;
         unite+r; uniti+r;
         assocl+; assocr+;
         swap+cauchy;
         unite*; uniti*;
         unite*r; uniti*r;
         assocl*; assocr*;
         swap⋆cauchy;
         dist*+; factor*+;
         distl*+; factorl*+;
         right-zero*l; right-zero*r)

open import FinVecProperties
  using (∘̂-assoc; ∘̂-lid; ∘̂-rid;
         1C⊎1C≡1C; 1C×1C≡1C; 1C₀⊎x≡x;
         ⊎c-distrib; ×c-distrib;
         unite+∘̂uniti+~id; uniti+∘̂unite+~id;
         unite+r∘̂uniti+r~id; uniti+r∘̂unite+r~id;
         assocl+∘̂assocr+~id; assocr+∘̂assocl+~id;
         swap+-inv;
         unite*∘̂uniti*~id; uniti*∘̂unite*~id;
         unite*r∘̂uniti*r~id; uniti*r∘̂unite*r~id;
         assocl*∘̂assocr*~id; assocr*∘̂assocl*~id;
         swap*-inv;
         dist*+∘̂factor*+~id; factor*+∘̂dist*+~id;
         distl*+∘̂factorl*+~id; factorl*+∘̂distl*+~id;
         right-zero*l∘̂right-zero*r~id; right-zero*r∘̂right-zero*l~id)

------------------------------------------------------------------------------
-- A concrete permutation has 4 components:
-- - the one-line notation for a permutation
-- - the one-line notation for the inverse permutation
-- - and 2 proofs that these are indeed inverses

record CPerm (values : ℕ) (size : ℕ) : Set where
  constructor cp
  field
    π  : FinVec values size
    πᵒ : FinVec size values
    αp : π ∘̂ πᵒ ≡ 1C
    βp : πᵒ ∘̂ π ≡ 1C

------------------------------------------------------------------------------
-- Now the goal is to prove that CPerm m n is a commutative semiring
-- (including symmetry now)

-- First it is an equivalence relation

idp : ∀ {n} → CPerm n n
idp {n} = cp 1C 1C (∘̂-rid _) (∘̂-lid _)

symp : ∀ {m n} → CPerm m n → CPerm n m
symp (cp p₁ p₂ α β) = cp p₂ p₁ β α

transp : ∀ {m₁ m₂ m₃} → CPerm m₂ m₁ → CPerm m₃ m₂ → CPerm m₃ m₁
transp {n} (cp π πᵒ αp βp) (cp π₁ πᵒ₁ αp₁ βp₁) = cp (π ∘̂ π₁) (πᵒ₁ ∘̂ πᵒ) pf₁ pf₂
  where
    open ≡-Reasoning
    pf₁ : (π ∘̂ π₁) ∘̂ (πᵒ₁ ∘̂ πᵒ) ≡ 1C
    pf₁ =
      begin (
        (π ∘̂ π₁) ∘̂ (πᵒ₁ ∘̂ πᵒ) ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((π ∘̂ π₁) ∘̂ πᵒ₁) ∘̂ πᵒ ≡⟨ cong (λ x → x ∘̂ πᵒ) (sym (∘̂-assoc _ _ _)) ⟩
        (π ∘̂ (π₁ ∘̂ πᵒ₁)) ∘̂ πᵒ ≡⟨ cong (λ x → (π ∘̂ x) ∘̂ πᵒ) (αp₁) ⟩
        (π ∘̂ 1C) ∘̂ πᵒ         ≡⟨ cong (λ x → x ∘̂ πᵒ) (∘̂-rid _) ⟩
        π ∘̂ πᵒ                ≡⟨ αp ⟩
        1C ∎)
    pf₂ : (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁) ≡ 1C
    pf₂ =
      begin (
        (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁) ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((πᵒ₁ ∘̂ πᵒ) ∘̂ π) ∘̂ π₁ ≡⟨ cong (λ x → x ∘̂ π₁) (sym (∘̂-assoc _ _ _)) ⟩
        (πᵒ₁ ∘̂ (πᵒ ∘̂ π)) ∘̂ π₁ ≡⟨ cong (λ x → (πᵒ₁ ∘̂ x) ∘̂ π₁) βp ⟩
        (πᵒ₁ ∘̂ 1C) ∘̂ π₁       ≡⟨ cong (λ x → x ∘̂ π₁) (∘̂-rid _) ⟩
         πᵒ₁ ∘̂ π₁             ≡⟨ βp₁ ⟩
        1C ∎)

-- units
-- zero permutation

0p : CPerm 0 0
0p = idp {0}

-- Additive monoid

_⊎p_ : ∀ {m₁ m₂ n₁ n₂} → CPerm m₁ m₂ → CPerm n₁ n₂ → CPerm (m₁ + n₁) (m₂ + n₂)
_⊎p_ {m₁} {m₂} {n₁} {n₂} π₀ π₁ =
  cp ((π π₀) ⊎c (π π₁)) ((πᵒ π₀) ⊎c (πᵒ π₁)) pf₁ pf₂
  where
    open CPerm
    open ≡-Reasoning
    pf₁ : (π π₀ ⊎c π π₁) ∘̂ (πᵒ π₀ ⊎c πᵒ π₁) ≡ 1C
    pf₁ =
      begin (
        (π π₀ ⊎c π π₁) ∘̂ (πᵒ π₀ ⊎c πᵒ π₁)
          ≡⟨ ⊎c-distrib {p₁ = π π₀} ⟩
       (π π₀ ∘̂ πᵒ π₀) ⊎c (π π₁ ∘̂ πᵒ π₁)
          ≡⟨ cong₂ _⊎c_ (αp π₀) (αp π₁) ⟩
        1C {m₂} ⊎c 1C {n₂}
          ≡⟨ 1C⊎1C≡1C {m₂} ⟩
        1C ∎)
    pf₂ : (πᵒ π₀ ⊎c πᵒ π₁) ∘̂ (π π₀ ⊎c π π₁) ≡ 1C
    pf₂ =
      begin (
        (πᵒ π₀ ⊎c πᵒ π₁) ∘̂ (π π₀ ⊎c π π₁)
          ≡⟨ ⊎c-distrib {p₁ = πᵒ π₀} ⟩
        (πᵒ π₀ ∘̂ π π₀) ⊎c (πᵒ π₁ ∘̂ π π₁)
          ≡⟨ cong₂ _⊎c_ (βp π₀) (βp π₁) ⟩
        1C {m₁} ⊎c 1C {n₁}
          ≡⟨ 1C⊎1C≡1C {m₁} ⟩
        1C ∎ )

-- units

unite+p : {m : ℕ} → CPerm m (0 + m)
unite+p {m} =
  cp (unite+ {m}) (uniti+ {m}) (unite+∘̂uniti+~id {m}) (uniti+∘̂unite+~id {m})

uniti+p : {m : ℕ} → CPerm (0 + m) m
uniti+p {m} = symp (unite+p {m})

unite+rp : {m : ℕ} → CPerm m (m + 0)
unite+rp {m} =
  cp (unite+r {m}) (uniti+r) (unite+r∘̂uniti+r~id) (uniti+r∘̂unite+r~id)

uniti+rp : {m : ℕ} → CPerm (m + 0) m
uniti+rp {m} = symp (unite+rp {m})

-- commutativity

swap+p : {m n : ℕ} → CPerm (n + m) (m + n)
swap+p {m} {n} =
  cp (swap+cauchy m n) (swap+cauchy n m) (swap+-inv {m}) (swap+-inv {n})

-- associativity

assocl+p : {m n o : ℕ} → CPerm ((m + n) + o) (m + (n + o))
assocl+p {m} =
  cp
    (assocl+ {m}) (assocr+ {m})
    (assocl+∘̂assocr+~id {m}) (assocr+∘̂assocl+~id {m})

assocr+p : {m n o : ℕ} → CPerm (m + (n + o)) ((m + n) + o)
assocr+p {m} = symp (assocl+p {m})

-- Multiplicative monoid

_×p_ : ∀ {m₁ m₂ n₁ n₂} → CPerm m₁ m₂ → CPerm n₁ n₂ → CPerm (m₁ * n₁) (m₂ * n₂)
_×p_ {m₁} {m₂} {n₁} {n₂} π₀ π₁ =
  cp ((π π₀) ×c (π π₁)) ((πᵒ π₀) ×c (πᵒ π₁)) pf₁ pf₂
  where
    open CPerm
    open ≡-Reasoning
    pf₁ : (π π₀ ×c π π₁) ∘̂ (πᵒ π₀ ×c πᵒ π₁) ≡ 1C
    pf₁ = 
      begin (
        (π π₀ ×c π π₁) ∘̂ (πᵒ π₀ ×c πᵒ π₁) ≡⟨ ×c-distrib {p₁ = π π₀} ⟩
        (π π₀ ∘̂ πᵒ π₀) ×c (π π₁ ∘̂ πᵒ π₁)  ≡⟨ cong₂ _×c_ (αp π₀) (αp π₁) ⟩
        1C ×c 1C                          ≡⟨ 1C×1C≡1C ⟩
        1C ∎)
    pf₂ : (πᵒ π₀ ×c πᵒ π₁) ∘̂ (π π₀ ×c π π₁) ≡ 1C
    pf₂ = 
      begin (
        (πᵒ π₀ ×c πᵒ π₁) ∘̂ (π π₀ ×c π π₁) ≡⟨ ×c-distrib {p₁ = πᵒ π₀} ⟩
        (πᵒ π₀ ∘̂ π π₀) ×c (πᵒ π₁ ∘̂ π π₁) ≡⟨ cong₂ _×c_ (βp π₀) (βp π₁) ⟩
        1C ×c 1C                          ≡⟨ 1C×1C≡1C ⟩
        1C ∎)

-- units

unite*p : {m : ℕ} → CPerm m (1 * m)
unite*p {m} =
  cp (unite* {m}) (uniti* {m}) (unite*∘̂uniti*~id {m}) (uniti*∘̂unite*~id {m})

uniti*p : {m : ℕ} → CPerm (1 * m) m
uniti*p {m} = symp (unite*p {m})

unite*rp : {m : ℕ} → CPerm m (m * 1)
unite*rp {m} =
  cp
    (unite*r {m}) (uniti*r {m})
    (unite*r∘̂uniti*r~id {m}) (uniti*r∘̂unite*r~id {m})

uniti*rp : {m : ℕ} → CPerm (m * 1) m
uniti*rp {m} = symp (unite*rp {m})

-- commutativity

swap*p : {m n : ℕ} → CPerm (n * m) (m * n)
swap*p {m} {n} =
  cp (swap⋆cauchy m n) (swap⋆cauchy n m) (swap*-inv {m}) (swap*-inv {n})

-- associativity

assocl*p : {m n o : ℕ} → CPerm ((m * n) * o) (m * (n * o))
assocl*p {m} =
  cp
    (assocl* {m}) (assocr* {m})
    (assocl*∘̂assocr*~id {m}) (assocr*∘̂assocl*~id {m})

assocr*p : {m n o : ℕ} → CPerm (m * (n * o)) ((m * n) * o)
assocr*p {m} = symp (assocl*p {m})

-- Distributivity

-- right-zero absorbing permutation

0pr : ∀ {n} → CPerm 0 (n * 0)
0pr {n} =
  cp
    (right-zero*l {n}) (right-zero*r {n}) 
    (right-zero*l∘̂right-zero*r~id {n}) (right-zero*r∘̂right-zero*l~id {n})

-- and its symmetric version

0pl : ∀ {n} → CPerm (n * 0) 0
0pl {n} = symp (0pr {n})

distp : {m n o : ℕ} → CPerm (m * o + n * o) ((m + n) * o)
distp {m} {n} {o} =
  cp
    (dist*+ {m}) (factor*+ {m})
    (dist*+∘̂factor*+~id {m}) (factor*+∘̂dist*+~id {m})

factorp : {m n o : ℕ} → CPerm ((m + n) * o) (m * o + n * o)
factorp {m} = symp (distp {m})

distlp : {m n o : ℕ} → CPerm (m * n + m * o) (m * (n + o))
distlp {m} {n} {o} =
  cp
    (distl*+ {m}) (factorl*+ {m})
    (distl*+∘̂factorl*+~id {m}) (factorl*+∘̂distl*+~id {m})

factorlp : {m n o : ℕ} → CPerm (m * (n + o)) (m * n + m * o)
factorlp {m} = symp (distlp {m})

------------------------------------------------------------------------------
-- Commutative semiring structure 

cpermIsEquiv : IsEquivalence {Level.zero} {Level.zero} {ℕ} CPerm
cpermIsEquiv = record {
  refl = idp; 
  sym = symp; 
  trans = λ p q → transp q p
  }

cpermPlusIsSG : IsSemigroup {Level.zero} {Level.zero} {ℕ} CPerm _+_
cpermPlusIsSG = record {
  isEquivalence = cpermIsEquiv ; 
  assoc = λ m n o → assocl+p {m} {n} {o} ; 
  ∙-cong = _⊎p_ 
  }

cpermTimesIsSG : IsSemigroup {Level.zero} {Level.zero} {ℕ} CPerm _*_
cpermTimesIsSG = record {
  isEquivalence = cpermIsEquiv ;
  assoc = λ m n o → assocl*p {m} {n} {o} ;
  ∙-cong = _×p_
  }

cpermPlusIsCM : IsCommutativeMonoid CPerm _+_ 0
cpermPlusIsCM = record {
  isSemigroup = cpermPlusIsSG ;
  identityˡ = λ m → idp ;
  comm = λ m n → swap+p {n} {m}
  }

cpermTimesIsCM : IsCommutativeMonoid CPerm _*_ 1
cpermTimesIsCM = record {
  isSemigroup = cpermTimesIsSG ;
  identityˡ = λ m → uniti*p {m} ;
  comm = λ m n → swap*p {n} {m}
  }

cpermIsCSR : IsCommutativeSemiring CPerm _+_ _*_ 0 1
cpermIsCSR = record {
  +-isCommutativeMonoid = cpermPlusIsCM ;
  *-isCommutativeMonoid = cpermTimesIsCM ; 
  distribʳ = λ o m n → factorp {m} {n} {o} ; 
  zeroˡ = λ m → 0p
  }

cpermCSR : CommutativeSemiring Level.zero Level.zero
cpermCSR = record {
  Carrier = ℕ ;
  _≈_ = CPerm;
  _+_ = _+_ ;
  _*_ = _*_ ;
  0# = 0 ;
  1# = 1 ;
  isCommutativeSemiring = cpermIsCSR
  }

------------------------------------------------------------------------------
