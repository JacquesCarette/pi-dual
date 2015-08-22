{-# OPTIONS --without-K #-}

module ConcretePermutation where

open import Level using (zero)

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; tabulate; allFin)
open import Data.Vec.Properties using (tabulate∘lookup; lookup-allFin)

open import Function using (_∘_)
open import Relation.Binary using (Setoid) 
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂;
        module ≡-Reasoning; proof-irrelevance; setoid)

--
open import FinVec using (_⊎c_; _×c_)
open import FinVecProperties 
  using (∘̂-assoc; ∘̂-lid; ∘̂-rid; ⊎c-distrib; 1C⊎1C≡1C;
        ×c-distrib; 1C×1C≡1C)
  
open import Proofs using (
  -- FiniteFunctions
       finext; 
  -- VectorLemmas
   _!!_; lookupassoc
   )

------------------------------------------------------------------------------
-- A concrete permutation has 4 components:
-- - the one-line notation for a permutation
-- - the one-line notation for the inverse permutation
-- - and 2 proofs that these are indeed inverses

-- One-line notation for permutations with identity and composition

FinVec : ℕ → ℕ → Set
FinVec m n = Vec (Fin m) n

1C : {n : ℕ} → FinVec n n
1C {n} = allFin n

_∘̂_ : {n₀ n₁ n₂ : ℕ} → Vec (Fin n₁) n₀ → Vec (Fin n₂) n₁ → Vec (Fin n₂) n₀
π₁ ∘̂ π₂ = tabulate (_!!_ π₂ ∘ _!!_ π₁)

-- Actual permutation

record CPerm (values : ℕ) (size : ℕ) : Set where
  constructor cp
  field
    π  : FinVec values size
    πᵒ : FinVec size values
    αp : π ∘̂ πᵒ ≡ 1C
    βp : πᵒ ∘̂ π ≡ 1C

-- Basic permutations and combinators on them

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
        (π ∘̂ π₁) ∘̂ (πᵒ₁ ∘̂ πᵒ)      ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((π ∘̂ π₁) ∘̂ πᵒ₁) ∘̂ πᵒ      ≡⟨ cong (λ x → x ∘̂ πᵒ) (sym (∘̂-assoc _ _ _)) ⟩
        (π ∘̂ (π₁ ∘̂ πᵒ₁)) ∘̂ πᵒ      ≡⟨ cong (λ x → (π ∘̂ x) ∘̂ πᵒ) (αp₁) ⟩
        (π ∘̂ 1C) ∘̂ πᵒ       ≡⟨ cong (λ x → x ∘̂ πᵒ) (∘̂-rid _) ⟩
        π ∘̂ πᵒ                     ≡⟨ αp ⟩
        1C ∎)        
    pf₂ : (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁) ≡ 1C
    pf₂ = 
      begin (
        (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁)     ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((πᵒ₁ ∘̂ πᵒ) ∘̂ π) ∘̂ π₁     ≡⟨ cong (λ x → x ∘̂ π₁) (sym (∘̂-assoc _ _ _)) ⟩
        (πᵒ₁ ∘̂ (πᵒ ∘̂ π)) ∘̂ π₁     ≡⟨ cong (λ x → (πᵒ₁ ∘̂ x) ∘̂ π₁) βp ⟩
        (πᵒ₁ ∘̂ 1C) ∘̂ π₁     ≡⟨ cong (λ x → x ∘̂ π₁) (∘̂-rid _) ⟩
         πᵒ₁ ∘̂ π₁                 ≡⟨ βp₁ ⟩
        1C ∎)
        
-- zero permutation

0p : CPerm 0 0
0p = idp {0}

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
        
------------------------------------------------------------------------------
-- We can compare concrete permutations for equality using _≡_
-- It is actually sufficient to compare just the forward π using _≡_

-- The set of permutations under _≡_

SCPerm : ℕ → ℕ → Setoid zero zero
SCPerm m n = setoid (CPerm m n)

-- This is just tabulate∘lookup, but it hides the details; should this
-- be called 'join' or 'flatten' ?

cauchyext : {m n : ℕ} (π : FinVec m n) → tabulate (_!!_ π) ≡ π
cauchyext π = tabulate∘lookup π

------------------------------------------------------------------------------

{- where should this go?  How should these be built?
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
-}
