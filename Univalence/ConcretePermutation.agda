{-# OPTIONS --without-K #-}

module ConcretePermutation where

open import Level using (zero)
open import Data.Nat using (ℕ;_+_;_*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans;
    proof-irrelevance; cong₂;
    module ≡-Reasoning)
open import Relation.Binary using (Setoid; module Setoid)

open import CauchyEquiv -- and below, import from that
open F

open import SetoidUtils using (≡-Setoid)

-- a concrete permutation has 4 components:
-- - the permutation
-- - its inverse
-- - and 2 proofs that it is indeed inverse
record CPerm (values : ℕ) (size : ℕ) : Set where
  constructor cp
  field
    π : Cauchy values size
    πᵒ : Cauchy size values
    αp : π ∘̂ πᵒ ≡ F.1C
    βp : πᵒ ∘̂ π ≡ F.1C

πᵒ≡ : ∀ {m n} → (π₁ π₂ : CPerm m n) → (CPerm.π π₁ ≡ CPerm.π π₂) → (CPerm.πᵒ π₁ ≡ CPerm.πᵒ π₂)
πᵒ≡ {n} (cp π πᵒ αp βp) (cp .π πᵒ₁ αp₁ βp₁) refl =
  begin (
    πᵒ                  ≡⟨ sym (∘̂-rid πᵒ) ⟩
    πᵒ ∘̂ 1C          ≡⟨  cong (_∘̂_ πᵒ) (sym αp₁)  ⟩
    πᵒ ∘̂ (π ∘̂ πᵒ₁)      ≡⟨ ∘̂-assoc πᵒ π πᵒ₁ ⟩
    (πᵒ ∘̂ π) ∘̂ πᵒ₁      ≡⟨ cong (λ x → x ∘̂ πᵒ₁) βp ⟩
    1C ∘̂ πᵒ₁            ≡⟨ ∘̂-lid πᵒ₁ ⟩
    πᵒ₁ ∎)
  where open ≡-Reasoning

p≡ : ∀ {m n} → {π₁ π₂ : CPerm m n} → (CPerm.π π₁ ≡ CPerm.π π₂) → π₁ ≡ π₂
p≡ {m} {n} {cp π πᵒ αp βp} {cp .π πᵒ₁ αp₁ βp₁} refl with πᵒ≡ (cp π πᵒ αp βp) (cp π πᵒ₁ αp₁ βp₁) refl
p≡ {m} {n} {cp π πᵒ αp βp} {cp .π .πᵒ αp₁ βp₁} refl | refl with proof-irrelevance αp αp₁ | proof-irrelevance βp βp₁
p≡ {m} {n} {cp π πᵒ αp βp} {cp .π .πᵒ .αp .βp} refl | refl | refl | refl = refl

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
        (π ∘̂ F.1C) ∘̂ πᵒ       ≡⟨ cong (λ x → x ∘̂ πᵒ) (∘̂-rid _) ⟩
        π ∘̂ πᵒ                     ≡⟨ αp ⟩
        F.1C ∎)
    pf₂ : (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁) ≡ 1C
    pf₂ =
      begin (
        (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁)     ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((πᵒ₁ ∘̂ πᵒ) ∘̂ π) ∘̂ π₁     ≡⟨ cong (λ x → x ∘̂ π₁) (sym (∘̂-assoc _ _ _)) ⟩
        (πᵒ₁ ∘̂ (πᵒ ∘̂ π)) ∘̂ π₁     ≡⟨ cong (λ x → (πᵒ₁ ∘̂ x) ∘̂ π₁) βp ⟩
        (πᵒ₁ ∘̂ F.1C) ∘̂ π₁     ≡⟨ cong (λ x → x ∘̂ π₁) (∘̂-rid _) ⟩
         πᵒ₁ ∘̂ π₁                 ≡⟨ βp₁ ⟩
        F.1C ∎)

-- zero permutation
0p : CPerm 0 0
0p = cp F.0C F.0C refl refl

_⊎p_ : ∀ {m₁ m₂ n₁ n₂} → CPerm m₁ m₂ → CPerm n₁ n₂ → CPerm (m₁ + n₁) (m₂ + n₂)
_⊎p_ {m₁} {m₂} {n₁} {n₂} π₀ π₁ = cp ((π π₀) ⊎c (π π₁)) ((πᵒ π₀) ⊎c (πᵒ π₁)) pf₁ pf₂
  where
    open CPerm
    open F
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

assocl+p : {m n o : ℕ} → CPerm ((m + n) + o) (m + (n + o))
assocl+p {m} = cp (assocl+ {m}) (assocr+ {m})  (assocl+∘̂assocr+~id {m}) (assocr+∘̂assocl+~id {m})

assocr+p : {m n o : ℕ} → CPerm (m + (n + o)) ((m + n) + o)
assocr+p {m} = symp (assocl+p {m})

swap+p : {m n : ℕ} → CPerm (n + m) (m + n)
swap+p {m} {n} = cp (swap+cauchy m n) (swap+cauchy n m) (swap+-inv {m}) (swap+-inv {n})

unite*p : {m : ℕ} → CPerm m (1 * m)
unite*p {m} = cp (unite* {m}) (uniti* {m}) (unite*∘̂uniti*~id {m}) (uniti*∘̂unite*~id {m})

uniti*p : {m : ℕ} → CPerm (1 * m) m
uniti*p {m} = symp (unite*p {m})

swap*p : {m n : ℕ} → CPerm (n * m) (m * n)
swap*p {m} {n} = cp (swap⋆cauchy m n) (swap⋆cauchy n m) (swap*-inv {m}) (swap*-inv {n})

assocl*p : {m n o : ℕ} → CPerm ((m * n) * o) (m * (n * o))
assocl*p {m} = cp (assocl* {m}) (assocr* {m})  (assocl*∘̂assocr*~id {m}) (assocr*∘̂assocl*~id {m})

assocr*p : {m n o : ℕ} → CPerm (m * (n * o)) ((m * n) * o)
assocr*p {m} = symp (assocl*p {m})

_×p_ : ∀ {m₁ m₂ n₁ n₂} → CPerm m₁ m₂ → CPerm n₁ n₂ → CPerm (m₁ * n₁) (m₂ * n₂)
_×p_ {m₁} {m₂} {n₁} {n₂} π₀ π₁ = cp ((π π₀) ×c (π π₁)) ((πᵒ π₀) ×c (πᵒ π₁)) pf₁ pf₂
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

distp : {m n o : ℕ} → CPerm (m * o + n * o) ((m + n) * o)
distp {m} {n} {o} = cp (dist*+ {m}) (factor*+ {m}) (dist*+∘̂factor*+~id {m}) (factor*+∘̂dist*+~id {m})

factorp : {m n o : ℕ} → CPerm ((m + n) * o) (m * o + n * o)
factorp {m} = symp (distp {m})

------------------------------------------------------------------------------------------------------
ridp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → transp p idp ≡ p
ridp {p = p} = p≡ (∘̂-rid (CPerm.π p))

SCPerm : ℕ → ℕ → Setoid zero zero
SCPerm m n = ≡-Setoid (CPerm m n)
