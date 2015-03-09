{-# OPTIONS --without-K #-}

module ConcretePermutation where

open import Level
open import Data.Nat using (ℕ;_+_)
-- open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; tabulate)
-- open import Data.Vec.Properties using (lookup∘tabulate; tabulate∘lookup; lookup-allFin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans;
    proof-irrelevance; subst; cong₂;
    module ≡-Reasoning)
open import Relation.Binary using (Setoid; module Setoid)
-- open import Data.Product using (_,′_; _×_)

open import VecOps -- and below, import from that
open F

-- open import Function using (_∘_; id)
-- open import RepresPerm
-- open import Equiv
-- open import Enumeration
-- open import Data.Product using (_,_; proj₁; proj₂)
open import EquivSetoid
open import SetoidUtils 
-- open import Function.Equality using (_⟶_; Π; _⟨$⟩_; _⇨_) renaming (_∘_ to _⊚_; id to id⊚)

-- open import FiniteFunctions

-- a concrete permutation has 4 components:
-- - the permutation
-- - its inverse
-- - and 2 proofs that it is indeed inverse
record CPerm (size : ℕ) : Set where
  constructor cp
  field
    π : Vec (Fin size) size
    πᵒ : Vec (Fin size) size
    αp : π ∘̂ πᵒ ≡ F.1C
    βp : πᵒ ∘̂ π ≡ F.1C

πᵒ≡ : ∀ {n} → (π₁ π₂ : CPerm n) → (CPerm.π π₁ ≡ CPerm.π π₂) → (CPerm.πᵒ π₁ ≡ CPerm.πᵒ π₂)
πᵒ≡ {n} (cp π πᵒ αp βp) (cp .π πᵒ₁ αp₁ βp₁) refl =
  begin (
    πᵒ                  ≡⟨ sym (∘̂-rid πᵒ) ⟩
    πᵒ ∘̂ F.1C       ≡⟨  cong (_∘̂_ πᵒ) (sym αp₁)  ⟩
    πᵒ ∘̂ (π ∘̂ πᵒ₁)      ≡⟨ ∘̂-assoc πᵒ π πᵒ₁ ⟩
    (πᵒ ∘̂ π) ∘̂ πᵒ₁      ≡⟨ cong (λ x → x ∘̂ πᵒ₁) βp ⟩
    F.1C ∘̂ πᵒ₁          ≡⟨ ∘̂-lid πᵒ₁ ⟩
    πᵒ₁ ∎)
  where open ≡-Reasoning

p≡ : ∀ {n} → {π₁ π₂ : CPerm n} → (CPerm.π π₁ ≡ CPerm.π π₂) → π₁ ≡ π₂
p≡ {n} {cp π πᵒ αp βp} {cp .π πᵒ₁ αp₁ βp₁} refl with πᵒ≡ (cp π πᵒ αp βp) (cp π πᵒ₁ αp₁ βp₁) refl
p≡ {n} {cp π πᵒ αp βp} {cp .π .πᵒ αp₁ βp₁} refl | refl with proof-irrelevance αp αp₁ | proof-irrelevance βp βp₁
p≡ {n} {cp π πᵒ αp βp} {cp .π .πᵒ .αp .βp} refl | refl | refl | refl = refl

idp : ∀ {n} → CPerm n
idp {n} = cp F.1C F.1C (∘̂-rid _) (∘̂-lid _)

symp : ∀ {n} → CPerm n → CPerm n
symp (cp p₁ p₂ α β) = cp p₂ p₁ β α

transp : ∀ {n} → CPerm n → CPerm n → CPerm n
transp {n} (cp π πᵒ αp βp) (cp π₁ πᵒ₁ αp₁ βp₁) = cp (π ∘̂ π₁) (πᵒ₁ ∘̂ πᵒ) pf₁ pf₂
  where
    open ≡-Reasoning
    pf₁ : (π ∘̂ π₁) ∘̂ (πᵒ₁ ∘̂ πᵒ) ≡ F.1C
    pf₁ = 
      begin (
        (π ∘̂ π₁) ∘̂ (πᵒ₁ ∘̂ πᵒ)      ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((π ∘̂ π₁) ∘̂ πᵒ₁) ∘̂ πᵒ      ≡⟨ cong (λ x → x ∘̂ πᵒ) (sym (∘̂-assoc _ _ _)) ⟩
        (π ∘̂ (π₁ ∘̂ πᵒ₁)) ∘̂ πᵒ      ≡⟨ cong (λ x → (π ∘̂ x) ∘̂ πᵒ) (αp₁) ⟩
        (π ∘̂ F.1C) ∘̂ πᵒ       ≡⟨ cong (λ x → x ∘̂ πᵒ) (∘̂-rid _) ⟩
        π ∘̂ πᵒ                     ≡⟨ αp ⟩
        F.1C ∎)
    pf₂ : (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁) ≡ F.1C
    pf₂ = 
      begin (
        (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁)     ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((πᵒ₁ ∘̂ πᵒ) ∘̂ π) ∘̂ π₁     ≡⟨ cong (λ x → x ∘̂ π₁) (sym (∘̂-assoc _ _ _)) ⟩
        (πᵒ₁ ∘̂ (πᵒ ∘̂ π)) ∘̂ π₁     ≡⟨ cong (λ x → (πᵒ₁ ∘̂ x) ∘̂ π₁) βp ⟩
        (πᵒ₁ ∘̂ F.1C) ∘̂ π₁     ≡⟨ cong (λ x → x ∘̂ π₁) (∘̂-rid _) ⟩
         πᵒ₁ ∘̂ π₁                 ≡⟨ βp₁ ⟩
        F.1C ∎)

-- zero permutation
0p : CPerm 0
0p = cp F.0C F.0C refl refl


_⊎p_ : ∀ {m n} → CPerm m → CPerm n → CPerm (m + n)
_⊎p_ {m} {n} π₀ π₁ = cp ((π π₀) ⊎c (π π₁)) ((πᵒ π₀) ⊎c (πᵒ π₁)) pf₁ pf₂
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
        1C {m} ⊎c 1C {n}
          ≡⟨ 1C⊎1C≡1C {m} ⟩
        1C ∎)
    pf₂ : (πᵒ π₀ ⊎c πᵒ π₁) ∘̂ (π π₀ ⊎c π π₁) ≡ 1C
    pf₂ = 
      begin (
        (πᵒ π₀ ⊎c πᵒ π₁) ∘̂ (π π₀ ⊎c π π₁)
          ≡⟨ ⊎c-distrib {p₁ = πᵒ π₀} ⟩
        (πᵒ π₀ ∘̂ π π₀) ⊎c (πᵒ π₁ ∘̂ π π₁)
          ≡⟨ cong₂ _⊎c_ (βp π₀) (βp π₁) ⟩
        1C {m} ⊎c 1C {n}
          ≡⟨ 1C⊎1C≡1C {m}⟩
         1C ∎ )

SCPerm : ℕ → Setoid zero zero
SCPerm n = ≡-Setoid (CPerm n)
