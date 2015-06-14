{-# OPTIONS --without-K #-}

module ConcretePermutation where

open import Level using (zero)
open import Data.Nat using (ℕ;_+_;_*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans;
    proof-irrelevance; cong₂;
    module ≡-Reasoning)
open import Relation.Binary using (Setoid; module Setoid)

open import FinVec -- and below, import from that
open F

open import SetoidUtils using (≡-Setoid)

-- a concrete permutation has 4 components:
-- - the permutation
-- - its inverse
-- - and 2 proofs that it is indeed inverse
record CPerm (values : ℕ) (size : ℕ) : Set where
  constructor cp
  field
    π : FinVec values size
    πᵒ : FinVec size values
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
0p = cp F.0C F.0C F.0C∘̂0C≡1C F.0C∘̂0C≡1C

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

unite+p : {m : ℕ} → CPerm m (m + 0)
unite+p {m} = cp (unite+ {m}) (uniti+ {m}) (unite+∘̂uniti+~id {m}) (uniti+∘̂unite+~id {m})

uniti+p : {m : ℕ} → CPerm (m + 0) m
uniti+p {m} = symp (unite+p {m})

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

distlp : {m n o : ℕ} → CPerm (m * n + m * o) (m * (n + o))
distlp {m} {n} {o} = cp (distl*+ {m}) (factorl*+ {m}) (distl*+∘̂factorl*+~id {m}) (factorl*+∘̂distl*+~id {m})

factorlp : {m n o : ℕ} → CPerm (m * (n + o)) (m * n + m * o)
factorlp {m} = symp (distlp {m})

-- right-zero absorbing permutation
0pr : ∀ {n} → CPerm 0 (n * 0)
0pr {n} = cp (right-zero*l {n}) (right-zero*r {n}) 
    right-zero*l∘̂right-zero*r~id right-zero*r∘̂right-zero*l~id

-- and its symmetric version
0pl : ∀ {n} → CPerm (n * 0) 0
0pl {n} = symp (0pr {n})

------------------------------------------------------------------------------------------------------

ridp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → transp p idp ≡ p
ridp {p = p} = p≡ (∘̂-rid (CPerm.π p))

lidp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → transp idp p ≡ p
lidp {p = p} = p≡ (∘̂-lid (CPerm.π p))

assocp : ∀ {m₁ m₂ m₃ n₁} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ m₁} → {p₃ : CPerm m₃ m₂} → 
  transp p₁ (transp p₂ p₃) ≡ transp (transp p₁ p₂) p₃
assocp {p₁ = p₁} {p₂} {p₃} = p≡ (∘̂-assoc (CPerm.π p₁) (CPerm.π p₂) (CPerm.π p₃))

linv : ∀ {m₁ m₂} (p : CPerm m₂ m₁) → transp p (symp p) ≡ idp
linv p = p≡ (CPerm.αp p)

rinv : ∀ {m₁ m₂} (p : CPerm m₂ m₁) → transp (symp p) p ≡ idp
rinv p = p≡ (CPerm.βp p)

transp-resp-≡ : ∀ {m₁ m₂ m₃} {f h : CPerm m₂ m₃} {g i : CPerm m₁ m₂} → 
  f ≡ h → g ≡ i → transp f g ≡ transp h i
transp-resp-≡ refl refl = refl

1p⊎1p≡1p : ∀ {m n} → idp {m} ⊎p idp {n} ≡ idp
1p⊎1p≡1p {m} = p≡ (1C⊎1C≡1C {m})

1p×1p≡1p : ∀ {m n} → idp {m} ×p idp {n} ≡ idp
1p×1p≡1p {m} = p≡ (1C×1C≡1C {m})

⊎p-distrib :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ n₂}
    → {p₃ : CPerm m₃ m₁} → {p₄ : CPerm m₄ m₂} →
      transp (p₁ ⊎p p₂) (p₃ ⊎p p₄) ≡ (transp p₁ p₃) ⊎p (transp p₂ p₄)
⊎p-distrib {p₁ = p₁} = p≡ (⊎c-distrib {p₁ = CPerm.π p₁})

×p-distrib :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ n₂}
    → {p₃ : CPerm m₃ m₁} → {p₄ : CPerm m₄ m₂} →
      (transp p₁ p₃) ×p (transp p₂ p₄) ≡ transp (p₁ ×p p₂) (p₃ ×p p₄)
×p-distrib {p₁ = p₁} = p≡ (sym (×c-distrib {p₁ = CPerm.π p₁}))

0p⊎x≡x : ∀ {m n} {p : CPerm m n} → 0p ⊎p p ≡ p
0p⊎x≡x {p = p} = p≡ F.0C⊎x≡x

-- this comes from looking at things categorically:
0p⊎x∘id≡id∘x : ∀ {m n} (p : CPerm m n) → transp (0p ⊎p p) idp ≡ transp idp p
0p⊎x∘id≡id∘x p = trans ridp (trans 0p⊎x≡x (sym lidp))

SCPerm : ℕ → ℕ → Setoid zero zero
SCPerm m n = ≡-Setoid (CPerm m n)
