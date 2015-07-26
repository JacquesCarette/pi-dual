{-# OPTIONS --without-K #-}

module ConcretePermutationProperties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning; proof-irrelevance)

--

open import FinVec using (1C; _∘̂_)
     
open import FinVecProperties 
  using (∘̂-assoc; ∘̂-lid; ∘̂-rid;
         1C₀⊎x≡x; 1C⊎1C≡1C; 1C×1C≡1C;
         ⊎c-distrib; ×c-distrib;
         unite+∘[0⊎x]≡x∘unite+; uniti+∘x≡[0⊎x]∘uniti+;
         uniti+r∘[x⊎0]≡x∘uniti+r; unite+r∘[x⊎0]≡x∘unite+r)

open import ConcretePermutation
  using (CPerm; cp; idp; symp; transp; _⊎p_; _×p_;
         0p; unite+p; uniti+p; unite+rp; uniti+rp) 

------------------------------------------------------------------------------
-- Properties of concrete permutations that are needed to show that
-- this is also a symmetric rig groupoid

-- If the forward components are equal, then so are the backward ones

πᵒ≡ : ∀ {m n} → (π₁ π₂ : CPerm m n) → (CPerm.π π₁ ≡ CPerm.π π₂) →
      (CPerm.πᵒ π₁ ≡ CPerm.πᵒ π₂)
πᵒ≡ {n} (cp π πᵒ αp βp) (cp .π πᵒ₁ αp₁ βp₁) refl =
  begin (
    πᵒ                  ≡⟨ sym (∘̂-rid πᵒ) ⟩
    πᵒ ∘̂ 1C          ≡⟨  cong (_∘̂_ πᵒ) (sym αp₁)  ⟩
    πᵒ ∘̂ (π ∘̂ πᵒ₁)      ≡⟨ ∘̂-assoc πᵒ π πᵒ₁ ⟩
    (πᵒ ∘̂ π) ∘̂ πᵒ₁      ≡⟨ cong (λ x → x ∘̂ πᵒ₁) βp ⟩
    1C ∘̂ πᵒ₁            ≡⟨ ∘̂-lid πᵒ₁ ⟩
    πᵒ₁ ∎)
  where open ≡-Reasoning

-- If the forward components are equal, then so are the entire
-- concrete permutations

p≡ : ∀ {m n} → {π₁ π₂ : CPerm m n} → (CPerm.π π₁ ≡ CPerm.π π₂) → π₁ ≡ π₂
p≡ {m} {n} {cp π πᵒ αp βp} {cp .π πᵒ₁ αp₁ βp₁} refl with
  πᵒ≡ (cp π πᵒ αp βp) (cp π πᵒ₁ αp₁ βp₁) refl
p≡ {m} {n} {cp π πᵒ αp βp} {cp .π .πᵒ αp₁ βp₁} refl | refl
  with proof-irrelevance αp αp₁ | proof-irrelevance βp βp₁
p≡ {m} {n} {cp π πᵒ αp βp} {cp .π .πᵒ .αp .βp} refl | refl | refl | refl = refl

------------------------------------------------------------------------------
-- Composition

assocp : ∀ {m₁ m₂ m₃ n₁} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ m₁} →
  {p₃ : CPerm m₃ m₂} → 
  transp p₁ (transp p₂ p₃) ≡ transp (transp p₁ p₂) p₃
assocp {p₁ = p₁} {p₂} {p₃} =
  p≡ (∘̂-assoc (CPerm.π p₁) (CPerm.π p₂) (CPerm.π p₃))

lidp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → transp idp p ≡ p
lidp {p = p} = p≡ (∘̂-lid (CPerm.π p))

ridp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → transp p idp ≡ p
ridp {p = p} = p≡ (∘̂-rid (CPerm.π p))

transp-resp-≡ : ∀ {m₁ m₂ m₃} {f h : CPerm m₂ m₃} {g i : CPerm m₁ m₂} → 
  f ≡ h → g ≡ i → transp f g ≡ transp h i
transp-resp-≡ refl refl = refl

-- Inverses

linv : ∀ {m₁ m₂} (p : CPerm m₂ m₁) → transp p (symp p) ≡ idp
linv p = p≡ (CPerm.αp p)

rinv : ∀ {m₁ m₂} (p : CPerm m₂ m₁) → transp (symp p) p ≡ idp
rinv p = p≡ (CPerm.βp p)

-- Additives

0p⊎x≡x : ∀ {m n} {p : CPerm m n} → idp {0} ⊎p p ≡ p
0p⊎x≡x {p = p} = p≡ 1C₀⊎x≡x

1p⊎1p≡1p : ∀ {m n} → idp {m} ⊎p idp {n} ≡ idp
1p⊎1p≡1p {m} = p≡ (1C⊎1C≡1C {m})

⊎p-distrib :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ n₂}
    → {p₃ : CPerm m₃ m₁} → {p₄ : CPerm m₄ m₂} →
      transp (p₁ ⊎p p₂) (p₃ ⊎p p₄) ≡ (transp p₁ p₃) ⊎p (transp p₂ p₄)
⊎p-distrib {p₁ = p₁} = p≡ (⊎c-distrib {p₁ = CPerm.π p₁})

-- interaction with composition

unite+p∘[0⊎x]≡x∘unite+p : ∀ {m n} (p : CPerm m n) →
  transp unite+p (0p ⊎p p) ≡ transp p unite+p
unite+p∘[0⊎x]≡x∘unite+p p = p≡ unite+∘[0⊎x]≡x∘unite+

uniti+p∘x≡[0⊎x]∘uniti+p : ∀ {m n} (p : CPerm m n) →
  transp uniti+p p ≡ transp (0p ⊎p p) uniti+p
uniti+p∘x≡[0⊎x]∘uniti+p p = p≡ (uniti+∘x≡[0⊎x]∘uniti+ {x = CPerm.π p})

uniti+rp∘[x⊎0]≡x∘uniti+rp : ∀ {m n} (p : CPerm m n) →
  transp uniti+rp (p ⊎p 0p) ≡ transp p uniti+rp
uniti+rp∘[x⊎0]≡x∘uniti+rp p = p≡ uniti+r∘[x⊎0]≡x∘uniti+r

unite+rp∘[x⊎0]≡x∘unite+rp : ∀ {m n} (p : CPerm m n) →
  transp unite+rp p ≡ transp (p ⊎p 0p) unite+rp
unite+rp∘[x⊎0]≡x∘unite+rp p = p≡ unite+r∘[x⊎0]≡x∘unite+r

-- Multiplicatives

1p×1p≡1p : ∀ {m n} → idp {m} ×p idp {n} ≡ idp
1p×1p≡1p {m} = p≡ (1C×1C≡1C {m})

×p-distrib :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ n₂}
    → {p₃ : CPerm m₃ m₁} → {p₄ : CPerm m₄ m₂} →
      (transp p₁ p₃) ×p (transp p₂ p₄) ≡ transp (p₁ ×p p₂) (p₃ ×p p₄)
×p-distrib {p₁ = p₁} = p≡ (sym (×c-distrib {p₁ = CPerm.π p₁}))

------------------------------------------------------------------------------
