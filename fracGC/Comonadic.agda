{-# OPTIONS --without-K #-}

module Comonadic where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Rational
  using (ℚ; _/_; _+_; _*_; _≢0)
  renaming (1/_ to recip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product -- using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Core using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; module ≡-Reasoning)
open import Category.Comonad

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_

------------------------------------------------------------------------------
-- Pi with fractionals comonad

record Pointed (A : Set) (v : A) : Set where
  constructor ⇑
  field
    ● : A
    v≡● : v ≡ ● 

open Pointed

Recip : (A : Set) → (v : A) → Set
Recip A v = (w : A) → (v ≡ w) → ⊤

--

data 𝕌 : Set 
⟦_⟧ : (A : 𝕌) → Set
data _⟷_ : 𝕌 → 𝕌 → Set 
eval : {A B : 𝕌} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧

data 𝕌 where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌
  ●_[_]   : (A : 𝕌) → ⟦ A ⟧ → 𝕌
  𝟙/●_[_] : (A : 𝕌) → ⟦ A ⟧ → 𝕌

⟦ 𝟘 ⟧ = ⊥ 
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ ● A [ v ] ⟧ = Pointed ⟦ A ⟧ v
⟦ 𝟙/● A [ v ] ⟧ = Recip ⟦ A ⟧ v

data _⟷_ where
  unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ⟷ t
  uniti₊l : {t : 𝕌} → t ⟷ 𝟘 +ᵤ t
  unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ⟷ t
  uniti₊r : {t : 𝕌} → t ⟷ t +ᵤ 𝟘
  swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ⟷ t₂ +ᵤ t₁
  assocl₊ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ +ᵤ t₂) +ᵤ t₃
  assocr₊ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ⟷ t₁ +ᵤ (t₂ +ᵤ t₃)
  unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ⟷ t
  uniti⋆l : {t : 𝕌} → t ⟷ 𝟙 ×ᵤ t
  unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ⟷ t
  uniti⋆r : {t : 𝕌} → t ⟷ t ×ᵤ 𝟙
  swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ⟷ t₂ ×ᵤ t₁
  assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  absorbr : {t : 𝕌} → 𝟘 ×ᵤ t ⟷ 𝟘
  absorbl : {t : 𝕌} → t ×ᵤ 𝟘 ⟷ 𝟘
  factorzr : {t : 𝕌} → 𝟘 ⟷ t ×ᵤ 𝟘
  factorzl : {t : 𝕌} → 𝟘 ⟷ 𝟘 ×ᵤ t
  dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
  factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤ t₃)
  id⟷     : {t : 𝕌} → t ⟷ t
  _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)
  -- comonad
  -- not informnation preserving; not reversible
  extract : {t : 𝕌} → {v : ⟦ t ⟧} → ● t [ v ] ⟷ t
  extend : {t₁ t₂ : 𝕌} → {v₁ : ⟦ t₁ ⟧} → 
           (c : ● t₁ [ v₁ ] ⟷ t₂) →
           (● t₁ [ v₁ ] ⟷ ● t₂ [ eval c (⇑ v₁ refl) ])
  tensorl : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            ● t₁ ×ᵤ t₂ [ v₁ , v₂ ] ⟷ ● t₁ [ v₁ ] ×ᵤ ● t₂ [ v₂ ]
  tensorr : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            ● t₁ [ v₁ ] ×ᵤ ● t₂ [ v₂ ] ⟷ ● t₁ ×ᵤ t₂ [ v₁ , v₂ ]
  -- fractionals
  η : {t : 𝕌} → (v : ⟦ t ⟧) → 𝟙 ⟷ ● t [ v ] ×ᵤ 𝟙/● t [ v ]
  ε : {t : 𝕌} → (v : ⟦ t ⟧) → ● t [ v ] ×ᵤ 𝟙/● t [ v ] ⟷ 𝟙

eval unite₊l (inj₂ v) = v 
eval uniti₊l v  = inj₂ v 
eval unite₊r (inj₁ v) = v
eval uniti₊r v  = inj₁ v 
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v) 
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆l (tt , v) = v
eval uniti⋆l v = (tt , v)
eval unite⋆r (v , tt) = v
eval uniti⋆r v = (v , tt)
eval swap⋆ (v₁ , v₂)          = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbl () 
eval absorbr () 
eval factorzl () 
eval factorzr () 
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval distl (v , inj₁ v₁) = inj₁ (v , v₁)
eval distl (v , inj₂ v₂) = inj₂ (v , v₂) 
eval factorl (inj₁ (v , v₁)) = (v , inj₁ v₁)
eval factorl (inj₂ (v , v₂)) = (v , inj₂ v₂) 
eval id⟷ v = v
eval (c₁ ⊚ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)
eval extract p = ● p
eval (extend {v₁ = v₁} c) p with ● p | v≡● p
eval (extend {v₁ = .v₂} c) p | v₂ | refl = ⇑ (eval c (⇑ v₂ refl)) refl
eval tensorl p with ● p | v≡● p
... | (v₁ , v₂) | refl = ⇑ v₁ refl , ⇑ v₂ refl 
eval tensorr (p₁ , p₂) with ● p₁ | v≡● p₁ | ● p₂ | v≡● p₂
... | v₁ | refl | v₂ | refl = ⇑ (v₁ , v₂) refl 
eval (η v) tt = ⇑ v refl , λ w v≡w → tt
eval (ε v) (p , f) = f (● p) (v≡● p)

------------------------------------------------------------------------------
-- Set up for examples

infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : 𝕌) {t₂ : 𝕌} {t₃ : 𝕌} →
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
_ ⟷⟨ α ⟩ β = α ⊚ β

_□ : (t : 𝕌) → {t : 𝕌} → (t ⟷ t)
_□ t = id⟷

𝟚 𝔹 : 𝕌
𝟚 = 𝟙 +ᵤ 𝟙
𝔹 = 𝟙 +ᵤ 𝟙

𝔹² : 𝕌
𝔹² = 𝔹 ×ᵤ 𝔹

𝔽 𝕋 : ⟦ 𝟚 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

lift : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} → 
       (c : t₁ ⟷ t₂) → (● t₁ [ v₁ ] ⟷ ● t₂ [ eval c v₁ ])
lift c = extend (extract ⊚ c) 

------------------------------------------------------------------------------
-- Examples

zigzag : ∀ b → ● 𝟚 [ b ] ⟷ ● 𝟚 [ b ]
zigzag b =
  lift uniti⋆l ⊚                       -- POINTED (ONE * TWO)
  tensorl ⊚                            -- POINTED ONE * POINTED TWO
  ((extract ⊚ η b) ⊗ id⟷) ⊚          -- (POINTED TWO * RECIP TWO) * POINTED TWO
  assocr⋆ ⊚                            -- POINTED TWO * (RECIP TWO * POINTED TWO)
  (id⟷ ⊗ swap⋆) ⊚                    -- POINTED TWO * (POINTED TWO * RECIP TWO)
  (id⟷ ⊗ ε b) ⊚                      -- POINTED TWO * ONE
  unite⋆r 

test1 = eval (zigzag 𝔽) (⇑ 𝔽 refl)      -- (⇑ #f refl)
-- test2 = eval (zigzag 𝔽) (⇑ 𝕋 refl)   -- typechecks if given proof #f=#t
-- test3 = eval (zigzag 𝕋) (⇑ 𝔽 refl)   -- typechecks if given proof #f=#t
test4 = eval (zigzag 𝕋) (⇑ 𝕋 refl)      -- (⇑ #t refl) 

-- Conventional PI examples

NOT : 𝔹 ⟷ 𝔹
NOT = swap₊

NEG1 NEG2 NEG3 NEG4 NEG5 : 𝔹 ⟷ 𝔹
NEG1 = swap₊
NEG2 = id⟷ ⊚ NOT
NEG3 = NOT ⊚ NOT ⊚ NOT
NEG4 = NOT ⊚ id⟷
NEG5 = uniti⋆l ⊚ swap⋆ ⊚ (NOT ⊗ id⟷) ⊚ swap⋆ ⊚ unite⋆l
NEG6 = uniti⋆r ⊚ (NOT ⊗ id⟷) ⊚ unite⋆r -- same as above, but shorter

CNOT : 𝔹² ⟷ 𝔹²
CNOT = 𝔹 ×ᵤ 𝔹
     ⟷⟨ id⟷ ⟩
       (x +ᵤ y) ×ᵤ 𝔹
     ⟷⟨ dist ⟩
       (x ×ᵤ 𝔹) +ᵤ (y ×ᵤ 𝔹)
     ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT) ⟩
       (x ×ᵤ 𝔹) +ᵤ (y ×ᵤ 𝔹)
     ⟷⟨ factor ⟩
       (x +ᵤ y) ×ᵤ 𝔹
     ⟷⟨ id⟷ ⟩
       𝔹 ×ᵤ 𝔹 □
  where x = 𝟙; y = 𝟙

TOFFOLI : 𝔹 ×ᵤ 𝔹² ⟷ 𝔹 ×ᵤ 𝔹²
TOFFOLI = 𝔹 ×ᵤ 𝔹²
        ⟷⟨ id⟷ ⟩
          (x +ᵤ y) ×ᵤ 𝔹²
        ⟷⟨ dist ⟩
          (x ×ᵤ 𝔹²) +ᵤ (y ×ᵤ 𝔹²)
        ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩
          (x ×ᵤ 𝔹²) +ᵤ (y ×ᵤ 𝔹²)
        ⟷⟨ factor ⟩
          (x +ᵤ y) ×ᵤ 𝔹²
        ⟷⟨ id⟷ ⟩
          𝔹 ×ᵤ 𝔹² □
  where x = 𝟙; y = 𝟙

PERES : (𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹 ⟷ (𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹
PERES = (id⟷ ⊗ NOT) ⊚ assocr⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ swap⋆) ⊚ (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚ assocl⋆

SWAP12 SWAP23 SWAP13 ROTL ROTR : 𝟙 +ᵤ 𝟙 +ᵤ 𝟙 ⟷ 𝟙 +ᵤ 𝟙 +ᵤ 𝟙
SWAP12 = assocl₊ ⊚ (swap₊ ⊕ id⟷) ⊚ assocr₊
SWAP23 = id⟷ ⊕ swap₊
SWAP13 = SWAP23 ⊚ SWAP12 ⊚ SWAP23
ROTR   = SWAP12 ⊚ SWAP23
ROTL   = SWAP13 ⊚ SWAP23

t3 : ∀ {b₁ b₂} → 
     ● (𝔹 ×ᵤ 𝔹²) [ 𝔽 , (b₁ , b₂) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝔽 , (b₁ , b₂) ]
t3 = lift TOFFOLI

{--
The following do not typecheck. Good

t4 : ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝔽 , 𝔽) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝔽 , 𝕋) ]
t4 = lift TOFFOLI

t5 : ∀ {b₁ b₂} → 
     ● (𝔹 ×ᵤ 𝔹²) [ b₁ , (𝔽 , b₂) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ b₁ , (𝔽 , b₂) ]
t5 = lift TOFFOLI
--}

t6 : ∀ {b} →
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝕋 , b) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝕋 , eval NOT b) ]
t6 = lift TOFFOLI

-- Ancilla examples from literature

-- Fig. 2 in Ricercar

CONTROLLED : {A : 𝕌} → (A ⟷ A) → 𝔹 ×ᵤ A ⟷ 𝔹 ×ᵤ A
CONTROLLED c = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ c)) ⊚ factor

fig2a : 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ⟷ 
        𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹
fig2a = CONTROLLED (CONTROLLED (CONTROLLED NOT))

_∧_ : ⟦ 𝟚 ⟧ → ⟦ 𝟚 ⟧ → ⟦ 𝟚 ⟧
inj₁ tt ∧ b = 𝔽
inj₂ tt ∧ b = b

_^_ : ⟦ 𝟚 ⟧ → ⟦ 𝟚 ⟧ → ⟦ 𝟚 ⟧
inj₁ x ^ inj₁ x₁ = 𝔽
inj₁ x ^ inj₂ y = 𝕋
inj₂ y ^ inj₁ x = 𝕋
inj₂ y ^ inj₂ y₁ = 𝔽

fig2b : ∀ {a b c d} →
        ● 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 [ a , b , c , d ] ⟷ 
        ● 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 [ a , b , c , ((a ∧ (b ∧ c)) ^ d) ]
fig2b = lift uniti⋆r ⊚
        tensorl ⊚ (tensorl ⊗ id⟷) ⊚ ((id⟷ ⊗ tensorl) ⊗ id⟷) ⊚
        ((id⟷ ⊗ (id⟷ ⊗ tensorl)) ⊗ id⟷) ⊚
        -- (B * (B * (B * B))) * 1
        (id⟷ ⊗ (extract ⊚ η 𝔽)) ⊚
        -- (B * (B * (B * B))) * (B * 1/B)
        assocl⋆ ⊚ (assocr⋆ ⊗ id⟷) ⊚ ((id⟷ ⊗ assocr⋆) ⊗ id⟷) ⊚
        ((id⟷ ⊗ (id⟷ ⊗ assocr⋆)) ⊗ id⟷) ⊚ 
        -- (B * (B * (B * (B * B)))) * 1/B
        {!!} 

------------------------------------------------------------------------------

