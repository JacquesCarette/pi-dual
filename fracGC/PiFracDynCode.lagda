\newcommand{\PIFD}{% Not used
\begin{code}
{-# OPTIONS --without-K --safe #-}
module _ where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to R[_])
open import Relation.Binary.Core
open import Relation.Nullary
open import Induction.Nat

infix 90 𝟙/_
infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infix  40 _↔_
infixr 50 _⊚_

data ◯ : Set where
  ○ : ◯

-- Pi
\end{code}}
\newcommand{\PIFDUdef}{%
\begin{code}[hide]
mutual
  data 𝕌 : Set where
    𝟘 : 𝕌
    𝟙 : 𝕌
    _+ᵤ_ : 𝕌 → 𝕌 → 𝕌
    _×ᵤ_ : 𝕌 → 𝕌 → 𝕌
\end{code}
\begin{code}
    𝟙/_ : {t : 𝕌} → ⟦ t ⟧ → 𝕌
\end{code}
\begin{code}[hide]
  ⟦_⟧ : 𝕌 → Set
  ⟦ 𝟘 ⟧ = ⊥
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ 𝟙/ t ⟧ = ◯
\end{code}}
\newcommand{\PIFDCombdef}{%
\begin{code}[hide]
  data _↔_ : 𝕌 → 𝕌 → Set where
    unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ↔ t
    uniti₊l : {t : 𝕌} → t ↔ 𝟘 +ᵤ t
    unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ↔ t
    uniti₊r : {t : 𝕌} → t ↔ t +ᵤ 𝟘
    swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ↔ t₂ +ᵤ t₁
    assocl₊ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ↔ (t₁ +ᵤ t₂) +ᵤ t₃
    assocr₊ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ↔ t₁ +ᵤ (t₂ +ᵤ t₃)
    unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ↔ t
    uniti⋆l : {t : 𝕌} → t ↔ 𝟙 ×ᵤ t
    unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ↔ t
    uniti⋆r : {t : 𝕌} → t ↔ t ×ᵤ 𝟙
    swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ↔ t₂ ×ᵤ t₁
    assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ ×ᵤ t₂) ×ᵤ t₃
    assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ↔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
    absorbr : {t : 𝕌} → 𝟘 ×ᵤ t ↔ 𝟘
    absorbl : {t : 𝕌} → t ×ᵤ 𝟘 ↔ 𝟘
    factorzr : {t : 𝕌} → 𝟘 ↔ t ×ᵤ 𝟘
    factorzl : {t : 𝕌} → 𝟘 ↔ 𝟘 ×ᵤ t
    dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ↔ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
    factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ +ᵤ t₂) ×ᵤ t₃
    distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ↔ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
    factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ↔ t₁ ×ᵤ (t₂ +ᵤ t₃)
    id↔     : {t : 𝕌} → t ↔ t
    _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ↔ t₂) → (t₂ ↔ t₃) → (t₁ ↔ t₃)
    _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ +ᵤ t₂ ↔ t₃ +ᵤ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ ×ᵤ t₂ ↔ t₃ ×ᵤ t₄)
\end{code}
\begin{code}
    η : {t : 𝕌} (v : ⟦ t ⟧) → 𝟙 ↔ t ×ᵤ (𝟙/ v)
    ε : {t : 𝕌} (v : ⟦ t ⟧) → t ×ᵤ (𝟙/ v) ↔ 𝟙
\end{code}}
\newcommand{\PIFDdec}{% Not used
\begin{code}
𝕌dec : (t : 𝕌) → Decidable (_≡_ {A = ⟦ t ⟧})
𝕌dec 𝟘 ()
𝕌dec 𝟙 tt tt = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ y) with 𝕌dec t₁ x y
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ .x) | yes refl = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ y)  | no ¬p = no (λ {refl → ¬p refl})
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₂ y) = no (λ ())
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₁ y) = no (λ ())
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ y) with 𝕌dec t₂ x y
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ .x) | yes refl = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ y) | no ¬p = no (λ {refl → ¬p refl})
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , y₂) with 𝕌dec t₁ x₁ x₂ | 𝕌dec t₂ y₁ y₂
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (.x₁ , .y₁) | yes refl | yes refl = yes refl
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (.x₁ , y₂) | yes refl | no ¬p = no (λ p → ¬p (cong proj₂ p))
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , .y₁) | no ¬p | yes refl = no (λ p → ¬p (cong proj₁ p))
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , y₂) | no ¬p | no ¬p₁ = no (λ p → ¬p (cong proj₁ p))
𝕌dec (𝟙/ v) ○ ○ = yes refl

_≟ᵤ_ : {t : 𝕌} → Decidable (_≡_ {A = ⟦ t ⟧})
_≟ᵤ_ {t} v w = 𝕌dec t v w
\end{code}}

\newcommand{\PIFDinterp}{%
\begin{code}[hide]
interp : {t₁ t₂ : 𝕌} → (t₁ ↔ t₂) → ⟦ t₁ ⟧ → Maybe ⟦ t₂ ⟧
interp unite₊l (inj₁ ())
interp unite₊l (inj₂ v) = just v
interp uniti₊l v = just (inj₂ v)
interp unite₊r (inj₁ v) = just v
interp unite₊r (inj₂ ())
interp uniti₊r v = just (inj₁ v)
interp swap₊ (inj₁ v) = just (inj₂ v)
interp swap₊ (inj₂ v) = just (inj₁ v)
interp assocl₊ (inj₁ v) = just (inj₁ (inj₁ v))
interp assocl₊ (inj₂ (inj₁ v)) = just (inj₁ (inj₂ v))
interp assocl₊ (inj₂ (inj₂ v)) = just (inj₂ v)
interp assocr₊ (inj₁ (inj₁ v)) = just (inj₁ v)
interp assocr₊ (inj₁ (inj₂ v)) = just (inj₂ (inj₁ v))
interp assocr₊ (inj₂ v) = just (inj₂ (inj₂ v))
interp unite⋆l v = just (proj₂ v)
interp uniti⋆l v = just (tt , v)
interp unite⋆r v = just (proj₁ v)
interp uniti⋆r v = just (v , tt)
interp swap⋆ (v₁ , v₂) = just (v₂ , v₁)
interp assocl⋆ (v₁ , v₂ , v₃) = just ((v₁ , v₂) , v₃)
interp assocr⋆ ((v₁ , v₂) , v₃) = just (v₁ , v₂ , v₃)
interp absorbr (() , v)
interp absorbl (v , ())
interp factorzr ()
interp factorzl ()
interp dist (inj₁ v₁ , v₃) = just (inj₁ (v₁ , v₃))
interp dist (inj₂ v₂ , v₃) = just (inj₂ (v₂ , v₃))
interp factor (inj₁ (v₁ , v₃)) = just (inj₁ v₁ , v₃)
interp factor (inj₂ (v₂ , v₃)) = just (inj₂ v₂ , v₃)
interp distl (v₁ , inj₁ v₂) = just (inj₁ (v₁ , v₂))
interp distl (v₁ , inj₂ v₃) = just (inj₂ (v₁ , v₃))
interp factorl (inj₁ (v₁ , v₂)) = just (v₁ , inj₁ v₂)
interp factorl (inj₂ (v₁ , v₃)) = just (v₁ , inj₂ v₃)
interp id↔ v = just v
interp (c₁ ⊚ c₂) v = interp c₁ v >>= interp c₂
interp (c₁ ⊕ c₂) (inj₁ v) = interp c₁ v >>= just ∘ inj₁
interp (c₁ ⊕ c₂) (inj₂ v) = interp c₂ v >>= just ∘ inj₂
interp (c₁ ⊗ c₂) (v₁ , v₂) = interp c₁ v₁ >>= (λ v₁' → interp c₂ v₂ >>= λ v₂' → just (v₁' , v₂'))
\end{code}
\begin{code}
interp (η v) tt = just (v , ○)
interp (ε v) (v' , ○) with v ≟ᵤ v'
... | yes _ = just tt
... | no _ = nothing
\end{code}}
\newcommand{\PFDxx}{% Not used
\begin{code}
--- Examples

𝟚 𝔹 : 𝕌
𝟚 = 𝟙 +ᵤ 𝟙
𝔹 = 𝟙 +ᵤ 𝟙

𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

xorr xorl : 𝟚 ×ᵤ 𝟚 ↔ 𝟚 ×ᵤ 𝟚
xorr = dist ⊚ (id↔ ⊕ (id↔ ⊗ swap₊)) ⊚ factor
xorl = distl ⊚ (id↔ ⊕ (swap₊ ⊗ id↔)) ⊚ factorl

--   ─────┬────⊕───  ───────
--        |    |   ⨉
--     ┌──⊕────┴───  ───┐
--     └────────────────┘
id' : 𝟚 ↔ 𝟚
id' = uniti⋆r ⊚ (id↔ ⊗ η 𝔽) ⊚ assocl⋆ ⊚
      ((xorr ⊚ xorl ⊚ swap⋆) ⊗ id↔) ⊚
      assocr⋆ ⊚ (id↔ ⊗ ε 𝔽) ⊚ unite⋆r

ex1 : interp id' 𝕋 ≡ just 𝕋
ex1 = refl

ex2 : interp id' 𝔽 ≡ just 𝔽
ex2 = refl

--     ┌──────  ───────┐
--     └──────╲╱───────┘
--            ╱╲
--     ┌─────    ──────┐
--     └───────────────┘
switch : 𝟙 ↔ 𝟙
switch = uniti⋆r ⊚ (η 𝔽 ⊗ η 𝔽) ⊚ assocl⋆ ⊚
         (((swap⋆ ⊗ id↔) ⊚ assocr⋆ ⊚
         (id↔ ⊗ swap⋆) ⊚ assocl⋆ ⊚ (swap⋆ ⊗ id↔)) ⊗ id↔) ⊚
         assocr⋆ ⊚ (ε 𝔽 ⊗ ε 𝔽) ⊚ unite⋆r

bad : 𝟚 ↔ 𝟚
bad = uniti⋆r ⊚ (id↔ ⊗ η 𝔽) ⊚ assocl⋆ ⊚
      ((xorr ⊚ swap⋆) ⊗ id↔) ⊚
      assocr⋆ ⊚ (id↔ ⊗ ε 𝔽) ⊚ unite⋆r

ex3 : interp bad 𝔽 ≡ just 𝔽
ex3 = refl

ex4 : interp bad 𝕋 ≡ nothing
ex4 = refl

--shouldn't_type_check : 𝟙 ↔ 𝟙
--shouldn't_type_check = η {v = 𝔽} ⊚ ε {v = 𝕋}

--ex5 : interp shouldn't_type_check tt ≡ nothing
--ex5 = refl

--more : 𝟙 ↔ 𝟙
--more = η {v = 𝔽} ⊚ (swap₊ ⊗ id↔) ⊚ ε {v = 𝕋}

--ex6 : interp more tt ≡ just tt
--ex6 = refl

-- Sec. 3.2 from https://people.engr.ncsu.edu/hzhou/quantum_assert.pdf

infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : 𝕌) {t₂ : 𝕌} {t₃ : 𝕌} →
          (t₁ ↔ t₂) → (t₂ ↔ t₃) → (t₁ ↔ t₃)
_ ⟷⟨ α ⟩ β = α ⊚ β

_□ : (t : 𝕌) → {t : 𝕌} → (t ↔ t)
_□ t = id↔

CONTROLLED : {A : 𝕌} → (A ↔ A) → 𝔹 ×ᵤ A ↔ 𝔹 ×ᵤ A
CONTROLLED c = dist ⊚ (id↔ ⊕ (id↔ ⊗ c)) ⊚ factor

NOT : 𝔹 ↔ 𝔹
NOT = swap₊

CNOT : 𝔹 ×ᵤ 𝔹 ↔ 𝔹 ×ᵤ 𝔹
CNOT = CONTROLLED NOT

CNOT13 : (𝔹 ×ᵤ 𝔹) ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝕋) ↔  (𝔹 ×ᵤ 𝔹) ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝕋)
CNOT13 = assocl⋆ ⊚ ((assocr⋆ ⊚ (id↔ ⊗ swap⋆) ⊚ assocl⋆ ⊚ (CNOT ⊗ id↔) ⊚ assocr⋆ ⊚ (id↔ ⊗ swap⋆) ⊚ assocl⋆) ⊗ id↔) ⊚ assocr⋆

CNOT23 : (𝔹 ×ᵤ 𝔹) ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝕋) ↔  (𝔹 ×ᵤ 𝔹) ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝕋)
CNOT23 = assocl⋆ ⊚ ((assocr⋆ ⊚ (id↔ ⊗ CNOT) ⊚ assocl⋆) ⊗ id↔) ⊚ assocr⋆
\end{code}}
\newcommand{\PIFDparity}{%
\begin{code}
parity : 𝔹 ×ᵤ 𝔹 ↔ 𝔹 ×ᵤ 𝔹
parity =             𝔹 ×ᵤ 𝔹
  ⟷⟨ uniti⋆r ⟩       (𝔹 ×ᵤ 𝔹) ×ᵤ 𝟙
  ⟷⟨ id↔ ⊗ (η 𝕋) ⟩  (𝔹 ×ᵤ 𝔹) ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝕋)
  ⟷⟨ CNOT13 ⟩        (𝔹 ×ᵤ 𝔹) ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝕋)
  ⟷⟨ CNOT23 ⟩        (𝔹 ×ᵤ 𝔹) ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝕋)
  ⟷⟨ id↔ ⊗ (ε 𝕋) ⟩   (𝔹 ×ᵤ 𝔹) ×ᵤ 𝟙
  ⟷⟨ unite⋆r ⟩       (𝔹 ×ᵤ 𝔹) □

t1 t2 t3 t4 : Maybe ⟦ 𝔹 ×ᵤ 𝔹 ⟧
t1 = interp parity (𝔽 , 𝔽) -- just (𝔽 , 𝔽)
t2 = interp parity (𝔽 , 𝕋) -- nothing
t3 = interp parity (𝕋 , 𝔽) -- nothing
t4 = interp parity (𝕋 , 𝕋) -- just (𝕋 , 𝕋)
\end{code}}
\newcommand{\PIFDtoffoli}{%
\begin{code}[hide]
0<1 : 0 <′ 1
0<1 = ≤′-refl

1<2 : 1 <′ 2
1<2 = ≤′-refl

2+n<3+n : ∀ {n} → 2 + n <′ 3 + n
2+n<3+n = ≤′-refl

2<3+n : ∀ {n} → 2 <′ 3 + n
2<3+n = s≤′s (s≤′s (s≤′s z≤′n))
\end{code}
\begin{code}
𝔹^_ : ℕ → 𝕌
𝔹^ zero   = 𝔹
𝔹^ suc n  = (𝔹^ n) ×ᵤ 𝔹

θ : (n : ℕ) → (𝔹^ n) ↔ (𝔹^ n)
θ = <′-rec (λ n → (𝔹^ n) ↔ (𝔹^ n)) θ'
 where
  θ' : (n : ℕ) →
       (∀ m → m <′ n → (𝔹^ m) ↔ (𝔹^ m)) → (𝔹^ n) ↔ (𝔹^ n)
  θ' 0 _ = NOT
  θ' 1 θ'' = dist ⊚ (id↔ ⊕ (id↔ ⊗ θ'' 0 0<1)) ⊚ factor
  θ' 2 θ'' =
   assocr⋆ ⊚ dist ⊚ (id↔ ⊕ (id↔ ⊗ θ'' 1 1<2)) ⊚ factor ⊚ assocl⋆
  θ' (suc (suc (suc n))) θ'' =
   (id↔ ⊗ (uniti⋆l ⊚ (η 𝔽 ⊗ id↔) ⊚ assocr⋆
          ⊚ (id↔ ⊗ swap⋆) ⊚ assocl⋆))
   ⊚ assocl⋆ ⊚ (assocl⋆ ⊗ id↔)
   ⊚ ((θₙ₋₁ ⊗ id↔) ⊗ id↔)
   ⊚ (θ₃ ⊗ id↔)
   ⊚ ((θₙ₋₁ ⊗ id↔) ⊗ id↔)
   ⊚ (assocr⋆ ⊗ id↔) ⊚ assocr⋆
   ⊚ (id↔ ⊗ (assocr⋆ ⊚ (id↔ ⊗ swap⋆)
             ⊚ assocl⋆ ⊚ (ε 𝔽 ⊗ id↔) ⊚ unite⋆l))
   where
     θₙ₋₁ : (𝔹^ (3 + n)) ↔ (𝔹^ (3 + n))
     θₙ₋₁ = assocr⋆ ⊚ (id↔ ⊗ swap⋆) ⊚ assocl⋆
          ⊚ (θ'' (2 + n) 2+n<3+n ⊗ id↔)
          ⊚ assocr⋆ ⊚ (id↔ ⊗ swap⋆) ⊚ assocl⋆

     θ₃ : (𝔹^ (4 + n)) ↔ (𝔹^ (4 + n))
     θ₃ = (assocr⋆ ⊗ id↔) ⊚ assocr⋆
        ⊚ (id↔ ⊗ θ'' 2 2<3+n)
        ⊚ assocl⋆ ⊚ (assocl⋆ ⊗ id↔)
\end{code}}
\newcommand{\PIFDtoffolitests}{% Not used
\begin{code}
test₁ : interp (θ 0) 𝔽 ≡ just 𝕋
test₁ = refl

test₂ : interp (θ 1) (𝕋 , 𝔽) ≡ just (𝕋 , 𝕋)
test₂ = refl

test₃ : interp (θ 2) ((𝕋 , 𝕋) , 𝕋) ≡ just ((𝕋 , 𝕋) , 𝔽)
test₃ = refl

test₄ : interp (θ 3) (((𝕋 , 𝕋) , 𝕋) , 𝔽) ≡ just (((𝕋 , 𝕋) , 𝕋) , 𝕋)
test₄ = refl

test₅ : interp (θ 4) ((((𝕋 , 𝕋) , 𝕋) , 𝕋) , 𝕋) ≡ just ((((𝕋 , 𝕋) , 𝕋) , 𝕋) , 𝔽)
test₅ = refl
\end{code}}
