
\newcommand{\Preamble}{%
\begin{code}
{-# OPTIONS --without-K #-}
module _ where
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Function
open import Relation.Binary.PropositionalEquality
  renaming ([_] to R[_])
open import Relation.Binary.Core
open import Relation.Nullary

infix 99 𝟙/_
infix  70 _×ᵤ_
infix  60 _+ᵤ_
infix  40 _↔_
infixr 50 _⊚_

data ◯ : Set where
  ○ : ◯

-- Pi

mutual
\end{code}}
\newcommand{\Udef}{%
\begin{code}
  data 𝕌 : Set where
    𝟘     : 𝕌
    𝟙     : 𝕌
    _+ᵤ_  : 𝕌 → 𝕌 → 𝕌
    _×ᵤ_  : 𝕌 → 𝕌 → 𝕌
    𝟙/_   : 𝕌 → 𝕌
\end{code}}
\newcommand{\CodeA}{%
\begin{code}
  ⟦_⟧ : 𝕌 → Set
  ⟦ 𝟘 ⟧ = ⊥
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ 𝟙/ t ⟧ = ◯

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
\end{code}}
\newcommand{\EtaEpsilon}{%
\begin{code}
    η : {t : 𝕌} {t≠0 : ¬ card t ≡ 0} → 𝟙 ↔ t ×ᵤ 𝟙/ t
    ε : {t : 𝕌} {t≠0 : ¬ card t ≡ 0} → t ×ᵤ 𝟙/ t ↔ 𝟙
\end{code}}
\newcommand{\CodeB}{%
\begin{code}
-- Number of points in type
  card : (t : 𝕌) → ℕ
  card 𝟘 = 0
  card 𝟙 = 1
  card (t₁ +ᵤ t₂) = card t₁ + card t₂
  card (t₁ ×ᵤ t₂) = card t₁ * card t₂
  card 𝟙/● = 1

-- If number of points is zero then it is impossible to find a value
-- of the type
0empty : {t : 𝕌} → card t ≡ 0 → (v : ⟦ t ⟧) → ⊥
0empty {𝟘} _ ()
0empty {𝟙} () tt
0empty {t₁ +ᵤ t₂} s (inj₁ v₁)
  with card t₁ | card t₂ | inspect card t₁
0empty {t₁ +ᵤ t₂} refl (inj₁ v₁) | 0 | 0 | R[ s₁ ] =
  0empty {t₁} s₁ v₁
0empty {t₁ +ᵤ t₂} s (inj₂ v₂)
  with card t₁ | card t₂ | inspect card t₂
0empty {t₁ +ᵤ t₂} refl (inj₂ v₂) | ℕ.zero | ℕ.zero | R[ s₂ ] =
  0empty {t₂} s₂ v₂
0empty {t₁ ×ᵤ t₂} s (v₁ , v₂)
  with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
0empty {t₁ ×ᵤ t₂} refl (v₁ , v₂) | ℕ.zero | _ | R[ s₁ ] | _ =
  0empty {t₁} s₁ v₁
0empty {t₁ ×ᵤ t₂} s (v₁ , v₂) | ℕ.suc n₁ | ℕ.zero | R[ s₁ ] | R[ s₂ ] =
  0empty {t₂} s₂ v₂
0empty {𝟙/ t} () f

default : (t : 𝕌) → {t≠0 : ¬ card t ≡ 0} → ⟦ t ⟧
default 𝟘 {t≠0} = ⊥-elim (t≠0 refl) 
default 𝟙 = tt
default (t₁ +ᵤ t₂) {p≠0} with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 refl)
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] =
  inj₂ (default t₂ {λ t2≡0 → ⊥-elim (p≠0 (trans (sym s₂) t2≡0))})
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] =
  inj₁ (default t₁ {λ t1≡0 →
    ⊥-elim (p≠0 ((trans (sym (trans s₁ (sym (+-identityʳ (suc m))))) t1≡0)))})
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] =
  inj₁ (default t₁ {λ t1≡0 → ⊥-elim (1+n≢0 (trans (sym s₁) t1≡0))})
default (t₁ ×ᵤ t₂) {p≠0} with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 refl)
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 refl)
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 (*-zeroʳ (suc m)))
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] =
  default t₁ {λ t1≡0 → ⊥-elim (1+n≢0 (trans (sym s₁) t1≡0))},
  default t₂ {λ t2≡0 → ⊥-elim (1+n≢0 (trans (sym s₂) t2≡0))}
default (𝟙/ t) = ○ 

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
𝕌dec (𝟙/ t) ○ ○ = yes refl

_≟ᵤ_ : {t : 𝕌} → Decidable (_≡_ {A = ⟦ t ⟧})
_≟ᵤ_ {t} v w = 𝕌dec t v w

\end{code}}
\newcommand{\dyninterp}{%
\begin{code}
interp : {t₁ t₂ : 𝕌} → (t₁ ↔ t₂) → ⟦ t₁ ⟧ → Maybe ⟦ t₂ ⟧
interp swap⋆ (v₁ , v₂) = just (v₂ , v₁)
interp (c₁ ⊚ c₂) v = interp c₁ v >>= interp c₂
-- (skip)
interp (η {t} {t≠0}) tt = just (default t {t≠0} , ○)
interp (ε {t} {t≠0}) (v' , ○) with v' ≟ᵤ (default t {t≠0})
... | yes _ = just tt
... | no _ = nothing
\end{code}}
\newcommand{\PFDCONE}{%
\begin{code}
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
interp (c₁ ⊕ c₂) (inj₁ v) = interp c₁ v >>= just ∘ inj₁
interp (c₁ ⊕ c₂) (inj₂ v) = interp c₂ v >>= just ∘ inj₂
interp (c₁ ⊗ c₂) (v₁ , v₂) = interp c₁ v₁ >>= (λ v₁' → interp c₂ v₂ >>= λ v₂' → just (v₁' , v₂'))
\end{code}}
\newcommand{\CodeC}{%
\begin{code}
--- Examples

𝟚 𝔹 : 𝕌
𝟚 = 𝟙 +ᵤ 𝟙
𝔹 = 𝟙 +ᵤ 𝟙

𝔽 𝕋 : ⟦ 𝟚 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

CNOT CNOT' : 𝔹 ×ᵤ 𝔹 ↔ 𝔹 ×ᵤ 𝔹
CNOT = dist ⊚ (id↔ ⊕ (id↔ ⊗ swap₊)) ⊚ factor
CNOT' = distl ⊚ (id↔ ⊕ (swap₊ ⊗ id↔)) ⊚ factorl


𝔹≠0 : ¬ (card 𝔹 ≡ 0)
𝔹≠0 ()

η' : 𝟙 ↔ 𝔹 ×ᵤ (𝟙/ 𝔹)
η' = η {t≠0 = 𝔹≠0}

ε' : 𝔹 ×ᵤ (𝟙/ 𝔹) ↔ 𝟙
ε' = ε {t≠0 = 𝔹≠0}

infixr 2  _↔⟨_⟩_
infix  3  _□

_↔⟨_⟩_ : (t₁ : 𝕌) {t₂ : 𝕌} {t₃ : 𝕌} →
          (t₁ ↔ t₂) → (t₂ ↔ t₃) → (t₁ ↔ t₃)
_ ↔⟨ α ⟩ β = α ⊚ β

_□ : (t : 𝕌) → {t : 𝕌} → (t ↔ t)
_□ t = id↔

idx : 𝔹 ↔ 𝔹
idx =
  uniti⋆r ⊚ (id↔ ⊗ η') ⊚ assocl⋆ ⊚
  ((CNOT ⊚ CNOT' ⊚ swap⋆) ⊗ id↔) ⊚
  assocr⋆ ⊚ (id↔ ⊗ ε') ⊚ unite⋆r

switchx : 𝟙 ↔ 𝟙
switchx =
  uniti⋆r ⊚ (η' ⊗ η') ⊚ assocl⋆ ⊚
  (((swap⋆ ⊗ id↔) ⊚ assocr⋆ ⊚
  (id↔ ⊗ swap⋆) ⊚ assocl⋆ ⊚ (swap⋆ ⊗ id↔)) ⊗ id↔) ⊚ 
  assocr⋆ ⊚ (ε' ⊗ ε') ⊚ unite⋆r

switch : {A : 𝕌} {A≠0 : ¬ card A ≡ 0} → 𝟙 ↔ 𝟙
switch {A} {A≠0} =
  let η' = η {t = A} {t≠0 = A≠0}
      ε' = ε {t = A} {t≠0 = A≠0}
  in 𝟙
  ↔⟨ uniti⋆r ⟩ 𝟙 ×ᵤ 𝟙
  ↔⟨ η' ⊗ η' ⟩ (A ×ᵤ 𝟙/ A) ×ᵤ (A ×ᵤ 𝟙/ A)
  ↔⟨ assocl⋆ ⟩ ((A ×ᵤ 𝟙/ A) ×ᵤ A) ×ᵤ 𝟙/ A
  ↔⟨ ((swap⋆ ⊗ id↔) ⊚ assocr⋆ ⊚ (id↔ ⊗ swap⋆) ⊚ assocl⋆ ⊚ (swap⋆ ⊗ id↔)) ⊗ id↔ ⟩ ((A ×ᵤ 𝟙/ A) ×ᵤ A) ×ᵤ 𝟙/ A
  ↔⟨ assocr⋆ ⟩ (A ×ᵤ 𝟙/ A) ×ᵤ (A ×ᵤ 𝟙/ A)
  ↔⟨ ε' ⊗ ε' ⟩ 𝟙 ×ᵤ 𝟙
  ↔⟨ unite⋆r ⟩ 𝟙 □
  
shuffle : {A B C D : 𝕌} → (A ×ᵤ B) ×ᵤ (C ×ᵤ D) ↔ (B ×ᵤ D) ×ᵤ (A ×ᵤ C)
shuffle = (swap⋆ ⊗ swap⋆) ⊚ assocr⋆ ⊚ (id↔ ⊗ (assocl⋆ ⊚ (swap⋆ ⊗ id↔) ⊚ assocr⋆)) ⊚ assocl⋆

postulate
  pr≠0 : (A B : 𝕌) → (A≠0 : ¬ card A ≡ 0) → (B≠0 : ¬ card B ≡ 0) →
         ¬ (card (A ×ᵤ B) ≡ 0)


pattern ?𝔽 = inj₁ tt
pattern ?𝕋 = inj₂ tt
\end{code}}
\newcommand{\EtaEpsilonExampleone}{%
\begin{code}
id' : 𝔹 ↔ 𝔹
id' =
  let η' = η {𝔹} {𝔹≠0}; ε' = ε {𝔹} {𝔹≠0}
  in 𝔹
  ↔⟨ uniti⋆r ⟩                        𝔹 ×ᵤ 𝟙
  ↔⟨ id↔ ⊗ η' ⟩                       𝔹 ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝔹)
  ↔⟨ assocl⋆ ⟩                        (𝔹 ×ᵤ 𝔹) ×ᵤ 𝟙/ 𝔹
  ↔⟨ (CNOT ⊚ CNOT' ⊚ swap⋆) ⊗ id↔ ⟩   (𝔹 ×ᵤ 𝔹) ×ᵤ 𝟙/ 𝔹
  ↔⟨ assocr⋆ ⟩                        𝔹 ×ᵤ (𝔹 ×ᵤ 𝟙/ 𝔹)
  ↔⟨ id↔ ⊗ ε' ⟩                       𝔹 ×ᵤ 𝟙
  ↔⟨ unite⋆r ⟩                        𝔹 □

idcheck : (b : ⟦ 𝔹 ⟧) → interp id' b ≡ just b
idcheck ?𝔽 = refl
idcheck ?𝕋 = refl 
\end{code}}
\newcommand{\EtaEpsilonExampletwo}{%
\begin{code}
rev× : {A B : 𝕌} {A≠0 : ¬ card A ≡ 0} {B≠0 : ¬ card B ≡ 0} → 
       𝟙/ (A ×ᵤ B) ↔ 𝟙/ A ×ᵤ 𝟙/ B
rev× {A} {B} {A≠0} {B≠0} =
  let η₁ = η {A} {A≠0}; η₂ = η {B} {B≠0}
      ε' = ε {A ×ᵤ B} {pr≠0 A B A≠0 B≠0}
    in  𝟙/ (A ×ᵤ B)
  ↔⟨ uniti⋆l ⊚ uniti⋆l ⊚ assocl⋆ ⟩
        (𝟙 ×ᵤ 𝟙) ×ᵤ 𝟙/ (A ×ᵤ B)
  ↔⟨ (η₁ ⊗ η₂) ⊗ id↔ ⟩
        ((A ×ᵤ 𝟙/ A) ×ᵤ (B ×ᵤ 𝟙/ B)) ×ᵤ 𝟙/ (A ×ᵤ B)
  ↔⟨ (shuffle ⊗ id↔) ⊚ assocr⋆ ⟩
        (𝟙/ A ×ᵤ 𝟙/ B) ×ᵤ ((A ×ᵤ B) ×ᵤ 𝟙/ (A ×ᵤ B))
  ↔⟨ id↔ ⊗ ε' ⟩
        (𝟙/ A ×ᵤ 𝟙/ B) ×ᵤ 𝟙
  ↔⟨ unite⋆r ⟩
        𝟙/ A ×ᵤ 𝟙/ B □
\end{code}}
\newcommand{\CodeD}{%
\begin{code}

ex1 : interp id' 𝕋 ≡ just 𝕋
ex1 = refl

ex2 : interp id' 𝔽 ≡ just 𝔽
ex2 = refl

bad : 𝟚 ↔ 𝟚
bad = uniti⋆r ⊚ (id↔ ⊗ η') ⊚ assocl⋆ ⊚
      ((CNOT ⊚ swap⋆) ⊗ id↔) ⊚
      assocr⋆ ⊚ (id↔ ⊗ ε') ⊚ unite⋆r

ex3 : interp bad 𝔽 ≡ just 𝔽
ex3 = refl

ex4 : interp bad 𝕋 ≡ nothing
ex4 = refl

{--
shouldn't_type_check : 𝟙 ↔ 𝟙
shouldn't_type_check = η {v = 𝔽} ⊚ ε {v = 𝕋}

ex5 : interp shouldn't_type_check tt ≡ nothing
ex5 = refl

more : 𝟙 ↔ 𝟙
more = η {v = 𝔽} ⊚ (swap₊ ⊗ id↔) ⊚ ε {v = 𝕋}

ex6 : interp more tt ≡ just tt
ex6 = refl
--}
\end{code}}
