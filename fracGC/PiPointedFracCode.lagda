\newcommand{\PIPF}{% Not used
\begin{code}
{-# OPTIONS --without-K --safe #-}

-- adding eta/epsilon to PiPointed
-- separate file for presentation in paper

module _ where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

infixr 90 _#_
infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_
infix 100 !_

infixr 70 _∙×ᵤ_
infixr 70 _∙⊗_
infixr 50 _∙⊚_
infix 100 !∙_

------------------------------------------------------------------------------
-- Pi

data 𝕌 : Set
⟦_⟧ : (A : 𝕌) → Set
data _⟷_ : 𝕌 → 𝕌 → Set
eval : {A B : 𝕌} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧

data 𝕌 where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌

⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

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

!_ : {A B : 𝕌} → A ⟷ B → B ⟷ A
! unite₊l = uniti₊l
! uniti₊l = unite₊l
! unite₊r = uniti₊r
! uniti₊r = unite₊r
! swap₊ = swap₊
! assocl₊ = assocr₊
! assocr₊ = assocl₊
! unite⋆l = uniti⋆l
! uniti⋆l = unite⋆l
! unite⋆r = uniti⋆r
! uniti⋆r = unite⋆r
! swap⋆ = swap⋆
! assocl⋆ = assocr⋆
! assocr⋆ = assocl⋆
! absorbr = factorzl
! absorbl = factorzr
! factorzr = absorbl
! factorzl = absorbr
! dist = factor
! factor = dist
! distl = factorl
! factorl = distl
! id⟷ = id⟷
! (c₁ ⊚ c₂) = (! c₂) ⊚ (! c₁)
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)

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

ΠisRev : ∀ {A B} → (c : A ⟷ B) (a : ⟦ A ⟧) → eval (c ⊚ ! c) a ≡ a
ΠisRev unite₊l (inj₂ y) = refl
ΠisRev uniti₊l a = refl
ΠisRev unite₊r (inj₁ x) = refl
ΠisRev uniti₊r a = refl
ΠisRev swap₊ (inj₁ x) = refl
ΠisRev swap₊ (inj₂ y) = refl
ΠisRev assocl₊ (inj₁ x) = refl
ΠisRev assocl₊ (inj₂ (inj₁ x)) = refl
ΠisRev assocl₊ (inj₂ (inj₂ y)) = refl
ΠisRev assocr₊ (inj₁ (inj₁ x)) = refl
ΠisRev assocr₊ (inj₁ (inj₂ y)) = refl
ΠisRev assocr₊ (inj₂ y) = refl
ΠisRev unite⋆l (tt , y) = refl
ΠisRev uniti⋆l a = refl
ΠisRev unite⋆r (x , tt) = refl
ΠisRev uniti⋆r a = refl
ΠisRev swap⋆ (x , y) = refl
ΠisRev assocl⋆ (x , (y , z)) = refl
ΠisRev assocr⋆ ((x , y) , z) = refl
ΠisRev dist (inj₁ x , z) = refl
ΠisRev dist (inj₂ y , z) = refl
ΠisRev factor (inj₁ (x , z)) = refl
ΠisRev factor (inj₂ (y , z)) = refl
ΠisRev distl (x , inj₁ y) = refl
ΠisRev distl (x , inj₂ z) = refl
ΠisRev factorl (inj₁ (x , y)) = refl
ΠisRev factorl (inj₂ (x , z)) = refl
ΠisRev id⟷ a = refl
ΠisRev (c₁ ⊚ c₂) a rewrite ΠisRev c₂ (eval c₁ a) = ΠisRev c₁ a
ΠisRev (c₁ ⊕ c₂) (inj₁ x) rewrite ΠisRev c₁ x = refl
ΠisRev (c₁ ⊕ c₂) (inj₂ y) rewrite ΠisRev c₂ y = refl
ΠisRev (c₁ ⊗ c₂) (x , y) rewrite ΠisRev c₁ x | ΠisRev c₂ y = refl

------------------------------------------------------------------------------
-- Pointed types and singleton types
\end{code}}
\newcommand{\PIPFUdef}{%
\begin{code}
Singleton : (A : Set) → (v : A) → Set
Singleton A v = ∃ (λ ● → v ≡ ●)

Recip : (A : Set) → (v : A) → Set
Recip A v = Singleton A v → ⊤

data ∙𝕌 : Set where
  _#_     : (t : 𝕌) → (v : ⟦ t ⟧) → ∙𝕌
  _∙×ᵤ_   : ∙𝕌 → ∙𝕌 → ∙𝕌
  ❰_❱     : ∙𝕌 → ∙𝕌
  ∙𝟙/     : ∙𝕌 → ∙𝕌

∙⟦_⟧ : ∙𝕌 → Σ[ A ∈ Set ] A
∙⟦ t # v ⟧       = ⟦ t ⟧ , v
∙⟦ T₁ ∙×ᵤ T₂ ⟧   = zip _×_ _,_ ∙⟦ T₁ ⟧ ∙⟦ T₂ ⟧
∙⟦ ❰ T ❱ ⟧       = let (t , v) = ∙⟦ T ⟧ in Singleton t v , (v , refl)
∙⟦ ∙𝟙/ T ⟧       = let (t , v) = ∙⟦ T ⟧ in Recip t v , λ _ → tt
\end{code}}
\newcommand{\PIPFonelift}{% Not used
\begin{code}
∙𝟙 : ∙𝕌
∙𝟙 = 𝟙 # tt
\end{code}}
\newcommand{\PIPFCombDef}{%
\begin{code}
data _∙⟶_ : ∙𝕌 → ∙𝕌 → Set where
  -- lifting from plain Π
  ∙c       :  {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} →
              (c : t₁ ⟷ t₂) → t₁ # v ∙⟶ t₂ # (eval c v)
  ∙times#  :  {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
              ((t₁ ×ᵤ t₂) # (v₁ , v₂)) ∙⟶ ((t₁ # v₁) ∙×ᵤ (t₂ # v₂))
  ∙#times  :  {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
              ((t₁ # v₁) ∙×ᵤ (t₂ # v₂)) ∙⟶ ((t₁ ×ᵤ t₂) # (v₁ , v₂))
  -- multiplicative structure (omitted)
  -- monad / comonad
  return   : (T : ∙𝕌) → T ∙⟶ ❰ T ❱
  extract  : (T : ∙𝕌) → ❰ T ❱ ∙⟶ T
  -- eta/epsilon
  η  :  (T : ∙𝕌) → ∙𝟙 ∙⟶ ❰ T ❱ ∙×ᵤ ∙𝟙/ T
  ε  :  (T : ∙𝕌) → ❰ T ❱ ∙×ᵤ ∙𝟙/ T ∙⟶ ∙𝟙
\end{code}}
\newcommand{\PIPFCombDefrest}{% Not used
\begin{code}
  ∙id⟷      :  {T : ∙𝕌} → T ∙⟶ T
  _∙⊚_      :  {T₁ T₂ T₃ : ∙𝕌} →
               (T₁ ∙⟶ T₂) → (T₂ ∙⟶ T₃) → (T₁ ∙⟶ T₃)
  ∙unite⋆l  :  {T : ∙𝕌} → ∙𝟙 ∙×ᵤ T ∙⟶ T
  ∙uniti⋆l  :  {T : ∙𝕌} → T ∙⟶ ∙𝟙 ∙×ᵤ T
  ∙unite⋆r  :  {T : ∙𝕌} → T ∙×ᵤ ∙𝟙 ∙⟶ T
  ∙uniti⋆r  :  {T : ∙𝕌} → T ∙⟶ T ∙×ᵤ ∙𝟙
  ∙swap⋆    :  {T₁ T₂ : ∙𝕌} → T₁ ∙×ᵤ T₂ ∙⟶ T₂ ∙×ᵤ T₁
  ∙assocl⋆  :  {T₁ T₂ T₃ : ∙𝕌} →
               T₁ ∙×ᵤ (T₂ ∙×ᵤ T₃) ∙⟶ (T₁ ∙×ᵤ T₂) ∙×ᵤ T₃
  ∙assocr⋆  :  {T₁ T₂ T₃ : ∙𝕌} →
               (T₁ ∙×ᵤ T₂) ∙×ᵤ T₃ ∙⟶ T₁ ∙×ᵤ (T₂ ∙×ᵤ T₃)
  _∙⊗_      :  {T₁ T₂ T₃ T₄ : ∙𝕌} → (T₁ ∙⟶ T₃) → (T₂ ∙⟶ T₄) →
               (T₁ ∙×ᵤ T₂ ∙⟶ T₃ ∙×ᵤ T₄)
\end{code}}
\newcommand{\PIPFCombderive}{%
\begin{code}
∙Singᵤ : {T₁ T₂ : ∙𝕌} → (T₁ ∙⟶ T₂) → ❰ T₁ ❱ ∙⟶ ❰ T₂ ❱
∙Singᵤ {T₁} {T₂} c = extract T₁ ∙⊚ c ∙⊚ return T₂

tensor : {T₁ T₂ : ∙𝕌} → ❰ T₁ ❱ ∙×ᵤ ❰ T₂ ❱ ∙⟶ ❰ T₁ ∙×ᵤ T₂ ❱
tensor {T₁} {T₂} = (extract T₁ ∙⊗ extract T₂) ∙⊚ return (T₁ ∙×ᵤ T₂)

cotensor : {T₁ T₂ : ∙𝕌} → ❰ T₁ ∙×ᵤ T₂ ❱ ∙⟶ ❰ T₁ ❱ ∙×ᵤ ❰ T₂ ❱
cotensor {T₁} {T₂} = extract (T₁ ∙×ᵤ T₂) ∙⊚ (return T₁ ∙⊗ return T₂)

join : {T₁ : ∙𝕌} →  ❰ ❰ T₁ ❱ ❱ ∙⟶ ❰ T₁ ❱
join {T₁} = extract ❰ T₁ ❱

duplicate : {T₁ : ∙𝕌} → ❰ T₁ ❱ ∙⟶ ❰ ❰ T₁ ❱ ❱
duplicate {T₁} = return ❰ T₁ ❱
\end{code}}

\newcommand{\PIPFCombderivedefs}{% Not used
\begin{code}
tensorl : {T₁ T₂ : ∙𝕌} → (❰ T₁ ❱ ∙×ᵤ T₂) ∙⟶  ❰ (T₁ ∙×ᵤ T₂) ❱
tensorl {T₁} {T₂} = (extract T₁ ∙⊗ ∙id⟷) ∙⊚ return (T₁ ∙×ᵤ T₂)

tensorr : {T₁ T₂ : ∙𝕌} → (T₁ ∙×ᵤ ❰ T₂ ❱) ∙⟶  ❰ (T₁ ∙×ᵤ T₂) ❱
tensorr {T₁} {T₂} = (∙id⟷ ∙⊗ extract T₂) ∙⊚ return (T₁ ∙×ᵤ T₂)

cotensorl : {T₁ T₂ : ∙𝕌} →  ❰ (T₁ ∙×ᵤ T₂) ❱ ∙⟶ (❰ T₁ ❱ ∙×ᵤ T₂)
cotensorl {T₁} {T₂} = extract (T₁ ∙×ᵤ T₂) ∙⊚ (return T₁ ∙⊗ ∙id⟷)

cotensorr : {T₁ T₂ : ∙𝕌} →  ❰ (T₁ ∙×ᵤ T₂) ❱ ∙⟶ (T₁ ∙×ᵤ ❰ T₂ ❱)
cotensorr {T₁} {T₂} = extract (T₁ ∙×ᵤ T₂) ∙⊚ (∙id⟷ ∙⊗ return T₂)



\end{code}}

\newcommand{\PIPFrev}{%
\begin{code}
!∙_ : {A B : ∙𝕌} → A ∙⟶ B → B ∙⟶ A
\end{code}}

\newcommand{\PIPFrevrest}{% Not used
\begin{code}
!∙ (∙c {t₁} {t₂} {v} c) =
  subst (λ x → t₂ # eval c v ∙⟶ t₁ # x) (ΠisRev c v) (∙c (! c))
!∙ ∙times# = ∙#times
!∙ ∙#times = ∙times#
!∙ ∙id⟷ = ∙id⟷
!∙ (c₁ ∙⊚ c₂) = (!∙ c₂) ∙⊚ (!∙ c₁)
!∙ ∙unite⋆l = ∙uniti⋆l
!∙ ∙uniti⋆l = ∙unite⋆l
!∙ ∙unite⋆r = ∙uniti⋆r
!∙ ∙uniti⋆r = ∙unite⋆r
!∙ ∙swap⋆ = ∙swap⋆
!∙ ∙assocl⋆ = ∙assocr⋆
!∙ ∙assocr⋆ = ∙assocl⋆
!∙ (c₁ ∙⊗ c₂) = (!∙ c₁) ∙⊗ (!∙ c₂)
!∙ return T = extract T
!∙ extract T = return T
!∙ η T = ε T
!∙ ε T = η T
\end{code}}

\newcommand{\PIPFeval}{% Not used
\begin{code}
∙eval : {T₁ T₂ : ∙𝕌} → (C : T₁ ∙⟶ T₂) →
  let (t₁ , v₁) = ∙⟦ T₁ ⟧; (t₂ , v₂) = ∙⟦ T₂ ⟧
  in Σ (t₁ → t₂) (λ f → f v₁ ≡ v₂)
\end{code}}

\newcommand{\PIPFevalrest}{% Not used
\begin{code}
∙eval ∙id⟷ = (λ x → x) , refl
∙eval (∙c c) = eval c , refl
∙eval (C₁ ∙⊚ C₂) with ∙eval C₁ | ∙eval C₂
... | (f , p) | (g , q) = (λ x → g (f x)) , trans (cong g p) q
∙eval ∙unite⋆l = (λ {(tt , x) → x}) , refl
∙eval ∙uniti⋆l = (λ {x → (tt , x)}) , refl
∙eval ∙unite⋆r = (λ {(x , tt) → x}) , refl
∙eval ∙uniti⋆r = (λ {x → (x , tt)}) , refl
∙eval ∙swap⋆ = (λ {(x , y) → y , x}) , refl
∙eval ∙assocl⋆ = (λ {(x , (y , z)) → ((x , y) , z)}) , refl
∙eval ∙assocr⋆ = (λ {((x , y) , z) → (x , (y , z))}) , refl
∙eval (C₀ ∙⊗ C₁) with ∙eval C₀ | ∙eval C₁
... | (f , p) | (g , q) = (λ {(t₁ , t₂) → f t₁ , g t₂}) , cong₂ _,_ p q
∙eval ∙times# = (λ x → x) , refl
∙eval ∙#times = (λ x → x) , refl
∙eval (return T) = (λ _ → proj₂ ∙⟦ T ⟧ , refl) , refl
∙eval (extract T) = (λ {(w , refl) → w}) , refl
∙eval (η T) = (λ tt → (proj₂ ∙⟦ T ⟧ , refl) , λ _ → tt) , refl
∙eval (ε T) = (λ { ((_ , refl) , f) → f (proj₂ ∙⟦ T ⟧ , refl)}) , refl
\end{code}}

\newcommand{\PIPFrevrev}{%
\begin{code}
revrev : {A : ∙𝕌} → ∙𝟙/ (∙𝟙/ A) ∙⟶ ❰ A ❱
revrev {A} =
  ∙uniti⋆l ∙⊚
  (η A ∙⊗ ∙id⟷) ∙⊚
  ((∙id⟷ ∙⊗ return (∙𝟙/ A)) ∙⊗ ∙id⟷) ∙⊚
  ∙assocr⋆ ∙⊚
  ∙id⟷ ∙⊗ ε (∙𝟙/ A) ∙⊚
  ∙unite⋆r
\end{code}}
