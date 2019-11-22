\newcommand{\PPFTone}{%
\begin{code}
{-# OPTIONS --without-K --safe #-}

-- Pi combinators inspired by duals and traced monoidal categories

module PiPointedFracTraceCode where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import PiPointedFracCode

\end{code}}

\newcommand{\PPFTname}{%
\begin{code}
dual : {A B : ∙𝕌} → (f : A ∙⟶ B) →  (∙𝟙/ B ∙⟶ ∙𝟙/ A)
dual {A} {B} f =
  ∙uniti⋆l ∙⊚ (η A ∙⊗ ∙id⟷) ∙⊚ ((∙Singᵤ f ∙⊗ ∙id⟷) ∙⊗ ∙id⟷) ∙⊚
  ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ ∙swap⋆) ∙⊚ ∙assocl⋆ ∙⊚ (ε B ∙⊗ ∙id⟷) ∙⊚ ∙unite⋆l

name : {A B : ∙𝕌} → (f : A ∙⟶ B) → ∙𝟙 ∙⟶ ❰ B ❱ ∙×ᵤ ∙𝟙/ A
name {A} {B} f = η A ∙⊚ (∙Singᵤ f ∙⊗ ∙id⟷)

coname : {A B : ∙𝕌} → (f : A ∙⟶ B) → ❰ A ❱ ∙×ᵤ ∙𝟙/ B ∙⟶ ∙𝟙
coname {A} {B} f = (∙Singᵤ f ∙⊗ ∙id⟷) ∙⊚ ε B

\end{code}}

\newcommand{\PPFTmore}{%
\begin{code}

-- Trace terminates!  The type C is pointed with point c; trace uses c
-- as the initial value for C. So f gets two values (a,c). It can do
-- whatever to produce (b',c'). But f is reversible so it is limited
-- to essentially either id or swap. Makes sense???

𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt
\end{code}}


\newcommand{\PPFTtrace}{%
\begin{code}

trace : {A B C : ∙𝕌} → (f : A ∙×ᵤ C ∙⟶ B ∙×ᵤ C) → A ∙⟶ B
trace {A} {B} {C} f =
  ∙uniti⋆r ∙⊚
  (return _ ∙⊗ η C) ∙⊚
  ∙assocl⋆ ∙⊚         
  (tensor ∙⊗ ∙id⟷) ∙⊚
  (∙Singᵤ f ∙⊗ ∙id⟷) ∙⊚
  (cotensor ∙⊗ ∙id⟷) ∙⊚
  ∙assocr⋆ ∙⊚          
  (extract _ ∙⊗ ε C) ∙⊚
  ∙unite⋆r

tracex : (A : 𝕌) (v : ⟦ A ⟧) → Σ (⟦ A ⟧ → ⟦ A ⟧) (λ f → f v ≡ v)
tracex A v = ∙eval (trace {A # v} ∙swap⋆)

-- Example in Sec. 4.3 from Abramsky's paper
-- http://www.cs.ox.ac.uk/files/341/calco05.pdf
∙q : {A1 A2 A3 A4 B1 B2 B3 B4 : ∙𝕌}
   → (f1 : A1 ∙⟶ B2)
   → (f2 : A2 ∙⟶ B4)
   → (f3 : A3 ∙⟶ B3)
   → (f4 : A4 ∙⟶ B1)
   → A1 ∙×ᵤ (A2 ∙×ᵤ (A3 ∙×ᵤ A4)) ∙⟶ B1 ∙×ᵤ (B2 ∙×ᵤ (B3 ∙×ᵤ B4))
∙q {A1} {A2} {A3} {A4} {B1} {B2} {B3} {B4} f1 f2 f3 f4 =
   (f1 ∙⊗ (f2 ∙⊗ (f3 ∙⊗ f4))) ∙⊚
   ∙assocl⋆ ∙⊚
   ∙swap⋆ ∙⊚
   ∙swap⋆ ∙⊗ ∙id⟷ ∙⊚
   ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ ∙assocl⋆) ∙⊚
   ∙id⟷ ∙⊗ (∙swap⋆ ∙⊗ ∙id⟷ ∙⊚ ∙assocr⋆)

∙q' : {A1 U2 U3 U4 B1 : ∙𝕌}
    → (f1 : A1 ∙⟶ U2)
    → (f2 : U2 ∙⟶ U4)
    → (f3 : U3 ∙⟶ U3)
    → (f4 : U4 ∙⟶ B1)
    → A1 ∙⟶ B1
∙q' f1 f2 f3 f4 = trace (∙q f1 f2 f3 f4)

\end{code}}

\newcommand{\PPFTtracemore}{%
\begin{code}


zz3 : (A : 𝕌) (v : ⟦ A ⟧) (T : ∙𝕌) → Σ (⟦ A ⟧ → ⟦ A ⟧) (λ f → f v ≡ v)
zz3 A v T = ∙eval (trace {A # v} {_} {T} ∙id⟷)

-- There are more thing you can put in trace as long as c is the fixpoint
NOT : 𝔹 ⟷ 𝔹
NOT = swap₊

CONTROLLED : {A : 𝕌} → (A ⟷ A) → 𝔹 ×ᵤ A ⟷ 𝔹 ×ᵤ A
CONTROLLED c = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ c)) ⊚ factor

CNOT : 𝔹 ×ᵤ 𝔹 ⟷ 𝔹 ×ᵤ 𝔹
CNOT = CONTROLLED NOT

ex1 : ∀ {b} → 𝔹 # b ∙⟶ 𝔹 # b
ex1 = trace {C = 𝔹 # 𝔽} (∙swap⋆ ∙⊚ ∙#times ∙⊚ ∙c CNOT ∙⊚ ∙times# ∙⊚ ∙swap⋆)

\end{code}}

\newcommand{\PPFThof}{%
\begin{code}
_⊸_ : (A B : ∙𝕌) → ∙𝕌
A ⊸ B = ∙𝟙/ A ∙×ᵤ ❰ B ❱

id⊸ : {A : ∙𝕌} → (A ⊸ A) ∙⟶ ∙𝟙
id⊸ {A} = ∙swap⋆ ∙⊚ ε A

comp⊸ : (A B C : ∙𝕌) → (A ⊸ B) ∙×ᵤ (B ⊸ C) ∙⟶ (A ⊸ C)
comp⊸ A B C = ∙assocr⋆ ∙⊚
              ∙id⟷ ∙⊗ ∙assocl⋆ ∙⊚
              ∙id⟷ ∙⊗ (ε B ∙⊗ ∙id⟷) ∙⊚
              ∙id⟷ ∙⊗ ∙unite⋆l

app : (A B : ∙𝕌) → (A ⊸ B) ∙×ᵤ ❰ A ❱ ∙⟶ ❰ B ❱
app A B = ∙swap⋆ ∙⊗ ∙id⟷ ∙⊚
          ∙assocr⋆ ∙⊚ (∙id⟷ ∙⊗ (∙swap⋆ ∙⊚ ε A)) ∙⊚
          ∙unite⋆r

dist×/ : {A B C D : ∙𝕌} → (A ⊸ B) ∙×ᵤ (C ⊸ D) ∙⟶ ((A ∙×ᵤ C) ⊸ (B ∙×ᵤ D))
rev× : {A B : ∙𝕌} → (A ⊸ ∙𝟙) ∙×ᵤ (B ⊸ ∙𝟙) ∙⟶ (A ∙×ᵤ B ⊸ ∙𝟙)
-- code omitted

\end{code}}

\newcommand{\PPFTfrac}{%
\begin{code}

dist×/ {A} {B} {C} {D} = ∙assocr⋆ ∙⊚
                         (∙id⟷ ∙⊗ ∙assocl⋆) ∙⊚
                         ∙id⟷ ∙⊗ (∙swap⋆ ∙⊗ ∙id⟷) ∙⊚
                         (∙id⟷ ∙⊗ ∙assocr⋆) ∙⊚ ∙assocl⋆ ∙⊚
                         c ∙⊗ tensor
  where
  c : (∙𝟙/ A ∙×ᵤ ∙𝟙/ C) ∙⟶ ∙𝟙/ (A ∙×ᵤ C)
  c = ∙uniti⋆l ∙⊚
      (η (A ∙×ᵤ C) ∙⊗ ∙id⟷) ∙⊚
      (∙swap⋆ ∙⊗ ∙id⟷) ∙⊚
      ∙assocr⋆ ∙⊚
      (∙id⟷ ∙⊗ (cotensor ∙⊗ ∙id⟷)) ∙⊚
      (∙id⟷ ∙⊗ (∙swap⋆ ∙⊗ ∙id⟷)) ∙⊚
      (∙id⟷ ∙⊗ ∙assocr⋆) ∙⊚
      (∙id⟷ ∙⊗ (∙id⟷ ∙⊗ ∙assocl⋆)) ∙⊚
      (∙id⟷ ∙⊗ (∙id⟷ ∙⊗ ((ε A ∙⊗ ∙id⟷) ∙⊚ ∙unite⋆l))) ∙⊚
      (∙id⟷ ∙⊗ ε C) ∙⊚
      ∙unite⋆r

rev× {A} {B} = dist×/ ∙⊚ (∙id⟷ ∙⊗ ∙Singᵤ ∙unite⋆l)
\end{code}}
