\documentclass[a4paper]{article}
\usepackage{graphicx}
\usepackage{onecolceurws}

% Not the final title!
\title{Reversible Programming for the BX enthusiast}

\author{
Jacques Carette\\ Dept. of Computing and Software\\
        (address) \\ carette@mcmaster.ca
\and
Amr Sabry \\ Computer Science Dept.\\
        (address) \\ sabry@indiana.edu
}

\institution{}

\begin{document}
\maketitle

\begin{abstract}
Show how BX is deeply entertwined with RP already,
so that BX enthusiast should really know all about RP too.
\end{abstract}
\vskip 32pt

\AgdaHide{
\begin{code}
module RCforBX where

open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; trans; refl)
open import Equiv
\end{code}
}
\section{Introduction}

The inspiration for this paper comes from a number of sources:
\begin{enumerate}
  \item Oleg Grenrus' \textit{Finding correct (lens) laws}~\cite{oleg-blog},
  \item The paper \textit{Synthesizing Bijective Lenses}~\cite{Miltner2018},
  \item Twan van Laarhoven's blog \textit{Isomorphism Lenses},
  \item (more?)
\end{enumerate}

There are many, many different representations for (monomorphic)
lenses. One of the first are the \emph{get-set lenses}:
\begin{code}
record GS-Lens {ℓs ℓa : Level} (S : Set ℓs) (A : Set ℓa) : Set (ℓs ⊔ ℓa) where
  field
    get : S → A
    set : S → A → S
    .getput : (s : S) (a : A) → get (set s a) ≡ a
    .putget : (s : S) → set s (get s) ≡ s
    .putput : (s : S) (a a' : A) → set (set s a) a' ≡ set s a'
\end{code}

There are also \emph{constant complement lenses}, informally those
where $\exists C. S ≅ C × A$. If encoded carelessly, these two
notions are not \textit{quite} equivalent. A $\AgdaRecord{GS-Lens}$
does not reveal any sort of complement $C$; so the constant complement
lenses should not either\footnote{unlike an early survey~\cite{survey}
which did not quite explain this gap}.

To do this, we must somehow hide our choice of $C$.  To do this, we
re-use a well-known trick from Haskell, where we build a data type
but do not export its constructor.
\begin{code}
module Hide where
  private
    data ReallyHidden {ℓ : Level} : Set (suc ℓ) where
      box : (C : Set ℓ) → ReallyHidden {ℓ}

  Hidden : {ℓ : Level} → Set (suc ℓ)
  Hidden = ReallyHidden
  hide : {ℓ : Level} → Set ℓ → Hidden
  hide C = box C
\end{code}
Given this infrastructure, we can build a record with two
parts, one hidden and another which is visible. For simplicity,
we'll assume everything is the same level.

\begin{code}
  private
    unbox : {ℓc : Level} → Hidden {ℓc} → Set ℓc
    unbox (box x) = x

  record ∃-Lens {ℓ : Level} (S : Set ℓ) (A : Set ℓ) : Set (suc ℓ) where
    field
      HC : Hidden {ℓ}
    private
      C : Set ℓ
      C = unbox HC
    field
      iso : S ≃ (C × A)

  ∃-lens : {ℓ : Level} (S A C : Set ℓ) → S ≃ (C × A) → ∃-Lens S A
  ∃-lens S A C iso = record {HC = hide C; iso = iso}
\end{code}

This gives us the needed infrastructure.  Let's show that, given
a $\AgdaType{∃-Lens}$, we can build a \AgdaType{GS-Lens}:
\begin{code}
open Hide

sound : {ℓ : Level} {S A : Set ℓ} → ∃-Lens S A → GS-Lens S A
sound record { HC = HC ; iso = (f , qinv g α β) } = record
  { get = λ s → proj₂ (f s)
  ; set = λ s a → g (proj₁ (f s) , a)
  ; getput = λ s a → cong proj₂ (α _)
  ; putget = λ s → β s
  ; putput = λ s a a' → cong g (cong₂ _,_ (cong proj₁ (α _)) refl) }
\end{code}

The other direction is considerably more challenging. One method
involves assuming additional principles --- proof irrelevance and
functional extensionality. But can we do without?

Yes, but doing so requires a detour via \AgdaType{Setoid}.

Paper: bijective lenses, p.5.

\section{Lens and other Optics}

Remember that (A + A + A) ~= 3*A. And that one can lens into the 3
on the right -- so one can lens into it on the left too!
The iso expresses the difference (in languages with proper sum-of-product
types) between implicit tags and explicit tags. On the left, the compiler
chooses how to represent it, on the right, the programmer. But there are
many types that can be ``exploded'' so as to move any discrete portion
to/from tags.

Rememer that the type Lens (A*B*C) (A*C) is inhabited. So is
Lens (A*B*C) (C*A).  Look familiar?

\section{Pi}

Intro to Pi.

\section{Happy together}

Really explore the relationship.

\section{Random thoughts}

What if we took different notions of iso (i.e. contractible or not)
instead of the usual one, would that change things? What about the
effect no the lens laws?

Possibly this should all be done in Agda? Or Haskell? Some PL for sure.

\section{Conclusion}

\bibliographystyle{alpha}
\bibliography{cites}
%inline the .bbl file directly for mailing to authors.

\end{document}
