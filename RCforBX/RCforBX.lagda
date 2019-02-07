\documentclass[a4paper]{article}
\usepackage{graphicx}
\usepackage{onecolceurws}

\usepackage{agda}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}

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
open import Data.Unit
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; trans; refl)
open import Function using (id)
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
    getput : (s : S) (a : A) → get (set s a) ≡ a
    putget : (s : S) → set s (get s) ≡ s
    putput : (s : S) (a a' : A) → set (set s a) a' ≡ set s a'
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
a $\AgdaRecord{∃-Lens}$, we can build a \AgdaRecord{GS-Lens}:
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

But before going down that path, let's see what happens.  Of course,
what we want to do is to manufacture the correct constant complement.
But we don't really know how.  Let us try a proxy: $S$ itself.

Roughly speaking the forward part of the isomorphism is forced:
given an $s:S$, there is only one way to get an $A$, and that is
via \AgdaFunction{get}. To get an $S$ back, there are two choices:
either use $s$ itself, or call \AgdaFunction{set}; the choice is
irrelevant (because of the laws). In the backwards direction,
the laws help in narrowing down the choices: basically, we want the
$s′ : S$ where $\AgdaFunction{get s′} ≡ a$, and so we again
use \AgdaFunction{set} for the purpose:
\begin{code}
complete : {ℓ : Level} {S A : Set ℓ} → GS-Lens S A → ∃-Lens S A
complete {ℓ} {S} {A} record { get = get ; set = set ; getput = getput ; putget = putget ; putput = putput } =
  record { HC = hide S
         ; iso = (λ s → s , get s) ,
                 qinv (λ { (s , a) → set s a })
                      (λ { (s , a) → cong₂ _,_ hole (getput s a)})
                       λ s → putget s }
\end{code}
That almost gets us there. The one whole we can't fill is one that says
\begin{code}
    where
      hole : {s : S} {a : A} → set s a ≡ s
      hole = {!!}
\end{code}
But that will only ever happen if $\AgdaFunction{get s}$ was already $a$ (by
\AgdaField{putget}).

Of course, we already knew this would happen: $S$ is too big. Basically, it is
too big by exactly the inverse image of $A$ by \AgdaFunction{get}.

Thus our next move is to make that part of $S$ not matter. In other words,
rather than using the \emph{type} $S$ as a proxy, we want to use a
\AgdaRecord{Setoid} where $s, t : S$ will be regarded as the same if they
only differ in their $A$ component.

\section{Exploring the Lens landscape}

Let's explore the simplest lenses first.  For a \AgdaRecord{GS-Lens}, the simplest is
when \AgdaField{get} is the identity, which forces the rest:

\begin{code}
module _ {ℓ : Level} (A : Set ℓ) where
  AA-gs-lens : GS-Lens A A
  AA-gs-lens = record { get = id ; set = λ _ → id
    ; getput = λ _ _ → refl ; putget = λ _ → refl ; putput = λ _ _ _ → refl }
\end{code}

What does that correspond to as a \AgdaRecord{∃-Lens}? Here, we can easily
guess the complement by solving the equation $A ≃ C × A$ for $C$: $C$ must
be $\AgdaSymbol{⊤}$. But then the $∃-Lens$ isn't quite as simple as above:
\begin{code}
  AA-∃-lens : ∃-Lens A A
  AA-∃-lens = record { HC = hide (Lift {zero} {ℓ} ⊤)
    ; iso = (λ a → (lift tt) , a) , qinv proj₂ (λ { ( (lift tt) , a) → refl}) λ _ → refl }
\end{code}

(The above is the 'wrong' way to go about telling the story!  I was trying to do
this without introducing Pi quite yet, but that's just going to make things harder than
needed.  So let's dive in, introduce Pi, and explore next.)


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

\section{Proof of equivalence}

Finish the proof that was started earlier.

\section{Conclusion}

\bibliographystyle{alpha}
\bibliography{cites}
%inline the .bbl file directly for mailing to authors.

\end{document}
