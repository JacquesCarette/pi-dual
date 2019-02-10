\documentclass[a4paper]{article}
\usepackage{graphicx}
\usepackage{onecolceurws}

\usepackage[LGR,TS1,T1]{fontenc}
\usepackage{agda}
\usepackage{ucs}
\usepackage{lmodern}
\usepackage{textgreek}  -- for some of the greek characters in text
\usepackage[utf8x]{inputenc}
\usepackage{comment}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Some needed unicode characters

% Convenient abbreviations
\newcommand{\AIC}[1]{\AgdaInductiveConstructor{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Comments

\newif\ifcomments\commentstrue

\ifcomments
\newcommand{\authornote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\else
\newcommand{\authornote}[3]{}
\newcommand{\todo}[1]{}
\fi

%% \newcommand{\amr}[1]{}
%% \newcommand{\jc}[1]{}

\newcommand{\jc}[1]{\authornote{purple}{JC}{#1}}
\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.9\textwidth}\color{red}{Amr says: {#1}}\end{minipage}}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; trans; refl)
open import Function using (id)

open import Equiv
open import TypeEquiv
\end{code}
}
\section{Introduction}

The inspiration for this paper comes from a number of sources:
\begin{enumerate}
  \item Oleg Grenrus' \textit{Finding correct (lens) laws}~\cite{oleg-blog},
  \item The paper \textit{Synthesizing Bijective Lenses}~\cite{Miltner2018},
  \item Twan van Laarhoven's blog \textit{Isomorphism Lenses},
  \item (many more, insert citations throughout)
\end{enumerate}

There are many, many different representations for (monomorphic)
very well behaved lenses. One of the first are the \emph{get-set lenses}:
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

To do this, we must somehow hide our choice of $C$.  We can
re-use a well-known trick from Haskell%
\footnote{but be wary that this does not generalize to more
constructors, as Agda can still see that the non-public constructors
are still injective; see Martin Escardo's counter-example at
\cite{XXX}}, where we build a data type
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
Locally, we will have a means to reveal, but again, this will not
be exported.
\begin{code}
  private
    unbox : {ℓc : Level} → Hidden {ℓc} → Set ℓc
    unbox (box x) = x
\end{code}
Again, later, we will need to be able to take products and sums
of hidden types, thus we need to provide such features now. In fact,
may as well provide a lift function to do so:
\begin{code}
  lift-to-hidden : {ℓa ℓb : Level} → (op : Set ℓa → Set ℓb → Set (ℓa ⊔ ℓb)) →
    Hidden {ℓa} → Hidden {ℓb} → Hidden {ℓa ⊔ ℓb}
  lift-to-hidden (_**_) (box A) (box B) = box (A ** B)

  _×h_ : {ℓa ℓb : Level} → Hidden {ℓa} → Hidden {ℓb} → Hidden {ℓa ⊔ ℓb}
  _×h_ = lift-to-hidden _×_
  _⊎h_ : {ℓa ℓb : Level} → Hidden {ℓa} → Hidden {ℓb} → Hidden {ℓa ⊔ ℓb}
  _⊎h_ = lift-to-hidden _⊎_
\end{code}
\jc{Do it in an appendix?}
Furthermore, we need to know that these induce equivalences. If we can
reveal the indirection, this is indeed trivial:
\begin{code}
  ×h-equiv : {ℓa ℓb : Level} {A : Hidden {ℓa}} {B : Hidden {ℓb}} →
    (unbox A × unbox B) ≃ unbox (A ×h B)
  ×h-equiv {A = box A} {B = box B} = id≃
\end{code}
Given this infrastructure, we can build a record with two
parts, one hidden and another which is visible. For simplicity,
we'll assume everything is at the same level.  This will form
the core of our implementation of Lens based on isomorphisms.

\begin{code}
  record ∃-Lens {ℓ : Level} (S : Set ℓ) (A : Set ℓ) : Set (suc ℓ) where
    field
      HC : Hidden {ℓ}
    private
      C : Set ℓ
      C = unbox HC
    field
      iso : S ≃ (C × A)

  ∃-lens : {ℓ : Level} {S A : Set ℓ} (C : Set ℓ) → S ≃ (C × A) → ∃-Lens S A
  ∃-lens C iso = record {HC = hide C; iso = iso}
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

The other direction is considerably more challenging. We leave that
to~\ref{sec:lens-equiv}.

What we wish to do is to explore the link betweens lens, especially
in the form of \AgdaRecord{∃-Lens}, and reversible computing.

\section{A typed reversible language}

Intro to Pi. the weak semiring of types. The language Pi.
The interpretation of Pi as a PL, and its denotation as
equivalences. List the equivalences?

\section{Exploring the Lens landscape}

Rather than exploring the most general setting for lenses (as has been done
in many papers), we will instead look inside the implementations. This will
reveal the \emph{inner structure} of lenses, rather than focusing on their
macro structure.

\subsection{Simple Lenses}
Let's explore the simplest lenses first.  For a \AgdaRecord{GS-Lens}, the simplest is
when \AgdaField{get} is the identity, which forces the rest:

\begin{code}
module _ (A B D E : Set) where
  open ∃-Lens

  AA-gs-lens : GS-Lens A A
  AA-gs-lens = record { get = id ; set = λ _ → id
    ; getput = λ _ _ → refl ; putget = λ _ → refl ; putput = λ _ _ _ → refl }
\end{code}

What does that correspond to as a \AgdaRecord{∃-Lens}? Here, we can easily
guess the complement by solving the equation $A ≃ C × A$ for $C$: $C$ must
be $\AgdaSymbol{⊤}$. But then the $∃-Lens$ isn't quite as simple as above:
\begin{code}
  AA-∃-lens : ∃-Lens A A
  AA-∃-lens = ∃-lens ⊤ uniti⋆equiv
\end{code}
\noindent where $\AgdaFunction{uniti⋆equiv}$ has type
$A ≃ (⊤ × A)$. In other words, as the complement is not actually
present in $A$, it must be introduced.

What about in the other direction, what is the \AgdaRecord{∃-Lens} whose
underlying isomorphism is the identity?
\begin{code}
  BAA-∃-lens : ∃-Lens (B × A) A
  BAA-∃-lens = ∃-lens B id≃
\end{code}
\noindent Since our definition of \AgdaRecord{∃-Lens} is right-biased
(we are looking for isomorphisms of shape $S ≃ C × A$), the above lens
extracts the $A$ on the right.  Of course, there is another lens which
switches the roles of $A$ and $B$ --- and this leaves a trace on the
isomorphism:
\begin{code}
  BAB-∃-lens : ∃-Lens (B × A) B
  BAB-∃-lens = ∃-lens A swap⋆equiv
\end{code}

Thus, looking at the Π combinators, which ones return a type
of shape $C × A$ ?  We have already seen \AIC{uniti⋆l},
\AIC{id⟷} and \AIC{swap⋆} arise. That leaves four:
\AIC{assocl⋆}, \AIC{factorzl}, \AIC{factor} and \AIC{⊗}.
These occur as follows (where we use the \AIC{equiv} version
directly):
\begin{code}
  DBA-lens : ∃-Lens (D × (B × A)) A
  DBA-lens = ∃-lens (D × B) assocl⋆equiv

  ⊥-lens : ∃-Lens ⊥ A
  ⊥-lens = ∃-lens ⊥ factorzequiv

  ⊎-lens : ∃-Lens ((D × A) ⊎ (B × A)) A
  ⊎-lens = ∃-lens (D ⊎ B) factorequiv

  ⊗-lens : (E ≃ B) → (D ≃ A) → ∃-Lens (E × D) A
  ⊗-lens iso₁ iso₂ = ∃-lens B (iso₁ ×≃ iso₂)
\end{code}

\jc{comment on each? Also, give an example of composition?}

These last two are intriguing indeed, and really give us a strong
sense that lenses are more than just conveniences for records! In
particular, it is possible to create lenses for things which are
not ``in'' a type at all.

Before we see an example of lensing onto a non-existent component,
we should complete the picture of lifting Π to lenses, and we're
missing composition:
\begin{code}
  ∘-lens : ∃-Lens D B → ∃-Lens B A → ∃-Lens D A
  ∘-lens l₁ l₂ = record
    { HC = (HC l₁) ×h (HC l₂)
    ; iso = (×h-equiv {A = HC l₁} ×≃ id≃) ● assocl⋆equiv ● (id≃ ×≃ iso l₂) ● iso l₁ }
\end{code}

\subsection{Unusual lenses}

Let's now get back to lensing into a component that is not immediately
present, through a concrete example.  For
completeness, both \AgdaRecord{GS-Lens} and \AgdaRecord{∃-Lens}
will be given.

Let us consider a type \AgdaType{Colour} with exactly $3$ inhabitants,
\begin{code}
module _ {A : Set} where
  data Colour : Set where red green blue : Colour
\end{code}

First, a \AgdaRecord{∃-Lens} built ``by hand'':
\begin{code}
  ∃-Colour-in-A+A+A : ∃-Lens (A ⊎ A ⊎ A) Colour
  ∃-Colour-in-A+A+A = ∃-lens A eq
   where
    f : A ⊎ A ⊎ A → A × Colour
    f (inj₁ x) = x , red
    f (inj₂ (inj₁ x)) = x , green
    f (inj₂ (inj₂ x)) = x , blue
    g : A × Colour → A ⊎ A ⊎ A
    g (a , red) = inj₁ a
    g (a , green) = inj₂ (inj₁ a)
    g (a , blue) = inj₂ (inj₂ a)
    eq : (A ⊎ A ⊎ A) ≃ (A × Colour)
    eq = f , qinv g (λ { (a , red) → refl ; (a , green) → refl ; (a , blue) → refl})
                    λ { (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl}
\end{code}
The equivalence is not too painful to establish. We will return to this.  But let's do
the same for the \AgdaType{GS-Lens}:
\begin{code}
  GS-Colour-in-A+A+A : GS-Lens (A ⊎ A ⊎ A) Colour
  GS-Colour-in-A+A+A = record
    { get = λ { (inj₁ x) → red ; (inj₂ (inj₁ x)) → green ; (inj₂ (inj₂ y)) → blue}
    ; set = λ { (inj₁ x) red → inj₁ x ; (inj₁ x) green → inj₂ (inj₁ x) ; (inj₁ x) blue → inj₂ (inj₂ x)
              ; (inj₂ (inj₁ x)) red → inj₁ x ; (inj₂ (inj₁ x)) green → inj₂ (inj₁ x) ; (inj₂ (inj₁ x)) blue → inj₂ (inj₂ x)
              ; (inj₂ (inj₂ y)) red → inj₁ y ; (inj₂ (inj₂ y)) green → inj₂ (inj₁ y) ; (inj₂ (inj₂ y)) blue → inj₂ (inj₂ y)}
    ; getput = λ { (inj₁ x) red → refl ; (inj₁ x) green → refl ; (inj₁ x) blue → refl
                 ; (inj₂ (inj₁ x)) red → refl ; (inj₂ (inj₁ x)) green → refl ; (inj₂ (inj₁ x)) blue → refl
                 ; (inj₂ (inj₂ y)) red → refl ; (inj₂ (inj₂ y)) green → refl ; (inj₂ (inj₂ y)) blue → refl}
    ; putget = λ { (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl}
    ; putput = λ { (inj₁ x) red red → refl ; (inj₁ x) green red → refl ; (inj₁ x) blue red → refl
                 ; (inj₁ x) red green → refl ; (inj₁ x) green green → refl ; (inj₁ x) blue green → refl
                 ; (inj₁ x) red blue → refl ; (inj₁ x) green blue → refl ; (inj₁ x) blue blue → refl

                 ; (inj₂ (inj₁ x)) red red → refl ; (inj₂ (inj₁ x)) green red → refl ; (inj₂ (inj₁ x)) blue red → refl
                 ; (inj₂ (inj₁ x)) red green → refl ; (inj₂ (inj₁ x)) green green → refl ; (inj₂ (inj₁ x)) blue green → refl
                 ; (inj₂ (inj₁ x)) red blue → refl ; (inj₂ (inj₁ x)) green blue → refl ; (inj₂ (inj₁ x)) blue blue → refl

                 ; (inj₂ (inj₂ y)) red red → refl ; (inj₂ (inj₂ y)) green red → refl ; (inj₂ (inj₂ y)) blue red → refl
                 ; (inj₂ (inj₂ y)) red green → refl ; (inj₂ (inj₂ y)) green green → refl ; (inj₂ (inj₂ y)) blue green → refl
                 ; (inj₂ (inj₂ y)) red blue → refl ; (inj₂ (inj₂ y)) green blue → refl ; (inj₂ (inj₂ y)) blue blue → refl}
    }
\end{code}

Note how the \AgdaRecord{∃-Lens} is linear in the size of the enumerated type, including
the proofs whilst \AgdaRecord{GS-Lens} is quadratic for the function size, and cubic in
the proof size!

But the deeper points is that $A ⊎ A ⊎ A$ does not ``contain'' a \AgdaSymbol{Colour},
and yet we can create a lens to get and set it.  The \AgdaRecord{GS-Lens} view makes this
quite mysterious but, in our opinion, the \AgdaRecord{∃-Lens} makes it clear that any
type that we can see \emph{up to isomorphism} can be focused on.

In a way, a ``better'' explanation of \AgdaRecord{∃-Colour-in-A+A+A} is to remark
that the types $⊤ ⊎ ⊤ ⊎ ⊤$ (which we'll call 𝟛) and \AgdaRecord{Colour} are isomorphic,
which leads to the chains of isomorphisms $A ⊎ A ⊎ A ≃ A × 𝟛 ≃ A × \AgdaRecord{Colour}$.

An interesting interpretation of that isomorphism is that we can freely move tagging
of data $A$ with \textit{finite information} between type-level tags and value-level
tags at will.

\section{More Optics}

Prisms just use ⊎ instead of ×. Other optics are similar (but not all).
The same things arise.
Affine is $∃C, D. S ≃ D ⊎ C × A$.
Achroma is $∃C. S ≃ ⊤ ⊎ C × A$.
Grate is $∃I. S ≃ I → A$, which isn't included in $Π$.
Setter is $∃ F : Set → Set. S ≃ F A$, which is even further off.

What about $∃C. S ≃ (⊤ ⊎ C) × A$ ?

Note that factor/distrib is crucial to move between them all.

\section{Optic transformations}

Level 2 of $Π$ lets us look at relations between isomorphisms.
In particular, we can see when some lens/prims/etc are simplifiable
to something simpler.

\section{Proof of equivalence}\label{sec:lens-equiv}

Finish the proof that was started earlier.  \jc{Or skip it entirely and
refer to Oleg's gist?}
One method
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

\section{Geometry of types}

Lens is a cartesian factoring.  Prism is a partition.

Note that we should really view $S$ as a sort of curve 2-dimensional type, while
$C × A$ is our cartesian, 2-dimensional version. $C$ doesn't depend on $A$, which is
why the name \emph{constant complement} is quite apt.  A Lens is a change of coordinates
that allows one to see $A$ as a cartesian projection. Similarly, a Prism is a
change of coordinates that shuffles all of $A$ ``to the right''.

\jc{What are the other optics?}

\section{Discussion}

So why all the complications with \texttt{Profunctor}? Basically, that is mostly
Haskell-isms: by relying on \emph{Free Theorems}, one can get the type system to
reject a lot of ill-formed lenses, though, of course, not all. Optics, in Agda and
using equivalences turn out to be \emph{simpler}, not harder!

Another thread is via the Yoneda lemma. Of course, one can see this here too:
the existentials correspond to a co-end, and the isomorphisms are exactly what is
in the Hom-set. But we get more mileage from looking ``under the hood'' to see
the fundamental \textbf{programming language} underlying Optics, rather than jumping
to abstractions too early.

\section{Conclusion}

\bibliographystyle{alpha}
\bibliography{cites}
%inline the .bbl file directly for mailing to authors.

\end{document}
