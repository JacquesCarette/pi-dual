%% \documentclass[a4paper]{article}
\documentclass{article}

\usepackage{graphicx}
\usepackage{onecolceurws}
\usepackage[LGR,TS1,T1]{fontenc}
\usepackage{agda}
\usepackage{lmodern}
\usepackage{textgreek}  %% for some of the greek characters in text
\usepackage[utf8x]{inputenc}
\usepackage{comment}
\usepackage{tikz}
\usepackage{tikz-cd}
\usepackage[nocenter]{qtree}
\usepackage{amssymb,amsthm,amsmath}
\usepackage{fullpage}
\usepackage{url}
\usepackage{multicol}
\usepackage{stmaryrd}
\usepackage{proof}
\usepackage{ucs}

%%

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}

\newcommand{\Gpd}{\ensuremath{\mathsf{Groupoid}}}
\newcommand{\nboxtimes}[2]{\,\,~{^{#1}\boxtimes^{#2}}~\,\,}
\newcommand{\mm}{\texttt{\textminus}}
\newcommand{\pp}{\texttt{+}}

\newcommand{\presumtype}{\uplus}
\newcommand{\preprodtype}{*}
\newcommand{\sumtype}{+}
\newcommand{\prodtype}{\times}
\newcommand{\fin}[1]{\ensuremath{\left[#1\right]}}
\newcommand{\Nat}{\ensuremath{\mathbb{N}}}

\newcommand{\inleft}[1]{\textsf{left}~#1}
\newcommand{\inright}[1]{\textsf{right}~#1}
\newcommand{\cp}[3]{#1\stackrel{#2}{\bullet}#3}
\newcommand{\idt}[3]{#2 \equiv_{#1} #3}
\newcommand{\idrt}[3]{#3 \equiv_{#1} #2}
\newcommand{\refl}[1]{\textsf{refl}~#1}
\newcommand{\alt}{~|~}
\newcommand{\linv}{l!}
\newcommand{\rinv}{r!}
\newcommand{\invinv}{!!}
\newcommand{\assoc}{\circ}
\newcommand{\identlp}{\ensuremath{\mathit{unite}_{\sumtype}\mathit{l}}}
\newcommand{\identrp}{\ensuremath{\mathit{uniti}_{\sumtype}\mathit{l}}}
\newcommand{\identlsp}{\ensuremath{\mathit{unite}_{\sumtype}\mathit{r}}}
\newcommand{\identrsp}{\ensuremath{\mathit{uniti}_{\sumtype}\mathit{r}}}
\newcommand{\swapp}{\ensuremath{\mathit{swap}_{\sumtype}}}
\newcommand{\assoclp}{\ensuremath{\mathit{assocl}_{\sumtype}}}
\newcommand{\assocrp}{\ensuremath{\mathit{assocr}_{\sumtype}}}
\newcommand{\identlt}{\ensuremath{\mathit{unite}_{\prodtype}\mathit{l}}}
\newcommand{\identrt}{\ensuremath{\mathit{uniti}_{\prodtype}\mathit{l}}}
\newcommand{\identlst}{\ensuremath{\mathit{unite}_{\prodtype}\mathit{r}}}
\newcommand{\identrst}{\ensuremath{\mathit{uniti}_{\prodtype}\mathit{r}}}
\newcommand{\swapt}{\ensuremath{\mathit{swap}_{\prodtype}}}
\newcommand{\assoclt}{\ensuremath{\mathit{assocl}_{\prodtype}}}
\newcommand{\assocrt}{\ensuremath{\mathit{assocr}_{\prodtype}}}
\newcommand{\absorbr}{\ensuremath{\mathit{absorbr}}}
\newcommand{\absorbl}{\ensuremath{\mathit{absorbl}}}
\newcommand{\factorzr}{\ensuremath{\mathit{factorzr}}}
\newcommand{\factorzl}{\ensuremath{\mathit{factorzl}}}
\newcommand{\dist}{\ensuremath{\mathit{dist}}}
\newcommand{\factor}{\ensuremath{\mathit{factor}}}
\newcommand{\distl}{\ensuremath{\mathit{distl}}}
\newcommand{\factorl}{\ensuremath{\mathit{factorl}}}
\newcommand{\iso}{\leftrightarrow}
\newcommand{\proves}{\vdash}
\newcommand{\idc}{\mathit{id}\!\!\leftrightarrow}
\newcommand{\Rule}[4]{
\makebox{{\rm #1}
$\displaystyle
\frac{\begin{array}{l}#2 \\\end{array}}
{\begin{array}{l}#3      \\\end{array}}$
 #4}}
\newcommand{\jdg}[3]{#2 \proves_{#1} #3}
\newcommand{\sem}[1]{\ensuremath{\llbracket{#1}\rrbracket}}

% Unicode declarations

%% \DeclareUnicodeCharacter{9678}{\ensuremath{\odot}}
%% \DeclareUnicodeCharacter{9636}{\ensuremath{\Box}}
%% shorten the longarrow
%% \DeclareUnicodeCharacter{10231}{\ensuremath{\leftrightarrow}}

\DeclareUnicodeCharacter{9679}{\ensuremath{\bullet}}

% TIKZ declarations
\tikzstyle{func}=[rectangle,draw,fill=black!20,minimum size=1.9em,
  text width=2.4em, text centered]

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
        McMaster University \\ carette@mcmaster.ca
\and
Amr Sabry \\ Computer Science Dept.\\
        Indiana University \\ sabry@indiana.edu
}

\institution{}

\begin{document}
\maketitle

\begin{abstract}
Bidirectional programming, lenses, prisms, and other optics have connections to reversible programming which have been explored from several perspectives, mostly by attempting to recover bidirectional transformations from unidirectional ones. We offer a novel and foundational perspective in which reversible programming is expressed using “type equivalences.” This perspective offers several advantages: first, it is possible to construct sets of sound and complete type equivalences for certain collections of types; these correspond to canonical optic constructions. Second, using ideas inspired by category theory and homotopy type theory, it is possible to construct sound and complete “equivalences between equivalences” which provide the canonical laws for reasoning about lens and prism equivalences.
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

\section{Lenses}

A \emph{lens} is a structure that mediates between a source $S$ and
view $A$. Typically a lens comes equipped with two functions
$\mathit{get}$ which projects a view from a source, and $\mathit{set}$
which takes a view and reconstructs an appropriate source with that
view. A monomorphic interface for such lenses is shown below,
including the commonly cited laws for the lens to be well-behaved:

\begin{code}
record GS-Lens {ℓs ℓa : Level} (S : Set ℓs) (A : Set ℓa) : Set (ℓs ⊔ ℓa) where
  field
    get     : S → A
    set     : S → A → S
    getput  : (s : S) (a : A) → get (set s a) ≡ a
    putget  : (s : S) → set s (get s) ≡ s
    putput  : (s : S) (a a' : A) → set (set s a) a' ≡ set s a'
\end{code}

A common theme in the literature on lenses is that the function
$\mathit{get}$ discards some information from the source to create a
view, and that this information can be explicitly represented using
the \emph{constant-complement} technique from the database
literature. In other words, lenses are viewed as elements of $\exists\
C. S \cong C × A$. Although correct in principle~\cite{survey}, and
although the discarded information $C$ appears to be hidden by the
existential quantifier, it is not really hidden. \amr{needs to be explained better}



\newpage



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

%% Intro to Pi. the weak semiring of types. The language Pi.  The
%% interpretation of Pi as a PL, and its denotation as
%% equivalences. List the equivalences?

Our starting point will be a basic type theory with the empty
type ($\bot$), the unit type ($\top$), the sum type ($\presumtype$), and
the product ($\preprodtype$) type. But rather than focusing on
\emph{functions} between these types, we will instead looks at
\emph{equivalences}.

%%%%%%%%%
\subsection{Type Equivalences}

\noindent The Curry-Howard correspondence teaches that logical
expressions form a commutative semiring -- and leads us to
expect that types
too form a commutative semiring. And indeed they do -- at least up to
\emph{type isomorphism}.  The reader unfamiliar with these can
find a leisurely introduction in~\cite{CaretteJamesSabryArxiv}. We
will furthermore assume that the reader is already familiar with
the basic definitions around \emph{type equivalences}.
That types, with ($\bot, \top, \presumtype,
\preprodtype$) interpreted as ($0, 1, +, ×$) and strict
equality replaced with equivalence $≃$
form a commutative semiring is a basic result of type theory.

However, we might be misled by the Curry-Howard correspondence:
In logic, it is true that $A \lor A = A$ and
$A \land A = A$. However, neither $A \presumtype A$ nor $A \preprodtype A$ are
equivalent to $A$. They are however \emph{equi-inhabited}. This is
a fancy way of saying
\[ A \presumtype A \ \text{is inhabited} \qquad \Leftrightarrow \qquad A \
  \text{is inhabited} \] The above is the real \textit{essence} of the
Curry-Howard correspondence.  In other words, classical Curry-Howard
tells us about \emph{logical equivalence} of types; there are indeed functions
$f : A \presumtype A \rightarrow A$ and $g : A \rightarrow A \presumtype A$;
however, they are not inverses.

\begin{figure}[t]
\begin{minipage}{0.48\textwidth}
\[\begin{array}{rcl}
a &=& a \\
\\
0 + a &=& a \\
a + b &=& b + a \\
a + (b + c) &=& (a + b) + c \\
\\
1 \cdot a &=& a \\
a \cdot b &=& b \cdot a \\
a \cdot (b \cdot c) &=& (a \cdot b) \cdot c \\
\\
0 \cdot a &=& 0 \\
(a + b) \cdot c &=& (a \cdot c) + (b \cdot c)
\end{array}\]
\end{minipage}
\begin{minipage}{0.48\textwidth}
\[
\begin{array}{rrcll}
& A & \simeq & A &\\
\\
&  \bot \presumtype A & \simeq & A &\\
&  A \presumtype B & \simeq & B \presumtype A &\\
&  A \presumtype (B \presumtype C) & \simeq & (A \presumtype B) \presumtype C &\\
\\
&  \top \preprodtype A & \simeq & A &\\
&  A \preprodtype B & \simeq & B \preprodtype A &\\
&  A \preprodtype (B \preprodtype C) & \simeq & (A \preprodtype B) \preprodtype C &\\
\\
& \bot \preprodtype A & \simeq & \bot &\\
& (A \presumtype B) \preprodtype C & \simeq & (A \preprodtype C) \presumtype (B \preprodtype C) &
\end{array}
\]
\end{minipage}
\caption{Semiring equalities and type isomorphisms.}
\label{type-isos}
\end{figure}

The generators for our type isomorphisms will exactly be those
of a semiring --- we place them side-by-side in
Fig.~\ref{type-isos}.

%%%%%%%%%
\subsection{A Language of Type Equivalences}

\begin{figure}[t]
\[
\begin{array}{rrcll}
\idc :& t & \iso & t &: \idc \\
\\
\identlp :&  0 \sumtype t & \iso & t &: \identrp \\
\swapp :&  t_1 \sumtype t_2 & \iso & t_2 \sumtype t_1 &: \swapp \\
\assoclp :&  t_1 \sumtype (t_2 \sumtype t_3) & \iso & (t_1 \sumtype t_2) \sumtype t_3 &: \assocrp \\
\\
\identlt :&  1 {\prodtype} t & \iso & t &: \identrt \\
\swapt :&  t_1 {\prodtype} t_2 & \iso & t_2 {\prodtype} t_1 &: \swapt \\
\assoclt :&  t_1 {\prodtype} (t_2 {\prodtype} t_3) & \iso & (t_1 {\prodtype} t_2) {\prodtype} t_3 &: \assocrt \\
\\
\absorbr :&~ 0 {\prodtype} t & \iso & 0 ~ &: \factorzl \\
\dist :&~ (t_1 \sumtype t_2) {\prodtype} t_3 & \iso & (t_1 {\prodtype} t_3) \sumtype (t_2 {\prodtype} t_3)~ &: \factor
\end{array}
\]
\caption{$\Pi$-terms.}
\label{pi-terms}
\end{figure}

This gives us the denotational semantics for types and for
equivalences. From this, we want to
a programming language, which we call $\Pi$,
where we have ground terms whose denotation are
all $16$ type isomorphisms of Fig.~\ref{type-isos}.
We can simply do this literally. To make the
analogy with commutative semirings stand out even more, we will use
$0, 1, \sumtype$, and ${\prodtype}$ at the type level, and will denote
``equivalence'' by $\iso$.  Thus Fig.~\ref{pi-terms} shows the
``constants'' of the language.  As these all come in symmetric pairs
(some of which are self-symmetric), we give names for both directions.
Note how we have continued with the spirit of Curry-Howard: the terms
of $\Pi$ are \emph{proof terms}, but rather than being witnesses of
inhabitation, they are witnesses of equivalences. Thus we get an
unexpected programming language design:

\begin{center}
\fbox{ The proof terms denoting commutative semiring equivalences
  induce the terms of $\Pi$.}
\end{center}
\vspace*{3mm}

\begin{figure}[t]
\[
\Rule{}
{\jdg{}{}{c_1 : t_1 \iso t_2} \quad \vdash c_2 : t_2 \iso t_3}
{\jdg{}{}{c_1 \odot c_2 : t_1 \iso t_3}}
{}
\qquad
\Rule{}
{\jdg{}{}{c_1 : t_1 \iso t_2} \quad \vdash c_2 : t_3 \iso t_4}
{\jdg{}{}{c_1 \oplus c_2 : t_1 \sumtype t_3 \iso t_2 \sumtype t_4}}
{}
\]
\[
\Rule{}
{\jdg{}{}{c_1 : t_1 \iso t_2} \quad \vdash c_2 : t_3 \iso t_4}
{\jdg{}{}{c_1 \otimes c_2 : t_1 {\prodtype} t_3 \iso t_2 {\prodtype} t_4}}
{}
\]
\caption{$\Pi$-combinators.}
\label{pi-combinators}
\end{figure}

\noindent
Of course, one does not get a programming language with just typed
constants! We need to put together multiple equivalences to form
other equivalences. There are
in fact three ways to do this: sequential composition $\odot$, choice
composition $\oplus$ (sometimes called juxtaposition), and parallel
composition $\otimes$. See Fig.~\ref{pi-combinators} for the
signatures. The construction $c_1 \odot c_2$ corresponds to performing
$c_1$ first, then $c_2$, and is the usual notion of composition.
The construction $c_1 \oplus c_2$ chooses to
perform $c_1$ or $c_2$ depending on whether the input is labelled
$\textsf{left}$ or $\textsf{right}$ respectively. Finally the
construction $c_1 \otimes c_2$ operates on a product structure, and
applies $c_1$ to the first component and $c_2$ to the second.

\begin{figure}[t]
\[
\Rule{}
{\jdg{}{}{c_1 : t_1 \iso t_2}}
{\jdg{}{}{\ !\ c_1 : t_2 \iso t_1}}
{}
\]
\caption{Derived $\Pi$-combinator.}
\label{derived-pi-combinator}
\end{figure}

Embedded in our definition of $\Pi$ is a conscious design decision: to make the
terms of $\Pi$ \emph{syntactically} reversible. In other words, to
every $\Pi$ constant, there is another $\Pi$ constant which is its
inverse. As this is used frequently, we give it the short name $!$,
and its type is given in Fig.~\ref{derived-pi-combinator}. This
combinator is \emph{defined}, by pattern matching on the syntax of
its argument and structural recursion.
This is not the only choice.  Another would be to add a
$\mathit{flip}$ combinator to the language; we could then remove
quite a few combinators as redundant. The drawback is that many
programs in $\Pi$ become longer. Furthermore, some of the symmetry
at ``higher levels'' (see next section) is also lost. Since the
extra burden of language definition and of proofs is quite low, we
prefer the structural symmetry over a minimalistic language definition.

\begin{figure}[t]
\[
\begin{array}{rrcll}
\identlsp :&  t \sumtype 0 & \iso & t &: \identrsp \\
\identlst :&  t {\prodtype} 1 & \iso & t &: \identrst \\
\\
\absorbl :&~ t {\prodtype} 0 & \iso & 0 ~ &: \factorzr \\
\distl :&~ t_1 {\prodtype} (t_2 \sumtype t_3) & \iso & (t_1 {\prodtype} t_2) \sumtype (t_1 {\prodtype} t_3)~ &: \factorl
\end{array}
\]
\caption{Additional $\Pi$-terms.}
\label{more-pi}
\end{figure}

We also make a second design decision, which is to make the $\Pi$
language itself symmetric in another sense: we want both left
and right introduction/elimination rules for units, $0$ absorption
and distributivity. Specifically, we add the $\Pi$-terms of
Fig.~\ref{more-pi} to our language. These are redundant because
of $\swapp$ and $\swapt$, but will later enable shorter programs
and more elegant presentation of program transformations.

This set of isomorphisms is known to be sound and
complete~\cite{Fiore:2004,fiore-remarks} for isomorphisms
of finite types.  Furthermore, it is also universal
for hardware combinational
circuits~\cite{James:2012:IE:2103656.2103667}.

%%%%%%%%%
\subsection{Operational Semantics}
\label{sec:opsem}

It is then quite straightforward to give an operational semantics to
$\Pi$: we write a ``forward evaluator'' which, given a
program program \ensuremath{c : b_1 \leftrightarrow b_2} in \ensuremath{\Pi },
and a value \ensuremath{ v_1 : b_1}, returns a value of type $b_2$. Of course,
what makes $\Pi$ interesting is that we can also write a ``backward
evaluator'' from values of type $b_2$ to values of type $b_1$. Furthermore
we can prove that these are exact inverses. Given our denotational semantics,
this should not be surprising. As the details are straightforward but
verbose, we elide them. As we mentioned before, $!$ is a defined combinator.
Only a few cases need commenting on.

Since there are no values that have the type \ensuremath{0}, the
reductions for the combinators \identlp, \identrp, \identlsp, and
\identrsp\ omit the impossible cases. \factorzr\ and \factorzl\
likewise do not appear as they have no possible cases at all. However,
\absorbr\ and \absorbl\ are treated slightly differently: rather than
\emph{eagerly} assuming they are impossible, the purported inhabitant
of $0$ given on one side is passed on to the other side. The reason
for this choice will have to wait for Sec.~\ref{langeqeq} when we
explain some higher-level symmetries (see Fig.~\ref{figc}).

%%%%%%%%%
\subsection{Further features}

The language $\Pi$ also captures ideas around the size of types, aka
cardinality, and their relation to type equivalences.

Combinators of \ensuremath{\Pi } can be written in terms of the
operators described previously or via a graphical language similar in
spirit to those developed for Geometry of Interaction
\cite{DBLP:conf/popl/Mackie95} and string diagrams for category
theory~\cite{BLUTE1996229,selinger-graphical}.
\ensuremath{\Pi } combinators expressed in this graphical language
look like ``wiring diagrams.'' Values take the form of ``particles''
that flow along the wires. Computation is expressed by the flow of
particles.

The interested reader can
find more details for both features in~\cite{CaretteJamesSabryArxiv}.

Lastly, in previous work~\cite{Carette2016}, we had shown that
the denotational and operational semantics correspond, and given
a constructive proof of this. In other words, to each $\Pi$
combinator we can associate an equivalence between the denotation
of each type, which has all the obvious desirable properties we
would want from such an association.

\subsection{Examples}
We can express a 3-bit word reversal operation as follows:

\ensuremath{\mathit{reverse} : \mathit{word}_3 \leftrightarrow \mathit{word}_3}

\ensuremath{\mathit{reverse} = \swapt \odot (\swapt  \otimes  \idc)~ \odot \assocrt}

\noindent We can check that \ensuremath{\mathit{reverse}} does the right thing by
applying it to a value \ensuremath{(v_1, (v_2, v_3))} and writing out the full
reduction, which can be visualized as:
\[\begin{array}{rlr}
 & (v_1, (v_2, v_3)) \\
 \swapt & ((v_2, v_3), v_1) \\
 \swapt \otimes  \idc & ((v_3, v_2), v_1) \\
 \assocrt & (v_3, (v_2, v_1)) \\
 \end{array}\]

There are several universal primitives for conventional (irreversible)
hardware circuits, such as \ensuremath{\mathit{nand}} and \ensuremath{\mathit{fanout}}. In the case
of reversible hardware circuits, the canonical universal primitive is
the Toffoli gate~\cite{Toffoli:1980}. The Toffoli gate takes three
boolean inputs: if the first two inputs are \ensuremath{\mathit{true}} then the third
bit is negated. The Toffoli gate, and its simple cousin the $\mathit{cnot}$ gate, are both
expressible in $\Pi$.

\subsection{Reversible Programs between Reversible Programs}
\label{sec:pi2}

Just as programs can be shown equivalent, so can reversible
programs. To illustrate, consider two programms that both
map between the types $A + B$ and $C+D$:

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.8}]
  \draw[>=latex,<->,double,red,thick] (2.25,-1.2) -- (2.25,-2.9) ;
  \draw[fill] (-2,-1.5) circle [radius=0.025];
  \node[below] at (-2.1,-1.5) {$A$};
  \node[below] at (-2.1,-1.9) {$+$};
  \draw[fill] (-2,-2.5) circle [radius=0.025];
  \node[below] at (-2.1,-2.5) {$B$};

  \draw[fill] (6.5,-1.5) circle [radius=0.025];
  \node[below] at (6.7,-1.5) {$C$};
  \node[below] at (6.7,-1.9) {$+$};
  \draw[fill] (6.5,-2.5) circle [radius=0.025];
  \node[below] at (6.7,-2.5) {$D$};

  \draw[<-] (-2,-1.5) to[bend left] (1,0.5) ;
  \draw[<-] (-2,-2.5) to[bend left] (1,-0.5) ;
  \draw[->] (3.5,0.5) to[bend left] (6.5,-1.45) ;
  \draw[->] (3.5,-0.5) to[bend left] (6.5,-2.45) ;

  \draw[<-] (-2,-1.5) to[bend right] (1,-3.5) ;
  \draw[<-] (-2,-2.5) to[bend right] (1,-4.5) ;
  \draw[->] (3.5,-3.5) to[bend right] (6.5,-1.55) ;
  \draw[->] (3.5,-4.5) to[bend right] (6.5,-2.55) ;


  \draw     (2,0.5)  -- (2.5,0.5)  ;
  \draw     (2,-0.5) -- (2.5,-0.5) ;

  \draw     (2.5,0.5)  -- (3.5,-0.5)  ;
  \draw     (2.5,-0.5) -- (3.5,0.5) ;

  \draw     (1,-3.5)  -- (2,-4.5)    ;
  \draw     (1,-4.5) -- (2,-3.5)   ;

  \draw     (2,-3.5)  -- (2.5,-3.5)    ;
  \draw     (2,-4.5) -- (2.5,-4.5)   ;

  \path (1.5,0.5) node (tc1) [func] {$c_1$};
  \path (1.5,-0.5) node (tc2) [func] {$c_2$};
  \path (3,-4.5) node (bc1) [func] {$c_1$};
  \path (3,-3.5) node (bc2) [func] {$c_2$};
\end{tikzpicture}
\end{center}
The top path is the $\Pi$ program
$(c_1~\oplus~c_2)~\odot~\swapp$ and the bottom path
$\swapp~\odot~(c_2~\oplus~c_1)$. These are equivalent --
and in fact denote the same permutation.
And, of course, not
all programs between the same types are equivalent. The simplest example
are the two automorphisms of $1+1$, namely $\idc$ and $\swapp$.

Our reversible language of type isomorphisms and equivalences between
them has a strong connection to \emph{univalent universes} in
HoTT~\cite{Carette2018}. Based on this connection, we refer to the
types as being at level-0, to the equivalences between types (i.e., the
combinators of Sec.~\ref{sec:pi1}) as being at level-1, and to the
equivalences between equivalences of types (i.e., the combinators
discussed in this section) as being at level-2.

$\Pi$ was defined by taking the the proof terms of commutative semiring
equivalences as terms. What we need
now is to understand how \emph{proofs} of algebraic identities should be
considered equivalent. Classical algebra does not help, as proofs
are not considered first-class citizens. However,
another route is available to us: since the work of
Hofmann and Streicher~\cite{hofmann96thegroupoid}, we know that
one can model types as \emph{groupoids}.  The additional
structure comes from explicitly modeling the ``identity
types'': instead of regarding all terms which witness
the equality of (say) $a$ and $b$ of type $A$ as being
indistinguishable, we posit that there may in fact be many.

Thus, rather than looking at (untyped) commutative semirings, we
should look at a \emph{typed} version. This process frequently goes by
the moniker of ``categorification.''  We want a categorical algebra,
where the basic objects are groupoids (to model our types), and where
there is a natural notion of $+$ and $*$.  At first, we hit what seems
like a serious stumbling block: the category of all groupoids, \Gpd,
have neither co-products nor products. However, we don't want to work
internally in \Gpd -- we want operations \emph{on} groupoids. In other
words, we want something akin to symmetric monoidal categories, but
with two interacting monoidal structures.  Luckily, this already
exists: the categorical analog to (commutative) semirings are
(symmetric) Rig Categories~\cite{laplaza72,kelly74}.  This
straightforwardly generalizes to symmetric Rig Groupoids.

How does this help? Coherence conditions! Symmetric monoidal categories,
to start somewhere simple, do not just introduce natural transformations
like the associator $\alpha$ and the left and right unitors ($\lambda$
and~$\rho$ respectively), but also coherence conditions that these must satisfy.
Looking, for example, at just the additive fragment of $\Pi$ (i.e. with just $0$,
$1$ and $+$ for the types, $\odot$ and $\oplus$ as combinators, and
only the terms so expressible), the sub-language would correspond,
denotationally, to exactly (non-empty) symmetric monoidal groupoids. And
here we \emph{equations between equations}, aka
commutative diagrams.  Transporting these coherence conditions, for
example those that express that various transformations are \emph{natural},
to $\Pi$ gives a list of equations between $\Pi$ programs.
Furthermore, all the natural transformations
that arise are in fact natural \emph{isomorphisms} -- and thus
reversible.

We can in fact prove that all the coherence conditions
of symmetric Rig Groupoids holds for the groupoid
interpretation of types~\cite{Carette2016}.  This is somewhat tedious
given the sheer numbers involved, but when properly formulated,
relatively straightforward, up to a couple of tricky cases.

But why are these particular coherence laws? Are they all necessary?
Conversely are they, in some appropriate sense, sufficient? This is
the so-called \emph{coherence problem}. Mac Lane, in his farewell address
as President of the American Mathematical Society~\cite{MacLane1976} gives
a good introduction and overview of such problems.  A more modern
interpretation (which can nevertheless be read into Mac Lane's own
exposition) would read as follows: given a set of equalities on abstract
words, regarded as a rewrite system, and two means of rewriting a word
in that language to another, is there some suitable notion of canonical
form that expresses the essential uniqueness of the non-trivial
rewrites?  Note how this word-and-rewrite problem is essentially
independent of the eventual interpretation. But one must take some care,
as there are obvious degenerate cases (involving ``trivial'' equations
involving $0$ or $1$) which lead to non-uniqueness. The landmark
results, first by Kelly-Mac Lane~\cite{KELLY197197} for closed
symmetric monoidal categories, then (independently) Laplaza and
Kelly~\cite{laplaza72,kelly74} for symmetric Rig Categories, is
that indeed there are sound and complete coherence conditions that
insure that all the ``obvious'' equalities between different abstract
words in these systems give rise to commutative diagrams. The
``obvious'' equalities come from \emph{syzygies} or
\emph{critical pairs} of the system of equations.
The problem is far from trivial --- Fiore et al.~\cite{Fiore-2008}
document some publications where the coherence set is in
fact incorrect. They furthermore give a quite general algorithm
to derive such coherence conditions.

%%%%%%%%%
\subsection{A Language of Equivalences between Type Equivalences}
\label{langeqeq}

As motivated in the previous section, the equivalences between type
equivalences are perfectly modeled by the coherence conditions of weak
Rig Groupoids. Syntactically, we take the easiest way there: simply
make every coherence isomorphism into a programming construct. These
constructs are collected in several figures (Fig.~\ref{figj} to
Fig.~\ref{figa}) and are discussed next.

Conveniently, the various coherence conditions can be naturally
grouped into ``related'' laws.  Each group basically captures the
interactions between compositions of level-1 $\Pi$ combinators.

\begin{figure}[t]
Let $c_1 : t_1 \leftrightarrow t_2$, $c_2 : t_3 \leftrightarrow t_4$, $c_3 : t_1 \leftrightarrow t_2$, and $c_4 : t_3 \leftrightarrow t_4$. \\
Let $a_1 : t_5 \leftrightarrow t_1$,  $a_2 : t_6 \leftrightarrow t_2$, $a_3 : t_1 \leftrightarrow t_3$, and $a_4 : t_2 \leftrightarrow t_4$.
\[\def\arraystretch{1.3}
\begin{array}{c}
\Rule{}
  {c_1 \Leftrightarrow c_3 \quad c_2 \Leftrightarrow c_4}
  {c_1 \oplus c_2 \Leftrightarrow c_3 \oplus c_4}
  {}
\qquad
\Rule{}
  {c_1 \Leftrightarrow c_3 \quad c_2 \Leftrightarrow c_4}
  {c_1 \otimes c_2 \Leftrightarrow c_3 \otimes c_4}
  {}
\\
  {(a_1 \odot a_3) \oplus (a_2 \odot a_4) \Leftrightarrow (a_1 \oplus a_2) \odot (a_3 \oplus a_4)}
\\
  {(a_1 \odot a_3) \otimes (a_2 \odot a_4) \Leftrightarrow (a_1 \otimes a_2) \odot (a_3 \otimes a_4)}
\end{array}\]
\caption{\label{fige}Signatures of level-2 $\Pi$-combinators: functors}
\end{figure}

Starting with the simplest constructions, the first two constructs in
Fig.~\ref{fige} are the level-2 analogs of~$+$ and~$*$, which
respectively model level-1 choice composition and parallel composition
(of equivalences).  These allow us to ``build up'' larger equivalences
from smaller ones.  The next two express that both of these
composition operators distribute over sequential composition $\odot$
(and vice versa).

\begin{figure}[t]
Let $c_1 : t_1 \leftrightarrow t_2$,  $c_2 : t_2 \leftrightarrow t_3$, and $c_3 : t_3 \leftrightarrow t_4$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {c_1 \odot (c_2 \odot c_3) \Leftrightarrow (c_1 \odot c_2) \odot c_3}
\\
  {(c_1 \oplus (c_2 \oplus c_3)) \odot \assoclp \Leftrightarrow \assoclp \odot ((c_1 \oplus c_2) \oplus c_3)}
\\
  {(c_1 \otimes (c_2 \otimes c_3)) \odot \assoclt \Leftrightarrow \assoclt \odot ((c_1 \otimes c_2) \otimes c_3)}
\\
  {((c_1 \oplus c_2) \oplus c_3) \odot \assocrp \Leftrightarrow \assocrp \odot (c_1 \oplus (c_2 \oplus c_3))}
\\
  {((c_1 \otimes c_2) \otimes c_3) \odot \assocrt \Leftrightarrow \assocrt \odot (c_1 \otimes (c_2 \otimes c_3))}
\\
  {\assocrp \odot \assocrp \Leftrightarrow ((\assocrp \oplus \idc) \odot \assocrp) \odot (\idc \oplus \assocrp)}
\\
  {\assocrt \odot \assocrt \Leftrightarrow ((\assocrt \otimes \idc) \odot \assocrt) \odot (\idc \otimes \assocrt)}
\end{array}\]
\caption{\label{figj}Signatures of level-2 $\Pi$-combinators: associativity}
\end{figure}

The constructs in Fig.~\ref{figj} capture the informal idea that all
the different ways of associating programs are equivalent. The first
says that sequential composition itself ($\odot$) is associative.
The next $4$ capture how
the $\oplus$ and $\otimes$ combinators ``commute'' with re-association.
In other words, it expresses that the type-level associativity of $+$ is
properly reflected by the properties of $\oplus$.
The last two equivalences show how composition of associativity combinators
interact together.

The bottom line in Fig.~\ref{figj} is actually a linear
restatement of the famous ``pentagon diagram'' stating a
particular coherence condition for monoidal categories~\cite{KELLY197197}.
To make the relation between $\Pi$ as a language and the
language of category theory, the figure below displays
the same morphism but in categorical terms.

\begin{center}
\begin{tikzcd}[column sep=normal]
   & (A \times (B \times C)) \times D \arrow [dr, "\assocrt"] & \\
((A \times B) \times C) \times D \arrow [ur, "\assocrt \otimes \mathit{id}\leftrightarrow"]
   \arrow [d, "\assocrt"] &
       & A \times ((B \times C) \times D) \arrow [d, "\mathit{id}\leftrightarrow \otimes \assocrt" ]\\
(A \times B) \times (C \times D) \arrow [rr, "\assocrt"] & & A \times (B \times (C \times D))
\end{tikzcd}
\end{center}

\begin{figure}[t]
Let $c_1 : t_1 \leftrightarrow t_2$, $c_2 : t_3 \leftrightarrow t_4$, and $c_3 : t_5 \leftrightarrow t_6$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {((c_1 \oplus c_2) \otimes c_3) \odot \dist \Leftrightarrow \dist \odot ((c_1 \otimes c_3) \oplus (c_2 \otimes c_3))}
\\
  {(c_1 \otimes (c_2 \oplus c_3)) \odot \distl \Leftrightarrow \distl \odot ((c_1 \otimes c_2) \oplus (c_1 \otimes c_3))}
\\
  {((c_1 \otimes c_3) \oplus (c_2 \otimes c_3)) \odot \factor \Leftrightarrow \factor \odot ((c_1 \oplus c_2) \otimes c_3)}
\\
  {((c_1 \otimes c_2) \oplus (c_1 \otimes c_3)) \odot \factorl \Leftrightarrow \factorl \odot (c_1 \otimes (c_2 \oplus c_3))}
\end{array}\]
\caption{\label{figi}Signatures of level-2 $\Pi$-combinators: distributivity and factoring}
\end{figure}

The constructs in Fig.~\ref{figi} are the basic coherence for
$\dist$, $\distl$, $\factor$ and $\factorl$: the type-level distribution
and factoring has to commute with the level-1 $\oplus$ and $\otimes$.

\begin{figure}[t]
Let $c_0, c_1, c_2, c_3 : t_1 \leftrightarrow t_2$ and $c_4, c_5 : t_3 \leftrightarrow t_4$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {\idc \odot \, c_0 \Leftrightarrow c_0}
\quad
  {c_0 \, \odot \idc \, \Leftrightarrow c_0}
\quad
  {c_0\,\, \odot\,!\, c_0 \Leftrightarrow \idc}
\quad
  {!\, c_0 \odot c_0 \Leftrightarrow \idc}
\\
  {\idc \oplus \, \idc \, \Leftrightarrow \idc}
\qquad
  {\idc \otimes \, \idc \, \Leftrightarrow \idc}
\\
  {c_0 \Leftrightarrow c_0}
\quad
\Rule{}
  {c_1 \Leftrightarrow c_2 \quad c_2 \Leftrightarrow c_3}
  {c_1 \Leftrightarrow c_3}
  {}
\quad
\Rule{}
  {c_1 \Leftrightarrow c_4 \quad c_2 \Leftrightarrow c_5}
  {c_1 \odot c_2 \Leftrightarrow c_4 \odot c_5}
  {}
\end{array}\]
\caption{\label{figh}Signatures of level-2 $\Pi$-combinators: identity and composition}
\end{figure}

The constructs in Fig.~\ref{figh} express various properties of composition.
The first two says that $\idc$ is a left and right identity for sequential composition.
The next two say that all programs are reversible, both on the left and the right:
running $c$ and then its reverse ($!\, c$) is equivalent to the identity, and the
same for doing $!\, c$ first then $c$. The last line say that there is an
identity level-2 combinator, a sequential composition, and that level-2
equivalence respects level-1 sequential composition $\odot$.

\begin{figure}[t]
Let $c_0 : 0 \leftrightarrow 0$, $c_1 : 1 \leftrightarrow 1$, and $c_3 : t_1 \leftrightarrow t_2$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {\identlp \odot c_3 \Leftrightarrow (c_0 \oplus c_3) \odot \identlp}
\qquad
  {\identrp \odot (c_0 \oplus c_3) \Leftrightarrow c_3 \odot \identrp}
\\
  {\identlsp \odot c_3 \Leftrightarrow (c_3 \oplus c_0) \odot \identlsp}
\qquad
  {\identrsp \odot (c_3 \oplus c_0) \Leftrightarrow c_3 \odot \identrsp}
\\
  {\identlt \odot c_3 \Leftrightarrow (c_1 \otimes c_3) \odot \identlt}
\qquad
  {\identrt \odot (c_1 \otimes c_3) \Leftrightarrow c_3 \odot \identrp}
\\
  {\identlst \odot c_3 \Leftrightarrow (c_3 \otimes c_1) \odot \identlst}
\qquad
  {\identrst \odot (c_3 \otimes c_1) \Leftrightarrow c_3 \odot \identrst}
\\
  {\identlt \Leftrightarrow \distl \odot (\identlt \oplus \identlt)}
\\
\identlp \Leftrightarrow \swapp \odot \identlsp
\qquad
\identlt \Leftrightarrow \swapt \odot \identlst
\end{array}\]
\caption{\label{figg}Signatures of level-2 $\Pi$-combinators: unit}
\end{figure}

The constructs in Fig.~\ref{figg} may at first blush look similarly straightforward,
but deserve some pause. One obvious question: What is the point of
$c_0 : 0 \leftrightarrow 0$, isn't that just the identity combinator $\idc$
for $A = 0$ (as defined in Fig.~\ref{type-isos})? Operationally, $c_0$
is indeed indistinguishable from $\idc$. However, there are multiple syntactic
ways of writing down combinators of type $0 \leftrightarrow 0$, and the
first combinator in Fig.~\ref{figg} applies to all of them uniformly.
This is another subtle aspect of coherence: all reasoning must be valid for
all possible models, not just the one we have in mind. So even though
operational reasoning may suggest that some relations \emph{may} be
true between combinators, it can also mislead. The same reasoning
applies to $c_1 : 1 \leftrightarrow 1$.  The first $8$ combinators can
then be read as basic coherence for unit introduction and elimination,
in both additive and multiplicative cases.

The last two capture
another simple idea, related to swapping: eliminating a unit
on the left is the same as first swapping then eliminating on the
right (both additively and multiplicatively). As a side note,
these are not related to \emph{commutativity}, but rather
come from one of the simplest coherence condition for
braided monoidal categories. In other words, it reflects the
idempotence of $\swapp$ and $\swapt$ rather than the
commutativity of $\oplus$ and $\otimes$.

\begin{figure}[t]
Let $c_1 : t_1 \leftrightarrow t_2$ and $c_2 : t_3 \leftrightarrow t_4$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {\swapp \odot (c_1 \oplus c_2) \Leftrightarrow (c_2 \oplus c_1) \odot \swapp}
\quad
  {\swapt \odot (c_1 \otimes c_2) \Leftrightarrow (c_2 \otimes c_1) \odot \swapt}
\\
  {(\assocrp \odot \swapp) \odot \assocrp \Leftrightarrow ((\swapp \oplus \idc) \odot \assocrp) \odot (\idc \oplus \swapp)}
\\
  {(\assoclp \odot \swapp) \odot \assoclp \Leftrightarrow ((\idc \oplus \swapp) \odot \assoclp) \odot (\swapp \oplus \idc)}
\\
  {(\assocrt \odot \swapt) \odot \assocrt \Leftrightarrow ((\swapt \otimes \idc) \odot \assocrt) \odot (\idc \otimes \swapt)}
\\
  {(\assoclt \odot \swapt) \odot \assoclt \Leftrightarrow ((\idc \otimes \swapt) \odot \assoclt) \odot (\swapt \otimes \idc)}
\end{array}\]
\caption{\label{figf}Signatures of level-2 $\Pi$-combinators: commutativity and associativity}
\end{figure}

The first two equivalences in Fig.~\ref{figf} reflect the basic
coherence between level-0 swapping and the level-1 combinator
actions. The next four arise because of interactions between (additive
and multiplicative) level-1 associativity and swapping.  In other
words, they arise as critical pairs.  For example, the first expresses
that the two ways of going from $\left(A \oplus B\right) \oplus C$ to
$B \oplus \left(C \oplus A\right)$ are equivalent, with the second
saying that the reverse (i.e.  the results of applying $!$\,) also
gives equivalent programs.  The last two say the same but for the
multiplicative structure.

\begin{figure}[t]
\[\def\arraystretch{1.3}
\begin{array}{c}
  {\identlsp \oplus \idc ~\Leftrightarrow~ \assocrp \odot (\idc \oplus \, \identlp)}
\\
  {\identlst \otimes \idc ~\Leftrightarrow~ \assocrt \odot (\idc \otimes \, \identlt)}
\end{array}\]
\caption{\label{figd}Signatures of level-2 $\Pi$-combinators: unit and associativity}
\end{figure}

The constructs in Fig.~\ref{figd} express how unit elimination ``in the middle''
can be expressed either as operating on the right or, (after re-association) on the left.


\begin{figure}[t]
Let $c : t_1 \leftrightarrow t_2$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {(c \otimes \idc) \odot \absorbl \Leftrightarrow \absorbl \odot \idc}
\quad
  {(\idc \, \otimes c) \odot \absorbr \Leftrightarrow \absorbr \odot \idc}
\\
  {\idc \odot \, \factorzl \Leftrightarrow \factorzl \odot (\idc \otimes c)}
\quad
  {\idc \odot \, \factorzr \Leftrightarrow \factorzr \odot (c \otimes \idc)}
\\
  {\absorbr \Leftrightarrow \absorbl}
\\
  {\absorbr \Leftrightarrow (\distl \odot (\absorbr \oplus \absorbr)) \odot \identlp}
\\
  {\identlst \Leftrightarrow \absorbr}
\qquad
  {\absorbl \Leftrightarrow \swapt \odot \absorbr}
\\
  {\absorbr \Leftrightarrow (\assoclt \odot (\absorbr \otimes \idc)) \odot \absorbr}
\\
  {(\idc \otimes \absorbr) \odot \absorbl \Leftrightarrow (\assoclt \odot (\absorbl \otimes \idc)) \odot \absorbr}
\\
  {\idc \otimes \, \identlp \Leftrightarrow (\distl \odot (\absorbl \oplus \idc)) \odot \identlp}
\end{array}\]
\caption{\label{figc}Signatures of level-2 $\Pi$-combinators: zero}
\end{figure}

The constructs in Fig.~\ref{figc} are significantly more subtle, as they
deal with combinators involving $0$, aka an impossibility.  For example,
\[  {(c \otimes \idc_{0}) \odot \absorbl \Leftrightarrow \absorbl \odot \idc_{0}}
\]
(where we have explicitly annotated the types of $\idc$ for increased clarity)
tells us that of the two ways of transforming from $t_1  *\  0$ to $0$,
namely first doing some arbitrary transformation $c$ from $t_1$ to $t_2$ and
(in parallel) leaving $0$ alone then eliminating $0$, or first eliminating $0$
then doing the identity (at $0$), are equivalent. This is the ``naturality'' of
$\absorbl$. One item to note is the fact that this combinator is not
irreducible, as the $\idc$ on the right can be eliminated. But that is actually
a property visible at an even higher level (which we will not touch in this
paper).  The next $3$ are similarly expressing the naturality of $\absorbr$,
$\factorzl$ and $\factorzr$.

The next combinator, $\absorbr \Leftrightarrow \absorbl$, is
particularly fascinating: while it says something simple --- that the
two obvious ways of transforming $0 * 0$ into $0$, namely absorbing
either the left or right $0$ --- it implies something subtle.  A
straightforward proof of $\absorbl$ which proceeds by saying that
$0 * t$ cannot be inhabited because the first member of the pair
cannot, is not in fact equivalent to $\absorbr$ on $0 * 0$.  However,
if we instead define $\absorbl$ to ``transport'' the putative
impossible first member of the pair to its (equally impossible)
output, then these do form equivalent pairs.  The next few in
Fig.~\ref{figc} also express how $\absorbr$ and $\absorbl$ interact
with other combinators. As seen previously, all of these arise as
critical pairs. What is much more subtle here is that the types
involved often are asymmetric: they do not have the same occurrences
on the left and right. Such cases are particularly troublesome for
finding normal forms. Laplaza~\cite{laplaza72} certainly comments on this,
but in mostly terse and technical terms. Blute et al.~\cite{BLUTE1996229}
offer much more intuitive explanations.

\begin{figure}[t]
\[\def\arraystretch{1.3}
\begin{array}{c}
  {((\assoclp \otimes \idc) \odot \dist) \odot (\dist \oplus \idc) \Leftrightarrow (\dist \odot (\idc \oplus \dist)) \odot \assoclp}
\\
  {\assoclt \odot \distl \Leftrightarrow ((\idc \otimes \distl) \odot \distl) \odot (\assoclt \oplus \assoclt)}
\end{array}\]
\vspace{ -0.5em}
\[\def\arraystretch{1.3}
\begin{array}{rcl}
  (\distl \odot (\dist \oplus \dist)) \odot \assoclp &\Leftrightarrow&
   \dist \odot (\distl \oplus \distl) \odot \assoclp ~\odot \\
&& (\assocrp \oplus \idc) ~\odot \\
&& ((\idc \oplus \swapp) \oplus \idc) ~\odot \\
&&      (\assoclp \oplus \idc)
\end{array}\]
\caption{\label{figb}Signatures of level-2 $\Pi$-combinators: associativity and distributivity}
\end{figure}

\begin{figure}[t]
\[\def\arraystretch{1.3}
\begin{array}{rcl}
  (\idc \otimes \swapp) \odot \distl &\Leftrightarrow& \distl \odot \swapp
\\
  \dist \odot (\swapt \oplus \swapt) &\Leftrightarrow & \swapt \odot \distl
\end{array}\]
\caption{\label{figa}Signatures of level-2 $\Pi$-combinators: commutativity and distributivity}
\end{figure}

The constructs in Fig.~\ref{figb} and Fig.~\ref{figa} relating associativity and
distributivity, and commutativity and distributivity, have more in common with
previous sets of combinators.  They do arise from non-trivial critical pairs
of different ways of going between equivalent types. The last one of
Fig.~\ref{figb} is particularly daunting, involving a sequence of $3$ combinators
on the left and $6$ on the right.

%%%%%%%%%
\newcommand{\evalone}{\ensuremath{\mathit{eval}_1}}
\newcommand{\transLR}{\AgdaInductiveConstructor{trans⇔}}

\subsection{Example}\label{sec:level2-example}

We can now illustrate how this all works with a small example.
Consider a circuit that takes an input type consisting of three values
\Tree [ {\small a} [ {\small b} {\small c} ] ]~
and swaps the leftmost value with the rightmost value to produce
\Tree [ {\small c} [ {\small b} {\small a} ] ]~.
We can implement two such circuits using our Agda library for $\Pi$:

\begin{code}
-- swap-fl1 ...
\end{code}

\noindent The first implementation rewrites the incoming values as follows:
\[
\Tree [ {\small a} [ {\small b} {\small c} ] ] ~\to~
\Tree [ [ {\small a} {\small b} ] {\small c} ] ~\to~
\Tree [ {\small c} [ {\small a} {\small b} ] ] ~\to~
\Tree [ {\small c} [ {\small b} {\small a} ] ] ~.
\]
\noindent
The second implementation rewrites the incoming values as follows:
\[
\Tree [ {\small a} [ {\small b} {\small c} ] ] ~\to~
\Tree [ {\small a} [ {\small c} {\small b} ] ] ~\to~
\Tree [ [ {\small a} {\small c} ] {\small b} ] ~\to~
\Tree [ [ {\small c} {\small a} ] {\small b} ] ~\to~
\Tree [ {\small c} [ {\small a} {\small b} ] ] ~\to~
\Tree [ {\small c} [ {\small b} {\small a} ] ] ~.
\]
\noindent The two circuits are extensionally equal. Using the level-2
isomorphisms we can \emph{explicitly} construct a sequence of
rewriting steps that transforms the second circuit to the first.

We write such proofs in an equational style: in the left column, we have
the current combinator which is equivalent to the first one, and in
the right column, the justification for that equivalence. The
joining combinator is syntactic sugar for \transLR.  The transformation
could be written (using \transLR) by just giving all the pieces in
the right hand column --- but such transformations are very hard for
humans to understand and follow.

The proof
can be read as follows: the first three lines ``refocus'' from a right-associated
isomorphism onto the (left-associated) composition of the first $3$ isomorphisms;
then apply a complex rewrite on these (the ``hexagon'' coherence condition
of symmetric braided monoidal categories); this exposes two inverse combinators
next to each other --- so we have to refocus on these to eliminate them; we
finally re-associate to get the result.

\renewcommand{\AgdaIndentSpace}{\;\;}
\setlength\mathindent{0.5em}

\begin{code}
-- swap-fl2
\end{code}

\renewcommand{\AgdaIndentSpace}{\AgdaSpace{}$\;\;$}

\subsection{Internal Language}

Recalling that the $\lambda$-calculus arises as the internal language
of Cartesian Closed Categories (Elliott~\cite{Elliott-2017} gives a particularly
readable account of this), we can think of $\Pi$ in similar terms, but
for symmetric Rig Groupoids instead. For example, we can ask what does
the derivation in Sec.~\ref{sec:level2-example} represent? It is
actually a ``linear'' representation of a 2-categorial commutative
diagram! In fact, it is a painfully verbose version thereof, as it
includes many \emph{refocusing} steps because our language does not
build associativity into its syntax. Categorical diagrams usually do.
Thus if we rewrite the example in diagrammatic form, eliding all uses
of associativity, but keeping explicit uses of identity transformations,
we get that \AgdaFunction{swap{-}fl2⇔swap{-}fl1} represents

\newcommand{\idd}{\mathit{id}\leftrightarrow}
\newcommand{\idf}{\mathit{id}\Leftrightarrow}
\vspace*{3mm}
\begin{tikzcd}[column sep=normal, row sep=normal]
 && (a+c)+b \arrow [r, "\swapp \oplus\idd", ""{name=U, below}] & (c+a)+b \arrow [dr, "\assocrp"] && \\
 & a+(c+b) \arrow [ur, "\assoclp"] & & & c+(a+b) \arrow [dr, "\idd\oplus\swapp"] &  \\
a+(b+c) \arrow [ur, "\idd\oplus\swapp"] \arrow [r, "\assoclp"]
  \arrow [dr, "\assoclp"]
  \arrow [ddr, swap, "\assoclp"]
    & (a+b)+c \arrow [r, "\swapp"] &
    c+(a+b) \arrow [r, swap, "\assoclp", ""{name=D, above}]
    & |[alias=Z]| (c+a)+b \arrow [r, "\assocrp"] &c+(a+b) \arrow [r, "\idd\oplus\swapp"] & c+(b+a) \\
 & (a+b)+c \arrow [dr, "\swapp"] &&&& \\
 & (a+b)+c \arrow [dr, swap, "\swapp"] & c+(a+b) \arrow [rr, swap, "\idd", ""{name=DD, above}]
             \arrow [d, Rightarrow, "\idf\, \mathit{idl}\odot{l}"] &&
    c+(a+b) \arrow [ruu, "\idd\oplus\swapp"] & \\
 && c+(a+b) \arrow [rrruuu, bend right = 40, swap, "\idd\oplus\swapp"] && \\
 \arrow[Rightarrow, from=U, to=D, "\mathit{hexagon}\oplus{r}\, \boxdot\, \idf"]
 \arrow[Rightarrow, from=Z, to=DD, swap, "\idf\boxdot\mathit{linv}\odot{l}\,\boxdot\,\idf"]
\end{tikzcd}

\noindent For some, the above diagram will be clearer --- it is only three layers
high rather than nine! Others will prefer the more programmatic feel of the
original definition.

We would be remiss in letting the reader believe that the above is ``the''
categorical diagram that would be found in categorical textbooks. Rather,
congruence would be used to elide the $\idf$. Furthermore, the various arrows
would also be named differently --- our \assoclp\ is often named $\alpha$,
\assocrp\ is $\alpha^{-1}$, $\swapp$ is $B$ (always with subscripts).
And the two steps needed to remove inverses (i.e. first cancelling
inverse arrows, then removing the resulting identity arrow ``in context'')
are often combined into one. Here we'll simply name this operation
$\mathit{cancel}$, which could be programmed as a defined function over
$\Pi$ level-2.  The result would then be the much simpler

\vspace*{3mm}
\begin{tikzcd}[column sep=normal, row sep=normal]
 & a+(c+b) \arrow [r, "\assoclp", ""{name=U, below}] & (a+c)+b \arrow [rd, "\swapp\oplus\idd"] & & & \\
a+(b+c) \arrow [ur, "\idd\oplus\swapp"] \arrow [dr, "\assoclp"]
  & & & (c+a)+b \arrow [r, "\assocrp", ""{name=UU, below}] & c+(a+b) \arrow [r, "\idd\oplus\swapp"] & c+(b+a) \\
 & (a+b)+c \arrow [r, swap, "\swapp", ""{name=D, above}] & c+(a+b) \arrow [ur, "\assoclp"]
  \arrow [urrr, swap, "\idd\oplus\swapp", ""{name=DD,above}] & & & & \\
 \arrow[Rightarrow, from=U, to=D, "\mathit{hexagon}\oplus{r}"]
 \arrow[Rightarrow, from=UU, to=DD, "\mathit{cancel}"]
\end{tikzcd}

In other words, each (non-refocusing) line of the proof of
\AgdaFunction{swap{-}fl2⇔swap{-}fl1}\; is a complete path
from left to right in each diagram above, and the annotation
on the right-hand-side becomes the natural transformation (denoted
by vertical $\Rightarrow$) justifying the move to the next line.
The first diagram uses lines $1,4,7,8$ in full; the second
diagram collapses $7$ and $8$ into one, as well as not duplicating
parts which are related by $\idf$.

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

Let us consider a type \verb|Colour| with exactly $3$ inhabitants,
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
the same for the \verb|GS-Lens|:
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

In a way, a ``better'' explanation of \AgdaRecord{∃-Colour-in-A+A+A}
is to remark that the types $⊤ ⊎ ⊤ ⊎ ⊤$ (which we'll call
$\mathbb{3}$) and \AgdaRecord{Colour} are isomorphic, which leads to
the chains of isomorphisms $A \uplus A \uplus A \simeq A × \mathbb{3}
\simeq A × \AgdaRecord{Colour}$.

An interesting interpretation of that isomorphism is that we can freely move tagging
of data $A$ with \textit{finite information} between type-level tags and value-level
tags at will.

\subsection{More ideas}
\jc{We should take a look at the optics generated by cnot and/or toffoli}

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
\bibliography{cites,cites2}
%inline the .bbl file directly for mailing to authors.

\end{document}
