\documentclass[authoryear,preprint]{sigplanconf}
\usepackage{agda}
%% \usepackage{fixltx2e}
\usepackage{fix2col}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{tikz}
\usepackage{amsthm}
\usepackage{latexsym}
\usepackage{courier}
\usepackage{thmtools}
\usepackage{bbold}
\usepackage{url}
\usepackage{bbm}
\usepackage{proof}
\usepackage{amstext}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{comment}
\usepackage{stmaryrd}
\usepackage{listings}
\usepackage{graphicx}
\usepackage{textgreek}
\usepackage{extarrows}
\usepackage{multicol}

\renewcommand{\AgdaCodeStyle}{\small}

\newcommand{\nodet}[2]{\fcolorbox{black}{white}{$#1$}\fcolorbox{black}{gray!20}{$#2$}}
\newcommand{\cubt}{\mathbb{T}}
\newcommand{\ztone}{\mathbb{0}}
\newcommand{\otone}{\mathbb{1}}
\newcommand{\eqdef}{\stackrel{\triangle}{=}}
\newcommand{\ptone}[2]{#1 \boxplus #2}
\newcommand{\ttone}[2]{#1 \boxtimes #2}
\newcommand{\isoone}{\Leftrightarrow}
\newcommand{\lolli}{\multimap} 
\newcommand{\pointed}[2]{\AgdaSymbol{•}\AgdaSymbol{[} #1 \AgdaSymbol{,} #2 \AgdaSymbol{]}}
\newcommand{\AgdaArgument}[1]{#1}
\newcommand{\inl}[1]{\textsf{inl}~#1}
\newcommand{\inr}[1]{\textsf{inr}~#1}
\newcommand{\idv}[3]{#2 \xrightarrow{#1} #3}
\newcommand{\cp}[3]{#1\stackrel{#2}{\bullet}#3}
\newcommand{\idt}[3]{#2 \equiv_{#1} #3}
\newcommand{\idrt}[3]{#3 \equiv_{#1} #2}
\newcommand{\refl}[1]{\textsf{refl}~#1}
\newcommand{\lid}{\textsf{lid}}
\newcommand{\rid}{\textsf{rid}}
\newcommand{\linv}{l!}
\newcommand{\rinv}{r!}
\newcommand{\invinv}{!!}
\newcommand{\assoc}{\circ}
\newcommand{\identlp}{\mathit{identl}_+}
\newcommand{\identrp}{\mathit{identr}_+}
\newcommand{\swapp}{\mathit{swap}_+}
\newcommand{\assoclp}{\mathit{assocl}_+}
\newcommand{\assocrp}{\mathit{assocr}_+}
\newcommand{\identlt}{\mathit{identl}_*}
\newcommand{\identrt}{\mathit{identr}_*}
\newcommand{\swapt}{\mathit{swap}_*}
\newcommand{\assoclt}{\mathit{assocl}_*}
\newcommand{\assocrt}{\mathit{assocr}_*}
\newcommand{\distz}{\mathit{dist}_0}
\newcommand{\factorz}{\mathit{factor}_0}
\newcommand{\dist}{\mathit{dist}}
\newcommand{\factor}{\mathit{factor}}
\newcommand{\iso}{\leftrightarrow}
\newcommand{\proves}{\vdash}
\newcommand{\idc}{\mathit{id}}
\newcommand{\ap}[2]{\mathit{ap}~#1~#2}
\newcommand{\alt}{~|~}
\newcommand{\evalone}[2]{#1~\triangleright~#2}
\newcommand{\evaloneb}[2]{#1~\triangleleft~#2}
\newcommand{\Rule}[4]{
\makebox{{\rm #1}
$\displaystyle
\frac{\begin{array}{l}#2\\\end{array}}
{\begin{array}{l}#3\\\end{array}}$
 #4}}
\newcommand{\jdg}[3]{#2 \proves_{#1} #3}
\newcommand{\adjoint}[1]{#1^{\dagger}}
\newcommand{\pc}{\fatsemi}                 % path composition

\newenvironment{floatrule}
    {\hrule width \hsize height .33pt \vspace{.5pc}}
    {\par\addvspace{.5pc}}

\DeclareUnicodeCharacter{9678}{$\circledcirc$}
\DeclareUnicodeCharacter{10231}{$\leftrightarrow$}
\DeclareUnicodeCharacter{10214}{$\llbracket$} 
\DeclareUnicodeCharacter{10215}{$\rrbracket$} 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}
\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\title{A Computational Reconstruction of \\ 
  Homotopy Type Theory for Finite Types}
\authorinfo{}{}{}
\maketitle

\begin{abstract}
Homotopy type theory (HoTT) relates some aspects of topology, algebra,
geometry, physics, logic, and type theory, in a unique novel way that
promises a new and foundational perspective on mathematics and
computation. The heart of HoTT is the \emph{univalence axiom}, which
informally states that isomorphic structures can be identified. One of the
major open problems in HoTT is a computational interpretation of this axiom.
We propose that, at least for the special case of finite types, reversible
computation via type isomorphisms \emph{is} the computational interpretation
of univalence.
\end{abstract}

\AgdaHide{
\begin{code}
module p where
open import Level 
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Bool
open import Data.Product
open import Data.Nat hiding (_⊔_)
open import Function

open import Groupoid

infixr 30 _⟷_
infixr 10 _◎_
infix  4  _≡_   -- propositional equality
infix  4  _∼_   -- homotopy between two functions (the same as ≡ by univalence)
infix  4  _≃_   -- type of equivalences
-- infix  2  _∎       -- equational reasoning for paths
-- infixr 2  _≡⟨_⟩_   -- equational reasoning for paths

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction} 

In a computational world in which the laws of physics are embraced and
resources are carefully maintained (e.g., quantum
computing~\cite{NC00,Abramsky:2004:CSQ:1018438.1021878}), programs must be
reversible. Although this is apparently a limiting idea, it turns out that
conventional computation can be viewed as a special case of such
resource-preserving reversible programs. This thesis has been explored for
many years from different
perspectives~\cite{fredkin1982conservative,Toffoli:1980,bennett2010notes,bennett2003notes,Bennett:1973:LRC,Landauer:1961,Landauer}. 

\paragraph*{Conventional HoTT/Agda approach}

We start with a computational framework: data (pairs, etc.) and functions
between them. There are computational rules (beta, etc.) that explain what a
function does on a given datum.

We then have a notion of identity which we view as a process that equates two
things and model as a new kind of data. Initially we only have identities
between beta-equivalent things.

Then we postulate a process that identifies any two functions that are
extensionally equivalent. We also postulate another process that identifies
any two sets that are isomorphic. This is done by adding new kinds of data
for these kinds of identities.

\paragraph*{Our approach} 

Our approach is to start with a computational framework that has finite data
and permutations as the operations between them. The computational rules
apply permutations.

HoTT~\cite{hottbook} says id types are an inductively defined type family
with refl as constructor. We say it is a family defined with pi combinators
as constructors. Replace path induction with refl as base case with our
induction.

\paragraph*{Generalization} 

How would that generalize to first-class functions? Using negative and
fractionals? Groupoids? 

In a computational world in which the laws of physics are embraced and
resources are carefully maintained (e.g., quantum
computing~\cite{NC00,Abramsky:2004:CSQ:1018438.1021878}), programs must be
reversible. Although this is apparently a limiting idea, it turns out that
conventional computation can be viewed as a special case of such
resource-preserving reversible programs. This thesis has been explored for
many years from different
perspectives~\cite{fredkin1982conservative,Toffoli:1980,bennett2010notes,bennett2003notes,Bennett:1973:LRC,Landauer:1961,Landauer}.
We build on the work of James and
Sabry~\citeyearpar{James:2012:IE:2103656.2103667} which expresses this thesis
in a type theoretic computational framework, expressing computation via type
isomorphisms.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Condensed Background on HoTT}
\label{hott}

Informally, and as a first approximation, one may think of HoTT as a
variation on Martin-L\"of type theory in which all equalities are given
\emph{computational content}. We explain the basic ideas below.

%%%%%%%%%%%%%%%%%%
\subsection{Paths}

Formally, Martin-L\"of type theory, is based on the principle that every
proposition, i.e., every statement that is susceptible to proof, can be
viewed as a type. Indeed, if a proposition $P$ is true, the corresponding
type is inhabited and it is possible to provide evidence or proof for $P$
using one of the elements of the type~$P$. If, however, a proposition $P$ is
false, the corresponding type is empty and it is impossible to provide a
proof for $P$. The type theory is rich enough to express the standard logical
propositions denoting conjunction, disjunction, implication, and existential
and universal quantifications. In addition, it is clear that the question of
whether two elements of a type are equal is a proposition, and hence that
this proposition must correspond to a type. In Agda, one may write proofs of
these propositions as shown in the two examples below:

\begin{multicols}{2}
\begin{code}
i0 : 3 ≡ 3
i0 = refl 3

i1 : (1 + 2) ≡ (3 * 1)
i1 = refl 3
\end{code}
\end{multicols}

\noindent More generally, given two values \AgdaBound{m} and \AgdaBound{n} of
type \AgdaPrimitiveType{ℕ}, it is possible to construct an element
\AgdaInductiveConstructor{refl} \AgdaBound{k} of the type \AgdaBound{m}
\AgdaDatatype{≡} \AgdaBound{n} if and only if \AgdaBound{m}, \AgdaBound{n},
and \AgdaBound{k} are all ``equal.'' As shown in example \AgdaFunction{i1},
this notion of \emph{propositional equality} is not just syntactic equality
but generalizes to \emph{definitional equality}, i.e., to equality that can
be established by normalizing the values to their normal forms.

An important question from the HoTT perspective is the following: given two
elements \AgdaBound{p} and \AgdaBound{q} of some type \AgdaBound{x}
\AgdaDatatype{≡} \AgdaBound{y} with
\AgdaBound{x}~\AgdaBound{y}~\AgdaSymbol{:}~\AgdaBound{A}, what can we say
about the elements of type \AgdaBound{p} \AgdaDatatype{≡} \AgdaBound{q}. Or,
in more familiar terms, given two proofs of some proposition $P$, are these
two proofs themselves ``equal.'' In some situations, the only interesting
property of proofs is their existence. This therefore suggests that the exact
sequence of logical steps in the proof is irrelevant, and ultimately that all
proofs of the same proposition are equivalent. This is however neither
necessary nor desirable. A twist that dates back to a paper by
\citet{Hofmann96thegroupoid} is that proofs actually possess a structure of
great combinatorial complexity. HoTT builds on this idea by interpreting
types as topological spaces or weak $\infty$-groupoids, and interpreting
identities between elements of a type
\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y} as \emph{paths} from the point
\AgdaBound{x} to the point \AgdaBound{y}. If \AgdaBound{x} and \AgdaBound{y}
are themselves paths, the elements of
\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y} become paths between paths
(2paths), or homotopies in the topological language. To be explicit, we will
often refer to types as \emph{spaces} which consist of \emph{points}, paths,
2paths, etc. and write $\AgdaDatatype{≡}_\AgdaBound{A}$ for the type of paths
in space \AgdaBound{A}.

As a simple example, we are used to thinking of types as sets of values. So
we typically view the type \AgdaPrimitiveType{Bool} as the figure on the left
but in HoTT we should instead think about it as the figure on the right where
there is a (trivial) path \AgdaInductiveConstructor{refl} \AgdaBound{b} from
each point \AgdaBound{b} to itself:
\[
\begin{tikzpicture}[scale=0.7]
  \draw (0,0) ellipse (2cm and 1cm);
  \draw[fill] (-1,0) circle (0.025);
  \node[below] at (-1,0) {false};
  \draw[fill] (1,0) circle (0.025);
  \node[below] at (1,0) {true};
\end{tikzpicture}
\qquad\qquad
\begin{tikzpicture}[scale=0.7]
  \draw (0,0) ellipse (2cm and 1cm);
  \draw[fill] (-1,0) circle (0.025);
  \draw[->,thick,cyan] (-1,0) arc (0:320:0.2);
  \node[above right] at (-1,0) {false};
  \draw[fill] (1,-0.2) circle (0.025);
  \draw[->,thick,cyan] (1,-0.2) arc (0:320:0.2);
  \node[above right] at (1,-0.2) {true};
\end{tikzpicture}
\]
In this particular case, it makes no difference, but in general we may have a
much more complicated path structure. The classical such example is the
topological \emph{circle} which is a space consisting of a point
\AgdaFunction{base} and a \emph{non trivial} path \AgdaFunction{loop} from
\AgdaFunction{base} to itself. As stated, this does not amount to
much. However, because paths carry additional structure (explained below),
that space has the following non-trivial structure:

\begin{center}
\begin{tikzpicture}[scale=0.74]
  \draw (-0.2,0) ellipse (5.5cm and 2.5cm);
  \draw[fill] (0,0) circle (0.025);
  \draw[->,thick,red] (0,0) arc (90:440:0.2);
  \node[above,red] at (0,0) {refl};
  \draw[->,thick,cyan] (0,0) arc (-180:140:0.7);
  \draw[->,thick,cyan] (0,0) arc (-180:150:1.2);
  \node[left,cyan] at (1.4,0) {loop};
  \node[right,cyan] at (2.4,0) {loop \AgdaSymbol{⊙} loop $\ldots$};
  \draw[->,thick,blue] (0,0) arc (360:40:0.7);
  \draw[->,thick,blue] (0,0) arc (360:30:1.2);
  \node[right,blue] at (-1.4,0) {!~loop};
  \node[left,blue] at (-2.3,0) {$\ldots$ !~loop \AgdaSymbol{⊙} !~loop};
\end{tikzpicture}
\end{center}

The additional structure of types is formalized as follows. Let
\AgdaBound{x}, \AgdaBound{y}, and \AgdaBound{z} be elements of some space
\AgdaBound{A}:
\begin{itemize}
\item For every path \AgdaBound{p} \AgdaSymbol{:} \AgdaBound{x}
  $\AgdaDatatype{≡}_\AgdaBound{A}$ \AgdaBound{y}, there exists a path
  \AgdaSymbol{!}  \AgdaBound{p} \AgdaSymbol{:} \AgdaBound{y}
  $\AgdaDatatype{≡}_\AgdaBound{A}$ \AgdaBound{x}; 
\item For every pair of paths \AgdaBound{p} \AgdaSymbol{:} \AgdaBound{x}
  $\AgdaDatatype{≡}_\AgdaBound{A}$ \AgdaBound{y} and \AgdaBound{q}
  \AgdaSymbol{:} \AgdaBound{y} $\AgdaDatatype{≡}_\AgdaBound{A}$
  \AgdaBound{z}, there exists a path \AgdaBound{p} \AgdaSymbol{⊙}
  \AgdaBound{q} \AgdaSymbol{:} \AgdaBound{x} $\AgdaDatatype{≡}_\AgdaBound{A}$
  \AgdaBound{z};
\item Subject to the following conditions:
\begin{itemize}
\item \AgdaBound{p} \AgdaSymbol{⊙} \AgdaInductiveConstructor{refl}
  \AgdaBound{y} $\AgdaDatatype{≡}_{(\AgdaBound{x} \AgdaDatatype{≡}_A
    \AgdaBound{y})}$ \AgdaBound{p}; 
\item \AgdaBound{p} $\AgdaDatatype{≡}_{(\AgdaBound{x} \AgdaDatatype{≡}_A
  \AgdaBound{y})}$ \AgdaInductiveConstructor{refl} \AgdaBound{x}
  \AgdaSymbol{⊙} \AgdaBound{p}
\item \AgdaSymbol{!} \AgdaBound{p} \AgdaSymbol{⊙} \AgdaBound{p}
  $\AgdaDatatype{≡}_{(\AgdaBound{y} \AgdaDatatype{≡}_A \AgdaBound{y})}$
  \AgdaInductiveConstructor{refl} \AgdaBound{y}
\item \AgdaBound{p} \AgdaSymbol{⊙} \AgdaSymbol{!} \AgdaBound{p}
  $\AgdaDatatype{≡}_{(\AgdaBound{x} \AgdaDatatype{≡}_A \AgdaBound{x})}$
  \AgdaInductiveConstructor{refl} \AgdaBound{x}
\item \AgdaSymbol{!} (\AgdaSymbol{!} \AgdaBound{p})
  $\AgdaDatatype{≡}_{(\AgdaBound{x} \AgdaDatatype{≡}_A \AgdaBound{y})}$
  \AgdaBound{p} 
\item \AgdaBound{p} \AgdaSymbol{⊙} (\AgdaBound{q} \AgdaSymbol{⊙}
  \AgdaBound{r}) $\AgdaDatatype{≡}_{(\AgdaBound{x} \AgdaDatatype{≡}_A
    \AgdaBound{z})}$ (\AgdaBound{p} \AgdaSymbol{⊙} \AgdaBound{q})
  \AgdaSymbol{⊙} \AgdaBound{r}
\end{itemize} 
\item This structure repeats one level up and so on ad infinitum.
\end{itemize}

\noindent A space that satisfies the properties above for $n$ levels is
called an $n$-groupoid.

%%%%%%%%%%%%%%%%%%
\subsection{Univalence} 

In addition to paths between the points within a space like
\AgdaPrimitiveType{Bool}, it is also possible to consider paths between the
space \AgdaPrimitiveType{Bool} and itself by considering
\AgdaPrimitiveType{Bool} as a ``point'' in the universe
\AgdaPrimitiveType{Set} of types. As usual, we have the trivial path which is
given by the constructor \AgdaInductiveConstructor{refl}:

\smallskip
\begin{code}
p : Bool ≡ Bool
p = refl Bool
\end{code}
\smallskip

\noindent There are, however, other (non trivial) paths between
\AgdaPrimitiveType{Bool} and itself and they are justified by the
\emph{univalence} \textbf{axiom}. As an example, the remainder of this
section justifies that there is a path between \AgdaPrimitiveType{Bool} and
itself corresponding to the boolean negation function.

We begin by formalizing the equivalence of functions
\AgdaSymbol{∼}. Intuitively, two functions are equivalent if their results
are propositionally equal for all inputs. A function \AgdaBound{f}
\AgdaSymbol{:} \AgdaBound{A} \AgdaSymbol{→} \AgdaBound{B} is called an
\emph{equivalence} if there are functions \AgdaBound{g} and \AgdaBound{h}
with whom its composition is the identity. Finally two spaces \AgdaBound{A}
and \AgdaBound{B} are equivalent, \AgdaBound{A} \AgdaSymbol{≃} \AgdaBound{B}, 
if there is an equivalence between them:

\smallskip
\begin{code}
_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) 
  : Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    h : B → A
    β : (h ∘ f) ∼ id

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv
\end{code}
\smallskip

We can now formally state the univalence axiom:

\smallskip
\begin{code}
postulate univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)
\end{code}
\smallskip

\noindent For our purposes, the important consequence of the univalence axiom
is that equivalence of spaces implies the existence of a path between the
spaces. In other words, in order to assert the existence of a path
\AgdaFunction{notpath} between \AgdaPrimitiveType{Bool} and itself, we need
to prove that the boolean negation function is an equivalence between the
space \AgdaPrimitiveType{Bool} and itself. This is easy to show:

\smallskip
\begin{code}
not2∼id : (not ∘ not) ∼ id 
not2∼id false  =  refl false
not2∼id true   =  refl true

notequiv : Bool ≃ Bool
notequiv = (not , 
            record {
            g = not ; α = not2∼id ; h = not ; β = not2∼id })

notpath : Bool ≡ Bool
notpath with univalence
... | (_ , eq) = isequiv.g eq notequiv
\end{code}
\smallskip

\noindent Although the code asserting the existence of a non trivial path
between \AgdaPrimitiveType{Bool} and itself ``compiles,'' it is no longer
executable as it relies on an Agda postulate. In the next section, we analyze
this situation from the perspective of reversible programming languages based
on type isomorphisms~\cite{James:2012:IE:2103656.2103667,rc2011,rc2012}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Computing with Type Isomorphisms}
\label{pi}

The main syntactic vehicle for the technical developments in this paper is a
simple language called $\Pi$ whose only computations are isomorphisms between
finite types~\citeyearpar{James:2012:IE:2103656.2103667}. After reviewing the
motivation for this language and its relevance to HoTT, we present its syntax
and semantics.

\begin{figure*}[ht]
\[\begin{array}{cc}
\begin{array}{rrcll}
\identlp :&  0 + \tau & \iso & \tau &: \identrp \\
\swapp :&  \tau_1 + \tau_2 & \iso & \tau_2 + \tau_1 &: \swapp \\
\assoclp :&  \tau_1 + (\tau_2 + \tau_3) & \iso & (\tau_1 + \tau_2) + \tau_3 
  &: \assocrp \\
\identlt :&  1 * \tau & \iso & \tau &: \identrt \\
\swapt :&  \tau_1 * \tau_2 & \iso & \tau_2 * \tau_1 &: \swapt \\
\assoclt :&  \tau_1 * (\tau_2 * \tau_3) & \iso & (\tau_1 * \tau_2) * \tau_3 
  &: \assocrt \\
\distz :&~ 0 * \tau & \iso & 0 &: \factorz \\
\dist :&~ (\tau_1 + \tau_2) * \tau_3 & 
  \iso & (\tau_1 * \tau_3) + (\tau_2 * \tau_3)~ &: \factor 
\end{array}
& 
\begin{minipage}{0.5\textwidth}
\begin{center} 
\Rule{}
{}
{\jdg{}{}{\idc : \tau \iso \tau}}
{}
\qquad
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_2 \iso \tau_3}
{\jdg{}{}{c_1 \fatsemi c_2 : \tau_1 \iso \tau_3}}
{}
\qquad
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \oplus c_2 : \tau_1 + \tau_3 \iso \tau_2 + \tau_4}}
{}
\qquad
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \otimes c_2 : \tau_1 * \tau_3 \iso \tau_2 * \tau_4}}
{}
\end{center}
\end{minipage}
\end{array}\]
\caption{$\Pi$-combinators~\cite{James:2012:IE:2103656.2103667}
\label{pi-combinators}}
\end{figure*}

%%%%%%%%%%%%%%%%%%%%%
\subsection{Reversibility} 

The relevance of reversibility to HoTT is based on the following
analysis. The conventional HoTT approach starts with two, a priori, different
notions: functions and paths, and then postulates an equivalence between a
particular class of functions and paths. As illustrated above, some functions
like \AgdaFunction{not} correspond to paths. Most functions, however, are
evidently unrelated to paths. In particular, any function of type
\AgdaBound{A}~\AgdaSymbol{→}~\AgdaBound{B} that does not have an inverse of
type \AgdaBound{B}~\AgdaSymbol{→}~\AgdaBound{A} cannot have any direct
correspondence to paths as all paths have inverses. An interesting question
then poses itself: since reversible computational models --- in which all
functions have inverses --- are known to be universal computational models,
what would happen if we considered a variant of HoTT based exclusively on
reversible functions?  Presumably in such a variant, all functions --- being
reversible --- would potentially correspond to paths and the distinction
between the two notions would vanish making the univalence postulate
unnecessary. This is the precise technical idea we investigate in detail in
the remainder of the paper.

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Syntax and Semantics of $\Pi$}
\label{opsempi}

The $\Pi$ family of languages is based on type isomorphisms. In the variant
we consider, the set of types $\tau$ includes the empty type 0, the unit type
1, and conventional sum and product types. The values classified by these
types are the conventional ones: $()$ of type 1, $\inl{v}$ and $\inr{v}$ for
injections into sum types, and $(v_1,v_2)$ for product types:
\[\begin{array}{lrcl}
(\textit{Types}) & 
  \tau &::=& 0 \alt 1 \alt \tau_1 + \tau_2 \alt \tau_1 * \tau_2 \\
(\textit{Values}) & 
  v &::=& () \alt \inl{v} \alt \inr{v} \alt (v_1,v_2) \\
(\textit{Combinator types}) &&& \tau_1 \iso \tau_2 \\
(\textit{Combinators}) & 
  c &::=& [\textit{see Fig.~\ref{pi-combinators}}]
\end{array}\]
The interesting syntactic category of $\Pi$ is that of \emph{combinators}
which are witnesses for type isomorphisms $\tau_1 \iso \tau_2$. They consist
of base combinators (on the left side of Fig.~\ref{pi-combinators}) and
compositions (on the right side of the same figure). Each line of the figure
on the left introduces a pair of dual constants\footnote{where $\swapp$ and
$\swapt$ are self-dual.} that witness the type isomorphism in the
middle. This set of isomorphisms is known to be
complete~\cite{Fiore:2004,fiore-remarks} and the language is universal for
hardware combinational
circuits~\cite{James:2012:IE:2103656.2103667}.\footnote{If recursive types
and a trace operator are added, the language becomes Turing
complete~\cite{James:2012:IE:2103656.2103667,rc2011}. We will not be
concerned with this extension in the main body of this paper but it will be
briefly discussed in the conclusion.}

From the perspective of category theory, the language $\Pi$ models what is
called a \emph{symmetric bimonoidal category} or a \emph{commutative rig
category}. These are categories with two binary operations and satisfying the
axioms of a commutative rig (i.e., a commutative ring without negative
elements also known as a commutative semiring) up to coherent
isomorphisms. And indeed the types of the $\Pi$-combinators are precisely the
commutative semiring axioms. A formal way of saying this is that $\Pi$ is the
\emph{categorification}~\cite{math/9802029} of the natural numbers. A simple
(slightly degenerate) example of such categories is the category of finite
sets and permutations in which we interpret every $\Pi$-type as a finite set,
interpret the values as elements in these finite sets, and interpret the
combinators as permutations. 

\begin{figure}[ht]
\[\begin{array}{r@{\!}lcl}
\evalone{\identlp}{&(\inr{v})} &=& v \\
\evalone{\identrp}{&v} &=& \inr{v} \\
\evalone{\swapp}{&(\inl{v})} &=& \inr{v} \\
\evalone{\swapp}{&(\inr{v})} &=& \inl{v} \\
\evalone{\assoclp}{&(\inl{v})} &=& \inl{(\inl{v})} \\
\evalone{\assoclp}{&(\inr{(\inl{v})})} &=& \inl{(\inr{v})} \\
\evalone{\assoclp}{&(\inr{(\inr{v})})} &=& \inr{v} \\
\evalone{\assocrp}{&(\inl{(\inl{v})})} &=& \inl{v} \\
\evalone{\assocrp}{&(\inl{(\inr{v})})} &=& \inr{(\inl{v})} \\
\evalone{\assocrp}{&(\inr{v})} &=& \inr{(\inr{v})} \\
\evalone{\identlt}{&((),v)} &=& v \\
\evalone{\identrt}{&v} &=& ((),v) \\
\evalone{\swapt}{&(v_1,v_2)} &=& (v_2,v_1) \\
\evalone{\assoclt}{&(v_1,(v_2,v_3))} &=& ((v_1,v_2),v_3) \\
\evalone{\assocrt}{&((v_1,v_2),v_3)} &=& (v_1,(v_2,v_3)) \\
\evalone{\dist}{&(\inl{v_1},v_3)} &=& \inl{(v_1,v_3)} \\
\evalone{\dist}{&(\inr{v_2},v_3)} &=& \inr{(v_2,v_3)} \\
\evalone{\factor}{&(\inl{(v_1,v_3)})} &=& (\inl{v_1},v_3) \\
\evalone{\factor}{&(\inr{(v_2,v_3)})} &=& (\inr{v_2},v_3) \\
\evalone{\idc}{&v} &=& v \\
\evalone{(c_1 \fatsemi c_2)}{&v} &=& 
  \evalone{c_2}{(\evalone{c_1}{v})} \\
\evalone{(c_1\oplus c_2)}{&(\inl{v})} &=& 
  \inl{(\evalone{c_1}{v})} \\
\evalone{(c_1\oplus c_2)}{&(\inr{v})} &=& 
  \inr{(\evalone{c_2}{v})} \\
\evalone{(c_1\otimes c_2)}{&(v_1,v_2)} &=& 
  (\evalone{c_1}v_1, \evalone{c_2}v_2) 
\end{array}\]
\caption{\label{opsem}Operational Semantics}
\end{figure}

In the remainder of this paper, we will be more interested in a model based
on groupoids. But first, we give an operational semantics for $\Pi$.
Operationally, the semantics consists of a pair of mutually recursive
evaluators that take a combinator and a value and propagate the value in the
``forward'' $\triangleright$ direction or in the
``backwards''~$\triangleleft$ direction. We show the complete forward
evaluator in Fig.~\ref{opsem}; the backwards evaluator differs in trivial
ways. 

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Groupoid Model} 

Instead of modeling the types of $\Pi$ using sets and the combinators using
permutations we use a semantics that identifies $\Pi$-combinators with
\emph{paths}. More precisely, we model the universe of $\Pi$-types as a space
\AgdaFunction{U} whose points are the individual $\Pi$-types (which are
themselves spaces \AgdaBound{t} containing points). We then postulate that
there is path between the spaces \AgdaBound{t₁} and \AgdaBound{t₂} if there
is a $\Pi$-combinator $c : t_1 \iso t_2$. Our postulate is similar in spirit
to the univalence axiom but, unlike the latter, it has a simple computational
interpretation. A path directly corresponds to a type isomorphism with a
clear operational semantics as presented in the previous section. As we will
explain in more detail below, this approach replaces the datatype
\AgdaSymbol{≡} modeling propositional equality with the datatype
\AgdaSymbol{⟷} modeling type isomorphisms. With this switch, the
$\Pi$-combinators of Fig.~\ref{pi-combinators} become \emph{syntax} for the
paths in the space $U$. Put differently, instead of having exactly one
constructor \AgdaInductiveConstructor{refl} for paths with all other paths
discovered by proofs (see Secs. 2.5--2.12 of the HoTT
book~\citeyearpar{hottbook}) or postulated by the univalence axiom, we have
an \emph{inductive definition} that completely specifies all the paths in the
space $U$.

We begin with the datatype definition of the universe \AgdaFunction{U} of finite
types which are constructed using \AgdaInductiveConstructor{ZERO},
\AgdaInductiveConstructor{ONE}, \AgdaInductiveConstructor{PLUS}, and
\AgdaInductiveConstructor{TIMES}. Each of these finite types will correspond
to a set of points with paths connecting some of the points. The underlying
set of points is computed by \AgdaSymbol{⟦}\_\AgdaSymbol{⟧} as follows:
\AgdaInductiveConstructor{ZERO} maps to the empty set~\AgdaSymbol{⊥},
\AgdaInductiveConstructor{ONE} maps to the singleton set \AgdaSymbol{⊤},
\AgdaInductiveConstructor{PLUS} maps to the disjoint union \AgdaSymbol{⊎},
and \AgdaInductiveConstructor{TIMES} maps to the cartesian product
\AgdaSymbol{×}.

\smallskip
\begin{code} 
data U : Set where
  ZERO   : U
  ONE    : U
  PLUS   : U → U → U
  TIMES  : U → U → U

⟦_⟧ : U → Set
⟦ ZERO ⟧         = ⊥ 
⟦ ONE ⟧          = ⊤
⟦ PLUS t₁ t₂ ⟧   = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧  = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
\end{code} 
\smallskip

We want to identify paths with $\Pi$-combinators. There is a small
complication however: paths are ultimately defined between points but the
$\Pi$-combinators of Fig.~\ref{pi-combinators} are defined between spaces. We
can bridge this gap using a popular HoTT concept, that of \emph{pointed
  spaces}. A pointed space \pointed{\AgdaBound{t}}{\AgdaBound{v}} is a space
\AgdaBound{t} \AgdaSymbol{:} \AgdaFunction{U} with a distinguished value
\AgdaBound{v} \AgdaSymbol{:} \AgdaSymbol{⟦} \AgdaBound{t} \AgdaSymbol{⟧}:

\smallskip
\begin{code} 
record U• : Set where
  constructor •[_,_]
  field
    ∣_∣  : U
    •    : ⟦ ∣_∣ ⟧
\end{code}
\smallskip

\AgdaHide{
\begin{code}
open U•
\end{code}
}

\begin{figure*}[ht]
\begin{multicols}{2}
\begin{code} 
data _⟷_ : U• → U• → Set where
  unite₊ : ∀ {t v} → •[ PLUS ZERO t , inj₂ v ] ⟷ •[ t , v ]
  uniti₊ : ∀ {t v} → •[ t , v ] ⟷ •[ PLUS ZERO t , inj₂ v ]
  swap1₊ : ∀ {t₁ t₂ v₁} → 
    •[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₂ t₁ , inj₂ v₁ ]
  swap2₊ : ∀ {t₁ t₂ v₂} → 
    •[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₂ t₁ , inj₁ v₂ ]
  assocl1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ]
  assocl2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ]
  assocl3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ]
  assocr1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] 
  assocr2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] 
  assocr3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
  unite⋆ : ∀ {t v} → •[ TIMES ONE t , (tt , v) ] ⟷ •[ t , v ]
  uniti⋆ : ∀ {t v} → •[ t , v ] ⟷ •[ TIMES ONE t , (tt , v) ] 
  swap⋆ : ∀ {t₁ t₂ v₁ v₂} → 
    •[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₂ t₁ , (v₂ , v₁) ]
  assocl⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ] ⟷ 
            •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ]
  assocr⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ] ⟷ 
            •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ]
  distz : ∀ {t v absurd} → 
    •[ TIMES ZERO t , (absurd , v) ] ⟷ •[ ZERO , absurd ]
  factorz : ∀ {t v absurd} → 
    •[ ZERO , absurd ] ⟷ •[ TIMES ZERO t , (absurd , v) ]
  dist1 : ∀ {t₁ t₂ t₃ v₁ v₃} → 
    •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ⟷ 
    •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ]
  dist2 : ∀ {t₁ t₂ t₃ v₂ v₃} → 
    •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ⟷ 
    •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ]
  factor1 : ∀ {t₁ t₂ t₃ v₁ v₃} → 
    •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ⟷ 
    •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ]
  factor2 : ∀ {t₁ t₂ t₃ v₂ v₃} → 
    •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ⟷ 
    •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ]
  id⟷ : ∀ {t v} → •[ t , v ] ⟷ •[ t , v ]
  _◎_ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
    (•[ t₂ , v₂ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ])
  _⊕1_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
    (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
    (•[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₃ t₄ , inj₁ v₃ ])
  _⊕2_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
    (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
    (•[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₃ t₄ , inj₂ v₄ ])
  _⊗_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
    (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
    (•[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₃ t₄ , (v₃ , v₄) ])
\end{code} 
\end{multicols}
\caption{Pointed version of $\Pi$-combinators or inductive definition of paths
\label{pointedcomb}}
\end{figure*}

\noindent Given pointed spaces, it is possible to re-express the
$\Pi$-combinators as shown in Fig.~\ref{pointedcomb}. The new presentation of
combinators directly relates points to points and in fact subsumes the
operational semantics of Fig.~\ref{opsem}. For example
\AgdaInductiveConstructor{swap1₊} is still an operation from the space
\AgdaInductiveConstructor{PLUS} \AgdaBound{t₁} \AgdaBound{t₂} to itself but
in addition it specifies that, within that spaces, it maps the point
\AgdaInductiveConstructor{inj₁} \AgdaBound{v₁} to the point
\AgdaInductiveConstructor{inj₂} \AgdaBound{v₁}.

We note that the refinement of the $\Pi$-combinators to combinators on
pointed spaces is given by an inductive family for \emph{heterogeneous}
equality that generalizes the usual inductive family for propositional
equality. Put differently, what used to be the only constructor for paths
\AgdaInductiveConstructor{refl} is now just one of the many constructors
(named \AgdaInductiveConstructor{id⟷} in the figure). Among the new
constructors and we have \AgdaInductiveConstructor{◎} that constructs path
compositions. By construction, every combinator has an inverse calculated as
shown in Fig.~\ref{sym}. These constructions are sufficient to guarantee that
the universe~\AgdaFunction{U} is a groupoid. Additionally, we have paths that
connect values in different but isomorphic spaces like
\pointed{{\AgdaInductiveConstructor{TIMES} \AgdaBound{t₁}
\AgdaBound{t₂}}}{{\AgdaSymbol{(} \AgdaBound{v₁} \AgdaSymbol{,} \AgdaBound{v₂}
\AgdaSymbol{)}}} and \pointed{{\AgdaInductiveConstructor{TIMES}
\AgdaBound{t₂} \AgdaBound{t₁}}}{{\AgdaSymbol{(} \AgdaBound{v₂} \AgdaSymbol{,}
\AgdaBound{v₁} \AgdaSymbol{)}}}.

\begin{figure}[ht]
\setlength{\columnsep}{15pt}
\begin{multicols}{2}
\begin{code}
! : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊      = uniti₊
! uniti₊      = unite₊
! swap1₊      = swap2₊
! swap2₊      = swap1₊
! assocl1₊    = assocr1₊
! assocl2₊    = assocr2₊
! assocl3₊    = assocr3₊
! assocr1₊    = assocl1₊
! assocr2₊    = assocl2₊
! assocr3₊    = assocl3₊
! unite⋆      = uniti⋆
! uniti⋆      = unite⋆
! swap⋆       = swap⋆


! assocl⋆     = assocr⋆
! assocr⋆     = assocl⋆
! distz       = factorz
! factorz     = distz
! dist1       = factor1 
! dist2       = factor2 
! factor1     = dist1 
! factor2     = dist2 
! id⟷         = id⟷
! (c₁ ◎ c₂)   = ! c₂ ◎ ! c₁ 
! (c₁ ⊕1 c₂)  = ! c₁ ⊕1 ! c₂ 
! (c₁ ⊕2 c₂)  = ! c₁ ⊕2 ! c₂ 
! (c₁ ⊗ c₂)   = ! c₁ ⊗ ! c₂ 
\end{code}
\end{multicols}
\caption{\label{sym}Pointed Combinators or paths inverses}
\end{figure}



The example \AgdaFunction{notpath} which earlier required the use of the
univalence axiom can now be directly defined using
\AgdaInductiveConstructor{swap1₊} and \AgdaInductiveConstructor{swap2₊}. To
see this, note that \AgdaPrimitiveType{Bool} can be viewed as a shorthand for
\AgdaInductiveConstructor{PLUS} \AgdaInductiveConstructor{ONE}
\AgdaInductiveConstructor{ONE} with \AgdaInductiveConstructor{true} and
\AgdaInductiveConstructor{false} as shorthands for
\AgdaInductiveConstructor{inj₁} \AgdaInductiveConstructor{tt} and
\AgdaInductiveConstructor{inj₂} \AgdaInductiveConstructor{tt}. With this in
mind, the path corresponding to boolean negation consists of two ``fibers'',
one for each boolean value as shown below:

\smallskip
\begin{code}
data Path (t₁ t₂ : U•) : Set where
  path : (c : t₁ ⟷ t₂) → Path t₁ t₂

BOOL : U
BOOL = PLUS ONE ONE

TRUE FALSE : ⟦ BOOL ⟧
TRUE   = inj₁ tt
FALSE  = inj₂ tt

BOOL•F : U•
BOOL•F = •[ BOOL , FALSE ]

BOOL•T : U•
BOOL•T = •[ BOOL , TRUE ]

NOT•T : BOOL•T ⟷ BOOL•F
NOT•T = swap1₊

NOT•F : BOOL•F ⟷ BOOL•T
NOT•F = swap2₊

notpath•T : Path BOOL•T BOOL•F
notpath•T = path NOT•T

notpath•F : Path BOOL•F BOOL•T
notpath•F = path NOT•F
\end{code} 
\smallskip

\noindent In other words, a path between spaces is really a collection of
paths connecting the various points. Note however that we never need to
``collect'' these paths using a universal quantification.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Computing with Paths} 

The previous section presented a language $\Pi$ whose computations are all
the possible isomorphisms between finite types. (Recall that the commutative
semiring structure is sound and complete for isomorphisms between finite
types~\cite{Fiore:2004,fiore-remarks}.) Instead of working with arbitrary
functions, then restricting them to equivalences, and then postulating that
these equivalences give rise to paths, the approach based on $\Pi$ starts
directly with the full set of possible isomorphisms and encodes it as an
inductive datatype of paths between pointed spaces. The resulting structure
is evidently a 1-groupoid as the isomorphisms are closed under inverses and
composition. We now investigate the higher groupoid structure. 

The pleasant result will be that the higher groupoid structure will result
from another ``lifted'' version of $\Pi$ in which computations manipulate
paths. The lifted version will have all the combinators from
Fig.~\ref{pointedcomb} to manipulate collections of paths (e.g., sums of
products of paths) in addition to combinators that work on individual
paths. The latter combinators will capture the higher groupoid structure
relating for example, the path \AgdaInductiveConstructor{id⟷} \AgdaSymbol{◎}
\AgdaBound{c} with \AgdaBound{c}. Computations in the lifted $\Pi$ will
therefore correspond to 2paths and the entire scheme can be repeated over
and over to capture the concept of weak $\infty$-groupoids.

%% Note:
%% x : {A B : Set} → (A ≃ B) ≃ (A ≃ B)
%% x = (id , mkisequiv id refl id refl)

%%%%%%%%%%%%%%%%%
\subsection{Examples}

We start with a few examples where we define a collection of paths
\AgdaFunction{p₁} to \AgdaFunction{p₅} all from the pointed space
\pointed{\AgdaFunction{BOOL}}{\AgdaFunction{TRUE}} to the pointed space
\pointed{\AgdaFunction{BOOL}}{\AgdaFunction{FALSE}}:

\smallskip
\begin{code}
T⟷F : Set
T⟷F = Path BOOL•T BOOL•F

p₁ p₂ p₃ p₄ p₅ : T⟷F
p₁ = path NOT•T
p₂ = path (id⟷ ◎ NOT•T)
p₃ = path (NOT•T ◎ NOT•F ◎ NOT•T)
p₄ = path (NOT•T ◎ id⟷)
p₅ = path  (uniti⋆ ◎ swap⋆ ◎ (NOT•T ⊗ id⟷) ◎ 
           swap⋆ ◎ unite⋆)
\end{code}
\smallskip

\noindent All the paths start at \AgdaFunction{TRUE} and end at
\AgdaFunction{FALSE} but follow different intermediate paths along the
way. Informally \AgdaFunction{p₁} is the most ``efficient'' canonical way of
connecting \AgdaFunction{TRUE} to \AgdaFunction{FALSE} via the appropriate
fiber of the boolean negation. Path \AgdaFunction{p₂} starts with the trivial
path from \AgdaFunction{TRUE} to itself and then uses the boolean
negation. The first step is clearly superfluous and hence we expect, via the
groupoid laws, to have a 2path connecting \AgdaFunction{p₂} to
\AgdaFunction{p₁}. Path \AgdaFunction{p₃} does not syntactically refer to a
trivial path but instead uses what is effectively a trivial path that follows
a negation path and then its inverse. We also expect to have a 2path between
this path and the other ones. Path \AgdaFunction{p₄} is also evidently
equivalent to the others but the situation with path \AgdaFunction{p₅} is
more subtle. We defer the discussion until we formally define 2paths. For
now, we note that --- viewed extensionally --- each path connects
\AgdaFunction{TRUE} to \AgdaFunction{FALSE} and hence all the paths are
extensionally equivalent.  In the conventional approach to programming
language semantics, which is also followed in the current formalization of
HoTT, this extensional equivalence would then be used to justify the
existence of the 2paths. In our setting, we do \emph{not} need to reason
using extensional methods since all functions (paths) are between pointed
spaces (i.e., are point to point) and we have an inductive definition of
paths which can be used to define computational rules that simplify paths as
shown next.

%%%%%%%%%%%%%%%%%
\subsection{Path Induction}

only REVERSIBLE functions from paths to paths are allowed. we could write
these functions as functions and prove inverses etc but then we are back to
the extensional view. better to axiomatize the groupoid laws using
combinators

In the conventional formalization to HoTT, the groupoid laws are a
consequence of \emph{path induction}. The situation is similar in our case
but with an important difference: our inductively defined type family of
paths includes many more constructors than just
\AgdaInductiveConstructor{refl}. Consider for example, the inductively
defined function \AgdaFunction{!} in Fig.~\ref{sym} which shows
that each path has an inverse by giving the computational rule for
calculating that inverse. We will use this definition to postulate a 2path
between \AgdaInductiveConstructor{??} \AgdaBound{c} and
\AgdaFunction{!} \AgdaBound{c}. More generally, we can postulate a
2-path between any path \AgdaBound{c} \AgdaSymbol{:} \AgdaSymbol{(}
\AgdaBound{t₁} \AgdaFunction{⟷} \AgdaBound{t₂} \AgdaSymbol{)} and the result
of replacing any constructor \AgdaInductiveConstructor{cons} in \AgdaBound{c}
by an inductively defined function \AgdaFunction{fcons}. The intuitive reason
this is correct is that the functional version of the constructor
\AgdaFunction{fcons} must respect the types which means it is extensionally
equivalent to the constructor itself as all the types are pointed. For
example, if \AgdaInductiveConstructor{??} \AgdaBound{c} maps
\AgdaFunction{FALSE} to \AgdaFunction{TRUE}, the result of
\AgdaFunction{!} \AgdaBound{c} must also do the same.

In the following we will use, without giving the full definitions, the
following inductive functions that can be used to replace various patterns of
constructors:
\begin{itemize}
\item \AgdaFunction{simplifyl◎} 
\item \AgdaFunction{simplifyr◎} 
\item 
\item 
\item 

\end{itemize}


We can similarly perform nested induction to simplify path composition. We
omit this large function but show a couple of interesting cases:

%%%%%%%%%%%%%%%%%%%%%
\subsection{Level 1 $\Pi$}

regular pi is level 0

\begin{code}
data 2U : Set where
  2ZERO  : 2U
  2ONE   : 2U
  2PLUS  : 2U → 2U → 2U
  2TIMES : 2U → 2U → 2U
  PATH   : (t₁ t₂ : U•) → 2U

2⟦_⟧ : 2U → Set
2⟦ 2ZERO ⟧         = ⊥
2⟦ 2ONE ⟧          = ⊤
2⟦ 2PLUS t₁ t₂ ⟧   = 2⟦ t₁ ⟧ ⊎ 2⟦ t₂ ⟧
2⟦ 2TIMES t₁ t₂ ⟧  = 2⟦ t₁ ⟧ × 2⟦ t₂ ⟧
2⟦ PATH t₁ t₂ ⟧    = Path t₁ t₂

\end{code}
              -- empty set of paths
              -- a trivial path
      -- disjoint union of paths
      -- pairs of paths
 -- level 0 paths between values
groupoid laws not enough

the equivalent of path induction is the induction principle for the type
family defining paths

\begin{code}
record 2U• : Set where
  constructor 2•[_,_]
  field
    2∣_∣ : 2U
    2• : 2⟦ 2∣_∣ ⟧
\end{code}
\smallskip

\AgdaHide{
\begin{code}
open 2U•
\end{code}
}




Simplify various compositions

We need to show that the groupoid path structure is faithfully
represented. The combinator $\idc$ introduces all the $\refl{\tau} : \tau
\equiv \tau$ paths in $U$. The adjoint introduces an inverse path
$!p$ for each path $p$ introduced by $c$. The composition operator $\fatsemi$
introduces a path $p$ \AgdaSymbol{⊙} $q$ for every pair of paths whose endpoints
match. In addition, we get paths like $\swapp$ between $\tau_1+\tau_2$ and
$\tau_2+\tau_1$. The existence of such paths in the conventional HoTT needs
to proved from first principles for some types and \emph{postulated} for the
universe type by the univalence axiom. The $\otimes$-composition gives a path
$(p,q) : (\tau_1*\tau_2) \equiv (\tau_3*\tau_4)$ whenever we have paths $p :
\tau_1 \equiv \tau_3$ and $q : \tau_2 \equiv \tau_4$. A similar situation for
the $\oplus$-composition. The structure of these paths must be discovered and
these paths must be \emph{proved} to exist using path induction in the
conventional HoTT development. So far, this appears too good to be true, and
it is. The problem is that paths in HoTT are subject to rules discussed at
the end of Sec.~\ref{hott}. For example, it must be the case that if $p :
\tau_1 \equiv_U \tau_2$ that $(p \circ \refl{\tau_2})
\equiv_{\tau_1\equiv_U\tau_2} p$.  This path lives in a higher universe:
nothing in our $\Pi$-combinators would justify adding such a path as all our
combinators map types to types. No combinator works one level up at the space
of combinators and there is no such space in the first place. Clearly we are
stuck unless we manage to express a notion of higher-order functions in
$\Pi$. This would allow us to internalize the type $\tau_1\iso\tau_2$ as a
$\Pi$-type which is then manipulated by the same combinators one level higher
and so on.

Structure of Paths:
\begin{itemize}
\item What do paths in $A \times B$ look like?  We can
prove that $(a_1,b_1) \equiv (a_2,b_2)$ in $A \times B$ iff $a_1 \equiv
a_2$ in $A$ and $b_1 \equiv b_2$ in $B$.
\item What do paths in $A_1 \uplus A_2$ look like? 
We can prove that $\mathit{inj}_i~x \equiv \mathit{inj}_j~y$ 
 in $A_1 \uplus A_2$ iff $i=j$ and $x \equiv y$ in $A_i$.
\item What do paths in $A \rightarrow B$ look like?
We cannot prove anything. Postulate function
extensionality axiom.
\item What do paths in $\mathrm{Set}_{\ell}$ look like?
We cannot prove anything. Postulate univalence axiom.
\end{itemize}

Let's start with a few simple types built from the empty type, the unit type,
sums, and products, and let's study the paths postulated by HoTT.

For every value in a type (point in a space) we have a trivial path from the
value to itself:



Level 0: 
Types at this level are just plain sets with no interesting path structure. 
The path structure is defined at levels 1 and beyond. 




for examples of 2 paths look at proofs of 
path assoc; triangle and pentagon rules

the idea I guess is that instead of having the usual evaluator where
values flow, we want an evaluator that rewrites the circuit to primitive
isos; for that we need some normal form for permutations and a proof that
we can rewrite any circuit to this normal form

plan after that: add trace; this make obs equiv much more interesting and
allows a limited form of h.o. functions via the int construction and then
do the ring completion to get more complete notion of h.o. functions

Level 1: 
Types are sets of paths. The paths are defined at the previous level
(level 0). At level 1, there is no interesting 2path structure. From
the perspective of level 0, we have points with non-trivial paths between
them, i.e., we have a groupoid. The paths cross type boundaries, i.e., we
have heterogeneous equality

%%%%%%%%%%%%%%%%%%%%%%
\subsection{2Paths}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Int Construction}
\label{intc}

2paths are functions on paths; the int construction reifies these
functions/2paths as 1paths

In the context of monoidal categories, it is known that a notion of
higher-order functions emerges from having an additional degree of
\emph{symmetry}. In particular, both the \textbf{Int} construction of Joyal,
Street, and Verity~\citeyearpar{joyal1996traced} and the closely related
$\mathcal{G}$ construction of linear logic~\cite{gcons} construct
higher-order \emph{linear} functions by considering a new category built on
top of a given base traced monoidal category. The objects of the new category
are of the form $\nodet{\tau_1}{\tau_2}$ where~$\tau_1$ and~$\tau_2$ are
objects in the base category. Intuitively, this object represents the
\emph{difference} $\tau_1-\tau_2$ with the component $\tau_1$ viewed as
conventional type whose elements represent values flowing, as usual, from
producers to consumers, and the component $\tau_2$ viewed as a \emph{negative
  type} whose elements represent demands for values or equivalently values
flowing backwards. Under this interpretation, and as we explain below, a
function is nothing but an object that converts a demand for an argument into
the production of a result.

We begin our formal development by extending $\Pi$ with a new universe of
types $\cubt$ that consists of composite types $\nodet{\tau_1}{\tau_2}$:
\[\begin{array}{lrcl}
(\textit{{1d} types}) & 
  \cubt &::=& \nodet{\tau_1}{\tau_2}
\end{array}\]
In anticipation of future developments, we will refer to the original types
$\tau$ as 0-dimensional (0d) types and to the new types $\cubt$ as
1-dimensional (1d) types. It turns out that, except for one case discussed
below, the 1d level is a ``lifted'' instance of $\Pi$ with its own notions of
empty, unit, sum, and product types, and its corresponding notion of
isomorphisms on these 1d types.

Our next step is to define lifted versions of the 0d types:
\[\begin{array}{rcl}
\ztone &\eqdef& \nodet{0}{0} \\
\otone &\eqdef& \nodet{1}{0} \\
\ptone{\nodet{\tau_1}{\tau_2}}{\nodet{\tau_3}{\tau_4}} &\eqdef& 
  \nodet{\tau_1+\tau_3}{\tau_2+\tau_4} \\
\ttone{\nodet{\tau_1}{\tau_2}}{\nodet{\tau_3}{\tau_4}} &\eqdef& \\
\noalign{\hfill$\nodet{(\tau_1*\tau_3)+(\tau_2*\tau_4)}{(\tau_1*\tau_4)+(\tau_2*\tau_3)}$}
\end{array}\]
Building on the idea that $\Pi$ is a categorification of the natural numbers
and following a long tradition that relates type isomorphisms and arithmetic
identities~\cite{DiCosmo:2005:SSI:1090732.1090734}, one is tempted to think
that the \textbf{Int} construction (as its name suggests) produces a
categorification of the integers. Based on this hypothesis, the definitions
above can be intuitively understood as arithmetic identities. The same
arithmetic intuition explains the lifting of isomorphisms to 1d types:
\[\begin{array}{rcl}
\nodet{\tau_1}{\tau_2} \isoone \nodet{\tau_3}{\tau_4} &\eqdef& 
  (\tau_1+\tau_4) \iso (\tau_2+\tau_3)
\end{array}\]
In other words, an isomorphism between 1d types is really an isomorphism
between ``re-arranged'' 0d types where the negative input $\tau_2$ is viewed
as an output and the negative output $\tau_4$ is viewed as an input. Using
these ideas, it is now a fairly standard exercise to define the lifted
versions of most of the combinators in
Table~\ref{pi-combinators}.\footnote{See
  Krishnaswami's~\citeyearpar{neelblog} excellent blog post implementing this
  construction in OCaml.} There are however a few interesting cases whose
appreciation is essential for the remainder of the paper that we discuss
below.

\paragraph*{Easy Lifting.} Many of the 0d combinators lift easily to the 1d
level. For example:
\[\begin{array}{rcl}
\idc &:& \cubt \isoone \cubt \\
     &:& \nodet{\tau_1}{\tau_2} \isoone \nodet{\tau_1}{\tau_2} \\
     &\eqdef& (\tau_1+\tau_2) \iso (\tau_2+\tau_1) \\
\idc &=& \swapp \\
\\
\identlp &:& \ztone \boxplus \cubt \isoone \cubt \\
%%         &\eqdef& (0+\tau_1)-(0+\tau_2) \isoone (\tau_1-\tau_2) \\
%%         &\eqdef& ((0+\tau_1)+\tau_2) \iso ((0+\tau_2)+\tau_1) \\
         &=& \assocrp \fatsemi (\idc \oplus \swapp) \fatsemi \assoclp
\end{array}\]

\paragraph*{Composition using $\mathit{trace}$.} 

\[\begin{array}{r@{\,\,\!}cl}
(\fatsemi) &:& 
  (\cubt_1 \isoone \cubt_2) \rightarrow 
  (\cubt_2 \isoone \cubt_3) \rightarrow 
  (\cubt_1 \isoone \cubt_3) \\
%% \mathit{seq} &:& 
%%   ((\tau_1-\tau_2) \isoone (\tau_3-\tau_4)) \rightarrow
%%   ((\tau_3-\tau_4) \isoone (\tau_5-\tau_6)) \rightarrow
%%   ((\tau_1-\tau_2) \isoone (\tau_5-\tau_6)) \\
%%   &\eqdef& 
%%   ((\tau_1+\tau_4) \iso (\tau_2+\tau_3)) \rightarrow
%%   ((\tau_3+\tau_6) \iso (\tau_4+\tau_5)) \rightarrow
%%   ((\tau_1+\tau_6) \iso (\tau_2+\tau_5)) \\
f \fatsemi g &=& \mathit{trace}~(\mathit{assoc}_1 \fatsemi 
  (f \oplus \idc) \fatsemi \mathit{assoc}_2 \fatsemi (g \oplus \idc) 
  \fatsemi \mathit{assoc}_3)
\end{array}\]

\paragraph*{New combinators $\mathit{curry}$ and $\mathit{uncurry}$ for higher-order functions.}

\[\begin{array}{rcl}
\boxminus(\nodet{\tau_1}{\tau_2}) &\eqdef& \nodet{\tau_2}{\tau_1} \\
\nodet{\tau_1}{\tau_2} \lolli \nodet{\tau_3}{\tau_4} &\eqdef& 
           \boxminus(\nodet{\tau_1}{\tau_2}) \boxplus \nodet{\tau_3}{\tau_4} \\
  &\eqdef& \nodet{\tau_2+\tau_3}{\tau_1+\tau_4}
\end{array}\]
\[\begin{array}{rcl}
\mathit{flip} &:& (\cubt_1 \isoone \cubt_2)
  \rightarrow (\boxminus\cubt_2 \isoone \boxminus\cubt_1) \\
%% \mathit{flip} &:& ((\tau_1-\tau_2) \isoone (\tau_3-\tau_4))
%%   \rightarrow (\boxminus(\tau_3-\tau_4) \isoone \boxminus(\tau_1-\tau_2)) \\
%%   &\eqdef& ((\tau_1-\tau_2) \isoone (\tau_3-\tau_4))
%%   \rightarrow ((\tau_4-\tau_3) \isoone (\tau_2-\tau_1)) \\
%%   &\eqdef& ((\tau_1+\tau_4) \iso (\tau_2+\tau_3))
%%   \rightarrow ((\tau_4+\tau_1) \iso (\tau_3+\tau_2)) \\
\mathit{flip}~f &=& \swapp \fatsemi f \fatsemi \swapp \\
\\
\mathit{curry} &:& 
  ((\cubt_1\boxplus\cubt_2) \isoone \cubt_3) \rightarrow
  (\cubt_1 \isoone (\cubt_2 \lolli \cubt_3)) \\
%% \mathit{curry} &:& 
%%   (((\tau_1-\tau_2)\boxplus(\tau_3-\tau_4)) \isoone (\tau_5-\tau_6)) \rightarrow
%%   ((\tau_1-\tau_2) \isoone ((\tau_3-\tau_4) \lolli (\tau_5-\tau_6))) \\
%%   &\eqdef& 
%%   (((\tau_1+\tau_3)-(\tau_2+\tau_4)) \isoone (\tau_5-\tau_6)) \rightarrow
%%   ((\tau_1-\tau_2) \isoone ((\tau_4+\tau_5)-(\tau_3+\tau_6))) \\
%%   &\eqdef& 
%%   (((\tau_1+\tau_3)+\tau_6) \iso ((\tau_2+\tau_4)+\tau_5)) \rightarrow
%%   ((\tau_1+(\tau_4+\tau_5)) \iso (\tau_2+(\tau_3+\tau_6))) \\
\mathit{curry}~f &=& \assoclp \fatsemi f \fatsemi \assocrp \\
\\
\mathit{uncurry} &:& 
  (\cubt_1 \isoone (\cubt_2 \lolli \cubt_3)) \rightarrow
  ((\cubt_1\boxplus\cubt_2) \isoone \cubt_3) \\
\mathit{uncurry}~f &=& \assocrp \fatsemi f \fatsemi \assoclp 
\end{array}\]

\paragraph*{The ``phony'' multiplication that is not a functor.} 
The definition for the product of 1d types used above is:
\[\begin{array}{l}
\ttone{\nodet{\tau_1}{\tau_2}}{\nodet{\tau_3}{\tau_4}} \eqdef \\
\noalign{$\hfill\nodet{(\tau_1*\tau_3)+(\tau_2*\tau_4)}{(\tau_1*\tau_4)+(\tau_2*\tau_3)}$}
\end{array}\]
That definition is ``obvious'' in some sense as it matches the usual
understanding of types as modeling arithmetic identities. Using this
definition, it is possible to lift all the 0d combinators involving products
\emph{except} the functor:
\[ (\otimes) : 
  (\cubt_1\isoone\cubt_2) \rightarrow 
  (\cubt_3\isoone\cubt_4) \rightarrow 
  ((\cubt_1\boxtimes\cubt_3) \isoone
   (\cubt_2\boxtimes\cubt_4))
\]
After a few failed attempts, we suspected that this definition of
multiplication is not functorial which would mean that the \textbf{Int}
construction only provides a limited notion of higher-order functions at the
cost of losing the multiplicative structure at higher-levels. This
observation is less well-known that it should be. Further investigation
reveals that this observation is intimately related to a well-known problem
in algebraic topology and homotopy theory that was identified thirty years
ago as the ``phony'' multiplication~\cite{thomason} in a special class
categories related to ours. This problem was recently
solved~\cite{ringcompletion} using a technique whose fundamental ingredients
are to add more dimensions and then take homotopy colimits. We exploit this
solution in the remainder of the paper.

\begin{verbatim}
Add eta/epsilon and trace to Int 
category

Explain the definitions in this 
section much better...
\end{verbatim}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

Talk about trace and recursive types

talk about h.o. functions, negative types, int construction, ring completion
paper

canonicity for 2d type theory; licata harper

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\bibliographystyle{abbrvnat}
\softraggedright
\bibliography{cites}

\end{document}
