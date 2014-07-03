\documentclass[authoryear,preprint]{sigplanconf}
\usepackage{agda}
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
\newcommand{\symc}[1]{\mathit{sym}~#1}
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
--infixr 30 _⟷1_
infixr 10 _◎_
--infixr 10 _◎1_
infix  4  _≡_   -- propositional equality
infix  4  _∼_   -- homotopy between two functions (the same as ≡ by univalence)
infix  4  _≃_   -- type of equivalences

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction} 

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

\smallskip
\begin{code}
i0 : 3 ≡ 3
i0 = refl 3

i1 : (1 + 2) ≡ (3 * 1)
i1 = refl 3
\end{code}

\noindent More generally, given two values \AgdaBound{m} and \AgdaBound{n} of
type \AgdaPrimitiveType{ℕ}, it is possible to construct an element
\AgdaInductiveConstructor{refl} \AgdaBound{k} of the type \AgdaBound{m}
\AgdaDatatype{≡} \AgdaBound{n} if and only if \AgdaBound{m}, \AgdaBound{n},
and \AgdaBound{k} are all ``equal.'' As shown in example \AgdaFunction{i1},
this notion of \emph{propositional equality} is not just syntactic equality
but generalizes to \emph{definitional equality}, i.e., to equality that can
be established by normalizing the two values to their normal forms.

The important question from the HoTT perspective is the following: given two
elements \AgdaBound{p} and \AgdaBound{q} of some type \AgdaBound{x}
\AgdaDatatype{≡} \AgdaBound{y} with
\AgdaBound{x}~\AgdaBound{y}~\AgdaSymbol{:}~\AgdaBound{A}, what can we say
about the elements of type \AgdaBound{p} \AgdaDatatype{≡} \AgdaBound{q}. Or,
in more familiar terms, given two proofs of some proposition $P$, are these
two proofs themselves ``equal.'' In some situations, the only interesting
property of proofs is their existence, i.e., all proofs of the same
proposition are considered equivalent. A twist that dates back to a paper by
\citet{Hofmann96thegroupoid} is that proofs actually possess a structure of
great combinatorial complexity. HoTT builds on this idea by interpreting
types as topological spaces or weak $\infty$-groupoids, and interpreting
identities between elements of a type
\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y} as \emph{paths} from the point
\AgdaBound{x} to the point \AgdaBound{y}. If \AgdaBound{x} and \AgdaBound{y}
are themselves paths, the elements of
\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y} become paths between paths, or
homotopies in the topological language. To be explicit, we will often refer
to types as \emph{spaces} which consist of \emph{points}, paths, 2-paths,
etc. and write $\AgdaDatatype{≡}_\AgdaBound{A}$ for the type of paths in
space \AgdaBound{A}.

As a simple example, we are used to thinking of types as sets of values. So
we typically view the type \AgdaPrimitiveType{Bool} as the figure on the left
but in HoTT we should instead think about it as the figure on the right where
there is a (trivial) path \AgdaInductiveConstructor{refl} \AgdaBound{b} from
each point \AgdaBound{b} to itself:
\[
\begin{tikzpicture}[scale=0.7]
  \draw (-0.2,0) ellipse (2cm and 1cm);
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
  \draw (0,0) ellipse (5.5cm and 2.5cm);
  \draw[fill] (0,0) circle (0.025);
  \draw[->,thick,red] (0,0) arc (90:440:0.2);
  \node[above,red] at (0,0) {refl};
  \draw[->,thick,cyan] (0,0) arc (-180:140:0.7);
  \draw[->,thick,cyan] (0,0) arc (-180:150:1.2);
  \node[left,cyan] at (1.4,0) {loop};
  \node[right,cyan] at (2.4,0) {loop $\circ$ loop $\ldots$};
  \draw[->,thick,blue] (0,0) arc (360:40:0.7);
  \draw[->,thick,blue] (0,0) arc (360:30:1.2);
  \node[right,blue] at (-1.4,0) {!~loop};
  \node[left,blue] at (-2.3,0) {$\ldots$ !~loop $\circ$ !~loop};
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

%%%%%%%%%%%%%%%%%%
\subsection{Univalence} 

In addition to paths between the points \AgdaInductiveConstructor{false} and
\AgdaInductiveConstructor{true} in the space \AgdaPrimitiveType{Bool}, it is
also possible to consider paths between the space \AgdaPrimitiveType{Bool}
and itself by considering \AgdaPrimitiveType{Bool} as a ``point'' in the
universe \AgdaPrimitiveType{Set} of types. As usual, we have the trivial path
which is given by the constructor \AgdaInductiveConstructor{refl}:

\smallskip
\begin{code}
p : Bool ≡ Bool
p = refl Bool
\end{code}

\noindent There are, however, other (non trivial) paths between
\AgdaPrimitiveType{Bool} and itself and they are justified by the
\emph{univalence} axiom. As an example, the remainder of this section
justifies that there is a path between \AgdaPrimitiveType{Bool} and itself
corresponding to the boolean negation function.

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

We can now formally state the univalence axiom:

\smallskip
\begin{code}
postulate univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)
\end{code}

\noindent For our purposes, the important consequence of the univalence axiom
is that equivalence of spaces implies the existence of a path between the
spaces. In other words, in order to assert the existence of a path
\AgdaBound{notpath} between \AgdaPrimitiveType{Bool} and itself, we need to
prove that the boolean negation function is an equivalence between the space
\AgdaPrimitiveType{Bool} and itself, as shown below:

\smallskip
\begin{code}
not2∼id : (not ∘ not) ∼ id 
not2∼id false  =  refl false
not2∼id true   =  refl true

notequiv : Bool ≃ Bool
notequiv = (not , 
            record {
              g = not ; α = not2∼id ; h = not ; β = not2∼id
           })
                      
                      

notpath : Bool ≡ Bool
notpath with univalence
... | (_ , eq) = isequiv.g eq notequiv
\end{code}

\noindent Although the code asserting the existence of a non trivial path
between \AgdaPrimitiveType{Bool} and itself ``compiles,'' it is no longer
executable as it relies on an Agda postulate. We analyze the situation from
the perspective of reversible programming languages based on type
isomorphisms~\cite{James:2012:IE:2103656.2103667,rc2011,rc2012}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Computing with Type Isomorphisms}
\label{pi}

The main syntactic vehicle for the technical developments in this paper is a
simple language called $\Pi$ whose only computations are isomorphisms between
finite types~\citeyearpar{James:2012:IE:2103656.2103667}. After reviewing the
motivation for this language and its relevance to HoTT, we present its syntax
and semantics.

%%%%%%%%%%%%%%%%%%%%%
\subsection{Reversibility} 

In a computational world in which the laws of physics are embraced and
resources are carefully maintained (e.g., quantum
computing~\cite{NC00,Abramsky:2004:CSQ:1018438.1021878}), programs must be
reversible. Although this is apparently a limiting idea, it turns out that
conventional computation can be viewed as a special case of such
resource-preserving reversible programs. This thesis has been explored for
many years from different
perspectives~\cite{fredkin1982conservative,Toffoli:1980,bennett2010notes,bennett2003notes,Bennett:1973:LRC,Landauer:1961,Landauer}. 

The relevance of reversibility to HoTT is based on the following
analysis. The conventional HoTT approach starts with two, a priori, different
notions: functions and paths, and then postulates an equivalence between a
particular class of functions and paths. As illustrated above, some functions
like \AgdaBound{not} correspond to paths. Most functions, however, are
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
unnecessary. This is the precise idea we investigate in detail in the
remainder of the paper.

\begin{table*}[t]
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
{\jdg{}{}{c : \tau_1 \iso \tau_2}}
{\jdg{}{}{\symc{c} : \tau_2 \iso \tau_1}}
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
\end{table*}

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
  c &::=& [\textit{see Table~\ref{pi-combinators}}]
\end{array}\]
The interesting syntactic category of $\Pi$ is that of \emph{combinators}
which are witnesses for type isomorphisms $\tau_1 \iso \tau_2$. They consist
of base combinators (on the left side of Table~\ref{pi-combinators}) and
compositions (on the right side of the same table). Each line of the table on
the left introduces a pair of dual constants\footnote{where $\swapp$ and
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
category}. These are categories with two binary operations $\oplus$ and
$\otimes$ satisfying the axioms of a rig (i.e., a ring without negative
elements also known as a semiring) up to coherent isomorphisms. And indeed
the types of the $\Pi$-combinators are precisely the semiring axioms. A
formal way of saying this is that $\Pi$ is the
\emph{categorification}~\cite{math/9802029} of the natural numbers. A simple
(slightly degenerate) example of such categories is the category of finite
sets and permutations in which we interpret every $\Pi$-type as a finite set,
the values as elements in these finite sets, and the combinators as
permutations. In the remainder of this paper, we will more interested in a
model based on groupoids. But first, we give an operational semantics for
$\Pi$.

Operationally, the semantics consists of a pair of mutually recursive
evaluators that take a combinator and a value and propagate the value in the
``forward'' $\triangleright$ direction or in the ``backwards''
$\triangleleft$ direction. We show the complete forward evaluator; the
backwards evaluator differs in trivial ways:
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
\evalone{(\symc{c})}{&v} &=& \evaloneb{c}{v} \\
\evalone{(c_1 \fatsemi c_2)}{&v} &=& 
  \evalone{c_2}{(\evalone{c_1}{v})} \\
\evalone{(c_1\oplus c_2)}{&(\inl{v})} &=& 
  \inl{(\evalone{c_1}{v})} \\
\evalone{(c_1\oplus c_2)}{&(\inr{v})} &=& 
  \inr{(\evalone{c_2}{v})} \\
\evalone{(c_1\otimes c_2)}{&(v_1,v_2)} &=& 
  (\evalone{c_1}v_1, \evalone{c_2}v_2) 
\end{array}\]

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Groupoid Model} 

Instead of modeling the types of $\Pi$ using sets and the combinators using
permutations on the sets, we use a semantics that identifies $\Pi$
combinators with \emph{paths}. More precisely, we model the universe of $\Pi$
types as a space \AgdaBound{U} whose points are the individual $\Pi$-types
(which are themselves spaces \AgdaBound{t} containing points). We then
postulate that there is path between the spaces \AgdaBound{t₁} and
\AgdaBound{t₂} if there is a $\Pi$ combinator $c : t_1 \iso t_2$. Our
postulate is similar in spirit to the univalence axiom but, unlike the
latter, it has a simple computational interpretation. A path directly
corresponds to a type isomorphism with a clear operational semantics as
presented in the previous section. As we will explain in more detail below,
this approach replaces the datatype \AgdaSymbol{≡} modeling propositional
equality with the datatype \AgdaSymbol{⟷} modeling type isomorphisms. With
this switch, the $\Pi$-combinators of Table~\ref{pi-combinators} become
\emph{syntax} for the paths in the space $U$. Put differently, instead of
having exactly one constructor \AgdaInductiveConstructor{refl} for paths with
all other paths discovered by proofs (see Secs. 2.5--2.12 of the HoTT
book~\citeyearpar{hott}) or postulated by the univalence axiom, we have an
\emph{inductive definition} that completely specifies all the paths in the
space $U$.

We begin with the datatype definition of the universe \AgdaBound{U} of finite
types which are constructed using \AgdaInductiveConstructor{ZERO},
\AgdaInductiveConstructor{ONE}, \AgdaInductiveConstructor{PLUS}, and
\AgdaInductiveConstructor{TIMES}. Each of these finite types will correspond
to a set of points with paths connecting some of the points. The underlying
set is computed by \AgdaSymbol{⟦}\_\AgdaSymbol{⟧} as follows:
\AgdaInductiveConstructor{ZERO} maps to the empty set \AgdaSymbol{⊥},
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

\newcommand{\pointed}[2]{\AgdaSymbol{•}\AgdaSymbol{[} \AgdaSymbol{∣} \AgdaBound{#1} \AgdaSymbol{∣} \AgdaSymbol{,} \AgdaBound{#2} \AgdaSymbol{]}}

Paths are ultimately defined between points: in order to be able to identify
them with $\Pi$ combinators, we refine the latter to operate on \emph{pointed
  sets} (or referred to as pointed types or pointed spaces) instead of the
unpointed sets above. A pointed set \pointed{t}{v} is a set \AgdaBound{t}
\AgdaSymbol{:} \AgdaBound{U} with a distinguished value \AgdaBound{v}
\AgdaSymbol{:} \AgdaSymbol{⟦} \AgdaBound{t} \AgdaSymbol{⟧}:

\smallskip
\begin{code} 
record U• : Set where
  constructor •[_,_]
  field
    ∣_∣  : U
    •    : ⟦ ∣_∣ ⟧
\end{code}

\AgdaHide{
\begin{code}
open U•
\end{code}
}

\begin{table*}
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
  sym⟷ : ∀ {t₁ t₂ v₁ v₂} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
           (•[ t₂ , v₂ ] ⟷ •[ t₁ , v₁ ])
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
\label{pointecomb}}
\end{table*}

\noindent The refinement of the $\Pi$ combinators to combinators on pointed
spaces is given by the inductive family in Table~\ref{pointedcomb}. The
definition effectively folds the operational semantics of each combinator
into the type of the path which explicitly connects its input point to its
output point. The definition also evidently generalizes the usual
propositional equality into a \emph{heterogeneous} equality that connects
points that may be in different spaces. Put differently, what used to be the
only constructor for paths \AgdaInductiveConstructor{refl} is now just one of
the many constructors (named \AgdaBound{id⟷} in the Table). Among the new
constructors, we have \AgdaBound{sym⟷} that constructs path inverses,
\AgdaBound{◎} that constructs path compositions. These are sufficient to
guarantee that the universe \AgdaBound{U} is a groupoid. Additionally, we
have paths \AgdaBound{swap1₊} and \AgdaBound{swap2₊} that are essentially the
encoding of the path \AgdaBound{notpath} above from the space
\AgdaBound{Bool} to itself. To see this, note that \AgdaBound{Bool} can be
viewed as a shorthand for \AgdaInductiveConstructor{PLUS}
\AgdaInductiveConstructor{ONE} \AgdaInductiveConstructor{ONE} with
\AgdaInductiveConstructor{true} and \AgdaInductiveConstructor{false} as
shorthands for \AgdaInductiveConstructor{inj₁} \AgdaInductiveConstructor{tt}
and \AgdaInductiveConstructor{inj₂} \AgdaInductiveConstructor{tt}. With this
in mind, the path corresponding to boolean negation consists of two
``fibers'', one for each boolean value as shown below:

\smallskip
\begin{code}
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

data Path (t₁ t₂ : U•) : Set where
  path : (c : t₁ ⟷ t₂) → Path t₁ t₂

notpath•T : Path BOOL•T BOOL•F
notpath•T = path NOT•T

notpath•F : Path BOOL•F BOOL•T
notpath•F = path NOT•F
\end{code} 

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
Table~\ref{pointedcomb} to manipulate collections of paths (e.g., sums of
products of paths) in addition to combinators that work on individual
paths. The latter combinators will capture the higher groupoid structure
relating for example, the path \AgdaBound{id⟷} \AgdaSymbol{◎} \AgdaBound{c}
with \AgdaBound{c}. Computations in the lifted $\Pi$ will therefore
correspond to 2-paths and the entire scheme can be repeated over and over to
capture the concept of weak $\infty$-groupoids.

%%%%%%%%%%%%%%%%%
\subsection{Examples}

We start with a few examples...

\smallskip
\begin{code}
T⇔F : Set
T⇔F = Path BOOL•T BOOL•F

F⇔T : Set
F⇔T = Path BOOL•F BOOL•T

p₁ p₂ p₃ p₄ p₅ : T⇔F
p₁ = path NOT•T
p₂ = path (id⟷ ◎ NOT•T)
p₃ = path (NOT•T ◎ NOT•F ◎ NOT•T)
p₄ = path (NOT•T ◎ id⟷)
p₅ = path (uniti⋆ ◎ swap⋆ ◎ (NOT•T ⊗ id⟷) ◎ swap⋆ ◎ unite⋆)
\end{code}

the paths p1 to p5
and then the proofs that they are the same using 2 paths

The evaluation of a program is not done in order to figure out the output
value. Both the input and output values are encoded in the type of the
program; what the evaluation does is follow the path to constructively
reach the output value from the input value. Even though programs of the
same pointed types are, by definition, observationally equivalent, they
may follow different paths. At this point, we simply declare that all such
programs are "the same." At the next level, we will weaken this "path
irrelevant" equivalence and reason about which paths can be equated to
other paths via 2paths etc.


Simplify various compositions

\smallskip
\begin{code}
simplifySym : {t₁ t₂ : U•} → (c₁ : t₁ ⟷ t₂) → (t₂ ⟷ t₁)
simplifySym unite₊ = uniti₊
simplifySym uniti₊ = unite₊
simplifySym swap1₊ = swap2₊
simplifySym swap2₊ = swap1₊
simplifySym assocl1₊ = assocr1₊
simplifySym assocl2₊ = assocr2₊
simplifySym assocl3₊ = assocr3₊
simplifySym assocr1₊ = assocl1₊
simplifySym assocr2₊ = assocl2₊
simplifySym assocr3₊ = assocl3₊
simplifySym unite⋆ = uniti⋆
simplifySym uniti⋆ = unite⋆
simplifySym swap⋆ = swap⋆
simplifySym assocl⋆ = assocr⋆
simplifySym assocr⋆ = assocl⋆
simplifySym distz = factorz
simplifySym factorz = distz
simplifySym dist1 = factor1 
simplifySym dist2 = factor2 
simplifySym factor1 = dist1 
simplifySym factor2 = dist2 
simplifySym id⟷ = id⟷
simplifySym (sym⟷ c) = c
simplifySym (c₁ ◎ c₂) = simplifySym c₂ ◎ simplifySym c₁ 
simplifySym (c₁ ⊕1 c₂) = simplifySym c₁ ⊕1 simplifySym c₂ 
simplifySym (c₁ ⊕2 c₂) = simplifySym c₁ ⊕2 simplifySym c₂ 
simplifySym (c₁ ⊗ c₂) = simplifySym c₁ ⊗ simplifySym c₂ 

simplifyl◎ : {t₁ t₂ t₃ : U•} → 
  (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
simplifyl◎ id⟷ c = c 
simplifyl◎ unite₊ uniti₊ = id⟷
simplifyl◎ uniti₊ unite₊ = id⟷ 
simplifyl◎ swap1₊ swap2₊ = id⟷ 
simplifyl◎ swap2₊ swap1₊ = id⟷ 
simplifyl◎ assocl1₊ assocr1₊ = id⟷ 
simplifyl◎ assocl2₊ assocr2₊ = id⟷ 
simplifyl◎ assocl3₊ assocr3₊ = id⟷ 
simplifyl◎ assocr1₊ assocl1₊ = id⟷ 
simplifyl◎ assocr2₊ assocl2₊ = id⟷ 
simplifyl◎ assocr3₊ assocl3₊ = id⟷ 
simplifyl◎ unite⋆ uniti⋆ = id⟷ 
simplifyl◎ uniti⋆ unite⋆ = id⟷ 
simplifyl◎ swap⋆ swap⋆ = id⟷ 
simplifyl◎ assocl⋆ assocr⋆ = id⟷ 
simplifyl◎ assocr⋆ assocl⋆ = id⟷ 
simplifyl◎ factorz distz = id⟷ 
simplifyl◎ dist1 factor1 = id⟷ 
simplifyl◎ dist2 factor2 = id⟷ 
simplifyl◎ factor1 dist1 = id⟷ 
simplifyl◎ factor2 dist2 = id⟷ 
simplifyl◎ (c₁ ◎ c₂) c₃ = c₁ ◎ (c₂ ◎ c₃) 
simplifyl◎ (c₁ ⊕1 c₂) swap1₊ = swap1₊ ◎ (c₂ ⊕2 c₁)
simplifyl◎ (c₁ ⊕2 c₂) swap2₊ = swap2₊ ◎ (c₂ ⊕1 c₁)
simplifyl◎ (_⊗_ {ONE} {ONE} c₁ c₂) unite⋆ = unite⋆ ◎ c₂
simplifyl◎ (c₁ ⊗ c₂) swap⋆ = swap⋆ ◎ (c₂ ⊗ c₁)
simplifyl◎ (c₁ ⊗ c₂) (c₃ ⊗ c₄) = (c₁ ◎ c₃) ⊗ (c₂ ◎ c₄) 
simplifyl◎ c₁ c₂ = c₁ ◎ c₂
\end{code}

\AgdaHide{
\begin{code}
simplifyr◎ : {t₁ t₂ t₃ : U•} → (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
simplifyr◎ c id⟷ = c
simplifyr◎ unite₊ uniti₊ = id⟷
simplifyr◎ uniti₊ unite₊ = id⟷ 
simplifyr◎ swap1₊ swap2₊ = id⟷ 
simplifyr◎ swap2₊ swap1₊ = id⟷ 
simplifyr◎ assocl1₊ assocr1₊ = id⟷ 
simplifyr◎ assocl2₊ assocr2₊ = id⟷ 
simplifyr◎ assocl3₊ assocr3₊ = id⟷ 
simplifyr◎ assocr1₊ assocl1₊ = id⟷ 
simplifyr◎ assocr2₊ assocl2₊ = id⟷ 
simplifyr◎ assocr3₊ assocl3₊ = id⟷ 
simplifyr◎ unite⋆ uniti⋆ = id⟷ 
simplifyr◎ uniti⋆ unite⋆ = id⟷ 
simplifyr◎ swap⋆ swap⋆ = id⟷ 
simplifyr◎ assocl⋆ assocr⋆ = id⟷ 
simplifyr◎ assocr⋆ assocl⋆ = id⟷ 
simplifyr◎ factorz distz = id⟷ 
simplifyr◎ dist1 factor1 = id⟷ 
simplifyr◎ dist2 factor2 = id⟷ 
simplifyr◎ factor1 dist1 = id⟷ 
simplifyr◎ factor2 dist2 = id⟷ 
simplifyr◎ (c₁ ◎ c₂) c₃ = c₁ ◎ (c₂ ◎ c₃) 
simplifyr◎ (c₁ ⊕1 c₂) swap1₊ = swap1₊ ◎ (c₂ ⊕2 c₁)
simplifyr◎ (c₁ ⊕2 c₂) swap2₊ = swap2₊ ◎ (c₂ ⊕1 c₁)
simplifyr◎ (_⊗_ {ONE} {ONE} c₁ c₂) unite⋆ = unite⋆ ◎ c₂
simplifyr◎ (c₁ ⊗ c₂) swap⋆ = swap⋆ ◎ (c₂ ⊗ c₁)
simplifyr◎ (c₁ ⊗ c₂) (c₃ ⊗ c₄) = (c₁ ◎ c₃) ⊗ (c₂ ◎ c₄) 
simplifyr◎ c₁ c₂ = c₁ ◎ c₂
\end{code} 
} 

We need to show that the groupoid path structure is faithfully
represented. The combinator $\idc$ introduces all the $\refl{\tau} : \tau
\equiv \tau$ paths in $U$. The adjoint $\symc{c}$ introduces an inverse path
$!p$ for each path $p$ introduced by $c$. The composition operator $\fatsemi$
introduces a path $p \circ q$ for every pair of paths whose endpoints
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

%% \begin{code}
%% data U : Set where
%%   ZERO  : U              -- empty set of paths
%%   ONE   : U              -- a trivial path
%%   PLUS  : U → U → U      -- disjoint union of paths
%%   TIMES : U → U → U      -- pairs of paths
%%   PATH  : {t₁ t₂ : P.U•} → (t₁ P.⟷ t₂) → U -- level 0 paths between values

%% data Path (t₁ t₂ : P.U•) : Set where
%%   path : (c : t₁ P.⟷ t₂) → Path t₁ t₂

%% ⟦_⟧ : U → Set
%% ⟦ ZERO ⟧             = ⊥
%% ⟦ ONE ⟧              = ⊤
%% ⟦ PLUS t₁ t₂ ⟧       = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
%% ⟦ TIMES t₁ t₂ ⟧      = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
%% ⟦ PATH {t₁} {t₂} c ⟧ = Path t₁ t₂

%% -- examples

%% T⇔F : Set
%% T⇔F = Path P.BOOL•T P.BOOL•F

%% F⇔T : Set
%% F⇔T = Path P.BOOL•F P.BOOL•T

%% -- all the following are paths from T to F; we will show below that they
%% -- are equivalent using 2paths

%% p₁ p₂ p₃ p₄ p₅ : T⇔F
%% p₁ = path P.NOT•T
%% p₂ = path (P.id⟷ P.◎ P.NOT•T)
%% p₃ = path (P.NOT•T P.◎ P.NOT•F P.◎ P.NOT•T)
%% p₄ = path (P.NOT•T P.◎ P.id⟷)
%% p₅ = path (P.uniti⋆ P.◎ P.swap⋆ P.◎ (P.NOT•T P.⊗ P.id⟷) P.◎ P.swap⋆ P.◎ P.unite⋆)
   
%% p₆ : (T⇔F × T⇔F) ⊎ F⇔T
%% p₆ = inj₁ (p₁ , p₂)

%% -- Programs map paths to paths. We also use pointed types.

%% record U• : Set where
%%   constructor •[_,_]
%%   field
%%     ∣_∣ : U
%%     • : ⟦ ∣_∣ ⟧

%% open U•

%% Path• : {t₁ t₂ : P.U•} → (c : t₁ P.⟷ t₂) → U•
%% Path• c = •[ PATH c , path c ]

%% data _⟷_ : U• → U• → Set where

%%   -- common combinators

%%   id⟷    : {t : U•} → t ⟷ t
%%   sym⟷   : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
%%   _◎_     : {t₁ t₂ t₃ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)

%%   -- groupoid combinators defined by induction on P.⟷ in Pi0.agda

%%   simplifyl◎l : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} 
%%              {c₁ : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} 
%%              {c₂ : P.U•.•[ t₂ , v₂ ] P.⟷ P.U•.•[ t₃ , v₃ ]} → 
%%     Path• (c₁ P.◎ c₂) ⟷ Path• (P.simplifyl◎ c₁ c₂)

%%   simplifyl◎r : {t₁ t₂ t₃ : P.U•} {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} → 
%%     Path• (P.simplifyl◎ c₁ c₂) ⟷ Path• (c₁ P.◎ c₂)

%%   simplifyr◎l : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} 
%%              {c₁ : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} 
%%              {c₂ : P.U•.•[ t₂ , v₂ ] P.⟷ P.U•.•[ t₃ , v₃ ]} → 
%%     Path• (c₁ P.◎ c₂) ⟷ Path• (P.simplifyr◎ c₁ c₂)

%%   simplifyr◎r : {t₁ t₂ t₃ : P.U•} {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} → 
%%     Path• (P.simplifyr◎ c₁ c₂) ⟷ Path• (c₁ P.◎ c₂)

%%   simplifySyml : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
%%     Path• (P.sym⟷ c) ⟷ Path• (P.simplifySym c)

%%   simplifySymr : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
%%     Path• (P.simplifySym c) ⟷ Path• (P.sym⟷ c)

%%   invll   : ∀ {t₁ t₂ v₁ v₂} → {c : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} → 
%%             Path• (P.sym⟷ c P.◎ c) ⟷ Path• (P.id⟷ {t₂} {v₂})
%%   invlr   : ∀ {t₁ t₂ v₁ v₂} → {c : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} → 
%%             Path• (P.id⟷ {t₂} {v₂}) ⟷ Path• (P.sym⟷ c P.◎ c)
%%   invrl   : ∀ {t₁ t₂ v₁ v₂} → {c : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} → 
%%             Path• (c P.◎ P.sym⟷ c) ⟷ Path• (P.id⟷ {t₁} {v₁})
%%   invrr   : ∀ {t₁ t₂ v₁ v₂} → {c : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} → 
%%             Path• (P.id⟷ {t₁} {v₁}) ⟷ Path• (c P.◎ P.sym⟷ c)
%%   tassocl : {t₁ t₂ t₃ t₄ : P.U•} 
%%             {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} {c₃ : t₃ P.⟷ t₄} → 
%%             Path• (c₁ P.◎ (c₂ P.◎ c₃)) ⟷ 
%%             Path• ((c₁ P.◎ c₂) P.◎ c₃)
%%   tassocr : {t₁ t₂ t₃ t₄ : P.U•} 
%%             {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} {c₃ : t₃ P.⟷ t₄} → 
%%             Path• ((c₁ P.◎ c₂) P.◎ c₃) ⟷ 
%%             Path• (c₁ P.◎ (c₂ P.◎ c₃))

%%   -- resp◎ is closely related to Eckmann-Hilton
%%   resp◎   : {t₁ t₂ t₃ : P.U•} 
%%             {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} 
%%             {c₃ : t₁ P.⟷ t₂} {c₄ : t₂ P.⟷ t₃} → 
%%             (Path• c₁ ⟷ Path• c₃) → 
%%             (Path• c₂ ⟷ Path• c₄) → 
%%             Path• (c₁ P.◎ c₂) ⟷ Path• (c₃ P.◎ c₄)

%%   -- commutative semiring combinators

%%   unite₊  : {t : U•} → •[ PLUS ZERO ∣ t ∣ , inj₂ (• t) ] ⟷ t
%%   uniti₊  : {t : U•} → t ⟷ •[ PLUS ZERO ∣ t ∣ , inj₂ (• t) ]
%%   swap1₊  : {t₁ t₂ : U•} → •[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₁ (• t₁) ] ⟷ 
%%                            •[ PLUS ∣ t₂ ∣ ∣ t₁ ∣ , inj₂ (• t₁) ]
%%   swap2₊  : {t₁ t₂ : U•} → •[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₂ (• t₂) ] ⟷ 
%%                            •[ PLUS ∣ t₂ ∣ ∣ t₁ ∣ , inj₁ (• t₂) ]
%%   assocl1₊ : {t₁ t₂ t₃ : U•} → 
%%              •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₁ (• t₁) ] ⟷ 
%%              •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₁ (inj₁ (• t₁)) ]
%%   assocl2₊ : {t₁ t₂ t₃ : U•} → 
%%              •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₂ (inj₁ (• t₂)) ] ⟷ 
%%              •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₁ (inj₂ (• t₂)) ]
%%   assocl3₊ : {t₁ t₂ t₃ : U•} → 
%%              •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₂ (inj₂ (• t₃)) ] ⟷ 
%%              •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₂ (• t₃) ]
%%   assocr1₊ : {t₁ t₂ t₃ : U•} → 
%%              •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₁ (inj₁ (• t₁)) ] ⟷ 
%%              •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₁ (• t₁) ] 
%%   assocr2₊ : {t₁ t₂ t₃ : U•} → 
%%              •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₁ (inj₂ (• t₂)) ] ⟷ 
%%              •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₂ (inj₁ (• t₂)) ] 
%%   assocr3₊ : {t₁ t₂ t₃ : U•} → 
%%              •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₂ (• t₃) ] ⟷ 
%%              •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₂ (inj₂ (• t₃)) ]
%%   unite⋆  : {t : U•} → •[ TIMES ONE ∣ t ∣ , (tt , • t) ] ⟷ t               
%%   uniti⋆  : {t : U•} → t ⟷ •[ TIMES ONE ∣ t ∣ , (tt , • t) ] 
%%   swap⋆   : {t₁ t₂ : U•} → •[ TIMES ∣ t₁ ∣ ∣ t₂ ∣ , (• t₁ , • t₂) ] ⟷ 
%%                            •[ TIMES ∣ t₂ ∣ ∣ t₁ ∣ , (• t₂ , • t₁) ]
%%   assocl⋆ : {t₁ t₂ t₃ : U•} → 
%%            •[ TIMES ∣ t₁ ∣ (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , (• t₁ , (• t₂ , • t₃)) ] ⟷ 
%%            •[ TIMES (TIMES ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , ((• t₁ , • t₂) , • t₃) ]
%%   assocr⋆ : {t₁ t₂ t₃ : U•} → 
%%            •[ TIMES (TIMES ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , ((• t₁ , • t₂) , • t₃) ] ⟷ 
%%            •[ TIMES ∣ t₁ ∣ (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , (• t₁ , (• t₂ , • t₃)) ]
%%   distz : {t : U•} {absurd : ⟦ ZERO ⟧} → 
%%           •[ TIMES ZERO ∣ t ∣ , (absurd , • t) ] ⟷ •[ ZERO , absurd ]
%%   factorz : {t : U•} {absurd : ⟦ ZERO ⟧} → 
%%             •[ ZERO , absurd ] ⟷ •[ TIMES ZERO ∣ t ∣ , (absurd , • t) ] 
%%   dist1   : {t₁ t₂ t₃ : U•} → 
%%             •[ TIMES (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , (inj₁ (• t₁) , • t₃) ] ⟷ 
%%             •[ PLUS (TIMES ∣ t₁ ∣ ∣ t₃ ∣) (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , 
%%                inj₁ (• t₁ , • t₃) ]
%%   dist2   : {t₁ t₂ t₃ : U•} → 
%%             •[ TIMES (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , (inj₂ (• t₂) , • t₃) ] ⟷ 
%%             •[ PLUS (TIMES ∣ t₁ ∣ ∣ t₃ ∣) (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , 
%%                inj₂ (• t₂ , • t₃) ]
%%   factor1   : {t₁ t₂ t₃ : U•} → 
%%             •[ PLUS (TIMES ∣ t₁ ∣ ∣ t₃ ∣) (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , 
%%                inj₁ (• t₁ , • t₃) ] ⟷ 
%%             •[ TIMES (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , (inj₁ (• t₁) , • t₃) ]
%%   factor2   : {t₁ t₂ t₃ : U•} → 
%%             •[ PLUS (TIMES ∣ t₁ ∣ ∣ t₃ ∣) (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , 
%%                inj₂ (• t₂ , • t₃) ] ⟷ 
%%             •[ TIMES (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , (inj₂ (• t₂) , • t₃) ]
%%   _⊕1_   : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
%%            (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₁ (• t₁) ] ⟷ 
%%             •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₁ (• t₃) ])
%%   _⊕2_   : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
%%            (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₂ (• t₂) ] ⟷ 
%%             •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₂ (• t₄) ])
%%   _⊗_     : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
%%             (•[ TIMES ∣ t₁ ∣ ∣ t₂ ∣ , (• t₁ , • t₂ ) ] ⟷ 
%%              •[ TIMES ∣ t₃ ∣ ∣ t₄ ∣ , (• t₃ , • t₄ ) ])

%% -- example programs

%% {--
%% α₁ : Path• P.NOT•T ⟷ Path• (P.id⟷ P.◎ P.NOT•T)
%% α₁ = simplify◎r

%% α₂ α₃ : •[ TIMES (PATH P.NOT•T) (PATH (P.NOT•T P.◎ P.id⟷)) , (p₁ , p₄) ] ⟷ 
%%         •[ TIMES (PATH P.NOT•T) (PATH P.NOT•T) , (p₁ , p₁) ] 
%% α₂ = id⟷ ⊗ simplify◎l
%% α₃ = swap⋆ ◎ (simplify◎l ⊗ id⟷) 

%% -- let's try to prove that p₁ = p₂ = p₃ = p₄ = p₅

%% -- p₁ ~> p₂
%% α₄ : •[ PATH P.NOT•T , p₁ ] ⟷ •[ PATH (P.id⟷ P.◎ P.NOT•T) , p₂ ]
%% α₄ = simplify◎r

%% -- p₂ ~> p₃
%% α₅ : •[ PATH (P.id⟷ P.◎ P.NOT•T) , p₂ ] ⟷ 
%%      •[ PATH (P.NOT•T P.◎ P.NOT•F P.◎ P.NOT•T) , p₃ ]
%% α₅ = simplify◎l ◎ simplify◎r ◎ (resp◎ id⟷ (invrr {c = P.NOT•F} ◎ resp◎ id⟷ simplifySyml))
%% --}
%% -- p₃ ~> p₄
%% α₆ : •[ PATH (P.NOT•T P.◎ P.NOT•F P.◎ P.NOT•T) , p₃ ] ⟷ 
%%      •[ PATH (P.NOT•T P.◎ P.id⟷) , p₄ ]
%% α₆ = resp◎ id⟷ ((resp◎ simplifySymr id⟷) ◎ invll)

%% -- p₅ ~> p₁

%% {--
%% α₈ : •[ PATH (P.uniti⋆ P.◎ P.swap⋆ P.◎ 
%%              (P.NOT•T P.⊗ P.id⟷) P.◎ P.swap⋆ P.◎ P.unite⋆) , 
%%         p₅ ] ⟷ 
%%      •[ PATH P.NOT•T , p₁ ] 
%% α₈ = resp◎ id⟷ (resp◎ id⟷ tassocl) ◎ 
%%      resp◎ id⟷ (resp◎ id⟷ (resp◎ simplify◎l id⟷)) ◎ 
%%      resp◎ id⟷ (resp◎ id⟷ tassocr) ◎
%%      resp◎ id⟷ tassocl ◎
%%      resp◎ id⟷ (resp◎ (resp◎ simplifySymr id⟷) id⟷) ◎
%%      resp◎ id⟷ (resp◎ invll id⟷) ◎
%%      resp◎ id⟷ simplify◎l ◎
%%      resp◎ id⟷ simplify◎l ◎
%%      resp◎ simplifySyml id⟷ ◎
%%      tassocl ◎ 
%%      resp◎ invll id⟷ ◎
%%      simplify◎l 

%% -- p₄ ~> p₅

%% α₇ : •[ PATH (P.NOT•T P.◎ P.id⟷) , p₄ ] ⟷ 
%%      •[ PATH (P.uniti⋆ P.◎ P.swap⋆ P.◎ 
%%              (P.NOT•T P.⊗ P.id⟷) P.◎ P.swap⋆ P.◎ P.unite⋆) , 
%%         p₅ ]
%% α₇ = simplify◎l ◎ (sym⟷ α₈)
%% --}

%% -- level 0 is a groupoid with a non-trivial path equivalence the various inv*
%% -- rules are not justified by the groupoid proof; they are justified by the
%% -- need for computational rules. So it is important to have not just a
%% -- groupoid structure but a groupoid structure that we can compute with. So
%% -- if we say that we want p ◎ p⁻¹ to be id, we must have computational rules
%% -- that allow us to derive this for any path p, and similarly for all the
%% -- other groupoid rules. (cf. The canonicity for 2D type theory by Licata and
%% -- Harper)

%% G : 1Groupoid
%% G = record
%%         { set = P.U•
%%         ; _↝_ = P._⟷_
%%         ; _≈_ = λ c₀ c₁ → Path• c₀ ⟷ Path• c₁
%%         ; id = P.id⟷
%%         ; _∘_ = λ c₀ c₁ → c₁ P.◎ c₀
%%         ; _⁻¹ = P.sym⟷
%%         ; lneutr = λ {t₁} {t₂} c → simplifyr◎l 
%%            {P.U•.∣ t₁ ∣} {P.U•.∣ t₂ ∣} {P.U•.∣ t₂ ∣} 
%%            {P.U•.• t₁} {P.U•.• t₂} {P.U•.• t₂} {c} {P.id⟷} 
%%         ; rneutr = λ {t₁} {t₂} c → simplifyl◎l 
%%            {P.U•.∣ t₁ ∣} {P.U•.∣ t₁ ∣} {P.U•.∣ t₂ ∣} 
%%            {P.U•.• t₁} {P.U•.• t₁} {P.U•.• t₂} {P.id⟷} {c}
%%         ; assoc = λ _ _ _ → tassocl
%%         ; equiv = record { refl = id⟷ 
%%                                 ; sym = λ c → sym⟷ c 
%%                                 ; trans = λ c₀ c₁ → c₀ ◎ c₁ }
%%         ; linv = λ {t₁} {t₂} c → 
%%                    invrl {P.U•.∣ t₁ ∣} {P.U•.∣ t₂ ∣} {P.U•.• t₁} {P.U•.• t₂}
%%         ; rinv = λ {t₁} {t₂} c → 
%%                    invll {P.U•.∣ t₁ ∣} {P.U•.∣ t₂ ∣} {P.U•.• t₁} {P.U•.• t₂}
%%         ; ∘-resp-≈ = λ f⟷h g⟷i → resp◎ g⟷i f⟷h 
%%         }

%% \end{code}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\bibliographystyle{abbrvnat}
\softraggedright
\bibliography{cites}

\end{document}
