\documentclass[authoryear,preprint]{sigplanconf}
\usepackage{agda}
%% \usepackage{fixltx2e}
\usepackage{fix2col}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{tikz}
\usepackage[all]{xy}
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

\newtheorem{theorem}{Theorem}

% XY-Pic definitions for making ``wire charts''
\newcommand{\sep}{\hspace{2em}} 

\def\wirechart#1#2{\let\labelstyle\objectstyle\xy*[*1.0]\xybox{\small%
\xymatrix@C=10mm@R=4mm#1{#2}}\endxy}
\def\wire#1#2{\ar@{-}[#1]^<>(.5){#2}}
\def\wireright#1#2{\wire{#1}{#2}\ar@{}[#1]|<>(.5)/.6ex/{\dir2{>}}}
\def\wireleft#1#2{\wire{#1}{#2}\ar@{}[#1]|<>(.5)/-.6ex/{\dir2{<}}}
\def\wwblank#1{*=<#1,0mm>{~}}
\def\wblank{\wwblank{11mm}}
\def\blank{\wwblank{8mm}}
\def\vublank{*=<0mm,2.3mm>!D{}}
\def\vdblank{*=<0mm,2.3mm>!U{}}
\def\vsblank{*=<0mm,5.6mm>{}}
\def\wirecross#1{\save[]!L;[#1]!R**@{-}\restore}
\def\wirebraid#1#2{\save[]!L;[#1]!R**{}?(#2)**@{-}\restore\save[#1]!R;[]!L**{}?(#2)**@{-}\restore}
\def\wireopen#1{\save[]!R;[#1]!R**\crv{[]!C&[#1]!C}\restore}
\def\wireclose#1{\save[]!L;[#1]!L**\crv{[]!C&[#1]!C}\restore}
\def\wireopenlabel#1#2{\save[]!R;[#1]!R**\crv{[]!C&[#1]!C}?<>(.5)*^+!R{#2}\restore}
\def\wirecloselabel#1#2{\save[]!L;[#1]!L**\crv{[]!C&[#1]!C}?<>(.5)*^+!L{#2}\restore}
\def\wireid{\blank\save[]!L*{};[]!R*{}**@{-}\restore}
\def\wwireid{\wblank\save[]!L*{};[]!R*{}**@{-}\restore}
\def\wwwireid#1{\wwblank{#1}\save[]!L*{};[]!R*{}**@{-}\restore}
\newcommand{\corner}{\rule{2.5mm}{2.5mm}}
\def\minheight{8mm}
\def\addheight{8mm}
\def\cornerbox#1#2#3{  % draw a box with a marked corner around
                   % the object #1. #2=label
                   % usage:   \ulbox{[ll].[].[ul]}{f}
  \save#1="box";
  "box"!C*+<0mm,\addheight>+=<0mm,\minheight>[|(5)]\frm{-}="box1";
  "box1"*{#2};
  ={"box1"!LU*!LU[]{\corner}}"ul";
  ={"box1"!RU*!RU[]{\corner}}"ur";
  ={"box1"!LD*!LD[]{\corner}}"dl";
  ={"box1"!RD*!RD[]{\corner}}"dr";
  #3
  \restore
}
\def\nnbox#1#2{\cornerbox{#1}{#2}{}}
\def\ulbox#1#2{\cornerbox{#1}{#2}{"ul"}}
\def\urbox#1#2{\cornerbox{#1}{#2}{"ur"}}
\def\dlbox#1#2{\cornerbox{#1}{#2}{"dl"}}
\def\drbox#1#2{\cornerbox{#1}{#2}{"dr"}}
\def\ubox#1#2{\cornerbox{#1}{#2}{"ul","ur"}}
\def\dbox#1#2{\cornerbox{#1}{#2}{"dl","dr"}}
\def\lbox#1#2{\cornerbox{#1}{#2}{"ul","dl"}}
\def\rbox#1#2{\cornerbox{#1}{#2}{"ur","dr"}}
\def\circbox#1{*+[o][F-]{#1}}

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
\DeclareUnicodeCharacter{8644}{$\rightleftarrows$}
\DeclareUnicodeCharacter{10231}{$\leftrightarrow$}
\DeclareUnicodeCharacter{10214}{$\llbracket$} 
\DeclareUnicodeCharacter{10215}{$\rrbracket$} 


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

\newcommand{\jc}[1]{\authornote{purple}{JC}{#1}}
\newcommand{\as}[1]{\authornote{magenta}{AS}{#1}}

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
%% geometry, physics, 
logic, and type theory, in a unique novel way that
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
{-# OPTIONS --without-K #-}

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
infix  2  _□       -- equational reasoning for paths
infixr 2  _⟷⟨_⟩_   -- equational reasoning for paths
--infix  2  _▤       -- equational reasoning for paths
--infixr 2  _⇔⟨_⟩_   -- equational reasoning for paths

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction} 

Homotopy type theory (HoTT)~\cite{hottbook} has a convoluted treatment of
functions. It starts with a class of arbitrary functions, singles out a
smaller class of ``equivalences'' via extensional methods, and then asserts
via the \emph{univalence} \textbf{axiom} that the class of functions just
singled out is equivalent to paths. Why not start with functions that are, by
construction, equivalences?

The idea that computation should be based on ``equivalences'' is an old one
and is motivated by physical considerations. Because physics requires various
conservation principles (including conservation of information) and because
computation is fundamentally a physical process, every computation is
fundamentally an equivalence that preserves information. This idea fits well
with the HoTT philosophy that emphasizes equalities, isomorphisms,
equivalences, and their computational content.

In more detail, a computational world in which the laws of physics are
embraced and resources are carefully maintained (e.g., quantum
computing~\cite{NC00,Abramsky:2004:CSQ:1018438.1021878}), programs must be
reversible. Although this is apparently a limiting idea, it turns out that
conventional computation can be viewed as a special case of such
resource-preserving reversible programs. This thesis has been explored for
many years from different
perspectives~\cite{fredkin1982conservative,Toffoli:1980,bennett2010notes,bennett2003notes,Bennett:1973:LRC,Landauer:1961,Landauer}
and more recently in the context of type
isomorphisms~\cite{James:2012:IE:2103656.2103667}. 

This paper explores the basic ingredients of HoTT from the perspective that
computation is all about type isomorphisms. Because the issues involved are
quite subtle, the paper is an executable \texttt{Agda 2.4.0} file with the
global \AgdaComment{without-K} option enabled. The main body of the paper
reconstructs the main features of HoTT for the limited universe of finite
types consisting of the empty type, the unit type, and sums and products of
types. Sec.~\ref{intc} outlines directions for extending the result to richer
types.

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
viewed as a type\footnote{but the converse is not part of the principle.
This is frequently misunderstood.}.
Indeed, if a proposition $P$ is true, the corresponding
type is inhabited and it is possible to provide evidence or proof for $P$
using one of the elements of the type~$P$. If, however, a proposition $P$ is
false, the corresponding type is empty and it is impossible to provide a
proof for $P$. The type theory is rich enough to express the standard logical
propositions denoting conjunction, disjunction, implication, and existential
and universal quantifications. In addition, it is clear that the question of
whether two elements of a type are equal is a proposition, and hence that
this proposition must correspond to a type.  We encode this type in Agda
as follows,

\smallskip
\begin{code}
data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)
\end{code}
\smallskip

\noindent where we make the evidence explicit.  In Agda, one may write proofs 
of such propositions as shown in the two examples below:

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
be established by normalizing the values to their normal forms.  This is 
also known as ``up to $\beta\eta$.''

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
great combinatorial complexity. 
\jc{Surely proof theory predates this by decades?  Lukasiewicz and Gentzen?}
HoTT builds on this idea by interpreting
types as topological spaces or weak $\infty$-groupoids, and interpreting
identities between elements of a type
\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y} as \emph{paths} from the point
\AgdaBound{x} to the point \AgdaBound{y}. If \AgdaBound{x} and \AgdaBound{y}
are themselves paths, the elements of
\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y} become paths between paths
(2-paths), or homotopies in topological language. To be explicit, we will
often refer to types as \emph{spaces} which consist of \emph{points}, paths,
2-paths, etc. and write $\AgdaDatatype{≡}_\AgdaBound{A}$ for the type of paths
in space \AgdaBound{A}.

\jc{We know that once we have polymorphism, we have no interpretations in 
Set anymore -- should perhaps put more warnings in the next paragraph?}
As a simple example, we are used to thinking of (simple) types as sets of
values. So we typically view the type \AgdaPrimitiveType{Bool} as the figure on
the left. In HoTT we should instead think about it as the figure on the
right where there is a (trivial) path \AgdaInductiveConstructor{refl}
\AgdaBound{b} from each point \AgdaBound{b} to itself:
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

\jc{Do you mean Set or U for the universe?  In HoTT the latter is standard,
while Set is really a weird Agda-ism}
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
\emph{univalence} \textbf{axiom}.  As an example, the remainder of this
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
~
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
briefly discussed in the conclusion.\jc{but don't we need trace for the Int
construction?}}

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

We now want to identify paths with $\Pi$-combinators. There is a small
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

\noindent Pointed spaces are often necessary in homotopy theory as various
important properties of spaces depend on the chosen basepoint. In our
setting, pointed spaces allow us to re-express the $\Pi$-combinators in a way
that unifies their status as isomorphisms between \emph{types} and as paths
between \emph{points} as shown in Fig.~\ref{pointedcomb}. The new
presentation of combinators directly relates points to points and in fact
subsumes the operational semantics of Fig.~\ref{opsem}. For example, note
that the $\Pi$-combinator $\swapp : \tau_1 + \tau_2 \iso \tau_2 + \tau_1$
requires two clauses in the interpreter:
\[\begin{array}{r@{\!}lcl}
\evalone{\swapp}{&(\inl{v})} &=& \inr{v} \\
\evalone{\swapp}{&(\inr{v})} &=& \inl{v} 
\end{array}\]
These two clauses give rise to two path constructors
\AgdaInductiveConstructor{swap1₊} and \AgdaInductiveConstructor{swap2₊}. When
viewed as maps between unpointed spaces, both constructors map from
\AgdaInductiveConstructor{PLUS} \AgdaBound{t₁} \AgdaBound{t₂} to
\AgdaInductiveConstructor{PLUS} \AgdaBound{t₂} \AgdaBound{t₁}. When, however,
viewed as maps between points spaces, each constructor specifies in addition
its action on the point in a way that mirrors the semantic evaluation
rule. The situation is the same for all other $\Pi$-constructors. \jc{The
  operational semantics have $24$ rules, while the groupoid model has $26$.
  This is because of the 2 rules with \emph{absurd} in them.  How shall they
  be explained?}

We note that the refinement of the $\Pi$-combinators to combinators on
pointed spaces is given by an inductive family for \emph{heterogeneous}
equality that generalizes the usual inductive family for propositional
equality. Put differently, what used to be the only constructor for paths
\AgdaInductiveConstructor{refl} is now just one of the many constructors
(named \AgdaInductiveConstructor{id⟷} in the figure). Among the new
constructors we have \AgdaInductiveConstructor{◎} that constructs path
compositions. By construction, every combinator has an inverse calculated as
shown in Fig.~\ref{sym}. These constructions are sufficient to guarantee that
the universe~\AgdaFunction{U} is a groupoid \jc{point to the proof in
some accompanying full Agda code?}. Additionally, we have paths that
connect values in different but isomorphic spaces like
\pointed{{\AgdaInductiveConstructor{TIMES} \AgdaBound{t₁}
\AgdaBound{t₂}}}{{\AgdaSymbol{(} \AgdaBound{v₁} \AgdaSymbol{,} \AgdaBound{v₂}
\AgdaSymbol{)}}} and \pointed{{\AgdaInductiveConstructor{TIMES}
\AgdaBound{t₂} \AgdaBound{t₁}}}{{\AgdaSymbol{(} \AgdaBound{v₂} \AgdaSymbol{,}
\AgdaBound{v₁} \AgdaSymbol{)}}}.

\begin{figure}[ht]
\setlength{\columnsep}{12pt}
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
\caption{\label{sym}Pointed Combinators (or paths) inverses}
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

\AgdaHide{
\begin{code}
_⟷⟨_⟩_ : (t₁ : U•) {t₂ : U•} {t₃ : U•} → 
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃) 
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U•) → {t : U•} → (t ⟷ t)
_□ t = id⟷
\end{code}
}

\smallskip
\begin{code}
data Path (t₁ t₂ : U•) : Set where
  path : (c : t₁ ⟷ t₂) → Path t₁ t₂

ZERO• : {absurd : ⟦ ZERO ⟧} → U•
ZERO• {absurd} = •[ ZERO , absurd ]

ONE• : U•
ONE• = •[ ONE , tt ]

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

\jc{Shouldn't we also show that \AgdaPrimitiveType{Bool} contains
exactly $2$ things, and that TRUE and FALSE are ``different'' ?}
\jc{The other thing is, whereas not used to be a path between Bool and
Bool, we no longer have that.  Shouldn't we show that, somehow,
BOOL and BOOL.F 'union' BOOL.T are somehow ``equivalent''?  And there
there is a coherent notpath built the same way?  Especially since I
am sure it is quite easy to build incoherent sets of paths!}

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

%%%%%%%%%%%%%%%%%
\subsection{Examples}

Given that all paths are between pointed spaces, i.e., are between particular
values, it might appear that all paths between the same pointed spaces are
extensionally equivalent. Consider first the following simple examples, which
are all paths from the pointed space
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
\AgdaFunction{FALSE} but follow different intermediate steps along the
way. Thinking extensionally, the paths are equivalent. But they are also
equivalent if we look at their internal structure using a few simple groupoid
identities. In particular, paths \AgdaFunction{p₂} and \AgdaFunction{p₄}
sequentially compose the boolean negation with the trivial path, and hence by
the groupoid laws are equivalent to \AgdaFunction{p₁}. Similarly, the first
two steps in path \AgdaFunction{p₃} sequentially compose a combinator with
its inverse which is equivalent to the trivial path by the groupoid laws. For
path \AgdaFunction{p₅}, the groupoid laws are not sufficient to prove its
equivalence with any of the other paths but one can argue, as shown below,
that it is also equivalent to the others. 

Ultimately, the question of whether path \AgdaFunction{p₅} should be
considered equivalent to the others should be based on whether there is a
``smooth deformation'' between the paths. This question can be addressed from
a purely categorical approach thanks to the various \emph{coherence theorems}
connecting the categorical wiring diagrams to special cases of homotopies
called isotopies. (See Selinger's paper~\citeyearpar{selinger-graphical} for
an excellent survey and the papers by Joyal and
Street~\citeyearpar{planardiagrams,geometrytensor} for the original
development.) We will not pursue this in detail except for a short discussion
in the next section. 

But first, we address the important question of whether all paths from a
given pointed space to another should be considered equivalent. We answer
this question negatively using the following two examples:

\smallskip
\begin{code}
BOOL² : U
BOOL² = TIMES BOOL BOOL

NOT•T2 CNOT•TT :
  •[ BOOL² , (TRUE , TRUE) ] ⟷ •[ BOOL² , (TRUE , FALSE) ]
           
NOT•T2 = id⟷ ⊗ NOT•T

CNOT•TT = 
  dist1 ◎ 
  ((id⟷ ⊗ NOT•T) ⊕1 (id⟷ {v = (tt , TRUE)})) ◎ 
  factor1
\end{code}
\smallskip

\noindent The path \AgdaFunction{NOT•T2} just negates the second component of
the pair. The path \AgdaFunction{CNOT•TT} is the conditional-not reversible
gate which only negates the second component of the pair if the first
component is \AgdaFunction{TRUE}. Although the two paths have the same
endpoints, they should not be considered equivalent. The simple reason is
that the paths can be given different more general types, i.e., they connect
different families of endpoints:

\smallskip
\begin{code}
NOT•T2' : ∀ {v} → 
  •[ BOOL² , (v , TRUE) ] ⟷ •[ BOOL² , (v , FALSE) ]
NOT•T2' = id⟷ ⊗ NOT•T

CNOT•TT' : ∀ {v} → 
  •[ BOOL² , (inj₁ v , TRUE) ] ⟷ •[ BOOL² , (inj₁ v , FALSE) ]
CNOT•TT' = 
  dist1 ◎ 
  ((id⟷ ⊗ NOT•T) ⊕1 (id⟷ {v = (tt , TRUE)})) ◎ 
  factor1
\end{code}
\smallskip

\noindent Indeed it is possible to use \AgdaFunction{NOT•T2'} with the value
\AgdaBound{v} bound to \AgdaFunction{FALSE} but this is not possible for
the other path. We should therefore be careful not to introduce 2-paths between
arbitrary paths just because they agree on some endpoints.

%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Isotopies} 

Returning to idea of ``smooth deformations'' of paths, we first introduce a
graphical notation for paths which is the ``space'' in which the deformations
happen. The conventional presentation of wiring diagrams is for unpointed
spaces. We adapt it for pointed spaces. First we show how to represent each
possible pointed space as a collection of ``wires'' and then we show how each
combinator ``shuffles'' or ``transforms'' the wires:
\begin{itemize}
\item It is not possible to produce a pointed space
  \pointed{\AgdaInductiveConstructor{ZERO}}{\AgdaBound{v}} for any
  \AgdaBound{v}.
\item The pointed space
  \pointed{\AgdaInductiveConstructor{ONE}}{\AgdaInductiveConstructor{tt}} is
  invisible in the graphical notation.
\item The pointed space \pointed{\AgdaInductiveConstructor{TIMES}
  \AgdaBound{t₁} \AgdaBound{t₂}}{\AgdaBound{(v₁ , v₂)}} is
  represented using two parallel wires labeled \AgdaBound{v₁} and
  \AgdaBound{v₂}:
\[
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
        *{}\wire{r}{\AgdaBound{v₁}}&\\
        *{}\wire{r}{\AgdaBound{v₂}}&
        }}
\]
 Note that if one of the types is \AgdaInductiveConstructor{ONE}, the
 corresponding wire disappears. If both the wires are
 \AgdaInductiveConstructor{ONE}, they both disappear.
\item The pointed space \pointed{\AgdaInductiveConstructor{PLUS}
  \AgdaBound{t₁} \AgdaBound{t₂}}{\AgdaInductiveConstructor{inj₁}
  \AgdaBound{v₁}} is represented by a wire labeled with
  \AgdaInductiveConstructor{inj₁} \AgdaBound{v₁}. The pointed space
  \pointed{\AgdaInductiveConstructor{PLUS} \AgdaBound{t₁}
    \AgdaBound{t₂}}{\AgdaInductiveConstructor{inj₂} \AgdaBound{v₂}} is
  similarly represented by a wire labeled with
  \AgdaInductiveConstructor{inj₂} \AgdaBound{v₂}. 
\[
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
        *{}\wire{r}{\AgdaInductiveConstructor{inj₁}~\AgdaBound{v₁}}&
        }}
\qquad
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
        *{}\wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v₂}}&
        }}
\]
\item Knowing how points are represented, we now show how various combinators
  act on the wires. The combinator \AgdaInductiveConstructor{id⟷} is
  invisible. The combinator \AgdaInductiveConstructor{◎} connects the
  outgoing wires of one diagram to the input wires of the other. The
  associativity of \AgdaInductiveConstructor{◎} is implicit in the graphical
  notation. 
\item The combinators \AgdaInductiveConstructor{unite₊} and
  \AgdaInductiveConstructor{uniti₊} are represented as follows:
\[
\vcenter{
\wirechart{}{\wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaInductiveConstructor{unite₊}}
  \wire{r}{\AgdaBound{v}}&}
}
\qquad
\vcenter{
\wirechart{}{\wire{r}{\AgdaBound{v}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaInductiveConstructor{uniti₊}}
  \wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v}}&}
}
\]
\item All other combinators that just re-label a value are similarly
  represented as one box with one incoming wire labeled by the input value
  and one outgoing wires labeled by the resulting value.
\item The combinators that operate on \AgdaInductiveConstructor{TIMES} types
  are a bit more involved as shown below. First, although the unit value
  \AgdaInductiveConstructor{tt} is invisible in the graphical notation, the
  combinators \AgdaInductiveConstructor{unite⋆} and
  \AgdaInductiveConstructor{uniti⋆} are still represented as boxes as shown
  below: 
\[
\vcenter{
\wirechart{}{\wire{r}{\AgdaBound{v}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaInductiveConstructor{unite⋆}}
  \wire{r}{\AgdaBound{v}}&}
}
\qquad
\vcenter{
\wirechart{}{\wire{r}{\AgdaBound{v}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaInductiveConstructor{uniti⋆}}
  \wire{r}{\AgdaBound{v}}&}
}
\]

  The combinator \AgdaInductiveConstructor{swap⋆} is represented by
  crisscrossing wires:
  \[
  \vcenter{\wirechart{@C=1.2cm@R=0.5cm}{
  *{}\wire{r}{\AgdaBound{v₁}}&\blank\wirecross{d}\wire{r}{\AgdaBound{v₂}}&\\
  *{}\wire{r}{\AgdaBound{v₂}}&\blank\wirecross{u}\wire{r}{\AgdaBound{v₁}}&
  }}
  \]
  As discussed below, it is possible to consider a 3d variation which makes
  explicit which of the wires is on top and which is on bottom. The
  combinators \AgdaInductiveConstructor{assocl⋆} and
  \AgdaInductiveConstructor{assocr⋆} are invisible in the graphical notation
  as associativity of parallel wires is implicit. In other words, three
  parallel wires could be seen as representing \AgdaBound{((v₁ , v₂) , v₃)}
  or \AgdaBound{(v₁ , (v₂ , v₃))}.

\item The combinators \AgdaInductiveConstructor{dist1},
  \AgdaInductiveConstructor{dist2}, \AgdaInductiveConstructor{factor1}, and
  \AgdaInductiveConstructor{factor2} have the following representation:
  \[
  \vcenter{\wirechart{@C=1.2cm@R=0.5cm}{
  *{}\wire{r}{\AgdaInductiveConstructor{inj₁}~\AgdaBound{v₁}}&& \\
  *{} & \wwblank{12mm}\nnbox{[u].[d]}{\AgdaInductiveConstructor{dist1}} & 
    \wire{r}{\AgdaInductiveConstructor{inj₁}~(\AgdaBound{v₁},\AgdaBound{v₃})}& \\
  *{}\wire{r}{\AgdaBound{v₃}}&&&
  }}
  \]

\as{fix this diagram and add the other 3 diagrams} 

%% -- inj1 v1 [      ]
%% --         [dist1 ] inj1 (v1 , v3) 
%% -- v3      [      ]


\item The composite combinator \AgdaBound{c₁} \AgdaSymbol{⊗} \AgdaBound{c₂}
  is the parallel composition shown below:
  \[ 
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
 \vsblank\wire{r}{\AgdaBound{v₁}}&\blank\nnbox{[]}
    {\AgdaBound{c₁}}\wire{r}{\AgdaBound{v₃}}&\\
 \vsblank\wire{r}{\AgdaBound{v₂}}&\blank\nnbox{[]}
    {\AgdaBound{c₂}}\wire{r}{\AgdaBound{v₄}}&
 }}
  \]
\item The combinators \AgdaBound{c₁} \AgdaSymbol{⊕1} \AgdaBound{c₂} and 
\AgdaBound{c₁} \AgdaSymbol{⊕2} \AgdaBound{c₂} are represented as follows:
  \[ 
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
 \blank\wire{r}{\AgdaInductiveConstructor{inj₁}~\AgdaBound{v₁}}
 \vsblank&\wwblank{15mm}\nnbox{[]}
   {\AgdaBound{v₁}\quad\AgdaBound{c₁}\quad\AgdaBound{v₃}}
   \wire{r}{\AgdaInductiveConstructor{inj₁}~\AgdaBound{v₃}}&\\
 \vsblank&\wwblank{15mm}\nnbox{[]}{\AgdaBound{c₂}}&
 }}
\]
\[
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
 \vsblank&\wwblank{15mm}\nnbox{[]}{\AgdaBound{c₁}}&\\
 \blank\wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v₂}}
 \vsblank&\wwblank{15mm}\nnbox{[]}
   {\AgdaBound{v₂}\quad\AgdaBound{c₁}\quad\AgdaBound{v₄}}
   \wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v₄}}&
 }}
  \]
\item Finally, when a box \AgdaBound{c} is sequentially composed with its
  mirror image \AgdaSymbol{!} \AgdaBound{c} (in either order), both boxes
  disappear.
\end{itemize}

Let us draw the five paths \AgdaFunction{p₁} to \AgdaFunction{p₅} introduced
in the previous section. Since \AgdaInductiveConstructor{id⟷} is invisible, 
the three paths \AgdaFunction{p₁}, \AgdaFunction{p₂}, and 
\AgdaFunction{p₄}, are all represented as follows:
\[
\vcenter{
\wirechart{}{\wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•T}}
  \wire{r}{\AgdaFunction{FALSE}}&}
}
\]
Path \AgdaFunction{p₃} would be represented as:
\[
\vcenter{
\wirechart{}{\wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•T}}
  \wire{r}{\AgdaFunction{FALSE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•F}}
  \wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•T}}
  \wire{r}{\AgdaFunction{FALSE}}&
}}
\]
but then we notice that any two of the adjacent boxes are mirror images and
erase them to produce the same wiring diagram as the previous three paths.
For \AgdaFunction{p₅}, we have the following representation:
\[
\vcenter{\wirechart{@C=1cm@R=1cm}{
  \wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{8mm}\nnbox{[]}{~\AgdaInductiveConstructor{uniti⋆}}
  \wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•T}}
  \wire{r}{\AgdaFunction{FALSE}}&
  \wwblank{8mm}\nnbox{[]}{~\AgdaInductiveConstructor{unite⋆}}
  \wire{r}{\AgdaFunction{FALSE}}&\\
  &&\wwblank{12mm}\nnbox{[]}{\AgdaInductiveConstructor{id⟷}}&
}}
\]
where the occurrences of \AgdaInductiveConstructor{swap⋆} have disappeared
since one of the wires is invisible. The occurrences of
\AgdaInductiveConstructor{id⟷} that acts on the invisible wire does
\emph{not}, however, disappear.

The graphical notation is justified by various \emph{coherence theorems}. We
quote one of these basic theorems (originally due to Joyal and Street).

\begin{theorem}
A well-formed equation between morphisms in the language of monoidal
categories follows from the axioms of monoidal categories if and only if it
holds, up to planar isotopy, in the graphical language.
\end{theorem}

\noindent Translating to our setting, the theorem says the following. In the
special case of diagrams involving just one monoid (say
\AgdaInductiveConstructor{ZERO} and \AgdaInductiveConstructor{PLUS} types
only) and no uses of swapping combinators, the two combinators represented by
the diagrams are equivalent if the diagrams can be transformed to each other
by moving wires and boxes around without crossing, cutting, or gluing any
wires and without detaching them from the plane. Using similar theorems, it
is possible, under certain assumptions, to prove that path \AgdaFunction{p₅}
is equivalent to the other paths.

Looking at the various coherence theorems for special cases of monoidal
categories, we note an interesting subtlety that should be further
investigated in detail: in our presentation of $\Pi$, we have
assumed that \AgdaInductiveConstructor{swap⋆} is its self-inverse. But
thinking of the categorical wiring diagrams more geometrically suggests that
two wires crossing each other requires a third dimension. In other words, 
a possible diagram for \AgdaInductiveConstructor{swap⋆} would be:
\smallskip
\[
 \vcenter{\wirechart{@C=1.5cm@R=0.8cm}{
        *{}\wire{r}{}&\blank\wirecross{d}\wire{r}{}&\\
        *{}\wire{r}{}&\blank\wirebraid{u}{.3}\wire{r}{}&
        }}
\]
\smallskip
\noindent where it is explicit which path is crossing over which during the swap
operation. Technically we have moved from a symmetric monoidal category to a
\emph{braided} one. From this idea, it follows that a sequence of two swaps 
might represent one of the following two diagrams:
\smallskip
\[
\vcenter{\wirechart{@C=1.5cm@R=0.8cm}{
    *{}\wire{r}{}&
    \blank\wirecross{d}\wire{r}{}&
    \blank\wirecross{d}\wire{r}{}&
    \\
    *{}\wire{r}{}&
    \blank\wirebraid{u}{.3}\wire{r}{}&
    \blank\wirebraid{u}{.3}\wire{r}{}&
    \\
    }}
\]
\[
\vcenter{\wirechart{@C=1.5cm@R=0.8cm}{
     *{}\wire{r}{}&
     \blank\wirecross{d}\wire{r}{}&
     \blank\wirebraid{d}{.3}\wire{r}{}&
     \\
     *{}\wire{r}{}&
     \blank\wirebraid{u}{.3}\wire{r}{}&
     \blank\wirecross{u}\wire{r}{}&
     \\
     }}
\]
\smallskip
\noindent In 3 dimensions, 
the first diagram creates a ``knot'' but the second reduces
to trivial identity paths. In the context of symmetric monoidal categories,
i.e., in the context of our original presentation of $\Pi$, the diagrams
are forced to be 2 dimensional: the distinction between them vanishes 
and they become equivalent.

%%%%%%%%%%%%%%%%%%%%%
\subsection{$\Pi$ Lifted and with Groupoid Axioms}

To summarize, there is a spectrum of possibilities to be explored for when
paths should be considered equivalent. The minimum requirement is that paths
that can be related using the groupoid laws should be considered equivalent
and hence should be related by a 2-path. In the sequel, we will adopt this
conservative approach and leave further investigations to future work. 

Formally, we lift the entire $\Pi$ language to compute with paths instead of
with points. The lifted version of $\Pi$ will have all the combinators of
Fig.~\ref{pointedcomb} as well as additional combinators witnessing the
groupoid laws. The groupoid combinators will allow us to relate paths like
\AgdaFunction{p₁} and \AgdaFunction{p₂} and the combinators from
Fig.~\ref{pointedcomb} will allow us to compute with sums and products of
paths up to the commutative semiring isomorphisms. What is pleasant about
this design is that 2-paths inherit a similar structure to 1-paths, and hence
the entire scheme can be repeated over and over lifting $\Pi$ to higher and
higher levels to capture the concept of weak $\infty$-groupoids.

We now present the detailed construction of the next level of $\Pi$. 

\begin{code}
data 1U : Set where
  1ZERO   : 1U
  1ONE    : 1U
  1PLUS   : 1U → 1U → 1U
  1TIMES  : 1U → 1U → 1U
  PATH    : U• → U• → 1U

1⟦_⟧ : 1U → Set
1⟦ 1ZERO ⟧         = ⊥
1⟦ 1ONE ⟧          = ⊤
1⟦ 1PLUS t₁ t₂ ⟧   = 1⟦ t₁ ⟧ ⊎ 1⟦ t₂ ⟧
1⟦ 1TIMES t₁ t₂ ⟧  = 1⟦ t₁ ⟧ × 1⟦ t₂ ⟧
1⟦ PATH t₁ t₂ ⟧    = Path t₁ t₂
\end{code}

The new universe \AgdaFunction{1U} is a universe whose spaces are path
spaces. The space \AgdaInductiveConstructor{1ZERO} is the empty set of
paths. The space \AgdaInductiveConstructor{1ONE} is the space of paths
containing one path that is the identity for path products. Sums and products
of paths are representing using disjoint union and cartesian products. In
addition, all paths from Fig.~\ref{pointedcomb} are reified as values in
\AgdaFunction{1U}.

As before, we define pointed spaces (now of paths instead of points) and
introduce $\Pi$ combinators on these pointed path spaces. In addition
to the commutative semiring combinators, there are also combinators that
witness the groupoid equivalences. (See Fig.~\ref{pointedcomb2}.) 

\smallskip
\begin{code}
record 1U• : Set where
  constructor 1•[_,_]
  field
    1∣_∣ : 1U
    1• : 1⟦ 1∣_∣ ⟧
\end{code}
\smallskip
\AgdaHide{
\begin{code}
open 1U•
\end{code}
}

\begin{figure*}
\begin{multicols}{2}
\renewcommand{\AgdaCodeStyle}{\scriptsize}
\begin{code} 
data _⇔_ : 1U• → 1U• → Set where
 -- Commutative semiring combinators
 unite₊ : ∀ {t v} → 1•[ 1PLUS 1ZERO t , inj₂ v ] ⇔ 1•[ t , v ]
 uniti₊ : ∀ {t v} → 1•[ t , v ] ⇔ 1•[ 1PLUS 1ZERO t , inj₂ v ]
 swap1₊ : ∀ {t₁ t₂ v₁} → 1•[ 1PLUS t₁ t₂ , inj₁ v₁ ] ⇔ 1•[ 1PLUS t₂ t₁ , inj₂ v₁ ]
 swap2₊ : ∀ {t₁ t₂ v₂} → 1•[ 1PLUS t₁ t₂ , inj₂ v₂ ] ⇔ 1•[ 1PLUS t₂ t₁ , inj₁ v₂ ]
 assocl1₊ : ∀ {t₁ t₂ t₃ v₁} → 
  1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₁ v₁ ] ⇔ 
  1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ]
 assocl2₊ : ∀ {t₁ t₂ t₃ v₂} → 
  1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] ⇔ 
  1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ]
 assocl3₊ : ∀ {t₁ t₂ t₃ v₃} → 
  1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] ⇔ 
  1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₂ v₃ ]
 assocr1₊ : ∀ {t₁ t₂ t₃ v₁} → 
  1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ] ⇔ 
  1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₁ v₁ ] 
 assocr2₊ : ∀ {t₁ t₂ t₃ v₂} → 
  1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ] ⇔ 
  1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] 
 assocr3₊ : ∀ {t₁ t₂ t₃ v₃} → 
  1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₂ v₃ ] ⇔ 
  1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
 unite⋆ : ∀ {t v} → 1•[ 1TIMES 1ONE t , (tt , v) ] ⇔ 1•[ t , v ]
 uniti⋆ : ∀ {t v} → 1•[ t , v ] ⇔ 1•[ 1TIMES 1ONE t , (tt , v) ] 
 swap⋆ : ∀ {t₁ t₂ v₁ v₂} → 
  1•[ 1TIMES t₁ t₂ , (v₁ , v₂) ] ⇔ 1•[ 1TIMES t₂ t₁ , (v₂ , v₁) ]
 assocl⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
  1•[ 1TIMES t₁ (1TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ] ⇔ 
  1•[ 1TIMES (1TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ]
 assocr⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
  1•[ 1TIMES (1TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ] ⇔ 
  1•[ 1TIMES t₁ (1TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ]
 distz : ∀ {t v absurd} → 
  1•[ 1TIMES 1ZERO t , (absurd , v) ] ⇔ 1•[ 1ZERO , absurd ]
 factorz : ∀ {t v absurd} → 
  1•[ 1ZERO , absurd ] ⇔ 1•[ 1TIMES 1ZERO t , (absurd , v) ]
 dist1 : ∀ {t₁ t₂ t₃ v₁ v₃} → 
  1•[ 1TIMES (1PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ⇔ 
  1•[ 1PLUS (1TIMES t₁ t₃) (1TIMES t₂ t₃) , inj₁ (v₁ , v₃) ]
 dist2 : ∀ {t₁ t₂ t₃ v₂ v₃} → 
  1•[ 1TIMES (1PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ⇔ 
  1•[ 1PLUS (1TIMES t₁ t₃) (1TIMES t₂ t₃) , inj₂ (v₂ , v₃) ]
 factor1 : ∀ {t₁ t₂ t₃ v₁ v₃} → 
  1•[ 1PLUS (1TIMES t₁ t₃) (1TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ⇔ 
  1•[ 1TIMES (1PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ]
 factor2 : ∀ {t₁ t₂ t₃ v₂ v₃} → 
  1•[ 1PLUS (1TIMES t₁ t₃) (1TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ⇔ 
  1•[ 1TIMES (1PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ]
 id⇔ : ∀ {t v} → 1•[ t , v ] ⇔ 1•[ t , v ]
 _◎_ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → (1•[ t₁ , v₁ ] ⇔ 1•[ t₂ , v₂ ]) → 
  (1•[ t₂ , v₂ ] ⇔ 1•[ t₃ , v₃ ]) → (1•[ t₁ , v₁ ] ⇔ 1•[ t₃ , v₃ ])
 _⊕1_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
  (1•[ t₁ , v₁ ] ⇔ 1•[ t₃ , v₃ ]) → (1•[ t₂ , v₂ ] ⇔ 1•[ t₄ , v₄ ]) → 
  (1•[ 1PLUS t₁ t₂ , inj₁ v₁ ] ⇔ 1•[ 1PLUS t₃ t₄ , inj₁ v₃ ])
 _⊕2_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
  (1•[ t₁ , v₁ ] ⇔ 1•[ t₃ , v₃ ]) → (1•[ t₂ , v₂ ] ⇔ 1•[ t₄ , v₄ ]) → 
  (1•[ 1PLUS t₁ t₂ , inj₂ v₂ ] ⇔ 1•[ 1PLUS t₃ t₄ , inj₂ v₄ ])
 _⊗_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
  (1•[ t₁ , v₁ ] ⇔ 1•[ t₃ , v₃ ]) → (1•[ t₂ , v₂ ] ⇔ 1•[ t₄ , v₄ ]) → 
  (1•[ 1TIMES t₁ t₂ , (v₁ , v₂) ] ⇔ 1•[ 1TIMES t₃ t₄ , (v₃ , v₄) ])

 -- Groupoid combinators
 lidl : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂} → 
  1•[ PATH t₁ t₂ , path (id⟷ ◎ c) ] ⇔ 1•[ PATH t₁ t₂ , path c ]
 lidr : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂} → 
  1•[ PATH t₁ t₂ , path c ] ⇔ 1•[ PATH t₁ t₂ , path (id⟷ ◎ c) ] 
 ridl : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂} → 
  1•[ PATH t₁ t₂ , path (c ◎ id⟷) ] ⇔ 1•[ PATH t₁ t₂ , path c ]
 ridr : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂} → 
  1•[ PATH t₁ t₂ , path c ] ⇔ 1•[ PATH t₁ t₂ , path (c ◎ id⟷) ] 
 assocl : ∀ {t₁ t₂ t₃ t₄} → {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
  1•[ PATH t₁ t₄ , path (c₁ ◎ (c₂ ◎ c₃)) ] ⇔ 1•[ PATH t₁ t₄ , path ((c₁ ◎ c₂) ◎ c₃) ]
 assocr : ∀ {t₁ t₂ t₃ t₄} → {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
  1•[ PATH t₁ t₄ , path ((c₁ ◎ c₂) ◎ c₃) ] ⇔ 1•[ PATH t₁ t₄ , path (c₁ ◎ (c₂ ◎ c₃)) ] 
 unite₊l : ∀ {t v} → 
  1•[ PATH (•[ PLUS ZERO t , inj₂ v ]) (•[ PLUS ZERO t , inj₂ v ]) , 
    path (unite₊ ◎ uniti₊) ] ⇔ 
  1•[ PATH (•[ PLUS ZERO t , inj₂ v ]) (•[ PLUS ZERO t , inj₂ v ]) , path id⟷ ] 
 unite₊r : ∀ {t v} → 
  1•[ PATH (•[ PLUS ZERO t , inj₂ v ]) (•[ PLUS ZERO t , inj₂ v ]) , path id⟷ ] ⇔ 
  1•[ PATH (•[ PLUS ZERO t , inj₂ v ]) (•[ PLUS ZERO t , inj₂ v ]) , 
    path (unite₊ ◎ uniti₊) ] 
 uniti₊l : ∀ {t v} → 
  1•[ PATH (•[ t , v ]) (•[ t , v ]) , path (uniti₊ ◎ unite₊) ] ⇔ 
  1•[ PATH (•[ t , v ]) (•[ t , v ]) , path id⟷ ] 
 uniti₊r : ∀ {t v} → 
  1•[ PATH (•[ t , v ]) (•[ t , v ]) , path id⟷ ] ⇔ 
  1•[ PATH (•[ t , v ]) (•[ t , v ]) , path (uniti₊ ◎ unite₊) ] 
 swap1₊l : ∀ {t₁ t₂ v₁} → 
  1•[ PATH •[ PLUS t₁ t₂ , inj₁ v₁ ] •[ PLUS t₁ t₂ , inj₁ v₁ ] ,
    path (swap1₊ ◎ ! swap1₊) ] ⇔
  1•[ PATH •[ PLUS t₁ t₂ , inj₁ v₁ ] •[ PLUS t₁ t₂ , inj₁ v₁ ] , path id⟷ ]
 swap1₊r : ∀ {t₁ t₂ v₁} → 
  1•[ PATH •[ PLUS t₁ t₂ , inj₁ v₁ ] •[ PLUS t₁ t₂ , inj₁ v₁ ] , path id⟷ ] ⇔
  1•[ PATH •[ PLUS t₁ t₂ , inj₁ v₁ ] •[ PLUS t₁ t₂ , inj₁ v₁ ] ,
    path (swap1₊ ◎ ! swap1₊) ] 
 swap2₊l : ∀ {t₁ t₂ v₂} → 
  1•[ PATH •[ PLUS t₁ t₂ , inj₂ v₂ ] •[ PLUS t₁ t₂ , inj₂ v₂ ] , 
    path (swap2₊ ◎ ! swap2₊) ] ⇔
  1•[ PATH •[ PLUS t₁ t₂ , inj₂ v₂ ] •[ PLUS t₁ t₂ , inj₂ v₂ ] , path id⟷ ]
 swap2₊r : ∀ {t₁ t₂ v₂} → 
  1•[ PATH •[ PLUS t₁ t₂ , inj₂ v₂ ] •[ PLUS t₁ t₂ , inj₂ v₂ ] , path id⟷ ] ⇔
  1•[ PATH •[ PLUS t₁ t₂ , inj₂ v₂ ] •[ PLUS t₁ t₂ , inj₂ v₂ ] , 
    path (swap2₊ ◎ ! swap2₊) ] 
 assocl1₊l : ∀ {t₁ t₂ t₃ v₁} → 
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] , 
    path (assocl1₊ ◎ ! assocl1₊) ] ⇔
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] , 
    path id⟷ ]
 assocl1₊r : ∀ {t₁ t₂ t₃ v₁} → 
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] , 
    path id⟷ ] ⇔
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] , 
  path (assocl1₊ ◎ ! assocl1₊) ] 
 assocl2₊l : ∀ {t₁ t₂ t₃ v₂} → 
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] 
     •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] , path (assocl2₊ ◎ ! assocl2₊) ] ⇔
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ]
    •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] , path id⟷ ]
 assocl2₊r : ∀ {t₁ t₂ t₃ v₂} → 
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ]
           •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] , path id⟷ ] ⇔
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ]
           •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] , 
  path (assocl2₊ ◎ ! assocl2₊) ] 
 assocl3₊l : ∀ {t₁ t₂ t₃ v₃} → 
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
           •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] , 
  path (assocl3₊ ◎ ! assocl3₊) ] ⇔
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
           •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] , path id⟷ ]
 assocl3₊r : ∀ {t₁ t₂ t₃ v₃} → 
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
           •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] , path id⟷ ] ⇔
  1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
           •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] , 
   path (assocl3₊ ◎ ! assocl3₊) ] 
 resp◎ : ∀ {t₁ t₂ t₃} → {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} → 
   (1•[ PATH t₁ t₂ , path c₁ ] ⇔ 1•[ PATH t₁ t₂ , path c₃ ]) → 
   (1•[ PATH t₂ t₃ , path c₂ ] ⇔ 1•[ PATH t₂ t₃ , path c₄ ]) → 
    1•[ PATH t₁ t₃ , path (c₁ ◎ c₂) ] ⇔ 1•[ PATH t₁ t₃ , path (c₃ ◎ c₄) ]
\end{code}
\renewcommand{\AgdaCodeStyle}{\small}
\end{multicols}
\caption{Inductive definition of 2-paths\label{pointedcomb2}}
\end{figure*}

\AgdaHide{
\begin{code}
1! : {t₁ t₂ : 1U•} → (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
1! unite₊ = uniti₊
1! uniti₊ = unite₊
1! swap1₊ = swap2₊
1! swap2₊ = swap1₊
1! assocl1₊ = assocr1₊
1! assocl2₊ = assocr2₊
1! assocl3₊ = assocr3₊
1! assocr1₊ = assocl1₊
1! assocr2₊ = assocl2₊
1! assocr3₊ = assocl3₊
1! unite⋆ = uniti⋆
1! uniti⋆ = unite⋆
1! swap⋆ = swap⋆
1! assocl⋆ = assocr⋆
1! assocr⋆ = assocl⋆
1! distz = factorz
1! factorz = distz
1! dist1 = factor1 
1! dist2 = factor2 
1! factor1 = dist1 
1! factor2 = dist2 
1! id⇔ = id⇔
1! (c₁ ◎ c₂) = 1! c₂ ◎ 1! c₁ 
1! (c₁ ⊕1 c₂) = 1! c₁ ⊕1 1! c₂ 
1! (c₁ ⊕2 c₂) = 1! c₁ ⊕2 1! c₂ 
1! (c₁ ⊗ c₂) = 1! c₁ ⊗ 1! c₂ 
1! (resp◎ c₁ c₂) = resp◎ (1! c₁) (1! c₂)
1! ridl = ridr
1! ridr = ridl
1! lidl = lidr
1! lidr = lidl
1! assocl = assocr
1! assocr = assocl
1! _ = {!!} 

linv : {t₁ t₂ : U•} → (c : t₁ ⟷ t₂) → 
       1•[ PATH t₁ t₁ , path (c ◎ ! c) ] ⇔ 1•[ PATH t₁ t₁ , path id⟷ ]
linv unite₊ = unite₊l
linv uniti₊ = uniti₊l
linv swap1₊ = swap1₊l
linv swap2₊ = swap2₊l
linv assocl1₊ = assocl1₊l
linv assocl2₊ = assocl2₊l
linv assocl3₊ = assocl3₊l
linv assocr1₊ = {!!}
linv assocr2₊ = {!!}
linv assocr3₊ = {!!}
linv unite⋆ = {!!}
linv uniti⋆ = {!!}
linv swap⋆ = {!!}
linv assocl⋆ = {!!}
linv assocr⋆ = {!!}
linv distz = {!!}
linv factorz = {!!}
linv dist1 = {!!}
linv dist2 = {!!}
linv factor1 = {!!}
linv factor2 = {!!}
linv id⟷ = {!!}
linv (c ◎ c₁) = {!!}
linv (c ⊕1 c₁) = {!!}
linv (c ⊕2 c₁) = {!!}
linv (c ⊗ c₁) = {!!} 

rinv : {t₁ t₂ : U•} → (c : t₁ ⟷ t₂) → 
       1•[ PATH t₂ t₂ , path (! c ◎ c) ] ⇔ 1•[ PATH t₂ t₂ , path id⟷ ]
rinv unite₊ = uniti₊l 
rinv uniti₊ = unite₊l
rinv swap1₊ = swap2₊l
rinv swap2₊ = swap1₊l
rinv assocl1₊ = {!!}
rinv assocl2₊ = {!!}
rinv assocl3₊ = {!!}
rinv assocr1₊ = assocl1₊l
rinv assocr2₊ = assocl2₊l
rinv assocr3₊ = assocl3₊l
rinv unite⋆ = {!!}
rinv uniti⋆ = {!!}
rinv swap⋆ = {!!}
rinv assocl⋆ = {!!}
rinv assocr⋆ = {!!}
rinv distz = {!!}
rinv factorz = {!!}
rinv dist1 = {!!}
rinv dist2 = {!!}
rinv factor1 = {!!}
rinv factor2 = {!!}
rinv id⟷ = {!!}
rinv (c ◎ c₁) = {!!}
rinv (c ⊕1 c₁) = {!!}
rinv (c ⊕2 c₁) = {!!}
rinv (c ⊗ c₁) = {!!} 
\end{code}
}

To verify that the universe \AgdaFunction{U•} with \AgdaSymbol{⟷} as 1-paths
and \AgdaSymbol{⇔} as 2-paths is indeed a groupoid, we have developed a small
library inspired by Thorsten Altenkirch's definition of groupoids (see
\url{http://github.com/txa/OmegaCats}) and copumpkin's definition of
category (see \url{http://github.com/copumpkin/categories}). The proof is
shown below:

\begin{code}
G : 1Groupoid
G = record
        { set = U•
        ; _↝_ = _⟷_
        ; _≈_ = λ {t₁} {t₂} c₀ c₁ → 
                1•[ PATH t₁ t₂ , path c₀ ] ⇔ 1•[ PATH t₁ t₂ , path c₁ ]
        ; id = id⟷
        ; _∘_ = λ c₀ c₁ → c₁ ◎ c₀
        ; _⁻¹ = ! 
        ; lneutr = λ _ → ridl 
        ; rneutr = λ _ → lidl 
        ; assoc = λ _ _ _ → assocl
        ; equiv = record { refl = id⇔
                                ; sym = λ c → 1! c 
                                ; trans = λ c₀ c₁ → c₀ ◎ c₁ }
        ; linv = λ {t₁} {t₂} c → linv c
        ; rinv = λ {t₁} {t₂} c → rinv c
        ; ∘-resp-≈ = λ f⟷h g⟷i → resp◎ g⟷i f⟷h 
        }
\end{code}

The proof refers to two simple functions \AgdaFunction{linv} and
\AgdaFunction{rinv} with the following types:

{\small{
\AgdaFunction{linv} \AgdaSymbol{:} \AgdaSymbol{\{}\AgdaBound{t₁}
\AgdaBound{t₂} \AgdaSymbol{:} \AgdaRecord{U•}\AgdaSymbol{\}} \AgdaSymbol{→}
\AgdaSymbol{(}\AgdaBound{c} \AgdaSymbol{:} \AgdaBound{t₁} \AgdaDatatype{⟷}
\AgdaBound{t₂}\AgdaSymbol{)} \AgdaSymbol{→}

\quad\AgdaInductiveConstructor{1•[} \AgdaInductiveConstructor{PATH}
  \AgdaBound{t₁} \AgdaBound{t₁} \AgdaInductiveConstructor{,}
  \AgdaInductiveConstructor{path} \AgdaSymbol{(}\AgdaBound{c}
  \AgdaInductiveConstructor{◎} \AgdaFunction{!}  \AgdaBound{c}\AgdaSymbol{)}
  \AgdaInductiveConstructor{]} \AgdaDatatype{⇔}
\AgdaInductiveConstructor{1•[} \AgdaInductiveConstructor{PATH} \AgdaBound{t₁}
  \AgdaBound{t₁} \AgdaInductiveConstructor{,} \AgdaInductiveConstructor{path}
  \AgdaInductiveConstructor{id⟷} \AgdaInductiveConstructor{]}
}}

\smallskip

{\small{
\AgdaFunction{rinv} \AgdaSymbol{:} \AgdaSymbol{\{}\AgdaBound{t₁}
\AgdaBound{t₂} \AgdaSymbol{:} \AgdaRecord{U•}\AgdaSymbol{\}} \AgdaSymbol{→}
\AgdaSymbol{(}\AgdaBound{c} \AgdaSymbol{:} \AgdaBound{t₁} \AgdaDatatype{⟷}
\AgdaBound{t₂}\AgdaSymbol{)} \AgdaSymbol{→}

\quad\AgdaInductiveConstructor{1•[} \AgdaInductiveConstructor{PATH} \AgdaBound{t₂} \AgdaBound{t₂} \AgdaInductiveConstructor{,} \AgdaInductiveConstructor{path} \AgdaSymbol{(}\AgdaFunction{!} \AgdaBound{c} \AgdaInductiveConstructor{◎} \AgdaBound{c}\AgdaSymbol{)} \AgdaInductiveConstructor{]} \AgdaDatatype{⇔} \AgdaInductiveConstructor{1•[} \AgdaInductiveConstructor{PATH} \AgdaBound{t₂} \AgdaBound{t₂} \AgdaInductiveConstructor{,} \AgdaInductiveConstructor{path} \AgdaInductiveConstructor{id⟷} \AgdaInductiveConstructor{]}
}}

\todo{show a few cases?}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Int Construction}
\label{intc}

\todo{transition}

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

%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Conventionl Construction on Unpointed Types} 

We begin our formal development by extending $\Pi$ --- at any level --- 
with a new universe of
types $\cubt$ that consists of composite types $\nodet{\tau_1}{\tau_2}$:
\[\begin{array}{lrcl}
(\textit{{1d} types}) & 
  \cubt &::=& \nodet{\tau_1}{\tau_2}
\end{array}\]
We will refer to the original types $\tau$ as 0-dimensional (0d) types and to
the new types $\cubt$ as 1-dimensional (1d) types. The 1d level is a
``lifted'' instance of $\Pi$ with its own notions of empty, unit, sum, and
product types, and its corresponding notion of isomorphisms on these 1d
types.

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
appreciation is essential for the remainder of the paper.

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
are to add more dimensions and then take homotopy colimits. It remains to
investigate whether this idea can be integrated with our development to get
higher-order functions while retaining the multiplicative structure.

%%%%%%%%%%%%%%%%
\subsection{Pointed Int Construction} 

Since our development is done using pointed spaces, we adapt the conventional
construction as follows. 

\begin{code}
record U- : Set where
  constructor _-_
  field
    pos  : U
    neg  : U

open U-

ZERO- ONE- : U-
ZERO- = ZERO - ZERO
ONE-  = ONE  - ZERO

PLUS- : U- → U- → U-
PLUS- (pos₁ - neg₁) (pos₂ - neg₂) = 
  PLUS pos₁ pos₂ - PLUS neg₁ neg₂

TIMES- : U- → U- → U-
TIMES- (pos₁ - neg₁) (pos₂ - neg₂) = 
  PLUS (TIMES pos₁ pos₂) (TIMES neg₁ neg₂) -
  PLUS (TIMES pos₁ neg₂) (TIMES neg₁ pos₂)

FLIP- : U- → U-
FLIP- (pos - neg) = neg - pos

LOLLI- : U- → U- → U-
LOLLI- (pos₁ - neg₁) (pos₂ - neg₂) = 
  PLUS neg₁ pos₂ - PLUS pos₁ neg₂

data U-• : Set where
  both• : (t : U-) → ⟦ pos t ⟧ → ⟦ neg t ⟧ → U-•

ZERO-• : {absurd : ⟦ ZERO ⟧} → U-•
ZERO-• {absurd} = both• ZERO- absurd absurd

ONE-• : {absurd : ⟦ ZERO ⟧} → U-•
ONE-• {absurd} = both• ONE- tt absurd

FLIP-• : U-• → U-• 
FLIP-• (both• t p n) = both• (FLIP- t) n p

PLUS-11• : U-• → U-• → U-•
PLUS-11• (both• t₁ p₁ n₁) (both• t₂ p₂ n₂) = 
  both• (PLUS- t₁ t₂) (inj₁ p₁) (inj₁ n₁) 

PLUS-12• : U-• → U-• → U-•
PLUS-12• (both• t₁ p₁ n₁) (both• t₂ p₂ n₂) = 
  both• (PLUS- t₁ t₂) (inj₁ p₁) (inj₂ n₂) 

PLUS-21• : U-• → U-• → U-•
PLUS-21• (both• t₁ p₁ n₁) (both• t₂ p₂ n₂) = 
  both• (PLUS- t₁ t₂) (inj₂ p₂) (inj₁ n₁) 

PLUS-22• : U-• → U-• → U-•
PLUS-22• (both• t₁ p₁ n₁) (both• t₂ p₂ n₂) = 
  both• (PLUS- t₁ t₂) (inj₂ p₂) (inj₂ n₂) 

LOLLI-11• : U-• → U-• → U-•
LOLLI-11• (both• t₁ p₁ n₁) (both• t₂ p₂ n₂) = 
  both• (LOLLI- t₁ t₂) (inj₁ n₁) (inj₁ p₁) 

LOLLI-12• : U-• → U-• → U-•
LOLLI-12• (both• t₁ p₁ n₁) (both• t₂ p₂ n₂) = 
  both• (LOLLI- t₁ t₂) (inj₁ n₁) (inj₂ n₂) 

LOLLI-21• : U-• → U-• → U-•
LOLLI-21• (both• t₁ p₁ n₁) (both• t₂ p₂ n₂) = 
  both• (LOLLI- t₁ t₂) (inj₂ p₂) (inj₁ p₁) 

LOLLI-22• : U-• → U-• → U-•
LOLLI-22• (both• t₁ p₁ n₁) (both• t₂ p₂ n₂) = 
  both• (LOLLI- t₁ t₂) (inj₂ p₂) (inj₂ n₂) 

data _⇄_ : U-• → U-• → Set where
  NN : ∀ {P₁ N₁ P₂ N₂ p₁ n₁ p₂ n₂} → 
       •[ PLUS P₁ N₂ , inj₂ n₂ ] ⟷ •[ PLUS N₁ P₂ , inj₁ n₁ ] → 
       (both• (P₁ - N₁) p₁ n₁) ⇄ (both• (P₂ - N₂) p₂ n₂)
  NP : ∀ {P₁ N₁ P₂ N₂ p₁ n₁ p₂ n₂} → 
       •[ PLUS P₁ N₂ , inj₂ n₂ ] ⟷ •[ PLUS N₁ P₂ , inj₂ p₂ ] → 
       (both• (P₁ - N₁) p₁ n₁) ⇄ (both• (P₂ - N₂) p₂ n₂)
  PN : ∀ {P₁ N₁ P₂ N₂ p₁ n₁ p₂ n₂} → 
       •[ PLUS P₁ N₂ , inj₁ p₁ ] ⟷ •[ PLUS N₁ P₂ , inj₁ n₁ ] → 
       (both• (P₁ - N₁) p₁ n₁) ⇄ (both• (P₂ - N₂) p₂ n₂)
  PP : ∀ {P₁ N₁ P₂ N₂ p₁ n₁ p₂ n₂} → 
       •[ PLUS P₁ N₂ , inj₁ p₁ ] ⟷ •[ PLUS N₁ P₂ , inj₂  p₂ ] → 
       (both• (P₁ - N₁) p₁ n₁) ⇄ (both• (P₂ - N₂) p₂ n₂)

-- there are two fibers for id in the int category

id⇄NN : {t : U-•} → t ⇄ t
id⇄NN {both• t p n} = NN swap2₊

id⇄PP : {t : U-•} → t ⇄ t
id⇄PP {both• t p n} = PP swap1₊

identl₊ : {t : U-•} → PLUS-22• ZERO-• t ⇄ t
identl₊ = {!!} -- PP (assocr2₊ ◎ (id⟷ ⊕2 swap1₊) ◎ assocl3₊)

-- define trace and composition

flip⇄ : {t₁ t₂ : U-•} → (t₁ ⇄ t₂) → (FLIP-• t₂ ⇄ FLIP-• t₁) 
flip⇄ (NN c) = PP (swap1₊ ◎ c ◎ swap1₊) 
flip⇄ (NP c) = PN (swap1₊ ◎ c ◎ swap2₊) 
flip⇄ (PN c) = NP (swap2₊ ◎ c ◎ swap1₊) 
flip⇄ (PP c) = NN (swap2₊ ◎ c ◎ swap2₊) 

curry1111⇄ : {t₁ t₂ t₃ : U-•} → (PLUS-11• t₁ t₂ ⇄ t₃) → (t₁ ⇄ LOLLI-11• t₂ t₃)
curry1111⇄ {t₁} {t₂} {t₃} f = {!!} 

-- define small example:

-- given in plain Pi level 0
-- c1 c2 : t1 + t4 <-> t2 + t3
-- given in plain Pi level 1
-- alpha : c1 <-> c2

-- in the int category
-- c1 and c2 are maps between (t1 - t2) and (t3 - t4)
-- 'name c1' and 'name c2' are maps between (0 - 0) and ((t1 - t2) --o (t3 - t4))
-- c1 and c2 themselves become elements of ((t1 - t2) --o (t3 - t4))
-- i.e., they become values
-- alpha that used to be a 2path, i.e., a path between paths, is now 
-- a path between the values c1 and c2 in the --o type

\end{code}

%%   

%%%%%%%%%%%%%%%%
\subsection{Example}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

2-paths are functions on paths; the int construction reifies these
functions/2-paths as 1-paths

Add eta/epsilon and trace to Int 
category

Talk about trace and recursive types

talk about h.o. functions, negative types, int construction, ring completion
paper

canonicity for 2d type theory; licata harper

triangle; pentagon rules; eckmann-hilton

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\bibliographystyle{abbrvnat}
\softraggedright
\bibliography{cites}

\end{document}

dist takes two inputs and produces one output

The conventional presentation of wiring diagrams is for unpointed spaces. We
adapt it for pointed spaces. First we show how to represent each possible
pointed space as a collection of ``wires'' and then we show how each
combinator ``shuffles'' or ``transforms'' the wires:
\begin{itemize}
\item It is not possible to produce a pointed space
  \pointed{\AgdaInductiveConstructor{ZERO}}{\AgdaBound{v}} for any
  \AgdaBound{v}.
\item The pointed space
  \pointed{\AgdaInductiveConstructor{ONE}}{\AgdaInductiveConstructor{tt}} is
  invisible in the graphical notation.
\item The pointed space \pointed{\AgdaInductiveConstructor{TIMES}
  \AgdaBound{t₁} \AgdaBound{t₂}}{\AgdaBound{(v₁ , v₂)}} is
  represented using two parallel wires labeled \AgdaBound{v₁} and
  \AgdaBound{v₂}:
\[
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
        *{}\wire{r}{\AgdaBound{v₁}}&\\
        *{}\wire{r}{\AgdaBound{v₂}}&
        }}
\]
 Note that if one of the types is \AgdaInductiveConstructor{ONE}, the
 corresponding wire disappears. If both the wires are
 \AgdaInductiveConstructor{ONE}, they both disappear.
\item The pointed space \pointed{\AgdaInductiveConstructor{PLUS}
  \AgdaBound{t₁} \AgdaBound{t₂}}{\AgdaInductiveConstructor{inj₁}
  \AgdaBound{v₁}} is represented by a wire labeled with
  \AgdaInductiveConstructor{inj₁} \AgdaBound{v₁}. The pointed space
  \pointed{\AgdaInductiveConstructor{PLUS} \AgdaBound{t₁}
    \AgdaBound{t₂}}{\AgdaInductiveConstructor{inj₂} \AgdaBound{v₂}} is
  similarly represented by a wire labeled with
  \AgdaInductiveConstructor{inj₂} \AgdaBound{v₂}. 
\[
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
        *{}\wire{r}{\AgdaInductiveConstructor{inj₁}~\AgdaBound{v₁}}&
        }}
\qquad
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
        *{}\wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v₂}}&
        }}
\]
\item Knowing how points are represented, we now show how various combinators
  act on the wires. The combinator \AgdaInductiveConstructor{id⟷} is
  invisible. The combinator \AgdaInductiveConstructor{◎} connects the
  outgoing wires of one diagram to the input wires of the other. The
  associativity of \AgdaInductiveConstructor{◎} is implicit in the graphical
  notation. 
\item The combinators \AgdaInductiveConstructor{unite₊} and
  \AgdaInductiveConstructor{uniti₊} are represented as follows:
\[
\vcenter{
\wirechart{}{\wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaInductiveConstructor{unite₊}}
  \wire{r}{\AgdaBound{v}}&}
}
\qquad
\vcenter{
\wirechart{}{\wire{r}{\AgdaBound{v}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaInductiveConstructor{uniti₊}}
  \wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v}}&}
}
\]
\item All other combinators that just re-label a value are similarly
  represented as one box with one incoming wire labeled by the input value
  and one outgoing wires labeled by the resulting value.
\item The combinators that operate on \AgdaInductiveConstructor{TIMES} types
  are a bit more involved as shown below. First, although the unit value
  \AgdaInductiveConstructor{tt} is invisible in the graphical notation, the
  combinators \AgdaInductiveConstructor{unite⋆} and
  \AgdaInductiveConstructor{uniti⋆} are still represented as boxes as shown
  below: 
\[
\vcenter{
\wirechart{}{\wire{r}{\AgdaBound{v}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaInductiveConstructor{unite⋆}}
  \wire{r}{\AgdaBound{v}}&}
}
\qquad
\vcenter{
\wirechart{}{\wire{r}{\AgdaBound{v}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaInductiveConstructor{uniti⋆}}
  \wire{r}{\AgdaBound{v}}&}
}
\]

  The combinator \AgdaInductiveConstructor{swap⋆} is represented by
  crisscrossing wires:
  \[
  \vcenter{\wirechart{@C=1.2cm@R=0.5cm}{
  *{}\wire{r}{\AgdaBound{v₁}}&\blank\wirecross{d}\wire{r}{\AgdaBound{v₂}}&\\
  *{}\wire{r}{\AgdaBound{v₂}}&\blank\wirecross{u}\wire{r}{\AgdaBound{v₁}}&
  }}
  \]
  As discussed below, it is possible to consider a 3d variation which makes
  explicit which of the wires is on top and which is on bottom. The
  combinators \AgdaInductiveConstructor{assocl⋆} and
  \AgdaInductiveConstructor{assocr⋆} are invisible in the graphical notation
  as associativity of parallel wires is implicit. In other words, three
  parallel wires could be seen as representing \AgdaBound{((v₁ , v₂) , v₃)}
  or \AgdaBound{(v₁ , (v₂ , v₃))}.

\item The composite combinator \AgdaBound{c₁} \AgdaSymbol{⊗} \AgdaBound{c₂}
  is the parallel composition shown below:
  \[ 
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
 \vsblank\wire{r}{\AgdaBound{v₁}}&\blank\nnbox{[]}
    {\AgdaBound{c₁}}\wire{r}{\AgdaBound{v₃}}&\\
 \vsblank\wire{r}{\AgdaBound{v₂}}&\blank\nnbox{[]}
    {\AgdaBound{c₂}}\wire{r}{\AgdaBound{v₄}}&
 }}
  \]
\item The combinators \AgdaBound{c₁} \AgdaSymbol{⊕1} \AgdaBound{c₂} and 
\AgdaBound{c₁} \AgdaSymbol{⊕2} \AgdaBound{c₂} are represented as follows:
  \[ 
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
 \blank\wire{r}{\AgdaInductiveConstructor{inj₁}~\AgdaBound{v₁}}
 \vsblank&\wwblank{15mm}\nnbox{[]}
   {\AgdaBound{v₁}\quad\AgdaBound{c₁}\quad\AgdaBound{v₃}}
   \wire{r}{\AgdaInductiveConstructor{inj₁}~\AgdaBound{v₃}}&\\
 \vsblank&\wwblank{15mm}\nnbox{[]}{\AgdaBound{c₂}}&
 }}
\]
\[
 \vcenter{\wirechart{@C=1.5cm@R=0.4cm}{
 \vsblank&\wwblank{15mm}\nnbox{[]}{\AgdaBound{c₁}}&\\
 \blank\wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v₂}}
 \vsblank&\wwblank{15mm}\nnbox{[]}
   {\AgdaBound{v₂}\quad\AgdaBound{c₁}\quad\AgdaBound{v₄}}
   \wire{r}{\AgdaInductiveConstructor{inj₂}~\AgdaBound{v₄}}&
 }}
  \]
\item Finally, when a box \AgdaBound{c} is sequentially composed with its
  mirror image \AgdaSymbol{!} \AgdaBound{c} (in either order), both boxes
  disappear.
\end{itemize}

Let us draw the five paths \AgdaFunction{p₁} to \AgdaFunction{p₅} introduced
in the previous section. Since \AgdaInductiveConstructor{id⟷} is invisible, 
the three paths \AgdaFunction{p₁}, \AgdaFunction{p₂}, and 
\AgdaFunction{p₄}, are all represented as follows:
\[
\vcenter{
\wirechart{}{\wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•T}}
  \wire{r}{\AgdaFunction{FALSE}}&}
}
\]
Path \AgdaFunction{p₃} would be represented as:
\[
\vcenter{
\wirechart{}{\wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•T}}
  \wire{r}{\AgdaFunction{FALSE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•F}}
  \wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•T}}
  \wire{r}{\AgdaFunction{FALSE}}&
}}
\]
but then we notice that any two of the adjacent boxes are mirror images and
erase them to produce the same wiring diagram as the previous three paths.
For \AgdaFunction{p₅}, we have the following representation:
\[
\vcenter{\wirechart{@C=1cm@R=1cm}{
  \wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{8mm}\nnbox{[]}{~\AgdaInductiveConstructor{uniti⋆}}
  \wire{r}{\AgdaFunction{TRUE}}&
  \wwblank{12mm}\nnbox{[]}{~\AgdaFunction{NOT•T}}
  \wire{r}{\AgdaFunction{FALSE}}&
  \wwblank{8mm}\nnbox{[]}{~\AgdaInductiveConstructor{unite⋆}}
  \wire{r}{\AgdaFunction{FALSE}}&\\
  &&\wwblank{12mm}\nnbox{[]}{\AgdaInductiveConstructor{id⟷}}&
}}
\]
where the occurrences of \AgdaInductiveConstructor{swap⋆} have disappeared
since one of the wires is invisible. The occurrences of
\AgdaInductiveConstructor{id⟷} that acts on the invisible wire does
\emph{not}, however, disappear.

The diagrammatic notation is justified by the following \emph{coherence
theorems}.

\begin{theorem}[Joyal and Street~\citeyearpar{geometrytensor}]
A well-formed equation between morphisms in the language of symmetric
monoidal categories follows from the axioms of symmetric monoidal categories
if and only if it holds, up to isomorphisms of diagrams, in the graphical
language. 
\end{theorem}

Two diagrams are considered isomorphic, if their wires and boxes are in
bijective correspondence that preserves the connections between boxes and
wires. 

path from \AgdaFunction{TRUE} to itself and then uses the boolean
negation. The first step is clearly superfluous and hence we expect, via the
groupoid laws, to have a 2-path connecting \AgdaFunction{p₂} to
\AgdaFunction{p₁}. Path \AgdaFunction{p₃} does not syntactically refer to a
trivial path but instead uses what is effectively a trivial path that follows
a negation path and then its inverse. We also expect to have a 2-path between
this path and the other ones. 

The situation with path \AgdaFunction{p₅} is more subtle. Viewed
extensionally, path \AgdaFunction{p₅} is obviously equivalent to the other
paths as it has the same input-output behavior connecting \AgdaFunction{TRUE}
to \AgdaFunction{FALSE}. In the conventional approach to programming language
semantics, this extensional equivalence would then be used to justify the
existence of a 2-path. In our setting, we do \emph{not} want to reason using
extensional methods. Instead, we would like to think of 2-paths are resulting
from homotopies (i.e., ``smooth deformations'') of paths into each other.


\[
  \vcenter{\wirechart{@R+0.1cm}{
      \blank\wire{rr}{B}&&\blank\\
      \nnbox{[u].[d]}{f} & \blank\nnbox{[]}{h} & \nnbox{[u].[d]}{g} \\
      \blank\wire{rr}{A}&&\blank\\
      }}
  \sep\neq\sep
  \vcenter{\wirechart{@R+0.1cm}{
      \blank\wire{rr}{B}&&\blank\\
      \blank\nnbox{[u].[]}{f}\wire{rr}{A}&&\blank\nnbox{[u].[]}{g},\\
      & \blank\nnbox{[]}{h} & \\
      }}
\]

\begin{verbatim}
f : A TIMES B -> A TIMES B
f = id

h : ONE -> ONE
h = id

g : A TIMES B -> A TIMES B 
g = id

left diagram = f ; ((uniti* ; (h x id_A) ; unite*) x id_B) ; g 
right diagram = f ; ((uniti* ; swap* ; (id_A x h) ; swap* ; unite*) x id_B) ; g

\end{verbatim}


\begin{tikzpicture}
\node[left] (T) at (-0.2,0) {\AgdaFunction{TRUE}};
\node (F) at (1.2,-0.75) {};
\node at (1,-1.1) {\AgdaFunction{FALSE}};
\draw (T) -- (0.25,0) -- (0.75,-0.75) -- (F);
%%
\node[left] (T1) at (3.3,0) {\AgdaFunction{TRUE}};
\node at (4.5,-0.75) {};
\node at (4.3,-1.1) {\AgdaFunction{FALSE}};
\node at (5.5,0.2) {\AgdaFunction{TRUE}};
\node (F2) at (6.7,-0.75) {};
\node at (6.5,-1.1) {\AgdaFunction{FALSE}};
\draw (T1) -- (3.75,0) -- (4.25,-0.75) -- (4.75,-0.75) 
   -- (5.25,0) -- (5.75,0) -- (6.25,-0.75) -- (F2);
\end{tikzpicture}


\begin{verbatim}
check axioms:

category:
id o f = f and f o id = f => same diagram
assoc seq comp => same diagram

monoidal:
tensors assoc = same diagram
0 + A = A  and A + 0 = A => same diagram
1 * A = A and A * 1 = A => different diagrams ??? ==> units must be invisible!
triangle and pentagon => same diagram

symmetric: swap o swap isomorphic to id

bimonoidal: distrib/factor: produces same diagrams when in pointed spaces
coherence conditions: A(B+C) -> AB+AC -> AC+AB
                               A(C+B) 

dagger: !(!c) is identical to c
all c o ! c and ! c o c are isom to id

so any two paths that produce the same diagram should have a 2-path between
them

need one example of two paths connecting the same values that do not produce
the same diagram; does the example on p.11 of selinger's paper work?

it's not too bad to add 2-path between any two paths that produce the same
diagram but what about the coherence conditions; do we have to add
paths for them or are these at the next level?


\end{verbatim}

