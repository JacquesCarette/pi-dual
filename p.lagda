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

\DeclareUnicodeCharacter{9678}{9678}
\DeclareUnicodeCharacter{10231}{10231}
\DeclareUnicodeCharacter{10214}{10214}
\DeclareUnicodeCharacter{10215}{10215}

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
open import Data.Product
open import Data.Nat hiding (_⊔_)
open import Function 

open import Groupoid

infixr 10 _◎_
infixr 30 _⟷_
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

HoTT says id types are an inductively defined type family with refl as
constructor. We say it is a family defined with pi combinators as
constructors. Replace path induction with refl as base case with our
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

Informally, and as a first approximation, one may think of HoTT as
mathematics, type theory, or computation but with all equalities replaced by
isomorphisms, i.e., with equalities given computational content. We explain
some of the basic ideas below.

One starts with Martin-L\"of type theory, interprets the types as topological
spaces or weak $\infty$-groupoids, and interprets identities between elements
of a type as \emph{paths}.  In more detail, one interprets the witnesses of
the identity $x \equiv y$ as paths from $x$ to $y$. If $x$ and $y$ are
themselves paths, then witnesses of the identity $x \equiv y$ become paths
between paths, or homotopies in the topological language. In Agda notation,
we can formally express this as follows:

\medskip
\begin{code}
data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

i0 : 3 ≡ 3
i0 = refl 3

i1 : (1 + 2) ≡ (3 * 1)
i1 = refl 3

i2 : ℕ ≡ ℕ
i2 = refl ℕ
\end{code}
\medskip

\noindent It is important to note that the notion of propositional
equality~$\equiv$ relates any two terms that are \emph{definitionally equal}
as shown in example \AgdaFunction{i1} above. In general, there may be
\emph{many} proofs (i.e., paths) showing that two particular values are
identical and that proofs are not necessarily identical. This gives rise to a
structure of great combinatorial complexity. To be explicit, we will use
$\equiv_U$ to refer to the space in which the path lives.

We are used to thinking of types as sets of values. So we typically view the
type \AgdaPrimitiveType{Bool} as the figure on the left but in HoTT we should
instead think about it as the figure on the right:
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
much more complicated path structure. 

We cannot generate non-trivial groupoids starting from the usual type
constructions. We need \emph{higher-order inductive types} for that purpose.
The classical example is the \emph{circle} that is a space consisting of a
point \AgdaFunction{base} and a path \AgdaFunction{loop} from
\AgdaFunction{base} to itself. As stated, this does not amount to
much. However, because paths carry additional structure (explained below),
that space has the following non-trivial structure:

\begin{center}
\begin{tikzpicture}[scale=0.78]
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
  \node[left,blue] at (-2.4,0) {$\ldots$ !~loop $\circ$ !~loop};
\end{tikzpicture}
\end{center}

The additional structure of types is formalized as follows. Let $x$, $y$, and
$z$ be elements of some $U$:
\begin{itemize}
\item For every path $p : x \equiv_U y$, there exists a path $! p : y
  \equiv_U x$;
\item For every $p : x \equiv_U y$ and $q : y \equiv_U z$, there exists a
  path $p \circ q : x \equiv_U z$;
\item Subject to the following conditions:
 \[\begin{array}{rcl}
  p \circ \mathit{refl}~y &\equiv_{{x \equiv_U y}} & p \\
  p &\equiv_{{x \equiv_U y}} & \mathit{refl}~x \circ p \\
  !p \circ p &\equiv_{{y \equiv_U y}} & \mathit{refl}~y \\
  p ~\circ~ !p &\equiv_{{x \equiv_U x}} & \mathit{refl}~x \\
  !~(!p) &\equiv_{{x \equiv_U y}} & p \\
  p \circ (q \circ r) &\equiv_{{x \equiv_U z}} & (p \circ q) \circ r
 \end{array}\]
\item With similar conditions one level up and so on and so forth.
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Computing with Type Isomorphisms}
\label{pi}

The main syntactic vehicle for the developments in this paper is a simple
language called $\Pi$ whose only computations are isomorphisms between finite
types. 

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
\subsection{Syntax and Examples}

The set of types $\tau$ includes the empty type 0, the unit type 1, and
conventional sum and product types. The values classified by these types are
the conventional ones: \lstinline|()| of type 1, $\inl{v}$ and $\inr{v}$ for
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

%%%%%%%%%%%%%%%%%%
\subsection{Semantics}
\label{opsempi}

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
permutations. Another common example of such categories is the category of
finite dimensional vector spaces and linear maps over any field. Note that in
this interpretation, the $\Pi$-type~0 maps to the 0-dimensional vector space
which is \emph{not} empty. Its unique element, the zero vector --- which is
present in every vector space --- acts like a ``bottom'' everywhere-undefined
element and hence the type behaves like the unit of addition and the
annihilator of multiplication as desired.

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Space of Types}

Instead of modeling the semantics of $\Pi$ using \emph{permutations}, which
are set-theoretic functions after all, we use \emph{paths} from the HoTT
framework. More precisely, we model the universe of $\Pi$ types as a space
whose points are the individual $\Pi$-types and we will consider that there
is path between two points $\tau_1$ and $\tau_2$ if there is a $\Pi$
combinator $c : \tau_1 \iso \tau_2$. If we focus on 1-paths, this is perfect
as we explain next.

\paragraph*{Note.} 
But first, we note that this is a significant deviation from the HoTT
framework which fundamentally includes functions, which are specialized to
equivalences, which are then postulated to be paths by the univalence
axiom. This axiom has no satisfactory computational interpretation,
however. Instead we completely bypass the idea of extensional functions and
use paths directly. Another way to understanding what is going on is the
following. In the conventional HoTT framework:
\begin{itemize}
\item We start with two different notions: paths and functions;
\item We use extensional non-constructive methods to identify a
particular class of functions that form isomorphisms;
\item We postulate that this particular class of functions can be
identified with paths.
\end{itemize}
In our case, 
\begin{itemize}
\item We start with a constructive characterization of \emph{reversible
  functions} or \emph{isomorphisms} built using inductively defined
  combinators; 
\item We blur the distinction between such combinators and paths from the
  beginning. We view computation as nothing more than \emph{following paths}!
  As explained earlier, although this appears limiting, it is universal and
  regular computation can be viewed as a special case of that.
\end{itemize}

\paragraph*{Construction.} 
We have a universe $U$ viewed as a groupoid whose points are the types
$\Pi$-types $\tau$. The $\Pi$-combinators of Table~\ref{pi-combinators} are
viewed as syntax for the paths in the space $U$. We need to show that the
groupoid path structure is faithfully represented. The combinator $\idc$
introduces all the $\refl{\tau} : \tau \equiv \tau$ paths in $U$. The adjoint
$\symc{c}$ introduces an inverse path $!p$ for each path $p$ introduced by
$c$. The composition operator $\fatsemi$ introduce a path $p \circ q$ for
every pair of paths whose endpoints match. In addition, we get paths like
$\swapp$ between $\tau_1+\tau_2$ and $\tau_2+\tau_1$. The existence of such
paths in the conventional HoTT developed is \emph{postulated} by the
univalence axiom. The $\otimes$-composition gives a path $(p,q) :
(\tau_1*\tau_2) \equiv (\tau_3*\tau_4)$ whenever we have paths $p : \tau_1
\equiv \tau_3$ and $q : \tau_2 \equiv \tau_4$. A similar situation for the
$\oplus$-composition. The structure of these paths must be discovered and
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

To make the correspondence between $\Pi$ and the HoTT concepts more apparent
we will, in the remainder of the paper, use \textsf{refl} instead of $\idc$
and $!$ instead of $\mathit{sym}$ when referring to $\Pi$ combinators when
viewed as paths.  Similarly we will use $\rightarrow$ instead of the
$\Pi$-notation $\iso$ or the HoTT notation $\equiv$ to refer to paths.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Agda Model} 

\begin{code} 
------------------------------------------------------------------------------
-- Level 0: 
-- Types at this level are just plain sets with no interesting path structure. 
-- The path structure is defined at levels 1 and beyond. 

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

⟦_⟧ : U → Set
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

-- Programs
-- We use pointed types; programs map a pointed type to another
-- In other words, each program takes one particular value to another; if we
-- want to work on another value, we generally use another program

record U• : Set where
  constructor •[_,_]
  field
    ∣_∣ : U
    • : ⟦ ∣_∣ ⟧

open U•

Space : (t• : U•) → Set
Space •[ t , v ] = ⟦ t ⟧

point : (t• : U•) → Space t• 
point •[ t , v ] = v

-- examples of plain types, values, and pointed types

ONE• : U•
ONE• = •[ ONE , tt ]

BOOL : U
BOOL = PLUS ONE ONE

BOOL² : U
BOOL² = TIMES BOOL BOOL

TRUE : ⟦ BOOL ⟧
TRUE = inj₁ tt

FALSE : ⟦ BOOL ⟧
FALSE = inj₂ tt

BOOL•F : U•
BOOL•F = •[ BOOL , FALSE ]

BOOL•T : U•
BOOL•T = •[ BOOL , TRUE ]

-- The actual programs are the commutative semiring isomorphisms between
-- pointed types.

data _⟷_ : U• → U• → Set where
  unite₊  : ∀ {t v} → •[ PLUS ZERO t , inj₂ v ] ⟷ •[ t , v ]
  uniti₊  : ∀ {t v} → •[ t , v ] ⟷ •[ PLUS ZERO t , inj₂ v ]
  swap1₊  : ∀ {t₁ t₂ v₁} → •[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₂ t₁ , inj₂ v₁ ]
  swap2₊  : ∀ {t₁ t₂ v₂} → •[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₂ t₁ , inj₁ v₂ ]
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
  unite⋆  : ∀ {t v} → •[ TIMES ONE t , (tt , v) ] ⟷ •[ t , v ]
  uniti⋆  : ∀ {t v} → •[ t , v ] ⟷ •[ TIMES ONE t , (tt , v) ] 
  swap⋆   : ∀ {t₁ t₂ v₁ v₂} → 
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
  dist1   : ∀ {t₁ t₂ t₃ v₁ v₃} → 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ⟷ 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ]
  dist2   : ∀ {t₁ t₂ t₃ v₂ v₃} → 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ⟷ 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ]
  factor1   : ∀ {t₁ t₂ t₃ v₁ v₃} → 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ⟷ 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ]
  factor2   : ∀ {t₁ t₂ t₃ v₂ v₃} → 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ⟷ 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ]
  id⟷    : ∀ {t v} → •[ t , v ] ⟷ •[ t , v ]
  sym⟷   : ∀ {t₁ t₂ v₁ v₂} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
           (•[ t₂ , v₂ ] ⟷ •[ t₁ , v₁ ])
  _◎_    : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
           (•[ t₂ , v₂ ] ⟷ •[ t₃ , v₃ ]) → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ])
  _⊕1_   : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₃ t₄ , inj₁ v₃ ])
  _⊕2_   : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₃ t₄ , inj₂ v₄ ])
  _⊗_     : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
          (•[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₃ t₄ , (v₃ , v₄) ])

-- example programs

NOT•T : •[ BOOL , TRUE ] ⟷ •[ BOOL , FALSE ]
NOT•T = swap1₊

NOT•F : •[ BOOL , FALSE ] ⟷ •[ BOOL , TRUE ]
NOT•F = swap2₊

CNOT•Fx : {b : ⟦ BOOL ⟧} → 
          •[ BOOL² , (FALSE , b) ] ⟷ •[ BOOL² , (FALSE , b) ]
CNOT•Fx = dist2 ◎ ((id⟷ ⊗ NOT•F) ⊕2 id⟷) ◎ factor2

CNOT•TF : •[ BOOL² , (TRUE , FALSE) ] ⟷ •[ BOOL² , (TRUE , TRUE) ]
CNOT•TF = dist1 ◎ 
          ((id⟷ ⊗ NOT•F) ⊕1 (id⟷ {TIMES ONE BOOL} {(tt , TRUE)})) ◎
          factor1

CNOT•TT : •[ BOOL² , (TRUE , TRUE) ] ⟷ •[ BOOL² , (TRUE , FALSE) ]
CNOT•TT = dist1 ◎ 
          ((id⟷ ⊗ NOT•T) ⊕1 (id⟷ {TIMES ONE BOOL} {(tt , TRUE)})) ◎ 
          factor1

-- The evaluation of a program is not done in order to figure out the output
-- value. Both the input and output values are encoded in the type of the
-- program; what the evaluation does is follow the path to constructively
-- reach the ouput value from the input value. Even though programs of the
-- same pointed types are, by definition, observationally equivalent, they
-- may follow different paths. At this point, we simply declare that all such
-- programs are "the same." At the next level, we will weaken this "path
-- irrelevant" equivalence and reason about which paths can be equated to
-- other paths via 2paths etc.

-- Even though individual types are sets, the universe of types is a
-- groupoid. The objects of this groupoid are the pointed types; the
-- morphisms are the programs; and the equivalence of programs is the
-- degenerate observational equivalence that equates every two programs that
-- are extensionally equivalent.

_obs≅_ : {t₁ t₂ : U•} → (c₁ c₂ : t₁ ⟷ t₂) → Set
c₁ obs≅ c₂ = ⊤ 

UG : 1Groupoid
UG = record
       { set = U•
       ; _↝_ = _⟷_
       ; _≈_ = _obs≅_
       ; id = id⟷
       ; _∘_ = λ y⟷z x⟷y → x⟷y ◎ y⟷z 
       ; _⁻¹ = sym⟷
       ; lneutr = λ _ → tt 
       ; rneutr = λ _ → tt 
       ; assoc = λ _ _ _ → tt
       ; equiv = record { refl = tt 
                        ; sym = λ _ → tt 
                        ; trans = λ _ _ → tt 
                        } 
       ; linv = λ _ → tt 
       ; rinv = λ _ → tt 
       ; ∘-resp-≈ = λ _ _ → tt
       }

------------------------------------------------------------------------------
-- Simplifiy various compositions

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

simplifyl◎ : {t₁ t₂ t₃ : U•} → (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Homotopy Type Theory}

Informally, and as a first approximation, one may think of \emph{homotopy
  type theory} (HoTT) as mathematics, type theory, or computation but with
all equalities replaced by isomorphisms, i.e., with equalities given
computational content. A bit more formally, one starts with Martin-L\"of type
theory, interprets the types as topological spaces or weak
$\infty$-groupoids, and interprets identities between elements of a type as
\emph{paths}.  In more detail, one interprets the witnesses of the identity
$x \equiv y$ as paths from $x$ to $y$. If $x$ and $y$ are themselves paths,
then witnesses of the identity $x \equiv y$ become paths between paths, or
homotopies in the topological language. 

Formally, Martin-L\"of type theory, is based on the principle that every
proposition, i.e., every statement that is susceptible to proof, can be
viewed as a type. The correspondence is validated by the following
properties: if a proposition $P$ is true, the corresponding type is
inhabited, i.e., it is possible to provide evidence for $P$ using one of the
elements of the type $P$. If, however, the proposition $P$ is false, the
corresponding type is empty, i.e., it is impossible to provide evidence for
$P$. The type theory is rich enough to allow propositions denoting
conjunction, disjunction, implication, and existential and universal
quantifications.

It is clear that the question of whether two elements of a type are equal is
a proposition, and hence that this proposition must correspond to a type.  It
is important to note that the notion of proposition equality $\equiv$ relates
any two terms that are \emph{definitionally equal} as shown in example $i1$
above. In general, there may be \emph{many} proofs (i.e., paths) showing that
two particular values are identical and that proofs are not necessarily
identical. This gives rise to a structure of great combinatorial complexity.

We are used to think of types as sets of values. So we think of the type
\texttt{Bool} as:

\begin{center}
\begin{tikzpicture}
  \draw (0,0) ellipse (2cm and 1cm);
  \draw[fill] (-1,0) circle (0.025);
  \node[below] at (-1,0) {false};
  \draw[fill] (1,0) circle (0.025);
  \node[below] at (1,0) {true};
\end{tikzpicture}
\end{center}

In HoTT, we should instead think about it as:

\begin{center}
\begin{tikzpicture}
  \draw (0,0) ellipse (2cm and 1cm);
  \draw[fill] (-1,0) circle (0.025);
  \draw[->,thick,cyan] (-1,0) arc (0:320:0.2);
  \node[above right] at (-1,0) {false};
  \draw[fill] (1,-0.2) circle (0.025);
  \draw[->,thick,cyan] (1,-0.2) arc (0:320:0.2);
  \node[above right] at (1,-0.2) {true};
\end{tikzpicture}
\end{center}

In this particular case, it makes no difference, but in general we might have
something like which shows that types are to be viewed as topological spaces
or groupoids:

\begin{center}
\begin{tikzpicture}
  \draw (0,0) ellipse (5cm and 2.5cm);
  \draw[fill] (-4,0) circle (0.025);
  \draw[->,thick,cyan] (-4,0) arc (0:320:0.2);
  \draw[fill] (0,0) circle (0.025);
  \draw[->,thick,cyan] (0,0) arc (-180:140:0.2);
  \draw[fill] (4,0) circle (0.025);
  \draw[->,double,thick,blue] (-2.3,0.8) to [out=225, in=135] (-2.3,-0.8);
  \draw[->,double,thick,blue] (-1.7,0.8) to [out=-45, in=45] (-1.7,-0.8);
  \draw[->,thick,red] (-2.4,0.1) -- (-1.6,0.1);
  \draw[->,thick,red] (-2.4,0) -- (-1.6,0);
  \draw[->,thick,red] (-2.4,-0.1) -- (-1.6,-0.1);
  \draw[->,thick,cyan] (-4,0) to [out=60, in=120] (0,0);
  \draw[->,thick,cyan] (0,0) to [out=-120, in=-60] (-4,0);
  \draw[->,thick,cyan] (4,0) arc (0:320:0.2);
  \draw[->,thick,cyan] (4,0) arc (0:330:0.7);
  \draw[->,thick,cyan] (4,0) arc (0:350:1.2);
  \draw[->,double,thick,blue] (1.8,0) -- (2.4,0);
\end{tikzpicture}
\end{center}

The additional structure of types is formalized as follows:
\begin{itemize}
\item For every path $p : x \equiv y$, there exists a path $! p : y
\equiv x$;
\item For every $p : x \equiv y$ and $q : y \equiv z$, there
exists a path $p \circ q : x \equiv z$;
\item Subject to the following conditions:
 \[\begin{array}{rcl}
  p \circ \mathit{refl}~y &\equiv& p \\
  p &\equiv& \mathit{refl}~x \circ p \\
  !p \circ p &\equiv& \mathit{refl}~y \\
  p ~\circ~ !p &\equiv& \mathit{refl}~x \\
  !~(!p) &\equiv& p \\
  p \circ (q \circ r) &\equiv& (p \circ q) \circ r
 \end{array}\]
\item With similar conditions one level up and so on and so forth.
\end{itemize}

We cannot generate non-trivial groupoids starting from the usual type
constructions. We need \emph{higher-order inductive types} for that purpose.
Example:

\begin{code}
-- data Circle : Set where
--   base : Circle
--   loop : base ≡ base

module Circle where
  private data S¹* : Set where base* : S¹*

  S¹ : Set
  S¹ = S¹*

  base : S¹
  base = base*

  postulate loop : base ≡ base
\end{code}

Here is the non-trivial structure of this example:

\begin{center}
\begin{tikzpicture}
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
  \node[left,blue] at (-2.4,0) {$\ldots$ !~loop $\circ$ !~loop};
\end{tikzpicture}
\end{center}

\begin{itemize}
\item A function from space $A$ to space $B$ must map the points of $A$
to the points of $B$ as usual but it must also \emph{respect the path
structure};
\item Logically, this corresponds to saying that every function
respects equality;
\item Topologically, this corresponds to saying that every function is
continuous.
\end{itemize}

\begin{center}
\begin{tikzpicture}
  \draw (-3,0) ellipse (1.5cm and 3cm);
  \draw (3,0) ellipse (1.5cm and 3cm);
  \draw[fill] (-3,1.5) circle (0.025);
  \draw[fill] (-3,-1.5) circle (0.025);
  \node[above] at (-3,1.5) {$x$};
  \node[below] at (-3,-1.5) {$y$};
  \draw[fill] (3,1.5) circle (0.025);
  \draw[fill] (3,-1.5) circle (0.025);
  \node[above] at (3,1.5) {$f(x)$};
  \node[below] at (3,-1.5) {$f(y)$};
  \draw[->,cyan,thick] (-3,1.5) -- (-3,-1.5);
  \node[left,cyan] at (-3,0) {$p$};
  \draw[->,cyan,thick] (3,1.5) -- (3,-1.5);
  \node[right,cyan] at (3,0) {$\mathit{ap}~f~p$};
  \draw[->,red,dashed,ultra thick] (-2,2.5) to [out=45, in=135] (2,2.5);
  \node[red,below] at (0,3) {$f$};
\end{tikzpicture}
\end{center}

\begin{itemize}
\item $\mathit{ap}~f~p$ is the action of $f$ on a path $p$;
\item This satisfies the following properties:
  \[\begin{array}{rcl}
  \mathit{ap}~f~(p \circ q) &\equiv&
                (\mathit{ap}~f~p) \circ (\mathit{ap}~f~q) \\
  \mathit{ap}~f~(!~p) &\equiv& ~!~(\mathit{ap}~f~p)  \\
  \mathit{ap}~g~(\mathit{ap}~f~p) &\equiv&
                \mathit{ap}~(g \circ f)~p  \\
  \mathit{ap}~\mathit{id}~p &\equiv& p
  \end{array}\]
\end{itemize}

Type families as fibrations. 
\begin{itemize}
\item A more complicated version of the previous idea for dependent
functions;
\item The problem is that for dependent functions, $f(x)$ and $f(y)$ may
not be in the same type, i.e., they live in different spaces;
\item Idea is to \emph{transport} $f(x)$ to the space of $f(y)$;
\item Because everything is ``continuous'', the path $p$ induces a
transport function that does the right thing: the action of $f$ on $p$
becomes a path between $\mathit{transport}~(f(x))$ and $f(y)$.
\end{itemize} 

\begin{center}
\begin{tikzpicture}
  \draw (-3,0) ellipse (1.5cm and 3cm);
  \draw (3,2) ellipse (0.5cm and 1cm);
  \draw (3,-1.4) ellipse (2cm and 2cm);
  \node[blue,ultra thick,above] at (3,3) {$P(x)$};
  \node[blue,ultra thick,below] at (3,-3.5) {$P(y)$};
  \draw[fill] (-3,1.5) circle (0.025);
  \draw[fill] (-3,-1.5) circle (0.025);
  \node[above] at (-3,1.5) {$x$};
  \node[below] at (-3,-1.5) {$y$};
  \draw[fill] (3,1.5) circle (0.025);
  \draw[fill] (3,-0.5) circle (0.025);
  \draw[fill] (3,-2.5) circle (0.025);
  \node[above] at (3,1.5) {$f(x)$};
  \node[above] at (3,-0.5) {$\mathit{transport}~P~p~f(x)$};
  \node[below] at (3,-2.5) {$f(y)$};
  \draw[left,cyan,thick] (-3,1.5) -- (-3,-1.5);
  \node[left,cyan] at (-3,0) {$p$};
  \draw[->,cyan,thick] (3,-0.5) -- (3,-2.5);
  \node[right,cyan] at (3,-1.5) {$\mathit{apd}~f~p$};
  \draw[->,red,dashed,ultra thick] (-2,2.5) to [out=45, in=135] (2.3,2.5);
  \node[red,below] at (0,3) {$f$ (fiber over $x$)};
  \draw[->,red,dashed,ultra thick] (-2,-2.5) to [out=-45, in=-135] (1.2,-2.5);
  \node[red,above] at (-0.5,-2.5) {$f$ (fiber over $y$)};
  \draw[->,red,dashed,ultra thick] (3.6,2.3) to [out=-45, in=45] (3.5,0.6);
  \node[red,right] at (3.9,1.45) {$\mathit{transport}~P~p$};
\end{tikzpicture}
\end{center}

\begin{itemize}
\item Let $x, y, z : A$, $p : x \equiv y$, $q : y \equiv z$, 
$f : A \rightarrow B$, $g : \Pi_{a \in A} P(a) \rightarrow P'(a)$, 
$P : A \rightarrow \mathit{Set}$, 
$P' : A \rightarrow \mathit{Set}$, $Q : B \rightarrow \mathit{Set}$, 
$u : P(x)$, and $w : Q(f(x))$.
\item The function $\mathit{transport}~P~p$ satisfies 
the following properties:
  \[\begin{array}{rcl}
  \mathit{transport}~P~q~(\mathit{transport}~P~p~u) &\equiv&
               \mathit{transport}~P~(p \circ q)~u \\
  \mathit{transport}~(Q \circ f)~p~w &\equiv&
               \mathit{transport}~Q~(\mathit{ap}~f~p)~w  \\
  \mathit{transport}~P'~p~(g~x~u) &\equiv&
               g~y~(\mathit{transport}~P~p~u)
  \end{array}\]
\end{itemize}

\begin{itemize}
\item Let $x,y : A$, $p : x \equiv y$, $P : A \rightarrow
\mathit{Set}$, and $f : \Pi_{a \in A} P(a)$;
\item We know we have a path in $P(y)$ between
$\mathit{transport}~P~p~(f(x))$ and $f(y)$.  
\item We do not generally know how the point 
$\mathit{transport}~P~p~(f(x)) : P(y)$ relates to $x$;
\item We do not generally know how the paths in $P(y)$ are
related to the paths in $A$.
\item First ``crack'' in the theory.
\end{itemize}

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

Function Extensionality:

\begin{code}
-- f ∼ g iff ∀ x. f x ≡ g x
_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

-- f is an equivalence if we have g and h such that
-- the compositions with f in both ways are ∼ id
record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    h : B → A
    β : (h ∘ f) ∼ id
\end{code}

\begin{code}
-- a path between f and g implies f ∼ g
happly : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (a : A) → B a} → 
         (f ≡ g) → (f ∼ g)
happly {ℓ} {ℓ'} {A} {B} {f} {g} p = {!!}

postulate -- that f ∼ g implies a path between f and g
  funextP :  {A : Set} {B : A → Set} {f g : (a : A) → B a} → 
             isequiv {A = f ≡ g} {B = f ∼ g} happly

funext :  {A : Set} {B : A → Set} {f g : (a : A) → B a} → 
          (f ∼ g) → (f ≡ g)
funext = isequiv.g funextP
\end{code}

A path between $f$ and $g$ is a collection of paths from $f(x)$ to $g(x)$.
We are no longer executable!

Univalence:

\begin{code}
-- Two spaces are equivalent if we have functions 
-- f, g, and h that compose to id
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

-- A path between spaces implies their equivalence
idtoeqv : {A B : Set} → (A ≡ B) → (A ≃ B)
idtoeqv {A} {B} p = {!!}

postulate -- that equivalence of spaces implies a path 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)
\end{code}

Again, we are no longer executable!

Analysis:
\begin{itemize}
\item We start with two different notions: paths and functions;
\item We use extensional non-constructive methods to identify a
particular class of functions that form isomorphisms;
\item We postulate that this particular class of functions can be
identified with paths.
\end{itemize}

Insight:
\begin{itemize}
\item Start with a constructive characterization of \emph{reversible
functions} or \emph{isomorphisms};
\item Blur the distinction between such reversible functions and paths
from the beginning.
\end{itemize}

Note that:
\begin{itemize}
\item Reversible functions are computationally universal
(Bennett's reversible Turing Machine from 1973!)
\item \emph{First-order} reversible functions can be inductively defined
in type theory (James and Sabry, POPL 2012).
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Examples} 

Let's start with a few simple types built from the empty type, the unit type,
sums, and products, and let's study the paths postulated by HoTT.

For every value in a type (point in a space) we have a trivial path from the
value to itself:

%% \begin{code}
%% data U : Set where
%%   ZERO  : U
%%   ONE   : U
%%   PLUS  : U → U → U
%%   TIMES : U → U → U

%% -- Points 

%% ⟦_⟧ : U → Set
%% ⟦ ZERO ⟧       = ⊥
%% ⟦ ONE ⟧        = ⊤
%% ⟦ PLUS t t' ⟧  = ⟦ t ⟧ ⊎ ⟦ t' ⟧
%% ⟦ TIMES t t' ⟧ = ⟦ t ⟧ × ⟦ t' ⟧

%% BOOL : U
%% BOOL = PLUS ONE ONE

%% BOOL² : U
%% BOOL² = TIMES BOOL BOOL

%% TRUE : ⟦ BOOL ⟧
%% TRUE = inj₁ tt

%% FALSE : ⟦ BOOL ⟧
%% FALSE = inj₂ tt

%% NOT : ⟦ BOOL ⟧ → ⟦ BOOL ⟧
%% NOT (inj₁ tt) = FALSE
%% NOT (inj₂ tt) = TRUE

%% CNOT : ⟦ BOOL ⟧ → ⟦ BOOL ⟧ → ⟦ BOOL ⟧ × ⟦ BOOL ⟧
%% CNOT (inj₁ tt) b = (TRUE , NOT b)
%% CNOT (inj₂ tt) b = (FALSE , b)

%% p₁ : FALSE ≡ FALSE
%% p₁ = refl FALSE

%% \end{code}

%% p₂ : _≡_ {A = ⟦ BOOL² ⟧} (FALSE , TRUE) (FALSE , (NOT FALSE))
%% p₂ = refl (FALSE , TRUE) 
%% p₃ : ⟦ BOOL ⟧ ≡ ⟦ BOOL ⟧
%% p₃ = refl ⟦ BOOL ⟧

In addition to all these trivial paths, there are structured paths. In
particular, paths in product spaces can be viewed as pair of paths. So in
addition to the path above, we also have:

%% \begin{code}
%% p₂' : (FALSE ≡ FALSE) × (TRUE ≡ TRUE) 
%% p₂' = (refl FALSE , refl TRUE) 

%% --α : p₂ ≡ p₂' not quite but something like that
%% --α = ? by some theorem in book

%% -- then talk about paths between bool and bool based on id / not;not
%% -- etc.
%% \end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Theory} 

\begin{figure*}
\Rule{}{}{() : 1}{} 
\qquad
\Rule{}{v_1 : t_1}{\inl{v_1} : t_1 + t_2}{} 
\qquad
\Rule{}{v_2 : t_2}{\inr{v_2} : t_1 + t_2}{} 
\qquad
\Rule{}{v_1 : t_1 \quad v_2 : t_2}{(v_1,v_2) : t_1 * t_2}{} 
\qquad
\Rule{}{}{\idv{\identlp}{\inr{v}}{v} : \idt{\identlp}{\inr{v}}{v}}{}
\qquad
\Rule{}{}{\idv{\identrp}{v}{\inr{v}} : \idt{\identrp}{v}{\inr{v}}}{}
\qquad
\Rule{}{}{\idv{\swapp}{\inl{v}}{\inr{v}} : \idt{\swapp}{\inl{v}}{\inr{v}}}{}
\qquad
\Rule{}{}{\idv{\swapp}{\inr{v}}{\inl{v}} : \idt{\swapp}{\inr{v}}{\inl{v}}}{}
\qquad
\Rule{}{}{\idv{\assoclp}{\inl{v}}{\inl{(\inl{v})}} : 
  \idt{\assoclp}{\inl{v}}{\inl{(\inl{v})}}}{}
\qquad
\Rule{}{}{\idv{\assoclp}{\inr{(\inl{v})}}{\inl{(\inr{v})}} : 
  \idt{\assoclp}{\inr{(\inl{v})}}{\inl{(\inr{v})}}}{}
\qquad
\Rule{}{}{\idv{\assoclp}{\inr{(\inr{v})}}{\inr{v}} : 
  \idt{\assoclp}{\inr{(\inr{v})}}{\inr{v}}}{}
\qquad
\Rule{}{}{\idv{\assocrp}{\inl{(\inl{v})}}{\inl{v}} : 
  \idt{\assocrp}{\inl{(\inl{v})}}{\inl{v}}}{}
\qquad
\Rule{}{}{\idv{\assocrp}{\inl{(\inr{v})}}{\inr{(\inl{v})}} : 
  \idt{\assocrp}{\inl{(\inr{v})}}{\inr{(\inl{v})}}}{}
\qquad
\Rule{}{}{\idv{\assocrp}{\inr{v}}{\inr{(\inr{v})}} : 
  \idt{\assocrp}{\inr{v}}{\inr{(\inr{v})}}}{}
\qquad
\Rule{}{}{\idv{\identlt}{((),v)}{v} : 
  \idt{\identlt}{((),v)}{v}}{}
\qquad
\Rule{}{}{\idv{\identrt}{v}{((),v)} : 
  \idt{\identrt}{v}{((),v)}}{}
\qquad
\Rule{}{}{(\idv{\swapt}{(v_1,v_2)}{(v_2,v_1)} :
  \idt{\swapt}{(v_1,v_2)}{(v_2,v_1)}}{}
\qquad
\Rule{}{}{\idv{\assoclt}{(v_1,(v_2,v_3))}{((v_1,v_2),v_3)} : 
  \idt{\assoclt}{(v_1,(v_2,v_3))}{((v_1,v_2),v_3)}}{}
\qquad
\Rule{}{}{\idv{\assocrt}{((v_1,v_2),v_3)}{(v_1,(v_2,v_3))} : 
  \idt{\assocrt}{((v_1,v_2),v_3)}{(v_1,(v_2,v_3))}}{}
\qquad
\Rule{}{}{\idv{\dist}{(\inl{v_1},v_2)}{\inl{(v_1,v_2)}} : 
  \idt{\dist}{(\inl{v_1},v_2)}{\inl{(v_1,v_2)}}}{}
\qquad
\Rule{}{}{\idv{\dist}{(\inr{v_1},v_2)}{\inr{(v_1,v_2)}} : 
  \idt{\dist}{(\inr{v_1},v_2)}{\inr{(v_1,v_2)}}}{}
\qquad
\Rule{}{}{\idv{\factor}{\inl{(v_1,v_2)}}{(\inl{v_1},v_2)} : 
  \idt{\factor}{\inl{(v_1,v_2)}}{(\inl{v_1},v_2)}}{}
\qquad
\Rule{}{}{\idv{\factor}{\inr{(v_1,v_2)}}{(\inr{v_1},v_2)} : 
  \idt{\factor}{\inr{(v_1,v_2)}}{(\inr{v_1},v_2)}}{}
\qquad
\Rule{}{}{\idv{\idc}{v}{v} : 
  \idt{\idc}{v}{v}}{}
\qquad
\Rule{}{p : \idrt{c}{v_1}{v_2}}{!p : \idt{\symc{c}}{v_1}{v_2}}{}
\qquad
\Rule{}{p : \idt{c_1}{v_1}{v_2} \quad q : \idt{c_2}{v_2}{v_3}}
  {\cp{p}{v_2}{q} : \idt{c_1\fatsemi c_2}{v_1}{v_3}}{}
\qquad
\Rule{}{p : \idt{c_1}{v}{v'}}
  {\inl{p} : \idt{c_1 \oplus c_2}{\inl{v}}{\inl{v'}}}{}
\qquad
\Rule{}{p : \idt{c_2}{v}{v'}}
  {\inr{p} : \idt{c_1 \oplus c_2}{\inr{v}}{\inr{v'}}}{}
\qquad
\Rule{}{p : \idt{c_1}{v_1}{v_1'} \quad q : \idt{c_2}{v_2}{v_2'}}
  {(p,q) : \idt{c_1 \otimes c_2}{(v_1,v_2)}{(v_1',v_2')}}{}
\qquad
\Rule{}{p : \idt{c}{v}{v'}}
  {\idv{\lid}{\cp{(\idv{\idc}{v}{v})}{v}{p}}{p} : 
  \idt{\lid}{\cp{(\idv{\idc}{v}{v})}{v}{p}}{p}}{}
\qquad
\Rule{}{p : \idt{c}{v'}{v}}
  {\idv{\rid}{\cp{p}{v}{(\idv{\idc}{v}{v})}}{p} : 
  \idt{\rid}{\cp{p}{v}{(\idv{\idc}{v}{v})}}{p}}{}
\qquad
\Rule{}{}{\idv{!1}{!(\idv{\identlp}{\inr{v}}{v})}{\idv{\identrp}{v}{\inr{v}}}}{}
\qquad
\Rule{}{p : \idt{c}{v'}{v}}
  {\idv{\linv}{(\cp{!p}{v'}{p})}{(\idv{\idc}{v}{v})} : 
  \idt{\linv}{(\cp{!p}{v'}{p})}{(\idv{\idc}{v}{v})}}{}
\qquad
\Rule{}{}{? : \idt{\rinv}{?}{?}}{}
\qquad
\Rule{}{}{? : \idt{\invinv}{?}{?}}{}
\qquad
\Rule{}{}{? : \idt{\assoc}{?}{?}}{}
\end{figure*}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Pi}

\subsection{Base isomorphisms}
\[\begin{array}{rrcll}
\identlp :&  0 + b & \iso & b &: \identrp \\
\swapp :&  b_1 + b_2 & \iso & b_2 + b_1 &: \swapp \\
\assoclp :&  b_1 + (b_2 + b_3) & \iso & (b_1 + b_2) + b_3 &: \assocrp \\
\identlt :&  1 * b & \iso & b &: \identrt \\
\swapt :&  b_1 * b_2 & \iso & b_2 * b_1 &: \swapt \\
\assoclt :&  b_1 * (b_2 * b_3) & \iso & (b_1 * b_2) * b_3 &: \assocrt \\
\distz :&~ 0 * b & \iso & 0 &: \factorz \\
\dist :&~ (b_1 + b_2) * b_3 & \iso & (b_1 * b_3) + (b_2 * b_3)~ &: \factor
\end{array}\]

\begin{center} 
\Rule{}
{}
{\jdg{}{}{\idc : b \iso b}}
{}
\quad 
\Rule{}
{\jdg{}{}{c : b_1 \iso b_2}}
{\jdg{}{}{\symc{c} : b_2 \iso b_1}}
{}
\\ \bigskip
\Rule{}
{\jdg{}{}{c_1 : b_1 \iso b_2} \quad c_2 : b_2 \iso b_3}
{\jdg{}{}{c_1 \fatsemi c_2 : b_1 \iso b_3}}
{}
\\ \bigskip
\Rule{}
{\jdg{}{}{c_1 : b_1 \iso b_2} \quad c_2 : b_3 \iso b_4}
{\jdg{}{}{c_1 \oplus c_2 : b_1 + b_3 \iso b_2 + b_4}}
{}
\quad 
\Rule{}
{\jdg{}{}{c_1 : b_1 \iso b_2} \quad c_2 : b_3 \iso b_4}
{\jdg{}{}{c_1 \otimes c_2 : b_1 * b_3 \iso b_2 * b_4}}
{}
\end{center}

These isomorphisms:
\begin{itemize}
\item Form an inductive type
\item Identify each isomorphism with a collection of paths
\item For example:
\[\begin{array}{rrcl}
\swapp :&  b_1 + b_2 & \iso & b_2 + b_1 
\end{array}\]
becomes:
\[\begin{array}{rrcll}
\swapp^1 :&  \mathit{inj}_1 v & \equiv & \mathit{inj}_2 v \\
\swapp^2 :&  \mathit{inj}_2 v & \equiv & \mathit{inj}_1 v 
\end{array}\]
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\bibliographystyle{abbrvnat}
\softraggedright
\bibliography{cites}

\end{document}
