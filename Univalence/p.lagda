\documentclass{article}

\usepackage{fullpage}
\usepackage{agda}
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand{\AgdaCodeStyle}{\small}

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

\title{Permutations etc.}
\author{Jacques Carette \and Amr Sabry}
\maketitle

\begin{abstract}
...
\end{abstract}

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module p where

open import Data.Nat     using (_+_) 
open import Data.Fin     using (Fin; inject+; raise) 
open import Data.Sum     using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec     using (tabulate) renaming (_++_ to _++V_)
open import Function     using (_∘_; id)

-- Properties from standard library

open import Data.Vec.Properties using    (lookup∘tabulate)
open import Relation.Binary     using    (module Setoid)
open import Function.Equality   using    (_⇨_; _⟨$⟩_; _⟶_)
                                renaming (_∘_ to _⊚_; id to id⊚)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
     
-- Next are imports from our libraries of Proofs (FiniteFunctions and
-- VectorLemmas)

open import Proofs using (finext; _!!_; tabulate-split) 

-- Next we import our notions of equivalences

open import Equiv using (_∼_; module qinv; mkqinv; _≃_)

-- Next we import sets equipped with equivalence relations and
-- specialize to our notions of equivalence

open import SetoidUtils using (≡-Setoid; →to⟶)
open import EquivSetoid
  using (_≃S_; module _≃S_; equiv; 0≃S; id≃S; _⊎≃S_; 
         _≋_; module _≋_; equivS;
         _≃S≡_; ≃S-Setoid)

-- Finally we import our definition of permutations. We start with Vec
-- (Fin m) n for arbitrary m and n which---if well-formed---would
-- define a permutation in the Cauchy representation. These vectors
-- assume a canonical enumeration of the finite sets which we make
-- explicit in the module Enumeration. To ensure these vectors are
-- well-formed, we define a concrete permutation as a pair of two such
-- vectors with two proofs that they compose to the identity
-- permutation.

open import FinVec using (module F) 
open F using (~⇒≡; !!⇒∘̂; _∘̂_; 1C!!i≡i; cauchyext)

open import Enumeration         using (Enum; 0E; _⊕e_; eval-left; eval-right) 
open import ConcretePermutation using (CPerm; cp; p≡; 0p; idp; _⊎p_; SCPerm) 

-- Syntax

open import PiLevel0

open import Level using (zero)
open import Relation.Binary using (Setoid; module Setoid)
Π-Rewriting : U → U → Setoid zero zero
Π-Rewriting t₁ t₂ = {!!} 
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction} 
 
Main points:

\begin{itemize}

\item We want a language for writing and reasoning about equivalences
\`a la HoTT. That would be a reversible language that comes with its
own executable optimizer. 

\item Doing this for a $\lambda$-calculus based language requires
finding an appropriate semantics for equivalences that gives a
computational interpretation to univalence; this is still subject of
research; our approach is to start with finite types and leave
higher-order functions for now. More about this later (talk then about
negative and fractional types as a possibility for extending the work
to accommodate some form of higher-order functions). More motivation
about our approach: starting with all functions makes it very
difficult to identify equivalences (must use function extensionality);
instead we build equivalences inductively. This is relatively easy for
finite types but will get much more interesting when we go to negative
and fractional types.

\item Equivalences between finite types can be expressed in many ways;
it is conjectured (Baez) that the canonical way is permutations on
finite sets.  However, it is important to note that we are not
talking about just the set (or setoid) of permutations, but with
the rig of permutations, with disjoint union as $+$ and tensor
product as $*$.

\item Even though operations (such as tensor product, and
even reversal) of permutations are operationally quite complex,
we can show that they originate (entirely) from simpler
operations on natural numbers and on types.

\item More abstractly these equivalences can be expressed using
\emph{symmetric rig categories}. The beauty of going to the categorial
setting is that the principles for reasoning about permutations are
essentially the coherence conditions for the categories. We quote:
\begin{quote}
What Mac Lane does can be described in logical terms in the
following manner. On the one hand, he has an axiomatization, and,
on the other hand, he has a model category where arrows are
permutations; then he shows that his axiomatization is complete
with respect to this model. It is no wonder that his coherence
problem reduces to the completeness problem for the usual
axiomatization of symmetric groups. (p.3 of
\url{http://www.mi.sanu.ac.rs/~kosta/coh.pdf})
\end{quote}

\item Putting the observations above together, we can develop a
programming language with the following characteristics:

  \begin{itemize}

  \item The set of types consists of the conventional finite types:
  empty, unit, sums, and products

  \item The set of terms consists of a rich enough set of combinators
  that can denote every equivalence between the types

  \item More interestingly, we have a higher-level of combinators that
  manipulate the first level of combinators to provide a sound and
  complete calculus for computing and reasoning about equivalences of
  equivalences.

  \item The language has a simple, intuitive, and almost conventional
  operational semantics

  \item Denotationally, the language can be interpreted in any
  \emph{symmetric rig category}. One possibility is the canonical
  category of finite sets and permutations; another would be the Agda
  universe \AgdaPrimitiveType{Set}.

  \end{itemize}

\item In the setting describe above, we can \emph{prove} a theorem
that intuitively corresponds to the statement of \emph{univalence} in
our setting. The theorem states that the set of equivalences between
equivalences is equivalent to identities of permutations.

\item Pi0: we have an operational semantics that maps each combinator to a
function; this is intuitive but bad for reasoning as it would require
reasoning about extensional equivalence of functions; it is also bad because
we completely lose the fact that we are starting with a reversible language;
we have an alternative semantics that maps each combinator to a
permutation. Semantically permutations (with a rich algebra) can be modeled
using a \emph{typed} semiring; we have several instances of these categories
that show that a few simple properties of natural numbers lift to properties
of Fin then vectors then permutations.

\item Pi1: we have a nice semantics which maps each combinator to a
permutation but we don’t have a way yet to reason about which permutations
are equivalent to each other? We would like to answer this question without
going to extensional equality of functions. It turns out that this question
has essentially been answered by category theorists and is encoded in the
coherence conditions for monoidal categories (precisely symmetric rig
categories). These conditions classify what is going on. We can turn these
coherence conditions into a typed operational semantics for program
transformations

\item Pi2: we can start seeing which program transformations are
equivalent. This requires a generalization of rig categories.

\item Possible application: reversible circuits + optimizations

\item Now how do you fit Thm 2 into that story and is it possible to do it in
a way that makes the structure of Pi0 and Pi1 part of the same general
pattern? At level 0, thm 2 says that, given a choice of enumeration,
permutations are \emph{initial} and \emph{complete}.

\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Finite Types}

Our first step is to recall a few properties of \emph{finite types}.
Syntactically, these types are constructed by the following grammar:
\[\begin{array}{lrcl}
(\textit{Types}) & 
  \tau &::=& 0 \alt 1 \alt \tau_1 + \tau_2 \alt \tau_1 * \tau_2 
\end{array}\]
The set of types $\tau$ includes the empty type 0, the unit type 1,
and conventional sum and product types. 

Semantically, each such type denotes a \emph{finite set}. The only
equivalence on the elements of these sets is the \emph{identity}
relation which we write as $=$. In other words if $x, y : A$ and
$x = y$ then it must be the case that $x$ and $y$ are identical. For
two finite sets $A$ and $B$, two maps $f, g : A \rightarrow B$ are
\emph{extensionally equivalent}, $f \sim g$, if for all $x : A$ we
have that $f(x) = g(x)$.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Equivalences between Finite Types}

In the general context of HoTT, there are several \emph{equivalent}
definitions of \emph{equivalences} between types. The most natural
definition for our purposes is the notion of ``bi-invertible maps.'' A
map $f : A \rightarrow B$ is \emph{bi-invertible} if it has both a
left inverse and a right inverse, i.e., if there exist maps
$g, h : B \rightarrow A$ such that $g \circ f \sim \textrm{id}_A$ and
$f \circ h \sim \textrm{id}_B$. A semantic equivalence between sets
$A$ and $B$ is completely specified by a bi-invertible map
$f : A \rightarrow B$. Our aim is to define a syntactic,
\emph{inductive}, characterization of this equivalence.

Intuitively, we expect two finite sets to be equivalent if there is a
\emph{permutation} between them and hence our aim is essentially to
produce a syntactic characterization of permutations on finite types
that is sound and complete with respect to the semantic equivalence on
finite sets above. We will immediately present a syntactic definition
of permutations on finite types and then proceed to prove that it
exactly corresponds to semantic equivalence.

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{$\Pi$-Combinators}
\label{pi}

\begin{figure*}[t]
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
\begin{minipage}{0.35\textwidth}
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

In previous work, we defined a reversible language $\Pi$ whose only
computations are witnesses to isomorphisms $\tau_1 \iso \tau_2$
between finite types~\cite{James:2012:IE:2103656.2103667}.
Syntactically, these computations consist of base combinators (on the
left side of Fig.~\ref{pi-combinators}) and compositions (on the right
side of the same figure). Each line of the figure on the left
introduces a pair of dual constants\footnote{where $\swapp$ and
  $\swapt$ are self-dual.}  that witness the type isomorphism in the
middle. This set of isomorphisms is known to be
complete~\cite{Fiore:2004,fiore-remarks} and the language is universal
for hardware combinational
circuits~\cite{James:2012:IE:2103656.2103667}.\footnote{If recursive
  types and a trace operator are added, the language becomes Turing
  complete~\cite{James:2012:IE:2103656.2103667,rc2011}. We will not be
  concerned with this extension in the main body of this paper but it
  will be briefly discussed in the conclusion.}

The technical goal now is to prove that every $\Pi$-combinator
corresponds to a semantic equivalence and vice-versa that every
semantic equivalence can be expressed as a
$\Pi$-combinator. Furthermore, going back and forth between these two
spaces produces ``equal'' objects, e.g., mapping a $\Pi$-combinator to
an equivalence and back produces an ``equal'' $\Pi$-combinator. To
express the main theorem, we therefore need to specify what it means
for two $\Pi$-combinators to be the ``same'' and similary what it
means for two equivalences to be the ``same''. The formal statement we
prove (to be dissected and explained in detail in the remainder of the
section) is:

\medskip
\begin{code}
thm : ∀ {τ₁ τ₂ : U} → (≃S-Setoid ⟦ τ₁ ⟧ ⟦ τ₂ ⟧) ≃S (Π-Rewriting τ₁ τ₂)
\end{code}
\AgdaHide{
\begin{code}
thm = {!!} 
\end{code}
}

For the main theorem we are given two types $A$ and $B$ and an
\emph{enumeration} \AgdaPrimitiveType{Enum} that establishes an
equivalence between each type and \AgdaPrimitiveType{Fin}~$n$. These
equivalences establish three things: (i) that each type is indeed a
finite type, (ii) that the two types have the same number of elements,
and (ii) fix an ordering on the elements of each type.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{acm}
\bibliography{cites}
\end{document}
