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
\section{Equivalences between Finite Types}

We begin our investigation of \emph{equivalences} in the context of
finite types constructed from the empty type, the unit type, and sums
and products. In the general context of HoTT, a possible specification
of equivalences is via ``bi-invertible maps.'' A map
$f : A \rightarrow B$ is \emph{bi-invertible} if it has both a left
inverse and a right inverse, i.e., if there exist maps
$g, h : B \rightarrow A$ such that $g \circ f \sim \textrm{id}_A$ and
$f \circ h \sim \textrm{id}_B$ where for two maps
$f, g : A \rightarrow B$, we define $f \sim g$ if for all $x : A$ if
$f(x) = g(x)$. The equality $=$ in the last equation refers to
\emph{identity}.  In the context of finite types, all these
definitions reduce to having a \emph{permutation} between the two
finite types.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}
