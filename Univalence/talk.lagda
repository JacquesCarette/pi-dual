\documentclass[11pt]{beamer}
\usetheme{Boadilla}

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
\title[Reversible Circuits]{Representing, Manipulating and Optimizing \ \\ Reversible Circuits}
\author[Carette-Sabry]{Jacques Carette \and Amr Sabry}
\institute[McMaster-IU]{McMaster University \and Indiana University}
\date{June 8-11, 2015}
\begin{document}
\maketitle

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module talk where

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
\begin{frame}{Reversible Computing}

The “obvious” intersection between quantum computing and programming
languages is reversible computing.

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Representing Reversible Circuits}

truth table, matrix, reed muller expansion, product of cycles,
decision diagram, etc.

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{A Syntactic Theory}

Ideally want a notation that is easy to write by programmers and that
is easy to mechnically manipulate for reasoning and optimizing of circuits.

Syntactic calculi good

Theseus?

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{A Calculus of Permutations} 

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{?}


\end{frame}
