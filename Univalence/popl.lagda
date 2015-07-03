\documentclass[authoryear,preprint]{sigplanconf}

\usepackage{agda}
\usepackage{alltt}
\usepackage{fancyvrb}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{tikz}
\usetikzlibrary{cd}
\usetikzlibrary{quotes}
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
\newcommand{\alt}{~|~}
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
\newcommand{\factorzl}{\mathit{factorl}_0}
\newcommand{\factorzr}{\mathit{factorr}_0}
\newcommand{\absorbl}{\mathit{absorbl}_0}
\newcommand{\absorbr}{\mathit{absorbr}_0}
\newcommand{\dist}{\mathit{dist}}
\newcommand{\factor}{\mathit{factor}}
\newcommand{\distl}{\mathit{distl}}
\newcommand{\factorl}{\mathit{factorl}}
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
\newcommand{\nodet}[2]{\fcolorbox{black}{white}{$#1$}\fcolorbox{black}{gray!20}{$#2$}}
\newcommand{\cubt}{\mathbb{T}}
\newcommand{\ztone}{\mathbb{0}}
\newcommand{\otone}{\mathbb{1}}
\newcommand{\ptone}[2]{#1 \boxplus #2}
\newcommand{\ttone}[2]{#1 \boxtimes #2}
\newcommand{\eqdef}{\stackrel{\triangle}{=}}
\newcommand{\isoone}{\Leftrightarrow}
\newcommand{\lolli}{\multimap} 
\newcommand{\isoarrow}{\stackrel{\sim}{\rightarrow}}


%% \DefineVerbatimEnvironment
%%   {code}{Verbatim}
%%  {} % Add fancy options here if you like.

\DeclareUnicodeCharacter{9678}{\ensuremath{\odot}}
\DeclareUnicodeCharacter{9636}{\ensuremath{\Box}}
%% shorten the longarrow
\DeclareUnicodeCharacter{10231}{\ensuremath{\leftrightarrow}}

\newtheorem{theorem}{Theorem}
\newtheorem{conj}{Conjecture}
\newtheorem{definition}{Definition}

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

\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.4\textwidth}\color{red}{Amr says: {#1}}\end{minipage}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

\title{ A Sound and Complete Calculus for Reversible Circuit Equivalence}
\authorinfo{Jacques Carette}
  {McMaster University}
  {carette@mcmaster.ca}
\authorinfo{Amr Sabry}
  {Indiana University}
  {sabry@indiana.edu}

\maketitle

\begin{abstract}

Many recent advances in quantum computing, low-power design,
nanotechnology, optical information processing, and bioinformatics are
based on \emph{reversible circuits}. With the aim of designing a
semantically well-founded approach for modeling and reasoning about
reversible circuits, we propose viewing such circuits as proof terms
witnessing equivalences between finite types. Proving that these type
equivalences satisfy the commutative semiring axioms, we proceed with
the categorification of type equivalences as \emph{symmetric rig
groupoids}. The coherence conditions of these categories then
produces, for free, a sound and complete calculus for reasoning about
reversible circuit equivalence. The paper consists of the
``unformalization'' of an Agda package formalizing the connections
between reversible circuits, equivalences between finite types,
permutations between finite sets, and symmetric rig groupoids.

\end{abstract}

\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Fin hiding (_+_)

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

size : U → ℕ
size ZERO          = 0
size ONE           = 1
size (PLUS t₁ t₂)  = size t₁ + size t₂
size (TIMES t₁ t₂) = size t₁ * size t₂

infix  30 _⟷_
infixr 50 _◎_

data _⟷_ : U → U → Set where
  unite₊  : {t : U} → PLUS ZERO t ⟷ t
  uniti₊  : {t : U} → t ⟷ PLUS ZERO t
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆  : {t : U} → t ⟷ TIMES ONE t
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr  : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) 
  factor  : {t₁ t₂ t₃ : U} → PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U}    → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

open import ConcretePermutation hiding (_⊎p_)

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊    = uniti₊
! uniti₊    = unite₊
! swap₊     = swap₊
! assocl₊   = assocr₊
! assocr₊   = assocl₊
! unite⋆    = uniti⋆
! uniti⋆    = unite⋆
! swap⋆     = swap⋆
! assocl⋆   = assocr⋆
! assocr⋆   = assocl⋆
! absorbl     = factorzr
! absorbr     = factorzl
! factorzl  = absorbr
! factorzr = absorbl
! dist      = factor 
! factor    = dist
! id⟷      = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁ 
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)

⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

infix  30 _⇔_

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
          (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
          ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  assocl⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⇔ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⇔ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocl⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆) ⇔ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃))
  assocl⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)) ⇔ ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆)
  assocr⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⇔ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
           (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃))) ⇔ (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assocr⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⇔ (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃)))
  assocr⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  assoc⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (c₁ ⊗ (c₂ ⊗ c₃)) ⇔ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assoc⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⇔ (c₁ ⊗ (c₂ ⊗ c₃))
  dist⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          ((c₁ ⊕ c₂) ⊗ c₃) ⇔ (dist ◎ ((c₁ ⊗ c₃) ⊕ (c₂ ⊗ c₃)) ◎ factor)
  factor⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (dist ◎ ((c₁ ⊗ c₃) ⊕ (c₂ ⊗ c₃)) ◎ factor) ⇔ ((c₁ ⊕ c₂) ⊗ c₃)
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ id⟷ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ id⟷) 
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c) 
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c) 
  unitel₊⇔ : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (unite₊ ◎ c₂) ⇔ ((c₁ ⊕ c₂) ◎ unite₊)
  uniter₊⇔ : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          ((c₁ ⊕ c₂) ◎ unite₊) ⇔ (unite₊ ◎ c₂)
  unitil₊⇔ : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (uniti₊ ◎ (c₁ ⊕ c₂)) ⇔ (c₂ ◎ uniti₊)
  unitir₊⇔ : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti₊) ⇔ (uniti₊ ◎ (c₁ ⊕ c₂))
  unitial₊⇔ : {t₁ t₂ : U} → (uniti₊ {PLUS t₁ t₂} ◎ assocl₊) ⇔ (uniti₊ ⊕ id⟷)
  unitiar₊⇔ : {t₁ t₂ : U} → (uniti₊ {t₁} ⊕ id⟷ {t₂}) ⇔ (uniti₊ ◎ assocl₊)
  swapl₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          (swap₊ ◎ (c₁ ⊕ c₂)) ⇔ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          ((c₂ ⊕ c₁) ◎ swap₊) ⇔ (swap₊ ◎ (c₁ ⊕ c₂))
  unitel⋆⇔ : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (unite⋆ ◎ c₂) ⇔ ((c₁ ⊗ c₂) ◎ unite⋆)
  uniter⋆⇔ : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          ((c₁ ⊗ c₂) ◎ unite⋆) ⇔ (unite⋆ ◎ c₂)
  unitil⋆⇔ : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (uniti⋆ ◎ (c₁ ⊗ c₂)) ⇔ (c₂ ◎ uniti⋆)
  unitir⋆⇔ : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti⋆) ⇔ (uniti⋆ ◎ (c₁ ⊗ c₂))
  unitial⋆⇔ : {t₁ t₂ : U} → (uniti⋆ {TIMES t₁ t₂} ◎ assocl⋆) ⇔ (uniti⋆ ⊗ id⟷)
  unitiar⋆⇔ : {t₁ t₂ : U} → (uniti⋆ {t₁} ⊗ id⟷ {t₂}) ⇔ (uniti⋆ ◎ assocl⋆)
  swapl⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          (swap⋆ ◎ (c₁ ⊗ c₂)) ⇔ ((c₂ ⊗ c₁) ◎ swap⋆)
  swapr⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          ((c₂ ⊗ c₁) ◎ swap⋆) ⇔ (swap⋆ ◎ (c₁ ⊗ c₂))
  swapfl⋆⇔ : {t₁ t₂ t₃ : U} → 
          (swap₊ {TIMES t₂ t₃} {TIMES t₁ t₃} ◎ factor) ⇔ 
          (factor ◎ (swap₊ {t₂} {t₁} ⊗ id⟷))
  swapfr⋆⇔ : {t₁ t₂ t₃ : U} → 
          (factor ◎ (swap₊ {t₂} {t₁} ⊗ id⟷)) ⇔ 
         (swap₊ {TIMES t₂ t₃} {TIMES t₁ t₃} ◎ factor)
  id⇔     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ c
  trans⇔  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : {t₁ t₂ t₃ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  -- below are the combinators added for the RigCategory structure
  id⟷⊕id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⇔ id⟷
  split⊕-id⟷ : {t₁ t₂ : U} → (id⟷ {PLUS t₁ t₂}) ⇔ (id⟷ ⊕ id⟷)
  hom⊕◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  id⟷⊗id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊗ id⟷ {t₂}) ⇔ id⟷
  split⊗-id⟷ : {t₁ t₂ : U} → (id⟷ {TIMES t₁ t₂}) ⇔ (id⟷ ⊗ id⟷)
  hom⊗◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)) ⇔ ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄))
  hom◎⊗⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)) ⇔ ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄))
  triangle⊕l : {t₁ t₂ : U} →
    ((swap₊ ◎ unite₊ {t₁}) ⊕ id⟷ {t₂}) ⇔ assocr₊ ◎ (id⟷ ⊕ unite₊)
  triangle⊕r : {t₁ t₂ : U} →
    (assocr₊ ◎ (id⟷ {t₁} ⊕ unite₊ {t₂})) ⇔ ((swap₊ ◎ unite₊) ⊕ id⟷)
  triangle⊗l : {t₁ t₂ : U} →
    ((swap⋆ ◎ unite⋆ {t₁}) ⊗ id⟷ {t₂}) ⇔ assocr⋆ ◎ (id⟷ ⊗ unite⋆)
  triangle⊗r : {t₁ t₂ : U} →
    (assocr⋆ ◎ (id⟷ {t₁} ⊗ unite⋆ {t₂})) ⇔ ((swap⋆ ◎ unite⋆) ⊗ id⟷)
  pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
    assocr₊ ◎ (assocr₊ {t₁} {t₂} {PLUS t₃ t₄}) ⇔ ((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊)
  pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr₊ {t₁} {t₂} {t₃} ⊕ id⟷ {t₄}) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊) ⇔ assocr₊ ◎ assocr₊
  pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
    assocr⋆ ◎ (assocr⋆ {t₁} {t₂} {TIMES t₃ t₄}) ⇔ ((assocr⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆)
  pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr⋆ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆) ⇔ assocr⋆ ◎ assocr⋆
  hexagonr⊕l : {t₁ t₂ t₃ : U} →
     (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃} ⇔ ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)
  hexagonr⊕r : {t₁ t₂ t₃ : U} →
     ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊) ⇔ (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃}
  hexagonl⊕l : {t₁ t₂ t₃ : U} →
     (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃} ⇔ ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷)
  hexagonl⊕r : {t₁ t₂ t₃ : U} →
     ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷) ⇔ (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃}
  hexagonr⊗l : {t₁ t₂ t₃ : U} →
     (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃} ⇔ ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆)
  hexagonr⊗r : {t₁ t₂ t₃ : U} →
     ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆) ⇔ (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃}
  hexagonl⊗l : {t₁ t₂ t₃ : U} →
     (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃} ⇔ ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷)
  hexagonl⊗r : {t₁ t₂ t₃ : U} →
     ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷) ⇔ (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃}
  absorbl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl ⇔ absorbl ◎ id⟷ {ZERO}
  absorbl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
     absorbl ◎ id⟷ {ZERO} ⇔ (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl
  absorbr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (id⟷ {ZERO} ⊗ c₁) ◎ absorbr ⇔ absorbr ◎ id⟷ {ZERO}
  absorbr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
     absorbr ◎ id⟷ {ZERO} ⇔ (id⟷ {ZERO} ⊗ c₁) ◎ absorbr
  factorzl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    id⟷ ◎ factorzl ⇔ factorzl ◎ (id⟷ ⊗ c₁)
  factorzl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
     factorzl ◎ (id⟷ {ZERO} ⊗ c₁) ⇔ id⟷ {ZERO} ◎ factorzl
  factorzr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
     id⟷ ◎ factorzr ⇔ factorzr ◎ (c₁ ⊗ id⟷)
  factorzr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
     factorzr ◎ (c₁ ⊗ id⟷) ⇔ id⟷ ◎ factorzr

-- better syntax for writing 2paths

infix  2  _▤       
infixr 2  _⇔⟨_⟩_   

_⇔⟨_⟩_ : {t₁ t₂ : U} (c₁ : t₁ ⟷ t₂) {c₂ : t₁ ⟷ t₂} {c₃ : t₁ ⟷ t₂} → 
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
_ ⇔⟨ α ⟩ β = trans⇔ α β

_▤ : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → (c ⇔ c)
_▤ c = id⇔

open import Equiv using (_≃_; _●_; path⊎; path×)
import TypeEquiv as TE

infixr 2  _⟷⟨_⟩_   
infix  2  _□       

_⟷⟨_⟩_ : (t₁ : U) {t₂ : U} {t₃ : U} → 
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃) 
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U) → {t : U} → (t ⟷ t)
_□ t = id⟷

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction} 

Reversible circuits are NOT a restriction; they are a generalization;
conventional irreversible circuits are a special case.

reversible circuits for supercomputers of the
future~\cite{DeBenedictis:2005:RLS:1062261.1062325}

\begin{itemize}
\item BACKGROUND: realizing HoTT requires we be able to program with type
  equivalences and equivalences of type equivalences and so on;
  univalence is a postulate; caveat Coquand et al.
\item RESULT: limit ourselves to finite types: what emerges is an interesting
  universal language for combinational reversible circuits that comes
  with a calculus for writing circuits and a calculus for manipulating
  that calculus; in other words; rules for writing circuits and rules
  for rewriting (optimizing) circuits
\end{itemize}

Define and motivate that we are interested in defining HoTT  
  equivalences of types, characterizing them, computing with them,
  etc.
  
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

Quantum Computing. Quantum physics differs from classical physics in \textcolor{red}{many} ways:

\begin{itemize}
\item Superpositions
\item Entanglement
\item Unitary evolution
\item Composition uses tensor products
\item Non-unitary measurement
\end{itemize}

Quantum Computing \& Programming Languages. 
\begin{itemize}
\item It is possible to adapt \textcolor{red}{all at once} classical programming
languages to quantum programming languages.
\item Some excellent examples discussed in this workshop
\item This assumes that classical programming languages (and implicitly classical physics)
can be smoothly adapted to the quantum world.
\item There are however what appear to be fundamental differences between the classical and quantum world that make them incompatible
\item Let us \emph{re-think} classical programming foundations before jumping to the quantum world.
\end{itemize}

Resource-Aware Classical Computing. 
\begin{itemize}
\item The biggest questionable assumption of classical programming is that it is possible
to freely copy and discard information
\item A classical programming language which respects no-cloning and no-discarding is
the right foundation for an eventual quantum extension
\item We want these properties to be \textcolor{red}{inherent} in the language; not an afterthought
filtered by a type system
\item We want to program with \textcolor{red}{isomorphisms} or \textcolor{red}{equivalences}
\item The simplest instance is \textcolor{red}{permutations between finite types} which happens to
correspond to \textcolor{red}{reversible circuits}.
\end{itemize}

Representing Reversible Circuits: truth table, matrix, reed muller
expansion, product of cycles, decision diagram, etc.

any easy way to reproduce Figure 4 on p.7 of Saeedi and Markov?
important remark: these are all \emph{Boolean} circuits!
Most important part: reversible circuits are equivalent to permutations.

A (Foundational) Syntactic Theory. Ideally, want a notation that
\begin{enumerate}
\item is easy to write by programmers
\item is easy to mechanically manipulate
\item can be reasoned about
\item can be optimized.
\end{enumerate}
Start with a \emph{foundational} syntactic theory on our way there:
\begin{enumerate}
\item easy to explain
\item clear operational rules
\item fully justified by the semantics
\item sound and complete reasoning
\item sound and complete methods of optimization
\end{enumerate}

A Syntactic Theory. 
Ideally want a notation that is easy to write by programmers and that
is easy to mechanically manipulate for reasoning and optimizing of circuits.

Syntactic calculi good. 
Popular semantics: Despite the increasing importance of formal
methods to the computing industry, there has been little advance to
the notion of a ``popular semantics'' that can be explained to
\emph{and used} effectively (for example to optimize or simplify
programs) by non-specialists including programmers and first-year
students. Although the issue is by no means settled, syntactic
theories are one of the candidates for such a popular semantics for
they require no additional background beyond knowledge of the
programming language itself, and they provide a direct support for the
equational reasoning underlying many program transformations.

The primary abstraction in HoTT is 'type equivalences.'
If we care about resource preservation, then we are concerned with 'type equivalences'.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Equivalences and Commutative Semirings} 

Our starting point is the notion of equivalence of types. We then
connect this notion to several semiring structures, on finite types,
permutations and equivalences,
with the goal of reducing the notion of equivalence for finite types to a
notion of reversible computation.

%%%%%%%%%%%%
\subsection{Finite Types}

The elementary building blocks of type theory are the empty type
($\bot$), the unit type ($\top$), and the sum ($\uplus$) and product
($\times$) types. These constructors can encode any \emph{finite
  type}. Traditional type theory also includes several facilities for
building infinite types, most notably function types. We will however
not address infinite types in this paper except for a discussion in
Sec.~\ref{sec:conc}. We will instead focus on thoroughly understanding
the computational structures related to finite types.

An essential property of a finite type $A$ is its size $|A|$ which is
defined as follows:
\[\begin{array}{rcl}
|\bot| &=& 0 \\
|\top| &=& 1 \\
|A \uplus B| &=& |A| + |B| \\
|A \times B| &=& |A| * |B| 
\end{array}\] 
Our starting point is a result by Fiore
et. al~\cite{Fiore:2004,fiore-remarks} that completely characterizes
the isomorphisms between finite types using the axioms of commutative
semirings. (See Appendix~\ref{sec:commrig} for the complete definition
of commutative semirings.) Intuitively this result states that one can
interpret each type by its size, and that this identification validates the familiar
properties of the natural numbers, and is in fact isomorphic to the
commutative semiring of the natural numbers.

In previous work ~\cite {James:2012:IE:2103656.2103667}, we introduced
the $\Pi$ family of languages whose core computations are these
isomorphisms between finite types. Building on that work and on the
growing-in-importance idea that isomorphisms have interesting
computational content and should not be silently or implicitly
identified, we first recast Fiore et. al's result in the next section,
making explicit that the commutative semiring structure can be defined
up to the HoTT relation of \emph{type equivalence} instead of strict
equality~$=$.

%%%%%%%%%%%%
\subsection{Commutative Semirings of Types}

There are several equivalent definitions of the notion of equivalence
of types. For concreteness, we use the following definition as it
appears to be the most intuitive in our setting.

\begin{definition}[Quasi-inverse]
  For a function $f : A \rightarrow B$, a \emph{quasi-inverse} of $f$
  is a triple $(g, \alpha, \beta)$, consisting of a function
  $g : B \rightarrow A$ and homotopies
  $\alpha : f \circ g = \mathrm{id}_B$ and
  $\beta : g \circ f = \mathrm{id}_A$.
\end{definition}
 
\begin{definition}[Equivalence of types]
  Two types $A$ and $B$ are equivalent $A ≃ B$ if there exists a
  function $f : A \rightarrow B$ together with a quasi-inverse for $f$.
\end{definition}
 
As the definition of equivalence is parameterized by a function~$f$,
we are concerned with, not just the fact that two types are
equivalent, but with the precise way in which they are equivalent. For
example, there are two equivalences between the type
\AgdaDatatype{Bool} and itself: one that uses the identity for $f$
(and hence for the quasi-inverse) and one that uses boolean negation
for $f$ (and hence for the quasi-inverse). These two equivalences are
themselves \emph{not} equivalent: each of them can be used to
``transport'' properties of \AgdaDatatype  {Bool} in a different way.

It is straightforward to prove that the universe of types
(\AgdaDatatype{Set} in Agda terminology) is a commutative semiring up
to equivalence of types~$\simeq$.

\begin{theorem}
The collection of all types (\AgdaDatatype{Set}) forms a commutative 
semiring (up to $\simeq$). 
\end{theorem}
\begin{proof}
  As expected, the additive unit is $\bot$, the multiplicative unit
  is~$\top$, and the two binary operations are $\uplus$ and $\times$.
\end{proof}

\jc{Do we want to have a bunch of appendices, or perhaps a web
link, to all the Agda code which formalizes all of this?}

\noindent For example, we have equivalences such as:
\[\begin{array}{rcl}
\bot ⊎ A &\simeq& A \\
\top \times A &\simeq& A \\
A \times (B \times C) &\simeq& (A \times B) \times C \\
A \times \bot &\simeq& \bot \\
A \times (B \uplus C) &\simeq& (A \times B) \uplus (A \times C) 
\end{array}\]

One of the advantages of using equivalence $\simeq$ instead of strict
equality $=$ is that we can reason one level up about the type of all
equivalences $\textsc{eq}_{A,B}$. For a given $A$ and $B$, the
elements of $\textsc{eq}_{A,B}$ are all the ways in which we can prove
$A \simeq B$. For example,
$\textsc{eq}_{\AgdaDatatype {Bool},\AgdaDatatype {Bool}}$ has two
elements corresponding to the $\mathrm{id}$-equivalence and to the
negation-equivalence that were mentioned before. More generally, 
for finite types $A$ and $B$,
the type $\textsc{eq}_{A,B}$ is only inhabited if $A$ and~$B$ have the
same size in which case the type has $|A|~!$ (factorial of the size of
$A$) elements witnessing the various possible identifications of $A$
and $B$. The type of all equivalences has some non-trivial structure:
in particular, it is itself a commutative semiring.

\begin{theorem}
  The type of all equivalences $\textsc{eq}_{A,B}$ for finite types
  $A$ and $B$ forms a commutative semiring up to extensional
  equivalence of equivalences.
\end{theorem}
\begin{proof}
  The most important insight is the definition of equivalence of
  equivalences. Two equivalences $e_1, e_2 : \textsc{eq}_{A,B}$ with
  underlying functions $f_1$ and $f_2$ and underlying quasi-inverses
  $g_1$ and $g_2$ are themselves equivalent if:
\begin{itemize}
\item for all $a \in A$, $f_1(a) = f_2(a)$, and 
\item for all $b \in B$, $g_1(b) = g_2(b)$.
\end{itemize}
Given this notion of equivalence of equivalences, the proof proceeds
smoothly with the additive unit being the vacuous equivalence
$\bot \simeq \bot$, the multiplicative unit being the trivial
equivalence $\top \simeq \top$, and the two binary operations being
essentially a mapping of $\uplus$ and $\times$ over equivalences.
\end{proof}

We reiterate that the commutative semiring axioms in this case are
satisfied up to extensional equality of the functions underlying the
equivalences.  We could, in principle, consider a weaker notion of
equivalence of equivalences and attempt to iterate the construction
but for the purposes of modeling circuits and optimizations, it is
sufficient to consider just one additional level.

%%%%%%%%%%%%
\subsection{Commutative Semirings of Permutations}

\jc{actually, it is equivalences-of-equivalences which are
fundamentally based on fun-ext; type equivalences themselves
are mostly computationally effective.  Otherwise they could not
be equivalent to permutations...  But they are somehow less
tangible, while permutations are quite concrete.}

Type equivalences are fundamentally based on function extensionality
and hence are generally not computationally effective. In the HoTT
context, this is the open problem of finding a computational
interpretation for \emph{univalence}. In the case of finite types
however, there is a computationally-friendly alternative (and as we
prove equivalent) characterization of type equivalences based on
permutations of finite sets.

The idea is that, up to equivalence, the only interesting property of
a finite type is its size, so that type equivalences must be
size-preserving maps and hence correspond to permutations. For
example, given two equivalent types $A$ and $B$ of completely
different structure, e.g.,
$A = (\top \uplus \top) \times (\top \uplus (\top \uplus \top))$ and
$B = \top \uplus (\top \uplus (\top \uplus (\top \uplus (\top \uplus
(\top \uplus \bot)))))$,
we can find equivalences from either type to the finite set
$\mathsf{Fin}~6$ and reduce all type equivalences between sets of size
6 to permutations.

We begin with the following theorem which precisely characterizes the
relationship between finite types and finite sets.

\begin{theorem}
  If $A\simeq \mathsf{Fin}~m$, $B\simeq \mathsf{Fin}~n$ and
  $A \simeq B$ then $m = n$.
\end{theorem}
\begin{proof}
We proceed by cases on the possible values for $m$ and $n$. If they
are different, we quickly get a contradiction. If they are both~0 we
are done. The interesting situation is when $m = \mathit{suc}~m'$ and
$n = \mathit{suc}~n'$. The result follows in this case by induction
assuming we can establish that the equivalence between $A$ and $B$,
i.e., the equivalence between $\mathsf{Fin}~(\mathit{suc}~m')$ and
$\mathsf{Fin}~(\mathit{suc}~n')$, implies an equivalence between
$\mathsf{Fin}~m'$ and $\mathsf{Fin}~n'$. In our setting, we actually
need to construct a particular equivalence between the smaller sets
given the equivalence of the larger sets with one additional
element. This lemma is quite tedious as it requires us to isolate one
element of $\mathsf{Fin}~(\mathit{suc}~m')$ and analyze every 
(class of) position
this element could be mapped to by the larger equivalence and in each
case construct an equivalence that excludes this element.
\end{proof}

Given the correspondence between finite types and finite sets, we now
prove that equivalences on finite types are equivalent to permutations
on finite sets. We proceed in steps: first by proving that finite sets
for a commutative semiring up to $\simeq$ (Thm.~\ref{thm:finrig});
second by proving that, at the next level, the type of permutations
between finite sets is also a commutative semiring up to strict
equality of the representations of permutations
(Thm.~\ref{thm:permrig}); third by proving that the type of type
equivalences is equivalent to the type of permutations
(Thm.~\ref{thm:eqeqperm}); and finally by proving that the commutative
semiring of type equivalences is isomorphic to the commutative
semiring of permutations (Thm.~\ref{thm:isoeqperm}). This series of
theorems will therefore justify our focus in the next section of
develop a term language for permutations as a way to compute with type
equivalences.

\begin{theorem}\label{thm:finrig}
  The collection of all finite types ($\AgdaDatatype{Fin}~m$ for
  natural number $m$) forms a commutative semiring (up to $\simeq$).
\end{theorem}
\begin{proof}
  The additive unit is \AgdaDatatype{Fin}~$0$ and the multiplicative unit
  is \AgdaDatatype{Fin}~$1$.  For the two binary operations, the proof
  crucially relies on the following equivalences:

    \begin{code}
iso-plus   : {m n : ℕ} → (Fin m ⊎ Fin n) ≃ Fin (m + n) 
iso-times  : {m n : ℕ} → (Fin m × Fin n) ≃ Fin (m * n)
    \end{code}
    \AgdaHide{
    \begin{code}
iso-plus = {!!}
iso-times = {!!}
     \end{code}
     }

\end{proof}
 
\begin{theorem}\label{thm:permrig}
  The collection of all permutations $\textsc{perm}_{m,n}$ between
  finite sets $\mathsf{Fin}~m$ and $\mathsf{Fin}~n$ forms a
  commutative semiring up to strict equality of the representations of
  the permutations.
\end{theorem}
\begin{proof}
  The proof requires delicate attention to the representation of
  permutations as straightforward attempts turn out not to capture
  enough of the properties of permutations. A permutation of one set
  to another is represented using two sizes: $n$ for the size of the
  input finite set and $m$ for the size of the resulting finite
  set. Naturally in any well-formed permutations, these two sizes are
  equal but the presence of both types allows us to conveniently
  define a permutation $\mathsf{CPerm}~m~n$ using four components. The
  first two components are:
  \begin{itemize}
  \item a vector of size $n$ containing elements drawn from the finite
    set $\mathsf{Fin}~m$;
  \item a dual vector of size $m$ containing elements drawn from the
    finite set $\mathsf{Fin}~n$;
  \end{itemize}
  Each of the above vectors can be interpreted as a map $f$ that acts
  on the incoming finite set sending the element at index $i$ to
  position $f !! i$ in the resulting finite set. To guarantee that
  these maps define an actual permutation, the last two components are
  proofs that the sequential composition of the maps in both direction
  produce the identity. Given this representation, we can prove that
  two permutations are equal if the underlying vectors are strictly
  equal. The proof proceeds using the vacuous permutation
  $\mathsf{CPerm}~0~0$ for the additive unit and the trivial
  permutation $\mathsf{CPerm}~1~1$ for the multiplicative unit.
\jc{we should detail sum and product as well, as they are 
non-trivial.}
\end{proof}

\begin{theorem}\label{thm:eqeqperm}
If $A ≃ \mathsf{Fin}~m$ and $B ≃ \mathsf{Fin}~n$, then the type of all
equivalences $\textsc{eq}_{A,B}$ is equivalent to the type of all
permutations $\textsc{perm}~m~n$.
\end{theorem}
\begin{proof}
  The main difficulty in this proof was to generalize from sets to
  setoids to make the equivalence relations explicit. The proof is
  straightforward but long and tedious.
\end{proof}

\begin{theorem}\label{thm:isoeqperm}
  The equivalence of Theorem~\ref{thm:eqeqperm} is an
  \emph{isomorphism} between the commutative semiring of equivalences
  of finite types and the commutative semiring of permutations.
\end{theorem}

\jc{the other thing worth pointing out is that every axiom of
semirings (of types) is an equivalence, and thus corresponds 
to a permutation.  Some are trivial: associativity of + in particular
gets mapped to the identity permutation.  However, some are
more interesting.  In particular, commutativity of * is intimately
related to matrix transpose.}

Before concluding, we briefly mention that, with the proper Agda
definitions, Thm.~\ref{thm:eqeqperm} can be rephrased in a more
evocative way as follows. 

\begin{theorem}
\[
(A ≃ B) ≃ \mathsf{Perm} |A| |B| 
\]
\end{theorem}

This formulation shows that the univalence \emph{postulate} can be
proved and given a computational interpretation for finite types.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Programming with Permutations}

In the previous section, we argued that, up to equivalence, the
equivalence of types reduces to permutations on finite sets. We recall
our previous work which proposed a term language for permutations and
adapt it to be used to express, compute with, and reason about type
equivalences between finite types.

%%%%%%%%%%%%
\subsection{The $\Pi$-Languages}

In previous work~\cite{James:2012:IE:2103656.2103667}, we introduced
the $\Pi$ family of languages whose only computations are isomorphisms
between finite types. We propose that this family of languages is
exactly the right programmatic interface for manipulating and
reasoning about type equivalences.

The syntax of the previously-developed $\Pi$ language consists of
types $\tau$ including the empty type 0, the unit type 1, and
conventional sum and product types. The values classified by these
types are the conventional ones: $()$ of type 1, $\inl{v}$ and
$\inr{v}$ for injections into sum types, and $(v_1,v_2)$ for product
types:
\[\begin{array}{lrcl}
(\textit{Types}) & 
  \tau &::=& 0 \alt 1 \alt \tau_1 + \tau_2 \alt \tau_1 * \tau_2 \\
(\textit{Values}) & 
  v &::=& () \alt \inl{v} \alt \inr{v} \alt (v_1,v_2) \\
(\textit{Combinator types}) &&& \tau_1 \iso \tau_2 \\
(\textit{Combinators}) & 
  c &::=& [\textit{see Fig.~\ref{pi-combinators}}]
\end{array}\]
The interesting syntactic category of $\Pi$ is that of
\emph{combinators} which are witnesses for type isomorphisms $\tau_1
\iso \tau_2$. They consist of base combinators (on the left side of
Fig.~\ref{pi-combinators}) and compositions (on the right side of the
same figure). Each line of the figure on the left introduces a pair of
dual constants\footnote{where $\swapp$ and $\swapt$ are self-dual.}
that witness the type isomorphism in the middle.

\begin{figure*}[ht]
\[\begin{array}{cc}
\begin{array}{rrcll}
\identlp :&  0 + \tau & \iso & \tau &: \identrp \\
\swapp :&  \tau_1 + \tau_2 & \iso & \tau_2 + \tau_1 &: \swapp \\
\assoclp :&  \tau_1 + (\tau_2 + \tau_3) & \iso & (\tau_1 + \tau_2) + \tau_3 &: \assocrp \\

\identlt :&  1 * \tau & \iso & \tau &: \identrt \\
\swapt :&  \tau_1 * \tau_2 & \iso & \tau_2 * \tau_1 &: \swapt \\
\assoclt :&  \tau_1 * (\tau_2 * \tau_3) & \iso & (\tau_1 * \tau_2) * \tau_3 &: \assocrt 
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

%%%%%%%%%%%%
\subsection{Example Circuits}

The language $\Pi$ is universal for reversible combinational
circuits~\cite{James:2012:IE:2103656.2103667}.\footnote{With the
addition of recursive types and trace operators, $\Pi$ become a Turing
complete reversible
language~\cite{James:2012:IE:2103656.2103667,rc2011}.} We illustrate
the expressiveness of the language with a few short examples.

The first example is simply boolean negation which is easily achieved:

\begin{code}
BOOL : U
BOOL = PLUS ONE ONE

NOT₁ : BOOL ⟷ BOOL
NOT₁ = swap₊
\end{code}

\noindent Viewing the combinator as a permutation on finite sets, we
might visualize it as follows:

\begin{center}
\begin{tikzpicture}[scale=0.3,every node/.style={scale=0.3}]
  \draw (0,0) ellipse (1cm and 2cm);
  \draw[fill] (0,1) circle [radius=0.025];
  \node[below] at (0,1) {F};
  \draw[fill] (0,-1) circle [radius=0.025];
  \node[below] at (0,-1) {T};

  \draw     (0,1)  -- (2,1)  ;
  \draw     (0,-1) -- (2,-1) ;
  \draw     (2,1)  -- (4,-1) ;
  \draw     (2,-1) -- (4,1)  ;
  \draw[->] (4,1)  -- (6,1)  ;
  \draw[->] (4,-1) -- (6,-1) ;

  \draw (6,0) ellipse (1cm and 2cm);
  \draw[fill] (6,1) circle [radius=0.025];
  \node[below] at (6,1) {F};
  \draw[fill] (6,-1) circle [radius=0.025];
  \node[below] at (6,-1) {T};
\end{tikzpicture}
\end{center}

Naturally there are many ways of encoding boolean negation. The
following example is a more convoluted circuit that computes the same
function:

\begin{code}
NOT₂ : BOOL ⟷ BOOL
NOT₂ =  uniti⋆ ◎
        swap⋆ ◎
        (swap₊ ⊗ id⟷) ◎
        swap⋆ ◎
        unite⋆
\end{code}

\noindent Viewing this combinator as a permutation on finite sets, we
might visualize it as follows:

\begin{center}
\begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,-0.5)   ;
  \draw     (2,0.5)  -- (3,2)      ;
  \draw     (2,-0.5) -- (3,1)      ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,1)    -- (3.5,1)    ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (4.5,1)    ;
  \draw     (3.5,1)    -- (4.5,2)    ;
  \draw     (3.5,-0.5) -- (4.5,-0.5) ; 

  \draw     (4.5,2)    -- (5,2)    ;
  \draw     (4.5,1)    -- (5,1)    ;
  \draw     (4.5,-0.5) -- (5,-0.5) ;

  \draw     (5,2)    -- (6,0.5)  ;
  \draw     (5,1)    -- (6,-0.5) ;
  \draw     (5,-0.5) -- (6,2)    ; 

  \draw     (6,2)    -- (7,2)    ;
  \draw     (6,0.5)  -- (8,0.5)  ;
  \draw     (6,-0.5) -- (8,-0.5) ; 

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

Writing circuits using the raw syntax for combinators is clearly
tedious. In other work, we have investigated a compiler from a
conventional functional language to generate the
circuits~\cite{James:2012:IE:2103656.2103667}, a systematic technique
to translate abstract machines to $\Pi$~\cite{rc2012}, and a
Haskell-like surface language~\cite{theseus} which can be of help in
writing circuits. These essential tools are however a distraction in
the current setting and we content ourselves with some Agda syntactic
sugar illustrated below:

\begin{code}
BOOL² : U
BOOL² = TIMES BOOL BOOL

CNOT : BOOL² ⟷ BOOL²
CNOT = TIMES BOOL BOOL
         ⟷⟨ id⟷ ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ dist ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT₁) ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ factor ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ id⟷ ⟩
       TIMES BOOL BOOL □
  where x = ONE; y = ONE

TOFFOLI : TIMES BOOL BOOL² ⟷ TIMES BOOL BOOL²
TOFFOLI = TIMES BOOL BOOL² 
            ⟷⟨ id⟷ ⟩
          TIMES (PLUS x y) BOOL² 
            ⟷⟨ dist ⟩
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩ 
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ factor ⟩
          TIMES (PLUS x y) BOOL²
            ⟷⟨ id⟷ ⟩ 
         TIMES BOOL BOOL² □
  where x = ONE; y = ONE
\end{code}
This style makes the intermediate steps explicit showing how the types
are transformed in each step by the combinators. The example
incidentally confirms that $\Pi$ is universal for reversible circuits
since the Toffoli gate is universal for such
circuits~\cite{Toffoli:1980}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Semantics}

In the previous sections, we established that type equivalences on
finite types can be, up to equivalence, expressed as permutations and
proposed a term language for expressing permutations on finite types
that is complete for reversible combinational circuits. We are now
ready for the main technical contribution of the paper: an effective
computational framework for reasoning \emph{about} type
equivalences. From a programming perspective, this framework manifests
itself as a collection of rewrite rules for optimizing circuit
descriptions in $\Pi$. Naturally we are not concerned with just any
collection of rewrite rules but with a sound and complete
collection. The current section will set up the framework and
illustrate its use on one example and the next sections will introduce
the categorical framework in which soundness and completeness can be
proved.

%%%%%%%%%%%%
\subsection{Operational and Denotational Semantics}

In conventional programming language research, valid optimizations are
specified with reference to the \emph{observational equivalence}
relation which itself is defined with reference to an \emph{evaluator}.
As the language is reversible, a reasonable starting point would then
be to define forward and backward evaluators with the following
signatures:

\begin{code}
eval   : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
evalB  : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
\end{code}
\AgdaHide{
\begin{code}
eval unite₊ (inj₁ ())
eval unite₊ (inj₂ v) = v
eval uniti₊ v = inj₂ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆ (tt , v) = v
eval uniti⋆ v = (tt , v)
eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbr (() , _)
eval absorbl (_ , ())
eval factorzl ()
eval factorzr ()
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval id⟷ v = v
eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

-- useful to have the backwards eval too

evalB unite₊ x = inj₂ x
evalB uniti₊ (inj₁ ())
evalB uniti₊ (inj₂ y) = y
evalB swap₊ (inj₁ x) = inj₂ x
evalB swap₊ (inj₂ y) = inj₁ y
evalB assocl₊ (inj₁ (inj₁ x)) = inj₁ x
evalB assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB assocl₊ (inj₂ y) = inj₂ (inj₂ y)
evalB assocr₊ (inj₁ x) = inj₁ (inj₁ x)
evalB assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB assocr₊ (inj₂ (inj₂ y)) = inj₂ y
evalB unite⋆ x = tt , x
evalB uniti⋆ (tt , x) = x
evalB swap⋆ (x , y) = y , x
evalB assocl⋆ ((x , y) , z) = x , y , z
evalB assocr⋆ (x , y , z) = (x , y) , z
evalB absorbr ()
evalB absorbl ()
evalB factorzr (_ , ())
evalB factorzl (() , _)
evalB dist (inj₁ (x , y)) = inj₁ x , y
evalB dist (inj₂ (x , y)) = inj₂ x , y
evalB factor (inj₁ x , z) = inj₁ (x , z)
evalB factor (inj₂ y , z) = inj₂ (y , z)
evalB id⟷ x = x
evalB (c₀ ◎ c₁) x = evalB c₀ (evalB c₁ x)
evalB (c₀ ⊕ c₁) (inj₁ x) = inj₁ (evalB c₀ x)
evalB (c₀ ⊕ c₁) (inj₂ y) = inj₂ (evalB c₁ y)
evalB (c₀ ⊗ c₁) (x , y) = evalB c₀ x , evalB c₁ y
\end{code}
}

\noindent In the definition, the function $⟦\cdot⟧$ maps each type
constructor to its Agda denotation, e.g., it maps the type 0 to
$\bot$, the type 1 to $\top$, etc. The complete definitions for these
evaluators can be found in previous
publications~\cite{rc2011,rc2012,James:2012:IE:2103656.2103667} and
will not be repeated here. The reason is that, although these
evaluators adequately serve as semantic specifications, they drive the
development towards extensional reasoning as evident from the
signatures which map a permutation to a function. We will instead
pursue a denotational approach mapping the combinators to type
equivalences or equivalently to permutations:

\begin{code}
c2equiv  :  {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → ⟦ t₁ ⟧ ≃ ⟦ t₂ ⟧
c2perm   :  {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → 
            CPerm (size t₂) (size t₁)
\end{code}
\AgdaHide{
\begin{code}
c2equiv unite₊ = TE.unite₊equiv
c2equiv uniti₊ = TE.uniti₊equiv
c2equiv swap₊ = TE.swap₊equiv
c2equiv assocl₊ = TE.assocl₊equiv
c2equiv assocr₊ = TE.assocr₊equiv
c2equiv unite⋆ = TE.unite⋆equiv
c2equiv uniti⋆ = TE.uniti⋆equiv
c2equiv swap⋆ = TE.swap⋆equiv
c2equiv assocl⋆ = TE.assocl⋆equiv
c2equiv assocr⋆ = TE.assocr⋆equiv
c2equiv absorbr = TE.distzequiv
c2equiv absorbl = TE.distzrequiv
c2equiv factorzr = TE.factorzrequiv
c2equiv factorzl = TE.factorzequiv
c2equiv dist = TE.distequiv
c2equiv factor = TE.factorequiv
c2equiv id⟷ = TE.idequiv
c2equiv (c ◎ c₁) = c2equiv c₁ ● c2equiv c
c2equiv (c ⊕ c₁) = path⊎ (c2equiv c) (c2equiv c₁)
c2equiv (c ⊗ c₁) = path× (c2equiv c) (c2equiv c₁)
c2perm = {!!}
\end{code}
}

\noindent The advantage is that permutations have a concrete
representation which can be effectively compared for equality as
explained in the proof of Thm.~\ref{thm:permrig}.

%%%%%%%%%%%%
\subsection{Rewriting Approach} 

Having mapped each combinator to a permutation, we can reason about
valid optimizations mapping a combinator to another by studying the
equivalence of permutations on finite sets. The traditional definition
of equivalence might equate two permutations if their actions on every
input produce the same output but we again resist that extensional
reasoning. Instead we are interested in a calculus, a set of rules,
that can be used to rewrite combinators preserving their meaning. It
is trivial to come up with a few rules such as:

\AgdaHide{
\begin{code}
module X where
 data _⇔'_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
\end{code}
}
\begin{code}
  id⇔     :  {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔' c 

  trans⇔  :  {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
             (c₁ ⇔' c₂) → (c₂ ⇔' c₃) → (c₁ ⇔' c₃) 

  assoc⇔  :  {t₁ t₂ t₃ t₄ : U}
             {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
             (c₁ ◎ (c₂ ◎ c₃)) ⇔' ((c₁ ◎ c₂) ◎ c₃)

  id◎⇔    :  {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔' c

  swap₊⇔  :  {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
             (swap₊ ◎ (c₁ ⊕ c₂)) ⇔' ((c₂ ⊕ c₁) ◎ swap₊)

\end{code}

\noindent which are evidently sound. The challenge of course is to
come up with a sound and complete set of such rules.

Before we embark on the categorification program in the next section,
we show that, with some ingenuity, one can develop a reasonable set of
rewrite rules that would allow us to prove that the two negation
circuits from the previous section are actual equivalent:

\begin{code}

negEx : NOT₂ ⇔ NOT₁
negEx =
  uniti⋆ ◎ (swap⋆ ◎ ((swap₊ ⊗ id⟷) ◎ (swap⋆ ◎ unite⋆)))
          ⇔⟨ id⇔ ⊡ assoc◎l ⟩
  uniti⋆ ◎ ((swap⋆ ◎ (swap₊ ⊗ id⟷)) ◎ (swap⋆ ◎ unite⋆))
          ⇔⟨ id⇔ ⊡ (swapl⋆⇔ ⊡ id⇔) ⟩
  uniti⋆ ◎ (((id⟷ ⊗ swap₊) ◎ swap⋆) ◎ (swap⋆ ◎ unite⋆))
          ⇔⟨ id⇔ ⊡ assoc◎r ⟩
  uniti⋆ ◎ ((id⟷ ⊗ swap₊) ◎ (swap⋆ ◎ (swap⋆ ◎ unite⋆)))
          ⇔⟨ id⇔ ⊡ (id⇔ ⊡ assoc◎l) ⟩
  uniti⋆ ◎ ((id⟷ ⊗ swap₊) ◎ ((swap⋆ ◎ swap⋆) ◎ unite⋆))
          ⇔⟨ id⇔ ⊡ (id⇔ ⊡ (linv◎l ⊡ id⇔)) ⟩
  uniti⋆ ◎ ((id⟷ ⊗ swap₊) ◎ (id⟷ ◎ unite⋆))
          ⇔⟨ id⇔ ⊡ (id⇔ ⊡ idl◎l) ⟩
  uniti⋆ ◎ ((id⟷ ⊗ swap₊) ◎ unite⋆)
          ⇔⟨ assoc◎l ⟩
  (uniti⋆ ◎ (id⟷ ⊗ swap₊)) ◎ unite⋆
          ⇔⟨ unitil⋆⇔ ⊡ id⇔ ⟩
  (swap₊ ◎ uniti⋆) ◎ unite⋆
          ⇔⟨ assoc◎r ⟩
  swap₊ ◎ (uniti⋆ ◎ unite⋆)
          ⇔⟨ id⇔ ⊡ linv◎l ⟩
  swap₊ ◎ id⟷
          ⇔⟨ idr◎l ⟩
  swap₊ ▤
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Categorification}

The problem of finding a sound and complete set of rules for reasoning
about equivalence of permutations is solved by appealing to various
results about specialized monoidal categories. The following quote
sets up the context for our development.
\begin{quote}
  In Mac Lane’s second coherence result of [...], which has to do with
  symmetric monoidal categories, it is not intended that all equations
  between arrows of the same type should hold. What Mac Lane does can
  be described in logical terms in the following manner. On the one
  hand, he has an axiomatization, and, on the other hand, he has a
  model category where arrows are permutations; then he shows that his
  axiomatization is complete with respect to this model. It is no
  wonder that his coherence problem reduces to the completeness
  problem for the usual axiomatization of symmetric
  groups~\cite{coherence}.
\end{quote}

%%%%%%%%%%%%
\subsection{Monoidal Categories} 

\begin{definition}[Category]
  \label{ch:pi:def:category}
  A \emph{category} $\mathbf{C}$ consists of:
  \begin{itemize}
    \item a class $|\mathbf{C}|$ of \emph{objects}, denoted $A,B,C,\ldots$;
    \item for each pair of objects $A,B$, a set
    $\mathrm{hom}_{\mathbf{C}}(A,B)$ of \emph{morphisms}, which are denoted
    $f : A \rightarrow B$;
    \item \emph{identity morphisms} $\mathrm{id}_A : A \rightarrow A$ and the
    operation of \emph{composition}: if $f : A \rightarrow B$ and $g : B
    \rightarrow C$, then $g \circ f : A \rightarrow C$ subject to three         
    equations stating that $\mathrm{id}$ is the left and right unit for
    composition and that composition is associative:
    \begin{itemize}
    \item Unit:
      $f \circ \mathrm{id} = f = \mathrm{id} \circ f$
    \item Associativity:
      $h \circ (g \circ f) = (h \circ g) \circ f$
    \end{itemize}
  \end{itemize}
\end{definition}

An important subtlety of this definition is in the equality of
arrows. Indeed the programs $f$ and $\mathrm{id} \circ f$ are
different syntactic programs and their compilation might be different
in any concrete implementation of the language. Hence the equality of
arrows should be based upon the semantic equivalence of these two
programs, for example, using \emph{observational equivalence}. The
definition of categories allows one to specify the arrows and the
objects, but is not parametrized by an equivalence relationship over
the arrows. The $=$ in the definition of categories is the
mathematical equivalence of the mathematical entities that are the
arrows. Hence the `operations' that are the arrows must already
include the relevant equivalence relation on programs. This is
sometimes referred to as a \emph{term model} and essentially states
that operations of the language are the equivalence classes of the
programs one writes in the language. Thus $f$ and $\mathrm{id} \circ
f$ become \emph{the same arrow}.  See Section 2.2 of Barr and Wells's
book~\cite{DBLP:books/daglib/0080381} for a detailed discussion and
Def.~2.4 of Moggi's paper~\cite{Moggi:1991:NCM} for an example of such
usage.

\begin{definition}[Monoidal Category]
\label{ch:pi:def:MC}
A \emph{monoidal category}~\cite{nla.cat-vn1051288} is a category with
the following additional structure:
\begin{itemize}
\item a functor $\otimes$ called the monoidal or tensor product,
\item an object $I$ called the unit object, and
\item natural isomorphisms
  $\alpha_{A,B,C} : (A \otimes B) \otimes C \isoarrow A \otimes (B
  \otimes C)$,
  $\lambda_A : I \otimes A \isoarrow A$, and
  $\rho_A : A \otimes I \isoarrow A$, such that the following two
  diagrams (known as the \emph{associativity pentagon} and the
  \emph{triangle for unit}) commute:
\end{itemize}
%                                                                               
\begin{center}
\begin{tikzcd}[column sep=tiny]
((A \otimes B) \otimes C) \otimes D)
  \arrow[rr, "\alpha"]
  \arrow[d, "\alpha \otimes \mathrm{id}_D"']
&& (A \otimes B) \otimes (C \otimes D)
   \arrow[d, "\alpha"]
\\
(A \otimes (B \otimes C)) \otimes D
  \arrow[dr, "\alpha"']
&& A \otimes (B \otimes (C \otimes D))
   \arrow[dl, "\mathrm{id}_A \otimes \alpha"]
\\
& A \otimes ((B \otimes C) \otimes D)
\end{tikzcd}
\end{center}
%                                                                               
\begin{center}
\begin{tikzcd}[column sep=tiny]
(A \otimes I) \otimes B
  \arrow[rr, "\alpha"]
  \arrow[dr, "\rho_A \otimes \mathrm{id}_B"']
&& A \otimes (I \otimes B)
  \arrow[dl, "\mathrm{id}_A \otimes \lambda_B"]
\\
& A \otimes B
\end{tikzcd}
\end{center}
\end{definition}

\begin{definition}[Symmetric Monoidal Category]
\label{ch:pi:def:SMC}
A monoidal category is \emph{symmetric} if it has an isomorphism
$\sigma_{A,B} : A \otimes B \isoarrow B \otimes A$ where $\sigma$ is a
natural transformation which satisfies the following two coherence conditions
(called \emph{bilinerarity} and \emph{symmetry}):
\end{definition}
\begin{center}
\begin{tikzcd}[column sep=tiny]
& A \otimes (B \otimes C) 
  \arrow[dr, "\sigma"]
  \arrow[dl, "\alpha"']
\\
(A \otimes B) \otimes C
  \arrow[d, "\sigma \otimes \mathrm{id}_C"] && 
(B \otimes C) \otimes A
 \arrow[d, "\alpha"] 
\\
(B \otimes A) \otimes C 
  \arrow[dr, "\alpha"'] &&
B \otimes (C \otimes A)
  \arrow[dl, "\mathrm{id}_B \otimes \sigma"]
\\
& B \otimes (A \otimes C)
\end{tikzcd}
\end{center}
%                                                                               
\begin{center}
\begin{tikzcd}[column sep=tiny]
& A \otimes B 
  \arrow[dl, "\sigma"']
  \arrow[dr, "\mathrm{id}_A\otimes\mathrm{id}_B"] 
\\
B \otimes A \arrow[rr, "\sigma"] && A \otimes B
\end{tikzcd}
\end{center}

Define monoidal categories; 
explain categorification of monoid
explain that arrows can be viewed as permutations; not all arrows are
'equal'; leads to coherence conditions

%%%%%%%%%%%%
\subsection{Coherence Conditions} 

for monoidal categories are reasonably easy; explain in detail

%%%%%%%%%%%%
\subsection{Commutative Rig Groupoids} 

these things are not very well-known; these are the right beasts that
are the categorification of commutative semigroups.

\emph{categorification}~\cite{math/9802029} of 
the natural numbers. A simple (slightly degenerate) example of such

This has been done generically: coherence conditions for commutative  
rig groupoids. These generalize type equivalences and permutations;
 
We haven't said anything about the categorical structure: it is not
just a commutative semiring but a commutative rig; this is crucial
because the former doesn't take composition into account. Perhaps that
is the next section in which we talk about computational
interpretation as one of the fundamental things we want from a notion
of computation is composition (cf. Moggi's original paper on monads).

Type equivalences (such as between $A × B$ and $B × A$) are \textcolor{red}{Functors}.

\noindent Equivalences between Functors are \textcolor{red}{Natural Isomorphisms}.  At the value-level,
they induce $2$-morphisms:

\begin{code}
postulate
  c₁ : {B C : U} → B ⟷ C
  c₂ : {A D : U} → A ⟷ D

p₁ p₂ : {A B C D : U} → PLUS A B ⟷ PLUS C D
p₁ = swap₊ ◎ (c₁ ⊕ c₂)
p₂ = (c₂ ⊕ c₁) ◎ swap₊
\end{code}

2-morphism of circuits

\begin{center}
\begin{tikzpicture}[scale=0.6,every node/.style={scale=0.6}]
  \draw[->,double,red,thick] (2.25,-1.5) -- (2.25,-2.5) ;
  \node at (2.6,-2) {$\alpha$} ;

  \draw (-2,-2) ellipse (0.5cm and 1cm);
  \draw[fill] (-2,-1.5) circle [radius=0.025];
  \node[below] at (-2,-1.5) {$A$};
  \draw[fill] (-2,-2.5) circle [radius=0.025];
  \node[below] at (-2,-2.5) {$B$};

  \draw (6.5,-2) ellipse (0.5cm and 1cm);
  \draw[fill] (6.5,-1.5) circle [radius=0.025];
  \node[below] at (6.5,-1.5) {$C$};
  \draw[fill] (6.5,-2.5) circle [radius=0.025];
  \node[below] at (6.5,-2.5) {$D$};

  \draw (-2,-1.5) to[bend left] (1,0.5) ;
  \draw (-2,-2.5) to[bend left] (1,-0.5) ;
  \draw[->] (3.5,0.5) to[bend left] (6.5,-1.5) ;
  \draw[->] (3.5,-0.5) to[bend left] (6.5,-2.5) ;

  \draw (-2,-1.5) to[bend right] (1,-3.5) ;
  \draw (-2,-2.5) to[bend right] (1,-4.5) ;
  \draw[->] (3.5,-3.5) to[bend right] (6.5,-1.5) ;
  \draw[->] (3.5,-4.5) to[bend right] (6.5,-2.5) ;

  \draw     (2.5,-3)  -- (3.5,-3) -- (3.5,-4) -- (2.5,-4) -- cycle ;
  \draw     (2.5,-4)  -- (3.5,-4) -- (3.5,-5) -- (2.5,-5) -- cycle ;

  \draw     (1,1)  -- (2,1) -- (2,0) -- (1,0) -- cycle ;
  \draw     (1,0)  -- (2,0) -- (2,-1) -- (1,-1) -- cycle ;

  \node at (3,-3.5) {c₁};
  \node at (3,-4.5) {c₂};

  \node at (1.5,0.5) {c₂};
  \node at (1.5,-0.5) {c₁};

  \draw     (2,0.5)  -- (2.5,0.5)  ;
  \draw     (2,-0.5) -- (2.5,-0.5) ; 

  \draw     (2.5,0.5)  -- (3.5,-0.5)  ;
  \draw     (2.5,-0.5) -- (3.5,0.5) ; 

  \draw     (1,-3.5)  -- (2,-4.5)    ;
  \draw     (1,-4.5) -- (2,-3.5)   ; 

  \draw     (2,-3.5)  -- (2.5,-3.5)    ; 
  \draw     (2,-4.5) -- (2.5,-4.5)   ; 

\end{tikzpicture}
\end{center}


Categorification II. 
The \textcolor{red}{categorification} of a semiring is called a \textcolor{red}{Rig Category}.
As with a semiring, there are two monoidal structures, which interact through some distributivity laws.
\begin{theorem}
The following are \textcolor{red}{Symmetric Bimonoidal Groupoids}:
\begin{itemize}
\item The class of all types (\AgdaDatatype{Set})
\item The set of all finite types
\item The set of permutations
\item The set of equivalences between finite types
\item Our syntactic combinators
\end{itemize}
\end{theorem}
The \textcolor{red}{coherence rules} for Symmetric Bimonoidal groupoids give us 
\textcolor{red}{58 rules}.

Categorification III.
\begin{conj}
The following are \textcolor{red}{Symmetric Rig Groupoids}:
\begin{itemize}
\item The class of all types (\AgdaDatatype{Set})
\item The set of all finite types, of permutations, of equivalences between finite types
\item Our syntactic combinators
\end{itemize}
\end{conj}
and of course the punchline:
\begin{theorem}[Laplaza 1972]
There is a sound and complete set of \textcolor{red}{coherence rules} for 
Symmetric Rig Categories.
\end{theorem}
\begin{conj}
The set of coherence rules for Symmetric Rig Groupoids are a sound
and complete set for \textcolor{red}{circuit equivalence}.
\end{conj}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Revised $\Pi$ and its Optimizer}

%%%%%%%%%%%%
\subsection{Revised Syntax}

  The refactoring of Pi from the inspiration of symmetric
  rig groupoids.  The added combinators are redundant (from an
  operational perspective) exactly because of the coherences.  But
  some of these higher combinators have rather non-trivial relations
  to each other [ex: pentagon, hexagon, and some of the weirder
  Laplaza rules].  Plus the 'minimalistic' Pi leads to much larger
  programs with LOTS of extra redexes.

\[\begin{array}{rrcll}
\absorbr :&~ 0 * \tau & \iso & 0 &: \factorzl \\
\absorbl :&~ \tau * 0 & \iso & 0 &: \factorzr \\

\dist :&~ (\tau_1 + \tau_2) * \tau_3 & \iso & (\tau_1 * \tau_3) + (\tau_2 * \tau_3)~ &: \factor \\
\distl :&~ \tau_1 * (\tau_2 + \tau_3) & \iso & (\tau_1 * \tau_2) + (\tau_1 * \tau_3)~ &: \factorl 
\end{array}\]      

%%%%%%%%%%%%
\subsection{Optimization Rules}

What we need now is Pi plus another layer to top to optimize Pi
  programs; no ad hoc rules; principled rules; 

%%%%%%%%%%%%
\subsection{Examples}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Problem with Higher-Order Functions}
\label{intc}

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
\subsection{Conventional Construction on Unpointed Types} 

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}
\label{sec:conc}

\begin{itemize}
\item add trace to make language Turing complete
\item generalize from commutative rig to field as a way to get some
  notion of h.o. functions
\end{itemize}

We start with the class of all functions $A \rightarrow B$, then
introduce constraints to filter those functions which correspond to
type equivalences $A \simeq B$, and then attempt to look for a
convenient computational framework for effective programming with type
equivalences. In the case of finite types, this is just convoluted as
the collection of functions corresponding to type equivalences is the
collection of isomorphisms between finite types and these isomorphisms
can be inductively defined giving rise to a programming language that
is complete for combinational
circuits~\cite{James:2012:IE:2103656.2103667}.

To make these connections precise, we now explore permutations over
finite sets as an explicit computational realization of isomorphisms
between finite types and prove that the type of all permutations
between finite sets is equivalent to the type of type equivalences but
with better computational properties, i.e., without the reliance on
function extensionality. 

Our theorem shows that, in the case of finite types, reversible
computation via type isomorphisms \emph{is} the computational
interpretation of univalence. The alternative presentation of the
theorem exposes it as an instance of \emph{univalence}. In the
conventional HoTT setting, univalence is postulated as an axiom that
lacking computational content. In more detail, the conventional HoTT
approach starts with two, a priori, different notions: functions and
identities (paths), and then postulates an equivalence between a
particular class of functions (equivalences) and paths. Most functions
are not equivalences and hence are evidently unrelated to paths. An
interesting question then poses itself: since reversible computational
models --- in which all functions have inverses --- are known to be
universal computational models, what would happen if we considered a
variant of HoTT based exclusively on reversible functions?  Presumably
in such a variant, all functions --- being reversible --- would
potentially correspond to paths and the distinction between the two
notions would vanish making the univalence postulate unnecessary. This
is the precise technical idea that is captured in theorem above for
the limited case of finite types.

We focused on commutative semiring structures. An obvious question is
whether the entire setup can be generalized to a larger algebraic
structure like a field. That requires additive and multiplicative
inverses. There is evidence that this negative and fractional types
are sensible and that they would give rise to some form of
higher-order functions. There is also evidence for even more exotic
types that are related to algebraic numbers including roots and
imaginary numbers.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% \bibliographystyle{abbrvnat}
\bibliographystyle{abbrvnat}
\softraggedright
\bibliography{cites}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\appendix
\section{Commutative Semirings}
\label{sec:commrig}
 
Given that the structure of commutative semirings is central to this
paper, we recall the formal algebraic definition. Commutative rings
are sometimes called \emph{commutative rigs} as they are commutative
ring without negative elements.

\begin{definition}
  A \emph{commutative semiring} consists of a set $R$, two
  distinguished elements of $R$ named 0 and 1, and two binary
  operations $+$ and $\cdot$, satisfying the following relations for
  any $a,b,c \in R$:
\[\begin{array}{rcl}
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
\end{definition}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Diagrammatic Optimization}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,-0.5)   ;
  \draw     (2,0.5)  -- (3,2)      ;
  \draw     (2,-0.5) -- (3,1)      ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,1)    -- (3.5,1)    ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (4.5,1)    ;
  \draw     (3.5,1)    -- (4.5,2)    ;
  \draw     (3.5,-0.5) -- (4.5,-0.5) ; 

  \draw     (4.5,2)    -- (5,2)    ;
  \draw     (4.5,1)    -- (5,1)    ;
  \draw     (4.5,-0.5) -- (5,-0.5) ;

  \draw     (5,2)    -- (6,0.5)  ;
  \draw     (5,1)    -- (6,-0.5) ;
  \draw     (5,-0.5) -- (6,2)    ; 

  \draw     (6,2)    -- (7,2)    ;
  \draw     (6,0.5)  -- (8,0.5)  ;
  \draw     (6,-0.5) -- (8,-0.5) ; 

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (4.8,-1.5) -- cycle; 
  \draw[red,dashed] (3.3,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (3.3,-1.7) -- cycle; 
  \draw[red,dashed] (1.8,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.8,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,-0.5)   ;
  \draw     (2,0.5)  -- (3,2)      ;
  \draw     (2,-0.5) -- (3,1)      ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,1)    -- (3.5,1)    ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (4.5,1)    ;
  \draw     (3.5,1)    -- (4.5,2)    ;
  \draw     (3.5,-0.5) -- (4.5,-0.5) ; 

  \draw     (4.5,2)    -- (5,2)    ;
  \draw     (4.5,1)    -- (5,1)    ;
  \draw     (4.5,-0.5) -- (5,-0.5) ;

  \draw     (5,2)    -- (6,0.5)  ;
  \draw     (5,1)    -- (6,-0.5) ;
  \draw     (5,-0.5) -- (6,2)    ; 

  \draw     (6,2)    -- (7,2)    ;
  \draw     (6,0.5)  -- (8,0.5)  ;
  \draw     (6,-0.5) -- (8,-0.5) ; 

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (4.8,-1.5) -- cycle; 
  \draw[red,dashed] (3.3,2.8) -- (4.4,2.8) -- (4.4,-1.3) -- (3.3,-1.3) -- cycle; 
  \draw[red,dashed,thick] (1.8,3.0) -- (4.6,3.0) -- (4.6,-1.5) -- (1.8,-1.5) -- cycle; 
  \draw[red,dashed] (1.6,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (1.6,-1.7) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,-0.5)   ;
  \draw     (2,0.5)  -- (3,2)      ;
  \draw     (2,-0.5) -- (3,1)      ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,1)    -- (3.5,1)    ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (4.5,1)    ;
  \draw     (3.5,1)    -- (4.5,2)    ;
  \draw     (3.5,-0.5) -- (4.5,-0.5) ; 

  \draw     (4.5,2)    -- (5,2)    ;
  \draw     (4.5,1)    -- (5,1)    ;
  \draw     (4.5,-0.5) -- (5,-0.5) ;

  \draw     (5,2)    -- (6,0.5)  ;
  \draw     (5,1)    -- (6,-0.5) ;
  \draw     (5,-0.5) -- (6,2)    ; 

  \draw     (6,2)    -- (7,2)    ;
  \draw     (6,0.5)  -- (8,0.5)  ;
  \draw     (6,-0.5) -- (8,-0.5) ; 

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (4.8,-1.5) -- cycle; 
  \draw[red,dashed] (3.3,2.8) -- (4.4,2.8) -- (4.4,-1.3) -- (3.3,-1.3) -- cycle; 
  \draw[red,dashed,thick] (1.8,3.0) -- (4.6,3.0) -- (4.6,-1.5) -- (1.8,-1.5) -- cycle; 
  \draw[red,dashed] (1.6,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (1.6,-1.7) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,2)   ;
  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (4.5,-0.5) ;
  \draw     (3.5,0.5)  -- (4.5,2)    ;
  \draw     (3.5,-0.5) -- (4.5,1)    ; 

  \draw     (4.5,2)    -- (5,2)    ;
  \draw     (4.5,1)    -- (5,1)    ;
  \draw     (4.5,-0.5) -- (5,-0.5) ;

  \draw     (5,2)    -- (6,0.5)  ;
  \draw     (5,1)    -- (6,-0.5) ;
  \draw     (5,-0.5) -- (6,2)    ; 

  \draw     (6,2)    -- (7,2)    ;
  \draw     (6,0.5)  -- (8,0.5)  ;
  \draw     (6,-0.5) -- (8,-0.5) ; 

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (4.8,-1.5) -- cycle; 
  \draw[red,dashed] (3.3,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (3.3,-1.7) -- cycle; 
  \draw[red,dashed] (1.6,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.6,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,2)   ;
  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (4.5,-0.5) ;
  \draw     (3.5,0.5)  -- (4.5,2)    ;
  \draw     (3.5,-0.5) -- (4.5,1)    ; 

  \draw     (4.5,2)    -- (5,2)    ;
  \draw     (4.5,1)    -- (5,1)    ;
  \draw     (4.5,-0.5) -- (5,-0.5) ;

  \draw     (5,2)    -- (6,0.5)  ;
  \draw     (5,1)    -- (6,-0.5) ;
  \draw     (5,-0.5) -- (6,2)    ; 

  \draw     (6,2)    -- (7,2)    ;
  \draw     (6,0.5)  -- (8,0.5)  ;
  \draw     (6,-0.5) -- (8,-0.5) ; 

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,2.6) -- (5.8,2.6) -- (5.8,-1.1) -- (4.8,-1.1) -- cycle; 
  \draw[red,dashed,thick] (3.5,2.8) -- (6.0,2.8) -- (6.0,-1.3) -- (3.5,-1.3) -- cycle; 
  \draw[red,dashed] (3.3,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (3.3,-1.7) -- cycle; 
  \draw[red,dashed] (1.6,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.6,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,2)   ;
  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (4.5,-0.5) ;
  \draw     (3.5,0.5)  -- (4.5,2)    ;
  \draw     (3.5,-0.5) -- (4.5,1)    ; 

  \draw     (4.5,2)    -- (5,2)    ;
  \draw     (4.5,1)    -- (5,1)    ;
  \draw     (4.5,-0.5) -- (5,-0.5) ;

  \draw     (5,2)    -- (6,0.5)  ;
  \draw     (5,1)    -- (6,-0.5) ;
  \draw     (5,-0.5) -- (6,2)    ; 

  \draw     (6,2)    -- (7,2)    ;
  \draw     (6,0.5)  -- (8,0.5)  ;
  \draw     (6,-0.5) -- (8,-0.5) ; 

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed,thick] (3.5,2.8) -- (6.0,2.8) -- (6.0,-1.3) -- (3.5,-1.3) -- cycle; 
  \draw[red,dashed] (3.3,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (3.3,-1.7) -- cycle; 
  \draw[red,dashed] (1.6,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.6,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,2)   ;
  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (7,2)    ;
  \draw     (3.5,0.5)  -- (8,0.5)  ;
  \draw     (3.5,-0.5) -- (8,-0.5) ;

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (1.6,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.6,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,2)   ;
  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (7,2)    ;
  \draw     (3.5,0.5)  -- (8,0.5)  ;
  \draw     (3.5,-0.5) -- (8,-0.5) ;

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (1.6,2.6) -- (5.8,2.6) -- (5.8,-1.1) -- (1.6,-1.1) -- cycle; 
  \draw[red,dashed] (-0.5,2.8) -- (6.0,2.8) -- (6.0,-1.3) -- (-0.5,-1.3) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,2)   ;
  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,2)    -- (7,2)    ;
  \draw     (3.5,0.5)  -- (8,0.5)  ;
  \draw     (3.5,-0.5) -- (8,-0.5) ;

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (3.6,2.6) -- (5.8,2.6) -- (5.8,-1.1) -- (3.6,-1.1) -- cycle; 
  \draw[red,dashed] (-0.5,2.8) -- (6.0,2.8) -- (6.0,-1.3) -- (-0.5,-1.3) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (4.2,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (4.2,2) circle [radius=0.025];
  \node[below] at (4.2,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (4.2,2)    -- (7,2)      ; %% ()

  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,0.5)  -- (8,0.5)  ;
  \draw     (3.5,-0.5) -- (8,-0.5) ;

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (3.6,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (3.6,-1.5) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (4.2,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (4.2,2) circle [radius=0.025];
  \node[below] at (4.2,2) {()};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (4.2,2)    -- (7,2)      ; %% ()

  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,0.5)  -- (8,0.5)  ;
  \draw     (3.5,-0.5) -- (8,-0.5) ;

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {()};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (3.6,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (3.6,-1.5) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,0.5)  -- (8,0.5)  ;
  \draw     (3.5,-0.5) -- (8,-0.5) ;

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,0.5)  -- (3,-0.5)  ;
  \draw     (2,-0.5) -- (3,0.5)   ;

  \draw     (3,0.5)  -- (3.5,0.5)  ;
  \draw     (3,-0.5) -- (3.5,-0.5) ; 

  \draw     (3.5,0.5)  -- (8,0.5)  ;
  \draw     (3.5,-0.5) -- (8,-0.5) ;

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}
