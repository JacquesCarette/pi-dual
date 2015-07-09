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
\usepackage{textcomp}
\usepackage{multicol}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros

\newcommand{\nboxtimes}[2]{\,\,~{^{#1}\boxtimes^{#2}}~\,\,}
\newcommand{\mm}{\texttt{\textminus}}
\newcommand{\pp}{\texttt{+}}
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
\newcommand{\identlsp}{\mathit{identls}_+}
\newcommand{\identrsp}{\mathit{identrs}_+}
\newcommand{\swapp}{\mathit{swap}_+}
\newcommand{\assoclp}{\mathit{assocl}_+}
\newcommand{\assocrp}{\mathit{assocr}_+}
\newcommand{\identlt}{\mathit{identl}_*}
\newcommand{\identrt}{\mathit{identr}_*}
\newcommand{\identlst}{\mathit{identls}_*}
\newcommand{\identrst}{\mathit{identrs}_*}
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
\DeclareUnicodeCharacter{2097}{\ensuremath{{}_l}}
\DeclareUnicodeCharacter{7523}{\ensuremath{{}_r}}
\DeclareUnicodeCharacter{8343}{\ensuremath{{}_l}}

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

\title{A Sound and Complete Calculus for Reversible Circuit Equivalence}
\authorinfo{}{}{}

%% 12 pages + bib
%% all citations citet (text) or citep (paren)

% \authorinfo{Jacques Carette}
%                   {McMaster University}
%                   {carette@mcmaster.ca}
% \authorinfo{Amr Sabry}
%                   {Indiana University}
%                   {sabry@indiana.edu}

\maketitle

\begin{abstract}

  Many recent advances in quantum computing, low-power design,
  nanotechnology, optical information processing, and bioinformatics
  are based on \emph{reversible circuits}. With the aim of designing a
  semantically well-founded approach for modeling and reasoning about
  reversible circuits, we propose viewing such circuits as proof terms
  witnessing equivalences between finite types. Proving that these
  type equivalences satisfy the commutative semiring axioms, we
  proceed with the categorification of type equivalences as
  \emph{symmetric rig weak groupoids}. The coherence conditions of
  these categories then produce, for free, a sound and complete
  calculus for reasoning about reversible circuit equivalence. The
  paper consists of the ``unformalization'' of an Agda package
  formalizing the connections between reversible circuits,
  equivalences between finite types, permutations between finite sets,
  and symmetric rig weak groupoids.

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
import TypeEquiv as TE hiding (swap₊)

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

%% \jc{do remember that the code which is embedded in this file
%% is not the one in the sources below (anymore).  Not sure if it
%% matters?}
%% 
%% \jc{Also: double-blind this year!  I guess we need to omit our names.
%% I don't think the text will need changed for that.}
%% \url{https://github.com/JacquesCarette/pi-dual}

Because physical laws obey various conservation principles (including
conservation of information) and because computation is fundamentally
a physical process, every computation is, at the physical level,
fundamentally an equivalence that preserves information.  The idea
that computation, at the logical and programming level, should also be
based on ``equivalences'' (i.e., invertible processes) was originally
motivated by such physical
considerations~\citep{springerlink:10.1007/BF02650179,Landauer:1961,PhysRevA.32.3266,Bennett:1973:LRC,Toffoli:1980,fredkin1982conservative}. More
recently, the rising importance of energy conservation, the shrinking
size of technology at which quantum effects become noticeable, and the
potential for quantum computation and communication, are additional
physical considerations adding momentum to such reversible
computational
models~\citep{Frank:1999:REC:930275,DeBenedictis:2005:RLS:1062261.1062325}. From
a more theoretical perspective, the recently proposed ``univalent''
foundation of mathematics~\citep{hottbook}, based on Homotopy Type
Theory (HoTT), greatly emphasizes computation based on
\emph{equivalences} that are satisfied up to equivalences that are
themselves satisfied up to equivalence, etc.

To summarize, we are witnessing a convergence of ideas from several
distinct research communities (physics, mathematics, and computer
science) towards basing computations on
equivalences~\citep{baez2011physics}. A first step in that direction
was the development of many \emph{reversible programming
  languages}~(e.g.,
\citep{Yokoyama:2007:RPL:1244381.1244404,Mackie2011,DiPierro:2006:RCL:1166042.1166047,Kluge:1999:SEMCD,Mu:2004:ILRC,abramsky2005structural}.)
Typically, programs in these languages correspond to some notion of
equivalence. But reasoning \emph{about} these programs abandons the
notion of equivalence and uses conventional irreversible functions to
specify evaluators and the derived notions of program
equivalence. This unfortunately misses the beautiful combinatorial
structure of programs and proofs that was first exposed in the
historical paper by \citet{Hofmann96thegroupoid} and that is currently
the center of attention of HoTT and that requires keeping the focus on
equivalences not only at the conventional level of programs but also
at the higher levels of programs manipulating equivalences about other
programs. 

This paper addresses --- and completely solves --- a well-defined part
of the general problem of programming with equivalences up to
equivalences. Our approach, we argue, might also be suitable for the
more general problem. The particular problem we focus on is that of
programming with the finite types built from the empty type, the unit
type, and closed under sums and products. Although limited in their
expressive power, these types are rich enough to express all
combinational (with no state or feedback) hardware circuits and as we
show already exhibit substantial combinatorial structure at the ``next
level'', i.e., at the level of equivalences about equivalences of
types. What emerges from our study are the following results:
\begin{itemize}
\item a universal language for combinational reversible circuits that
  comes with a calculus for writing circuits and a calculus for
  manipulating that calculus;
\item the language itself subsumes various representations for
  reversible circuits, e.g., truth tables, matrices, product of
  permutation cycles, etc.~\citep{Saeedi:2013:SOR:2431211.2431220};
\item the first set of rules is sound and complete with respect to 
  equivalences of types;
\item the second set of rules is sound and complete with respect to
  equivalences of equivalences of types as specified by the first set
  of rules.
\end{itemize}

\paragraph*{Outline.} The next section reviews equivalences between
finite types and relates them to various commutative semiring
structures. The main message of that section is that, up to
equivalence, the concept of equivalence of finite types is equivalent
to permutations between finite sets. The latter is computationally
well-behaved with existing reversible programming languages developed
for programming with permutations and finite-type isomorphisms. This
family of languages, called $\Pi$, is universal for describing
combinational reversible circuits (see Sec.~\ref{sec:3}). The
infrastructure of the HoTT-inspired type equivalences enriches these
languages by viewing their original design as 1-paths and
systematically producing 2-paths (equivalences between equivalences)
manifesting themselves as syntactic rules for reasoning about
equivalences of programs representing reversible
circuits. Sec.~\ref{sec:4} starts the semantic investigation of the
$\Pi$ languages emphasizing the denotational approach that maps each
$\Pi$ program to a type equivalence or a permutation. The section also
gives a small example showing how a few rules that are sound with
respect to equivalence of permutations can be used to transform $\Pi$
programs without reliance on any extensional
reasoning. Sec.~\ref{sec:5} then reveals that these rules are
intimately related to the coherence conditions of the categorified
analogues of type equivalences and permutations, namely, the so-called
\emph{symmetric rig weak groupoids}. Sec.~\ref{sec:6} contains that
``punchline'': a sound and complete set of rules that can be used to
reason about $\Pi$ programs and their equivalences. Before concluding,
we devote Sec.~\ref{sec:7} to a detailed analysis of higher-order
functions in the setting we describe suggesting a possible path
towards a solution. We note that because the issues involved are quite
subtle, the paper is the ``unformalization'' of an executable
\texttt{Agda 2.4.2.3} package with the global \AgdaComment{without-K}
option enabled.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Equivalences and Commutative Semirings} 
\label{sec:2}

Our starting point is the notion of equivalence of types. We then
connect this notion to several semiring structures on finite types, on
permutations, and on equivalences, with the goal of reducing the
notion of equivalence for finite types to a notion of reversible
computation.

%%%%%%%%%%%%
\subsection{Finite Types}

The elementary building blocks of type theory are the empty type
($\bot$), the unit type ($\top$), and the sum ($\uplus$) and product
($\times$) types. These constructors can encode any \emph{finite
  type}. Traditional type theory also includes several facilities for
building infinite types, most notably function types. We will however
not address infinite types in this paper except for a discussion in
Sec.~\ref{intc}. We will instead focus on thoroughly understanding the
computational structures related to finite types.

An essential property of a finite type $A$ is its size $|A|$ which is
defined as follows:
\[\begin{array}{rcl}
|\bot| &=& 0 \\
|\top| &=& 1 \\
|A \uplus B| &=& |A| + |B| \\
|A \times B| &=& |A| * |B| 
\end{array}\] 
A result by \citet{Fiore:2004,fiore-remarks} completely characterizes
the isomorphisms between finite types using the axioms of commutative
semirings.\footnote{Appendix~\ref{sec:commrig} recalls the
  definition.}  Intuitively this result states that one can interpret
each type by its size, and that this identification validates the
familiar properties of the natural numbers, and is in fact isomorphic
to the commutative semiring of the natural numbers.

Our work builds on this identification together with work by
\citet{James:2012:IE:2103656.2103667} which introduced the $\Pi$
family of languages whose core computations are these isomorphisms
between finite types. Taking into account the growing-in-importance
idea that isomorphisms have interesting computational content and
should not be silently or implicitly identified, we first recast Fiore
et. al's result in the next section, making explicit that the
commutative semiring structure can be defined up to the HoTT relation
of \emph{type equivalence} instead of strict equality~$=$.

%%%%%%%%%%%%
\subsection{Commutative Semirings of Types}

There are several equivalent definitions of the notion of equivalence
of types. For concreteness, we use the following definition. 

\begin{definition}[Quasi-inverse]
\label{def:quasi}
For a function $f : A \rightarrow B$, a \emph{quasi-inverse} is a
triple $(g, \alpha, \beta)$, consisting of a function
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
(and hence for $g$) and one that uses boolean negation for $f$ (and
hence for $g$). These two equivalences are themselves \emph{not}
equivalent: each of them can be used to ``transport'' properties of
\AgdaDatatype {Bool} in a different way.

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

%% \jc{Do we want to have a bunch of appendices, or perhaps a web
%% link, to all the Agda code which formalizes all of this?}

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
$\textsc{eq}_{\AgdaDatatype {Bool},\AgdaDatatype  {Bool}}$ has two
elements corresponding to the $\mathrm{id}$-equivalence and to the
negation-equivalence that were mentioned before. More generally, 
for finite types $A$ and $B$,
the type $\textsc{eq}_{A,B}$ is only inhabited if $A$ and~$B$ have the
same size in which case the type has $|A|~!$ (factorial of the size of
$A$) elements witnessing the various possible identifications of $A$
and $B$. The type of all equivalences has some non-trivial structure:
in particular, it is itself a commutative semiring.

\begin{theorem}
\label{thm:eqeq}
  The type of all equivalences $\textsc{eq}_{A,B}$ for finite types
  $A$ and $B$ forms a commutative semiring up to extensional
  equivalence of equivalences.
\end{theorem}
\begin{proof}
  The most important insight is the definition of equivalence of
  equivalences. Two equivalences $e_1, e_2 : \textsc{eq}_{A,B}$ with
  underlying functions $f_1$ and $f_2$ and underlying quasi-inverses
  $g_1$ and $g_2$ are themselves equivalent if we have that both
  $f₁ = f₂$ and $g₁ = g₂$ extensionally. Given this notion of
  equivalence of equivalences, the proof proceeds smoothly with the
  additive unit being the vacuous equivalence $\bot \simeq \bot$, the
  multiplicative unit being the trivial equivalence
  $\top \simeq \top$, and the two binary operations being essentially
  a mapping of $\uplus$ and $\times$ over equivalences.
\end{proof}

We reiterate that the commutative semiring axioms in this case are
satisfied up to extensional equality of the functions underlying the
equivalences.  We could, in principle, consider a weaker notion of
equivalence of equivalences and attempt to iterate the construction
but for the purposes of modeling circuits and optimizations, it is
sufficient to consider just one additional level.

%%%%%%%%%%%%
\subsection{Commutative Semirings of Permutations}

Type equivalences are fundamentally based on function extensionality.
(Def.~\ref{def:quasi} explicitly compares functions for extensional
equality.) It is folklore that, even when restricted to finite types,
function extensionality needs to be assumed for effective reasoning
about type equivalences. The situation gets worse when considering
equivalences of equivalences. In the HoTT context, this is the open
problem of finding a computational interpretation for
\emph{univalence}. In the case of finite types however, there is a
computationally-friendly alternative characterization of type
equivalences based on permutations of finite sets, which we prove to
be formally equivalent.

The idea is that, \emph{up to equivalence}, the only interesting property of
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
  are done. The interesting situation is when $m = \mathit{suc}~m'$
  and $n = \mathit{suc}~n'$. The result follows in this case by
  induction assuming we can establish that the equivalence between $A$
  and $B$, i.e., the equivalence between
  $\mathsf{Fin}~(\mathit{suc}~m')$ and
  $\mathsf{Fin}~(\mathit{suc}~n')$, implies an equivalence between
  $\mathsf{Fin}~m'$ and $\mathsf{Fin}~n'$. In a constructive setting,
  we actually need to construct a particular equivalence between the
  smaller sets given the equivalence of the larger sets with one
  additional element. This lemma is quite tedious as it requires us to
  isolate one element of $\mathsf{Fin}~(\mathit{suc}~m')$ and analyze
  every class of positions this element could be mapped to by the
  larger equivalence and in each case construct an equivalence that
  excludes it.
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
  first two components are (i) a vector of size $n$ containing
  elements drawn from the finite set $\mathsf{Fin}~m$, and (ii) a dual
  vector of size $m$ containing elements drawn from the finite set
  $\mathsf{Fin}~n$. Each of these vectors can be interpreted as a map
  $f$ that acts on the incoming finite set sending the element at
  index $i$ to position $f !! i$ in the resulting finite set. To
  guarantee that these maps define an actual permutation, the last two
  components are proofs that the sequential composition of the maps in
  both directions produce the identity. Given this representation, we
  can prove that two permutations are equal if the underlying vectors
  are strictly equal. The proof proceeds using the vacuous permutation
  $\mathsf{CPerm}~0~0$ for the additive unit and the trivial
  permutation $\mathsf{CPerm}~1~1$ for the multiplicative unit. The
  binary operations on permutations map $\mathsf{CPerm}~m₁~m₂$ and
  $\mathsf{CPerm}~n₁~n₂$ to $\mathsf{CPerm}~(m₁+n₁)~(m₂+n₂)$ and
  $\mathsf{CPerm}~(m₁*n₁)~(m₂*n₂)$ respectively. Their definition
  relies on the important property that the union or product of
  vectors denoting permutations distributes over the sequential
  composition of permutations.
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
\begin{proof}
  In the process of this proof, we show that every axiom of semirings
  of types is an equivalence, and thus corresponds to a permutation.
  Some of the axioms like the associativity of sums gets mapped to the
  trivial identity permutation.  However, some are axioms reveal
  interesting structure as permutations; the most notable is that the
  commutativity of products maps to a permutation solving the
  classical problem of in-place matrix transposition.
\end{proof}

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
\label{sec:3}

In the previous section, we argued that, up to equivalence, the
equivalence of types reduces to permutations on finite sets. We recall
background work which proposed a term language for permutations and
adapt it in later sections to be used to express, compute with, and
reason about type equivalences between finite types.

\begin{figure*}[ht]
\[\begin{array}{cc}
\begin{array}{rrcll}
\identlp :&  0 + \tau & \iso & \tau &: \identrp \\
\swapp :&  \tau_1 + \tau_2 & \iso & \tau_2 + \tau_1 &: \swapp \\
\assoclp :&  \tau_1 + (\tau_2 + \tau_3) & \iso & (\tau_1 + \tau_2) + \tau_3 &: \assocrp \\
\\
\identlt :&  1 * \tau & \iso & \tau &: \identrt \\
\swapt :&  \tau_1 * \tau_2 & \iso & \tau_2 * \tau_1 &: \swapt \\
\assoclt :&  \tau_1 * (\tau_2 * \tau_3) & \iso & (\tau_1 * \tau_2) * \tau_3 &: \assocrt \\
\\
\distz :&~ 0 * \tau & \iso & 0 ~ &: \factorzl \\
\dist :&~ (\tau_1 + \tau_2) * \tau_3 & \iso & (\tau_1 * \tau_3) + (\tau_2 * \tau_3)~ &: \factor
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
\caption{$\Pi$-combinators~\citep{rc2011,James:2012:IE:2103656.2103667}
\label{pi-combinators}}
\end{figure*}

%%%%%%%%%%%%
\subsection{The $\Pi$-Languages}

\citet{rc2011,James:2012:IE:2103656.2103667} introduced the~$\Pi$
family of languages whose only computations are permutations
(isomorphisms) between finite types and which is complete for all
reversible combinational circuits. We propose that this family of
languages is exactly the right programmatic interface for manipulating
and reasoning about type equivalences.

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
\emph{combinators} which are witnesses for type isomorphisms
$\tau_1 \iso \tau_2$. They consist of base combinators (on the left
side of Fig.~\ref{pi-combinators}) and compositions (on the right side
of the same figure). Each line of the figure on the left introduces a
pair of dual constants\footnote{where $\swapp$ and $\swapt$ are
  self-dual.}  that witness the type isomorphism in the middle. Every
combinator $c$ has an inverse $!c$ according to the figure. The
inverse is homomorphic on sums and products and flips the order of the
combinators in sequential composition.

%%%%%%%%%%%%
\subsection{Example Circuits}
\label{sec:circuits}

The language $\Pi$ is universal for reversible combinational
circuits~\citep{James:2012:IE:2103656.2103667}.\footnote{With the
  addition of recursive types and trace
  operators~\citep{Hasegawa:1997:RCS:645893.671607}, $\Pi$ become a
  Turing complete reversible
  language~\citep{James:2012:IE:2103656.2103667,rc2011}.} We
illustrate the expressiveness of the language with a few short
examples.

The first example is simply boolean encoding and negation which can
defined as shown on the left and visualized as a permutation on the right:

\smallskip

\begin{tabular}{cc}
\begin{minipage}{0.25\textwidth}
\begin{code}
BOOL : U
BOOL = PLUS ONE ONE

NOT₁ : BOOL ⟷ BOOL
NOT₁ = swap₊
\end{code}
\end{minipage}
& 
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
\end{tabular}

\smallskip  
 
Naturally there are many ways of encoding boolean negation. The
following combinator implements a more convoluted circuit that
computes the same function, which is also visualized as a permutation
on finite sets:

\begin{tabular}{cc}
\begin{minipage}{0.25\textwidth}
\begin{code}
NOT₂ : BOOL ⟷ BOOL
NOT₂ =
  uniti⋆ ◎
  swap⋆ ◎
  (swap₊ ⊗ id⟷) ◎
  swap⋆ ◎
  unite⋆
\end{code}
\end{minipage}
& 
\begin{tikzpicture}[scale=0.33,every node/.style={scale=0.33}]
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
\end{tabular}

Writing circuits using the raw syntax for combinators is clearly
tedious. In other work, one can find a compiler from a conventional
functional language to generate the
circuits~\citep{James:2012:IE:2103656.2103667}, a systematic technique
to translate abstract machines to $\Pi$~\citep{rc2012}, and a
Haskell-like surface language~\citep{theseus} which can be of help in
writing circuits. These essential tools are however a distraction in
the current setting and we content ourselves with some Agda syntactic
sugar illustrated below and used again in the next section:

\smallskip

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

\smallskip

This style makes the intermediate steps explicit showing how the types
are transformed in each step by the combinators. The example confirms
that $\Pi$ is universal for reversible circuits since the Toffoli gate
is universal for such circuits~\citep{Toffoli:1980}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Semantics}
\label{sec:4}

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
evaluators can be found in the papers by
\citet{rc2011,rc2012,James:2012:IE:2103656.2103667} and in the
accompanying Agda code and will not be repeated here. The reason is
that, although these evaluators adequately serve as semantic
specifications, they drive the development towards extensional
reasoning as evident from the signatures which map a permutation to a
function. We will instead pursue a denotational approach mapping the
combinators to type equivalences or equivalently to permutations:

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
\label{sec:rewriting}

Having mapped each combinator to a permutation, we can reason about
valid optimizations mapping a combinator to another by studying the
equivalence of permutations on finite sets. The definition of
equivalence might also equate two permutations if their actions on
every input produce the same output but we again resist that
extensional reasoning. Instead we are interested in a calculus, a set
of rules, that can be used to rewrite combinators preserving their
meaning. It is trivial to come up with a few rules such as:

\AgdaHide{
\begin{code} 
module X where
 data _⇔'_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
\end{code}
}

\smallskip 

\begin{code}
  id⇔     :  {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔' c 

  trans⇔  :  {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
    (c₁ ⇔' c₂) → (c₂ ⇔' c₃) → (c₁ ⇔' c₃) 

  assoc⇔  :  {t₁ t₂ t₃ t₄ : U}
    {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
    (c₁ ◎ (c₂ ◎ c₃)) ⇔' ((c₁ ◎ c₂) ◎ c₃)

  id◎⇔    :  {t₁ t₂ : U} {c : t₁ ⟷ t₂} → 
    (id⟷ ◎ c) ⇔' c

  swap₊⇔  :  {t₁ t₂ t₃ t₄ : U} 
    {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
    (swap₊ ◎ (c₁ ⊕ c₂)) ⇔' ((c₂ ⊕ c₁) ◎ swap₊)

\end{code}

\smallskip 
\noindent which are evidently sound. The challenge of course is to
come up with a sound and complete set of such rules.

Before we embark on the categorification program in the next section,
we show that, with some ingenuity, one can develop a reasonable set of
rewrite rules that would allow us to prove that the two negation
circuits from the previous section are actually equivalent:

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

\smallskip

The sequence of rewrites can be visualized in Appendix~\ref{app:opt}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Categorification}
\label{sec:5}

The problem of finding a sound and complete set of rules for reasoning
about equivalence of permutations is solved by appealing to various
results about specialized monoidal
categories~\citep{selinger-graphical}. The main technical vehicle is
that of \emph{categorification}~\citep{math/9802029} which is a
process, intimately related to homotopy theory, for finding
category-theoretic analogs of set-theoretic concepts. From an
intuitive perspective, the algebraic structure of a commutative
semiring only captures a ``static'' relationship between types; it
says nothing about how these relationships behave under
\emph{composition} which is after all the essence of computation
(cf. \citet{Moggi:1989:CLM:77350.77353}'s original paper on
monads). Thus from a programmer's perspective, this categorification
process is about understanding how type equivalences evolve under
compositions, e.g., how two different paths of type equivalences
sharing the same source and target relate two each other.

\begin{figure*}
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
\qquad\qquad\qquad
\begin{tikzcd}[column sep=tiny]
(A \otimes I) \otimes B
  \arrow[rr, "\alpha"]
  \arrow[dr, "\rho_A \otimes \mathrm{id}_B"']
&& A \otimes (I \otimes B)
  \arrow[dl, "\mathrm{id}_A \otimes \lambda_B"]
\\
& A \otimes B
\end{tikzcd}
\caption{\label{fig:mon}Pengaton and Triangle Diagrams}
\end{figure*}

%%%%%%%%%%%%
\subsection{Monoidal Categories} 

We begin with the conventional definitions for monoidal and symmetric
monoidal categories. 

\begin{definition}[Monoidal Category]
\label{ch:pi:def:MC}
A \emph{monoidal category}~\citep{nla.cat-vn1051288} is a category
with the following additional structure:
\begin{itemize}
\item a bifunctor $\otimes$ called the monoidal or tensor product,
\item an object $I$ called the unit object, and
\item natural isomorphisms
  $\alpha_{A,B,C} : (A \otimes B) \otimes C \isoarrow A \otimes (B
  \otimes C)$,
  $\lambda_A : I \otimes A \isoarrow A$, and
  $\rho_A : A \otimes I \isoarrow A$, such that the two diagrams
  (known as the \emph{associativity pentagon} and the \emph{triangle
    for unit}) in Fig.~\ref{fig:mon} commute.
\end{itemize}
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

According to Mac Lane's coherence theorem, the coherence laws for
monoidal categories are justified by the desire to equate any two
isomorphisms built using $\sigma$, $\lambda$, and $\rho$ and having
the same source and target. Similar considerations justify the
coherence laws for symmetric monoidal categories. It is important to
note that the coherence conditions do \emph{not} imply that every pair
of parallel morphisms with the same source and target are
equal. Indeed, as Dosen and Petric explain:
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
  groups~\citep{coherence}.
\end{quote} 
The informal idea was already silently used in the examples in
Sec.~\ref{sec:circuits} in which the types were named \AgdaFunction{x}
and \AgdaFunction{y} during the derivation to distinguish operations
that would otherwise be ambiguous if all the types were instantiated
with \AgdaInductiveConstructor{ONE}.

From a different perspective, \citet{math/9802029} explain the source
of these coherence laws as arising from homotopy theory. In this
theory, laws are only imposed up to homotopy with these homotopies
satisfying certain laws, up again only up to homotopy, with these
higher homotopies satisfying their own higher coherence laws, and so
on. Remarkably, they report, among other results, that the pentagon
identity of Fig.~\ref{fig:mon} arises when studying the algebraic
structure possessed by a space that is homotopy equivalent to a loop
space and that the hexagon identity arises in the context of spaces
homotopy equivalent to double loop spaces.

In our context, we will build monoidal categories where the objects
are finite types and the morphisms are reversible circuits represented
as $\Pi$-combinators. Clearly not all reversible circuits mapping
\AgdaDatatype{Bool} to \AgdaDatatype{Bool} are equal. There are at
least two distinct such circuits: the identity and boolean
negation. The coherence laws should not equate these two morphisms and
they do not. We might also hope that the two versions of boolean
negation in Sec.~\ref{sec:circuits} and Sec.~\ref{sec:rewriting} could
be identified using the coherence conditions of monoidal
categories. This will be the case but, for that, we need categories
that are richer than the symmetric monoidal categories which are only
categorifications of commutative monoids. We will need to consider the
categorification of commutative semirings.

%%%%%%%%%%%%
\subsection{Symmetric Rig Weak Groupoids}

The categorification of a commutative semiring is called a
\emph{symmetric rig category}.  It is build from a \emph{symmetric
  bimonoidal category} to which distributivity natural isomorphisms
are added, and accompanying coherence laws added.  Since we can easily
set things up so that every morphism is a isomorphism, the category
will also be a groupoid. Since the laws of the category only hold up
to a higher equivalence, the entire setting is that of weak categories.

There are several equivalent definitions of rig categories. We use the
following definition from \citet{nlabrig}.

\begin{definition}[Rig Category]
  A \emph{rig category} $C$ is a category with a symmetric monoidal
  structure $(C,\oplus,0)$ for addition and a monoidal structure
  $(C,\otimes,1)$ for multiplication together with left and right
  distributivity natural isomorphisms:
\[\begin{array}{rcl}
d_ℓ : x ⊗ (y ⊕ z) &\isoarrow& (x ⊗ y) ⊕ (x ⊗ z) \\
d_r : (x ⊕ y) ⊗ z &\isoarrow& (x ⊗ z) ⊕ (y ⊗ z) 
\end{array}\]
and absorption/annihilation isomorphisms:
\[\begin{array}{rcl}
a_ℓ : x ⊗ 0 &\isoarrow& 0 \\
a_r : 0 ⊗ x &\isoarrow& 0
\end{array}\]
satisfying coherence conditions worked out by \citet{laplaza}
and discussed below. 
\end{definition}

\begin{definition}[Symmetric Rig Category]
A \emph{symmetric rig category} is a rig category in which the 
multiplicative structure is symmetric. 
\end{definition}

\begin{definition}[Symmetric Rig Groupoid]
A \emph{symmetric rig groupoid} is a symmetric rig category in which
every morphism is invertible.
\end{definition}

The coherence conditions for rig categories were first worked out by
\citet{laplaza}. Pages 31-35 of his paper report 24 coherence
conditions that vary from simple diagrams to one that includes 9 nodes
showing that two distinct ways of simplifying $(A ⊕ B) ⊗ (C ⊕ D)$ to
$(((A ⊗ C) ⊕ (B ⊗ C)) ⊕ (A ⊗ D)) ⊕ (B ⊗ D)$ commute. The 24 coherence
conditions are not independent which somewhat simplifies the situation
and allows us to prove that our structures satisfy the coherence
conditions in a more economic way. 

% \begin{figure*}
% \AgdaHide{
% \begin{code}
% open import Level using (zero; suc)
% import Relation.Binary.PropositionalEquality as P
% open import Relation.Binary using (Rel)
% open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
% open import Data.Product using (_,_; proj₁; proj₂;_×_; Σ) renaming (map to map×)
% open import Data.Unit
% open import Data.Empty
% import Function as F

% open import Categories.Category
% open import Categories.Groupoid
% open import Categories.Monoidal
% open import Categories.Monoidal.Helpers
% open import Categories.Bifunctor
% open import Categories.NaturalIsomorphism
% open import Categories.Monoidal.Braided
% open import Categories.Monoidal.Symmetric
% open import Categories.RigCategory

% open import Equiv
% open import TypeEquiv hiding (swap₊)
% open import Data.Sum.Properties
% open import Data.SumProd.Properties

% -- see EquivSetoid for some additional justification
% -- basically we need g to "pin down" the inverse, else we
% -- get lots of unsolved metas.
% record _≋_ {A B : Set} (eq₁ eq₂ : A ≃ B) : Set where
%   constructor eq
%   field
%     f≡ : ∀ x → eq₁ ⋆ x P.≡ eq₂ ⋆ x
%     g≡ : ∀ x → (sym≃ eq₁) ⋆ x P.≡ (sym≃ eq₂) ⋆ x
 
% id≋ : ∀ {A B : Set} {x : A ≃ B} → x ≋ x
% id≋ = record { f≡ = λ x → P.refl ; g≡ = λ x → P.refl }

% sym≋ : ∀ {A B : Set} {x y : A ≃ B} → x ≋ y → y ≋ x
% sym≋ (eq f≡ g≡) = eq (λ a → P.sym (f≡ a)) (λ b → P.sym (g≡ b))

% flip≋ : {A B : Set} {x y : A ≃ B} → x ≋ y → (sym≃ x) ≋ (sym≃ y)
% flip≋ (eq f≡ g≡) = eq g≡ f≡

% trans≋ : ∀ {A B : Set} {x y z : A ≃ B} → x ≋ y → y ≋ z → x ≋ z
% trans≋ (eq f≡ g≡) (eq h≡ i≡) =
%    eq (λ a → P.trans (f≡ a) (h≡ a)) (λ b → P.trans (g≡ b) (i≡ b))

% ●-resp-≋ : {A B C : Set} {f h : B ≃ C} {g i : A ≃ B} → f ≋ h → g ≋ i →
%   (f ● g) ≋ (h ● i)
% ●-resp-≋ {f = f , _} {_ , mkqinv h⁻¹ _ _} {_ , mkqinv g⁻¹ _ _} {i , _}
%   (eq f≡ g≡) (eq h≡ i≡) =
%   eq (λ x → P.trans (P.cong f (h≡ x)) (f≡ (i x)))
%      (λ x → P.trans (P.cong g⁻¹ (g≡ x)) (i≡ (h⁻¹ x)))

% -- underlying it all, it uses ∘ and ≡ 
% ●-assoc : {A B C D : Set} {f : A ≃ B} {g : B ≃ C} {h : C ≃ D} →
%       ((h ● g) ● f) ≋ (h ● (g ● f))
% ●-assoc = eq (λ x → P.refl) (λ x → P.refl)
% \end{code}
% }
% \begin{code}
% TypeEquivCat : Category (Level.suc Level.zero) Level.zero Level.zero -- omitted
% \end{code}
% \AgdaHide{
% \begin{code}
% TypeEquivCat = record
%   { Obj = Set
%   ; _⇒_ = _≃_
%   ; _≡_ = _≋_
%   ; id = id≃
%   ; _∘_ = _●_
%   ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → ●-assoc {A} {B} {C} {D} {f} {g} {h}
%   ; identityˡ = eq (λ _ → P.refl) (λ _ → P.refl)
%   ; identityʳ = eq (λ _ → P.refl) (λ _ → P.refl)
%   ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ }
%   ; ∘-resp-≡ = ●-resp-≋
%   }
% \end{code}
% }
% \begin{code}

% TypeEquivGroupoid : Groupoid TypeEquivCat
% TypeEquivGroupoid = record 
%   { _⁻¹     = sym≃ 
%   ; iso     = λ  { {_} {_} {f , mkqinv g α β} → record {
%                     isoˡ  = eq β β
%                  ;  isoʳ  = eq α α }}}

% \end{code}
% \AgdaHide{
% \begin{code}
% ⊎-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
% ⊎-bifunctor = record
%   { F₀ = λ {( x , y) → x ⊎ y}
%   ; F₁ = λ {(x , y) → path⊎ x y}
%   ; identity = eq map⊎idid≡id map⊎idid≡id
%   ; homomorphism = eq map⊎-∘ map⊎-∘
%   ; F-resp-≡ = λ { (e₁ , e₂) → eq (map⊎-resp-≡ {e₁ = f≡ e₁} {f≡ e₂}) (map⊎-resp-≡ {e₁ =  g≡ e₁} {g≡ e₂}) }
%   }
%   where open _≋_
  
% module ⊎h = MonoidalHelperFunctors TypeEquivCat ⊎-bifunctor ⊥

% 0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
% 0⊎x≡x = record 
%   { F⇒G = record
%     { η = λ X → unite₊equiv
%     ; commute = λ f → eq unite₊∘[id,f]≡f∘unite₊ (λ x → P.refl) } 
%   ; F⇐G = record
%     { η = λ X → uniti₊equiv
%     ; commute = λ f → eq (λ x → P.refl) (sym∼ unite₊∘[id,f]≡f∘unite₊) } 
%   ; iso = λ X → record
%     { isoˡ = eq inj₂∘unite₊~id inj₂∘unite₊~id
%     ; isoʳ = eq (λ _ → P.refl) (λ _ → P.refl)
%     }
%   }

% x⊎0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
% x⊎0≡x = record
%   { F⇒G = record
%     { η = λ X → unite₊′equiv
%     ; commute = λ f → eq unite₊′∘[id,f]≡f∘unite₊′ (λ x → P.refl)
%     }
%   ; F⇐G = record
%     { η = λ X → uniti₊′equiv
%     ; commute = λ f → eq (λ x → P.refl) f∘unite₊′≡unite₊′∘[f,id]
%     }
%   ; iso = λ X → record
%     { isoˡ = eq inj₁∘unite₊′~id inj₁∘unite₊′~id
%     ; isoʳ = eq (λ x → P.refl) (λ x → P.refl)
%     }
%   }

% [x⊎y]⊎z≡x⊎[y⊎z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
% [x⊎y]⊎z≡x⊎[y⊎z] = record
%   { F⇒G = record
%     { η = λ X → assocr₊equiv
%     ; commute = λ f → eq assocr₊∘[[,],] [[,],]∘assocl₊
%     }
%   ; F⇐G = record
%     { η = λ X → assocl₊equiv
%     ; commute = λ f → eq (sym∼ [[,],]∘assocl₊) (sym∼ assocr₊∘[[,],])
%     }
%   ; iso = λ X → record
%     { isoˡ = eq (p∘!p≡id {p = assocr₊equiv}) (p∘!p≡id {p = assocr₊equiv})
%     ; isoʳ = eq ((p∘!p≡id {p = assocl₊equiv})) ((p∘!p≡id {p = assocl₊equiv}))
%     }
%   }
% \end{code}
% }
% \begin{code}
% CPM⊎    : Monoidal TypeEquivCat -- omitted
% \end{code}
% \AgdaHide{
% \begin{code}
% CPM⊎ = record
%   { ⊗ = ⊎-bifunctor
%    ; id = ⊥
%    ; identityˡ = 0⊎x≡x
%    ; identityʳ = x⊎0≡x
%    ; assoc = [x⊎y]⊎z≡x⊎[y⊎z]
%    ; triangle = eq triangle⊎-right triangle⊎-left
%    ; pentagon = eq pentagon⊎-right pentagon⊎-left
%    }

% -------
% -- and below, we will have a lot of things which belong in
% -- Data.Product.Properties.  In fact, some of them are ``free'',
% -- in that β-reduction is enough.  However, it might be a good
% -- idea to fully mirror all the ones needed for ⊎.


% path×-resp-≡ : {A B C D : Set} → {f₀ g₀ : A → B} {f₁ g₁ : C → D} →
%   {e₁ : f₀ ∼ g₀} → {e₂ : f₁ ∼ g₁} →  
%   (x : A × C) → (f₀ (proj₁ x) , f₁ (proj₂ x)) P.≡
%                 (g₀ (proj₁ x) , g₁ (proj₂ x))
% path×-resp-≡ {e₁ = f≡} {h≡} (a , c) = P.cong₂ _,_ (f≡ a) (h≡ c)

% ×-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
% ×-bifunctor = record
%   { F₀ = λ {( x , y) → x × y}
%   ; F₁ = λ {(x , y) → path× x y }
%   ; identity = eq (λ x → P.refl) (λ x → P.refl) -- η for products gives this
%   ; homomorphism = eq (λ x → P.refl) (λ x → P.refl) -- again η for products!
%   ; F-resp-≡ = λ { (e₁ , e₂) → eq (path×-resp-≡ {e₁ = f≡ e₁} {f≡ e₂}) ((path×-resp-≡ {e₁ = g≡ e₁} {g≡ e₂}))}
%   }
%   where open _≋_

% module ×h = MonoidalHelperFunctors TypeEquivCat ×-bifunctor ⊤

% -- again because of η for products, lots of the following have trivial proofs
% 1×y≡y : NaturalIsomorphism ×h.id⊗x ×h.x
% 1×y≡y = record
%   { F⇒G = record
%     { η = λ X → unite⋆equiv
%     ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl)
%     }
%   ; F⇐G = record
%     { η = λ X → uniti⋆equiv
%     ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl)
%     }
%   ; iso = λ X → record
%     { isoˡ = eq (λ x → P.refl) (λ x → P.refl)
%     ; isoʳ = eq (λ x → P.refl) (λ x → P.refl)
%     }
%   }

% y×1≡y : NaturalIsomorphism ×h.x⊗id ×h.x
% y×1≡y = record
%   { F⇒G = record 
%     { η = λ X → unite⋆′equiv 
%     ;  commute = λ f → eq (λ x → P.refl) (λ x → P.refl) 
%     }
%   ; F⇐G = record 
%     { η = λ X → uniti⋆′equiv 
%     ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl) 
%     }
%   ; iso = λ X → record 
%     { isoˡ = eq (λ x → P.refl) (λ x → P.refl) 
%     ; isoʳ = eq (λ x → P.refl) (λ x → P.refl) 
%     }
%   }

% [x×y]×z≡x×[y×z] : NaturalIsomorphism ×h.[x⊗y]⊗z ×h.x⊗[y⊗z]
% [x×y]×z≡x×[y×z] = record
%   { F⇒G = record
%     { η = λ X → assocr⋆equiv
%     ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl) }
%   ; F⇐G = record
%     { η = λ X → assocl⋆equiv
%     ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl) }
%   ; iso = λ X → record
%     { isoˡ = eq (λ x → P.refl) (λ x → P.refl)
%     ; isoʳ = eq (λ x → P.refl) (λ x → P.refl) }
%   }
% \end{code}
% }
% \begin{code}
% CPM×    : Monoidal TypeEquivCat -- omitted
% \end{code}
% \AgdaHide{
% \begin{code}
% CPM× = record
%   { ⊗ = ×-bifunctor
%   ; id = ⊤
%   ; identityˡ = 1×y≡y
%   ; identityʳ = y×1≡y
%   ; assoc = [x×y]×z≡x×[y×z]
%   ; triangle = eq (λ x → P.refl) (λ x → P.refl)
%   ; pentagon = eq (λ x → P.refl) (λ x → P.refl)
%   }

% x⊎y≈y⊎x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
% x⊎y≈y⊎x = record 
%   { F⇒G = record 
%     { η = λ X → swap₊equiv 
%     ; commute = λ f → eq swap₊∘[f,g]≡[g,f]∘swap₊ (sym∼ swap₊∘[f,g]≡[g,f]∘swap₊) 
%     } 
%   ; F⇐G = record 
%     { η = λ X → swap₊equiv 
%     ; commute = λ f → eq swap₊∘[f,g]≡[g,f]∘swap₊ (sym∼ swap₊∘[f,g]≡[g,f]∘swap₊) 
%     } 
%   ; iso = λ X → record -- cheat by using the symmetric structure
%     { isoˡ = eq swapswap₊ swapswap₊ 
%     ; isoʳ = eq swapswap₊ swapswap₊ 
%     }
%   }
% \end{code}
% }
% \begin{code}

% BM⊎       : Braided CPM⊎ -- omitted
% \end{code}
% \AgdaHide{
% \begin{code}
% BM⊎ = record 
%   { braid = x⊎y≈y⊎x 
%   ; hexagon₁ = eq hexagon⊎-right hexagon⊎-left 
%   ; hexagon₂ = eq hexagon⊎-left hexagon⊎-right 
%   }

% x×y≈y×x : NaturalIsomorphism ×h.x⊗y ×h.y⊗x
% x×y≈y×x = record
%   { F⇒G = record
%     { η = λ X → swap⋆equiv
%     ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl)
%     }
%   ; F⇐G = record
%     { η = λ X → swap⋆equiv
%     ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl)
%     }
%   ; iso = λ X → record -- cheat by using the symmetric structure
%     { isoˡ = eq swapswap⋆ swapswap⋆
%     ; isoʳ = eq swapswap⋆ swapswap⋆
%     }
%   }
% \end{code}
% }
% \begin{code}
% BM×       : Braided CPM× -- omitted
% \end{code}
% \AgdaHide{
% \begin{code}
% BM× = record 
%   { braid = x×y≈y×x 
%   ; hexagon₁ = eq (λ x → P.refl) (λ x → P.refl) 
%   ; hexagon₂ = eq (λ x → P.refl) (λ x → P.refl) 
%   }
% \end{code}
% }
% \begin{code}

% SBM⊎    : Symmetric BM⊎ 
% SBM⊎    = record { symmetry = eq swapswap₊ swapswap₊ }

% SBM×    : Symmetric BM× 
% SBM×    = record { symmetry = eq swapswap⋆ swapswap⋆ }

% \end{code}
% \AgdaHide{
% \begin{code}
% module r = BimonoidalHelperFunctors BM⊎ BM×

% x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
% x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record
%   { F⇒G = record
%     { η = λ X → distlequiv
%     ; commute = λ f → eq distl-commute (λ x → P.sym (factorl-commute x))
%     }
%   ; F⇐G = record
%     { η = λ X → factorlequiv
%     ; commute = λ f → eq factorl-commute (λ x → P.sym (distl-commute x))
%     }
%   ; iso = λ X → record { isoˡ = eq factorl∘distl factorl∘distl
%                        ; isoʳ = eq distl∘factorl distl∘factorl }
%   }

% [x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
% [x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
%   { F⇒G = record
%     { η = λ X → distequiv
%     ; commute = λ f → eq dist-commute (λ x → P.sym (factor-commute x))
%     }
%   ; F⇐G = record
%     { η = λ X → factorequiv
%     ; commute = λ f → eq factor-commute (λ x → P.sym (dist-commute x))
%     }
%   ; iso = λ X → record { isoˡ = eq factor∘dist factor∘dist
%                        ; isoʳ = eq dist∘factor dist∘factor }
%   }
  
% x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
% x⊗0≡0 = record
%   { F⇒G = record
%     { η = λ X → distzrequiv
%     ; commute = λ f → eq (λ { (_ , ()) }) (λ { () })
%     }
%   ; F⇐G = record
%     { η = λ X → factorzrequiv
%     ; commute = λ f → eq (λ { () }) (λ { (_ , ()) })
%     }
%   ; iso = λ X → record
%     { isoˡ = eq factorzr∘distzr factorzr∘distzr
%     ; isoʳ = eq distzr∘factorzr distzr∘factorzr
%     }
%   }

% 0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
% 0⊗x≡0 = record
%   { F⇒G = record
%     { η = λ X → distzequiv
%     ; commute = λ f → eq (λ { (() , _) }) (λ { () })
%     }
%   ; F⇐G = record
%     { η = λ X → factorzequiv
%     ; commute = λ f → eq (λ { () }) (λ { (() , _)})
%     }
%   ; iso = λ X → record
%     { isoˡ = eq factorz∘distz factorz∘distz
%     ; isoʳ = eq distz∘factorz distz∘factorz
%     }
%   }
% \end{code}
% }
% \begin{code}
% TERig     : RigCategory SBM⊎ SBM×
% TERig = record
%   { distribₗ      = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
%   ; distribᵣ      = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z]
%   ; annₗ          = 0⊗x≡0
%   ; annᵣ          = x⊗0≡0
%   ; laplazaI      = eq distl-swap₊-lemma factorl-swap₊-lemma
%   ; laplazaII     = eq dist-swap⋆-lemma factor-swap⋆-lemma
%   ; laplazaIV     = eq dist-dist-assoc-lemma assoc-factor-factor-lemma
%   ; laplazaVI     = eq distl-assoc-lemma assoc-factorl-lemma
%   ; laplazaIX     = eq fully-distribute fully-factor
%   ; laplazaX      = eq distz0≡distrz0 factorz0≡factorzr0
%   ; laplazaXI     = eq distz0≡unite₊∘[distz,distz]∘distl factorz0≡factorl∘[factorz,factorz]∘uniti₊
%   ; laplazaXIII   = eq unite⋆r0≡absorb1 uniti⋆r0≡factorz
%   ; laplazaXV     = eq absorbl≡absorbr∘swap⋆ factorzr≡swap⋆∘factorz
%   ; laplazaXVI    = eq absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr factorz⇔factorz◎[factorz⊗id]◎assocr⋆
%   ; laplazaXVII   = eq elim-middle-⊥ insert-middle-⊥
%   ; laplazaXIX    = eq elim⊥-A[0⊕B] insert⊕⊥-AB
%   ; laplazaXXIII  = eq elim⊤-1[A⊕B] insert⊤l⊗-A⊕B
%   }
% \end{code}
% \caption{\label{fig:terig}Symmetric Rig Groupoid of Type Equivalences}
% \end{figure*}
 
\begin{figure}
\[\begin{array}{rrcll}
\identlsp :&  \tau + 0 & \iso & \tau &: \identrsp \\
\identlst :&  \tau * 1 & \iso & \tau &: \identrst \\

\absorbr :&~ 0 * \tau & \iso & 0 &: \factorzl \\
\absorbl :&~ \tau * 0 & \iso & 0 &: \factorzr \\

\distl :&~ \tau_1 * (\tau_2 + \tau_3) & \iso & (\tau_1 * \tau_2) &: \factorl \\
&&&                                                               +~ (\tau_1 * \tau_3)
\end{array}\]      
\caption{\label{fig:more}Additional $\Pi$-combinators}
\end{figure}

%%%%%%%%%%%%
\subsection{Instances of Symmetric Rig Categories} 

Most of the structures we have discussed so far are instances of
symmetric rig weak groupoids. 

\begin{theorem}
  The collection of all types and type equivalences is a symmetric rig
  groupoid.
\end{theorem}
\begin{proof}
  The objects of the category are Agda types and the morphisms are
  type equivalences. These morphisms directly satisfy the axioms
  stated in the definitions of the various categories. The bulk of the
  work is in ensuring that the coherence conditions are satisfied up
  to extensional equality.  We only show the proof of one coherence
  condition, the first one in Laplaza's paper shown below:

\smallskip

\begin{tikzcd}[column sep=tiny]
A \otimes (B \oplus C)
  \arrow[rrr, "\distl"]
  \arrow[d, "\mathrm{id}_A \otimes \swapp"']
&&& (A \otimes B) \oplus (A \otimes C)
   \arrow[d, "\swapp"]
\\
A \otimes (C \oplus B)
  \arrow[rrr, "\distl"']
&&& (A \otimes C) \oplus (A \otimes B)
\end{tikzcd}

\smallskip

\noindent We first have a lemma that shows that the two paths starting from the
top left node are equivalent:

\AgdaHide{
\begin{code}
open import Level using (zero; suc)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (Rel)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (map to map×)
open import Data.Empty
open import Data.Unit
import Function as F
open import Equiv
open import TypeEquiv as TE
open import Data.SumProd.Properties hiding (distl-swap₊-lemma; factorl-swap₊-lemma)
\end{code}
}

\smallskip

\begin{code}
distl-swap₊-lemma : {A B C : Set} → (x : (A × (B ⊎ C))) →
  TE.distl (map× F.id TE.swap₊ x) P.≡
  (TE.swap₊ (distl x))
distl-swap₊-lemma (x , inj₁ y) = P.refl
distl-swap₊-lemma (x , inj₂ y) = P.refl
\end{code}

\smallskip

\noindent The lemma asserts the extensional equivalence of the
functions representing the two paths for all arguments
\AgdaBound{x}. This lemma is sufficient to prove we have a rig
\emph{category}. To prove we also have a groupoid, we need a converse
lemma starting from the bottom right node and following the paths
backwards towards the top left node:

\smallskip

\begin{code}
factorl-swap₊-lemma : {A B C : Set} →
  (x : (A × C) ⊎ (A × B)) →
  map× F.id TE.swap₊ (TE.factorl x) P.≡
  TE.factorl (TE.swap₊ x)
factorl-swap₊-lemma (inj₁ x) = P.refl
factorl-swap₊-lemma (inj₂ y) = P.refl
\end{code}

\smallskip

\noindent Finally we show that the forward equivalence and the backward
equivalence are themselves equivalent:
\[
\AgdaFunction{laplazaI} =
  \AgdaInductiveConstructor{eq}~\AgdaFunction{distl-swap₊-lemma}~\AgdaFunction{factorl-swap₊-lemma}
\]
where \AgdaInductiveConstructor{eq} is the equivalence of equivalences used in the
proof of Thm.~\ref{thm:eqeq}.
\end{proof}

More relevant for our purposes, is the next theorem which applies to
reversible circuits (represented as $\Pi$-combinators).

\begin{theorem}
The collection of finite types and $\Pi$-combinators is a symmetric rig
groupoid.
\end{theorem}
\begin{proof}
  The objects of the category are finite types and the morphisms are
  the $\Pi$-combinators. Short proofs establish that these morphisms
  satisfy the axioms stated in the definitions of the various
  categories. The bulk of the work is in ensuring that the coherence
  conditions are satisfied. This required us to add a few $\Pi$
  combinators (see Fig.~\ref{fig:more}) and then to add a whole new
  layer of 2-combinators (discussed in the next section) witnessing
  enough equivalences of~$\Pi$ combinators to prove the coherence
  laws. The new $\Pi$ combinators, also discussed in more detail in
  the next section, are redundant (from an operational perspective)
  exactly because of the coherence conditions; they are however
  important as they have rather non-trivial relations to each other
  that are captured in the more involved coherence laws. 
\end{proof}

Putting the result above together with Laplaza's coherence result
about rig categories, we conclude with our main result (but the
punchline detailed the second level of combinators is in
Fig.~\ref{fig:more2} in the next section).

\begin{theorem}
We have two levels of $\Pi$-combinators such that:
\begin{itemize}
\item The first level of $\Pi$-combinators is complete for
  representing reversible combinational circuits.
\item The second level of $\Pi$-combinators is sound and complete for
  the equivalence of circuits represented by the first level.
\end{itemize}
\end{theorem}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Revised $\Pi$ and its Optimizer}
\label{sec:6}

Collecting the previous results we arrive at a universal language for
expressing reversible combinational circuits \emph{together with} a
sound and complete metalanguage for reasoning about equivalences of
programs written in the lower level language.

%%%%%%%%%%%%
\subsection{Example}

Given two $\Pi$-combinators:
\AgdaHide{
\begin{code}
postulate
\end{code}
}

\smallskip 

\begin{code}
 c₁ : {B C : U} →  B ⟷ C
 c₂ : {A D : U} →  A ⟷ D
\end{code}

\smallskip 

\noindent we can build two larger combinators $p_1$ and $p_2$,

\smallskip 

\begin{code}
p₁ p₂ : {A B C D : U} → PLUS A B ⟷ PLUS C D
p₁ = _⟷_.swap₊ ◎ (c₁ ⊕ c₂)
p₂ = (c₂ ⊕ c₁) ◎ _⟷_.swap₊
\end{code}

\smallskip 

\noindent As reversible circuits, $p_1$ and $p_2$ evaluate as
follows. If $p_1$ is given the value $\inl{a}$, it first transforms it
to $\inr{a}$, and then passes it to $c₂$. If $p_2$ is given the value
$\inl{a}$, it first passes it to $c₂$ and then flips the tag of the
result. Since $c₂$ is functorial, it must act polymorphically on its
input and hence, it must be the case that the two evaluations produce
the same result. The situation for the other possible input value is
symmetric. This extensional reasoning is embedded once and for all in
the proofs of coherence and distilled in a 2-level combinator:
\AgdaHide{
\begin{code}
module Y where
 data _⇔'_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
\end{code}
}

\smallskip 

\jc{it would be nice to remove the leading _⟷_ qualifier as
it is an artifact how all the pieces were put together
rather than something essential.}
\begin{code}
  swapl₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
   (_⟷_.swap₊ ◎ (c₁ ⊕ c₂)) ⇔' ((c₂ ⊕ c₁) ◎ _⟷_.swap₊)
\end{code}

\smallskip 

Pictorially, this 2-level combinator is a 2-path showing how the two
paths can be transformed to one another. The proof of equivalence can
be visualized by simply imagining the connections as wires whose
endpoints are fixed: holding the wires on the right side of the top
path and flipping them produces the connection in the bottom path:

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

Categorically speaking, this combinator expresses exactly that
the braiding $\sigma_{A,B}$ is a natural transformation, in other
words that $\sigma_{A,B}$ must commute with $\oplus$.

%%%%%%%%%%%%
\subsection{Revised Syntax}

The inspiration of symmetric rig groupoids suggested a refactoring of
$\Pi$ with additional level-1 combinators.  The added
combinators~\ref{fig:more} are redundant (from an operational
perspective) exactly because of the coherence conditions.  In addition
to being critical to the proofs, they are useful when representing
circuits, leading to smaller programs with fewer redexes.

The big addition of course is the level-2 combinators which are
collected in Fig.~\ref{fig:more2}. To avoid clutter we omit the names
of the combinators and only show the signatures.

Even though we know that these combinators come from the
coherence conditions inherence in the definition of a
symmetric rig weak groupoid, it would still be nice to
get a better understanding of what these really say.
About a third of the combinators come from the definition
of the various natural isomorphisms ($\alpha_{A,B,C},
\lambda_{A}, \rho_{A}, \sigma_{A,B}, dₗ, dᵣ, aₗ$ and
$aᵣ$).  The first $4$ natural isomorphisms actually
occur twice, once for each of the symmetric
monoidal structures at play.  Each natural
isomorphism is composed of 2 natural transformations
(one in each direction) that must compose to the
identity.  This in turn induces $4$ coherences laws:
two \emph{naturality laws} which indicate that the
combinator commuteswith structure construction, and two which 
express that the resulting combinators are
left and right inverses of each other.  But note also that
there mere desire that 
$\oplus$ be a bifunctor induces 3 coherence laws.  And then
of course each ``structure'' (monoidal, braided, symmetric)
comes with more, as outlined in the previous section,
culminating with 13 additional coherence laws for rig.

The coherence laws for a symmetric rig category, whether
presented in their full diagrammatic glory or through
their signatures, may at first appear rather obscure.  But
these can be ``unformalized'' to relatively understandable
statements:
\begin{itemize}
\item[I] given $A ⊗ (B ⊕ C)$, swapping $B$ and $C$ then
distributing (on the left) is the same as first distributing,
then swapping the two summands,
\item[II] given $(A ⊕ B) ⊗ C$, first switch the order of the
products then distributing (on the left) is the same as
distributing (on the right) and then switching the order of
both products.
\item[IV] given $(A ⊕ (B ⊕ C)) ⊗ D$, we can either distribute
then associate, or associate then distribute.
\item[VI] given $A ⊗ (B ⊗ (C ⊕ D))$, we can either
associate then distribute, or first do the inner
distribution, then the outer, and map associativity
on each term.
\item[IX] given $(A ⊕ B) ⊗ (C ⊕ D)$, we can either first
distribute on the left, map right-distribution and finally
associate, or we can go ``the long way around'' by
right-distributing first, then mapping left-distribution,
and then a long chain of administrative shuffles to get
to the same point.
\item[X] given $0 ⊗ 0$, left or right absorption both
give $0$ in equivalent ways
\item[XI] given $0 ⊗ (A ⊕ B)$, left absorption or
distribution, then mapping left absorption, followed
by (additive) left unit are equivalent.
\item[XIII] given $0 * 1$, left absorption or
(multiplicative) right unit are equivalent.
\item[XV] given $A ⊗ 0$, we can either absorb $0$
on the left, or commute and absorb $0$ on the right.
\item[XVI] given $0 ⊗ (A ⊗ B)$, we can either
absorb $0$ on the left, or associate, and then
absorb twice.
\item[XVII] given $A ⊗ (0 ⊗ B)$, the two obvious
paths to $0$ commute.
\item[XIX] given $A ⊗ (0 ⊕ B)$, we can either
eliminate the (additive) identity in the right
term, or distribute, right absorb $0$ in the
left term, then eliminate the resulting
(additive) identity to get to $A ⊗ B$.
\item[XXIII] Given $1 ⊗ (A ⊕ B)$, we can either
eliminate the (multiplicative) identity on the
left or distribute the map left-elimination.
\end{itemize}

Going through the details of the proof of the coherence theorem
in~\citet{laplaza} with a ``modern'' eye, one cannot help but
think of Knuth-Bendix completion.  Although it is known that
coherence laws for some categorical structures can be obtained
in this way~\cite{Beke}, it is also known that in the presence
of certain structures (such as symmetry), Knuth-Bendix completion
will not terminate.  It would be interesting to know if there is
indeed a systematic way to obtain these laws; we asked the wider
mathematical community~\cite{mathoverflowq}, but did not get any
answers.

It is worth noting that most (but not all) of the properties of
$⊎$ were already in Agda's standard library (in
\AgdaModule{Data.Sum.Properties} to be precise), whereas all
properties of $×$ were immediately provable due to $η$ expansion.
None of the mixed properties involved with distributivity
and absorption were present, although the proof of all of them
was very straightforward.

\begin{figure*}
\[\begin{array}{cc}
\begin{array}{rcl}
\idc \fatsemi c & \isoone & c \\
c \fatsemi \idc & \isoone & c \\
c \fatsemi (!~c) & \isoone & \idc \\
(!~c) \fatsemi c & \isoone & \idc \\
\idc ⊕ \idc & \isoone & \idc \\
\idc ⊗ \idc & \isoone & \idc \\
c₁ \fatsemi (c₂ \fatsemi c₃) & \isoone & (c₁ \fatsemi c₂) \fatsemi c₃ \\
(c₁ \fatsemi c₃) ⊕ (c₂ \fatsemi c₄) & \isoone & (c₁ ⊕ c₂) \fatsemi (c₃ ⊕ c₄) \\
(c₁ \fatsemi c₃) ⊗ (c₂ \fatsemi c₄) & \isoone & (c₁ ⊗ c₂) \fatsemi (c₃ ⊗ c₄) \\
\\
\swapp \fatsemi (c₁ ⊕ c₂) & \isoone &  (c₂ ⊕ c₁) \fatsemi \swapp \\
\swapt \fatsemi (c₁ ⊗ c₂) & \isoone &  (c₂ ⊗ c₁) \fatsemi \swapt \\
\swapp \fatsemi \factor & \isoone &  \factor \fatsemi (\swapp ⊗ \idc) \\
\\
\identlp \fatsemi c₂ & \isoone & (c₁ ⊕ c₂) \fatsemi \identlp \\
\identrp \fatsemi (c₁ ⊕ c₂) & \isoone &  c₂ \fatsemi \identrp \\
\identlsp \fatsemi c₂ & \isoone & (c₂ ⊕ c₁) \fatsemi \identlsp \\
\identrsp \fatsemi (c₂ ⊕ c₁) & \isoone &  c₂ \fatsemi \identrsp \\
\identlsp ⊕ \idc & \isoone & \assocrp \fatsemi (\idc ⊕ \identlp) \\
\\
(c₁ ⊕ (c₂ ⊕ c₃)) \fatsemi \assoclp & \isoone & \assoclp \fatsemi ((c₁ ⊕ c₂) ⊕ c₃) \\
((c₁ ⊕ c₂) ⊕ c₃) \fatsemi \assocrp & \isoone & \assocrp \fatsemi (c₁ ⊕ (c₂ ⊕ c₃)) \\
(c₁ ⊗ (c₂ ⊗ c₃)) \fatsemi \assoclt & \isoone & \assoclt \fatsemi ((c₁ ⊗ c₂) ⊗ c₃) \\
((c₁ ⊗ c₂) ⊗ c₃) \fatsemi \assocrt & \isoone & \assocrt \fatsemi (c₁ ⊗ (c₂ ⊗ c₃)) \\
((a ⊕ b) ⊗ c) \fatsemi \dist & \isoone & \dist \fatsemi ((a ⊗ c) ⊕ (b ⊗ c)) \\
((a ⊗ c) ⊕ (b ⊗ c)) \fatsemi \factor & \isoone & \factor \fatsemi ((a ⊕ b) ⊗ c) \\
(a ⊗ (b ⊕ c)) \fatsemi \distl & \isoone & \distl \fatsemi ((a ⊗ b) ⊕ (a ⊗ c)) \\
((a ⊗ b) ⊕ (a ⊗ c)) \fatsemi \factorl & \isoone & \factorl \fatsemi (a ⊗ (b ⊕ c)) 
\end{array}
& 
\begin{array}{rcl}
\identlt \fatsemi c₂ & \isoone & (c₁ ⊗ c₂) \fatsemi \identlt \\
\identrt \fatsemi (c₁ ⊗ c₂) & \isoone &  c₂ \fatsemi \identrt \\
\identlst \fatsemi c₂ & \isoone & (c₂ ⊗ c₁) \fatsemi \identlst \\
\identrst \fatsemi (c₂ ⊗ c₁) & \isoone &  c₂ \fatsemi \identrst \\
\identlst ⊗ \idc & \isoone & \assocrt \fatsemi (\idc ⊕ \identlt) \\
\\
\absorbr & \isoone & \identlt \\
\absorbr & \isoone & \absorbl \\
\absorbr & \isoone & (\assoclt \fatsemi (\absorbr ⊗ \idc)) \\
              && \fatsemi \absorbr \\
\absorbr & \isoone & (\distl \\
             && \quad \fatsemi (\absorbr ⊕ \absorbr)) \\
             && \fatsemi \identlp \\
\absorbl & \isoone & \swapt \fatsemi \absorbr \\
(c ⊗ \idc) \fatsemi \absorbl & \isoone & \absorbl \fatsemi \idc \\
(\idc ⊗ c) \fatsemi \absorbr & \isoone & \absorbr \fatsemi \idc \\
(\idc ⊗ \absorbr) \fatsemi \absorbl & \isoone & (\assoclt \fatsemi (\absorbl ⊗ \idc) \\
             && \fatsemi \absorbr \\
(\idc ⊗ \identlp) & \isoone & (\distl \fatsemi (\absorbl ⊕ \idc)) \\
            && \fatsemi \identlp \\
\\
\identlp & \isoone & \distl \fatsemi (\identlp ⊕ \identlp) \\
(\idc ⊗ \swapp) \fatsemi \distl & \isoone & \distl \fatsemi \swapp \\
\dist \fatsemi (\swapt ⊕ \swapt) & \isoone & \swapt \fatsemi \distl \\
\idc \fatsemi \factorzl & \isoone & \factorzl \fatsemi (\idc ⊗ c) \\
\idc \fatsemi \factorzr & \isoone & \factorzr \fatsemi (c ⊗ \idc) 
\end{array}
\end{array}\]
\[\begin{array}{rcl}
((\assoclp ⊗ \idc) \fatsemi \dist) \fatsemi (\dist ⊕ \idc) & \isoone &
  (\dist \fatsemi (\idc ⊕ \dist)) \fatsemi \assoclp \\
(\distl \fatsemi (\dist ⊕ \dist)) \fatsemi \assoclp & \isoone &
  ((((\dist \fatsemi (\distl ⊕ \distl)) \fatsemi \assoclp) \fatsemi (\assocrp ⊕ \idc))\\
  && \fatsemi (\idc ⊕ \swapp) ⊕ \idc) \fatsemi (\assoclp ⊕ \idc) \\
\assoclt \fatsemi \distl & \isoone & 
  ((\idc ⊗ \distl) \fatsemi \distl) \fatsemi (\assoclt ⊕ \assoclt) \\
\assocrp \fatsemi \assocrp & \isoone &
  ((\assocrp ⊕ \idc) \fatsemi \assocrp) \fatsemi (\idc ⊕ \assocrp) \\
\assocrt \fatsemi \assocrt & \isoone &
  ((\assocrt ⊗ \idc) \fatsemi \assocrt) \fatsemi (\idc ⊗ \assocrt) \\
(\assocrp \fatsemi \swapp) \fatsemi \assocrp & \isoone &
  ((\swapp ⊕ \idc) \fatsemi \assocrp) \fatsemi (\idc ⊕ \swapp) \\
(\assoclp \fatsemi \swapp) \fatsemi \assoclp & \isoone &
  ((\idc ⊕ \swapp) \fatsemi \assoclp) \fatsemi (\swapp ⊕ \idc) \\
(\assocrt \fatsemi \swapt) \fatsemi \assocrt & \isoone &
  ((\swapt ⊕ \idc) \fatsemi \assocrt) \fatsemi (\idc ⊗ \swapt) \\
(\assoclt \fatsemi \swapt) \fatsemi \assoclt & \isoone &
  ((\idc ⊗ \swapt) \fatsemi \assoclt) \fatsemi (\swapt ⊗ \idc) 
\end{array}\]
\begin{minipage}{\textwidth}
\begin{center} 
\Rule{}
{}
{\jdg{}{}{c \isoone c}}
{}
%
\Rule{}
{\jdg{}{}{c₁ \isoone c₂} \quad \vdash c₂ \isoone c₃}
{\jdg{}{}{c₁ \isoone c₃}}
{}
%
\Rule{}
{\jdg{}{}{c₁ \isoone c₃} \quad \vdash c₂ \isoone c₄}
{\jdg{}{}{(c₁ \fatsemi c₂) \isoone (c₃ \fatsemi c₄)}}
{}
%
\Rule{}
{\jdg{}{}{c₁ \isoone c₃} \quad \vdash c₂ \isoone c₄}
{\jdg{}{}{(c₁ ⊕ c₂) \isoone (c₃ ⊕ c₄)}}
{}
%
\Rule{}
{\jdg{}{}{c₁ \isoone c₃} \quad \vdash c₂ \isoone c₄}
{\jdg{}{}{(c₁ ⊗ c₂) \isoone (c₃ ⊗ c₄)}}
{}
\end{center}
\end{minipage}
\caption{\label{fig:more2}Signatures of level-2 $\Pi$-combinators}
\end{figure*}

As Fig.~\ref{fig:more2} illustrates, we have rules to manipulate code
fragments rewriting them in a small-step fashion. The rules apply only
when both sides are well-typed. The small-step nature of the rules
should allow us to make efficient optimizers following the experience
in functional languages~\citep{PeytonJones:1998:TOH:299619.299621}. In
contrast the coherence conditions are much smaller in number and many
then express invariants about much bigger ``chunks.'' From our small
experiments, an effective way to use the rules is to fix a canonical
representation of circuits that has the ``right'' properties and use
the rules in a directed fashion to produce that canonical
representation. For example, \citet{Saeedi:2013:SOR:2431211.2431220}
survey several possible canonical representations that trade-off
various desired properties. Of course, finding a rewriting procedure
that makes progress towards the canonical representation is far from
trivial.

It should be noted that a few of the ``raw'' signatures in
Fig.~\ref{fig:more2} are slightly misleading, as we omit the
signature of the underlying combinators.  For example,
$\identlt \fatsemi c₂ & \isoone & (c₁ ⊗ c₂) \fatsemi \identlt$
hides the fact that $c₁$ here is restricted to have signature
$c₁ : \AgdaInductiveConstructor{ZERO} ⟷ \AgdaInductiveConstructor{ZERO}$.
The reader should consult the code for full details.

% \amr{However, it did let me observe one thing: we have 2! which says
%  that given (c <-> d), we can get (d <-> c).  What we don't have, and
%  SHOULD, is 2flip which would say that given (c <-> d), we can get (!
%  c <-> ! d).  This is "obviously true".  More, we also ought to be
%  able to prove (easily!) that all (e : c <-> d) 2! (2flip e) == 2flip
%  (2! e) where I really mean == there.}
%
\amr{One of the interesting conclusions of the coherence laws (see the
  comments in the file above) is that it forces all (putative)
  elements of bot to be equal.  This comes from the coherence law for
  the two ways of proving that 0 * 0 = 0.}

% \amr{Note that a few of those "id" in there are actually "id<-> {ZERO}
%  {ZERO}", that is very important.  Most of the laws having to do with
%  absorb0 have some occurrences of both kinds of id in their
%  signature, which made figuring them out very challenging!  Same with
%  laws involving factor0}
%
%\amr{Similarly, the c1 in the identl* exchange law MUST map between ONE
%  (same with identr*).  In the same vein, c1 in the identl+ and
%  identr+ laws must involve ZERO.}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Problem with Higher-Order Functions}
\label{intc}
\label{sec:7}

In the context of monoidal categories, it is known that a notion of
higher-order functions emerges from having an additional degree of
\emph{symmetry}. In particular, both the \textbf{Int} construction of
\citet{joyal1996traced} and the closely related $\mathcal{G}$
construction of linear logic~\citep{gcons} construct higher-order
\emph{linear} functions by considering a new category built on top of
a given base traced monoidal
category~\citep{Hasegawa:2009:TMC:1552068.1552069}. The objects of the
new category are of the form $\nodet{\tau_1}{\tau_2}$ where~$\tau_1$
and~$\tau_2$ are objects in the base category. Intuitively, this
object represents the \emph{difference} $\tau_1-\tau_2$ with the
component $\tau_1$ viewed as conventional type whose elements
represent values flowing, as usual, from producers to consumers, and
the component $\tau_2$ viewed as a \emph{negative type} whose elements
represent demands for values or equivalently values flowing
backwards. Under this interpretation, a function is nothing but an
object that converts a demand for an argument into the production of a
result. We will explain in this section that the na\"\i ve
generalization of the construction from monoidal to bimonoidal (aka
rig) categories fails but that a recent result by
\citet{ringcompletion} might provide a path towards a solution.

%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The  \textbf{Int} Construction} 

For this construction, we assume that we have extended $\Pi$ with a
trace operator to implement recursion or feedback, as done in some of
the work on $\Pi$~\citep{rc2011,James:2012:IE:2103656.2103667}. The trace operator has the following type rule:
\[
\Rule{}
{\jdg{}{}{c : a + b \leftrightarrow a + c}}
{\jdg{}{}{\mathit{trace}~c : b \leftrightarrow c}}
{}
\]
Under ``normal'' operation, a $b$ input is expected which is injected
into the sum and fed to the traced computation. The evaluation
continues until a $c$ value is produced, possibly after feeding
several intermediate $a$ results back to the input. 

We then extend $\Pi$ with a new universe of types $\cubt$ that
consists of composite types $\nodet{\tau_1}{\tau_2}$:
\[\begin{array}{lrcl}
(\textit{{1d} types}) & 
  \cubt &::=& \nodet{\tau_1}{\tau_2}
\end{array}\]
We will refer to the original types $\tau$ as 0-dimensional (0d) types
and to the new types $\cubt$ as 1-dimensional (1d) types. The 1d level
is a ``lifted'' instance of $\Pi$ with its own notions of empty, unit,
sum, and product types, and its corresponding notions of isomorphisms
and composition on these 1d types.

%% \jc{should define ; here too}
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
identities~\citep{DiCosmo:2005:SSI:1090732.1090734}, one is tempted to think
that the \textbf{Int} construction (as its name suggests) produces a
categorification of the integers. Based on this hypothesis, the definitions
above can be intuitively understood as arithmetic identities. The same
arithmetic intuition explains the lifting of isomorphisms to 1d types:
\[\begin{array}{rcl}
\nodet{\tau_1}{\tau_2} \isoone \nodet{\tau_3}{\tau_4} &\eqdef& 
  (\tau_1+\tau_4) \iso (\tau_2+\tau_3)
\end{array}\]
In other words, an isomorphism between 1d types is really an
isomorphism between ``re-arranged'' 0d types where the negative input
$\tau_2$ is viewed as an output and the negative output $\tau_4$ is
viewed as an input. Using these ideas, it is now a fairly standard
exercise to define the lifted versions of most of the combinators in
Table~\ref{pi-combinators}.\footnote{See \citet{neelblog}'s excellent
  blog post implementing this construction in OCaml.} We discuss a few
cases in detail.

\paragraph*{Trivial cases.} Many of the 0d combinators lift easily to the 1d
level. For example:
\[\begin{array}{rcl}
\idc &:& \cubt \isoone \cubt \\
     &:& \nodet{\tau_1}{\tau_2} \isoone \nodet{\tau_1}{\tau_2} \\
     &\eqdef& (\tau_1+\tau_2) \iso (\tau_2+\tau_1) \\
\idc &=& \swapp \\
\\
\identlp &:& \ztone \boxplus \cubt \isoone \cubt \\
         &\eqdef& \nodet{0+\tau_1}{0+\tau_2} \isoone \nodet{\tau_1}{\tau_2} \\
         &\eqdef& ((0+\tau_1)+\tau_2) \iso ((0+\tau_2)+\tau_1) \\
         &=& \assocrp \fatsemi (\idc \oplus \swapp) \fatsemi \assoclp
\end{array}\]

% \jc{are you sure about identl?  The combinator for this in
% PiWithLevel/Pi1.agda is longer and (not surprisingly)
% uses unite and uniti.}

\paragraph*{Composition using $\mathit{trace}$.} Let
$\mathit{assoc}_1$, $\mathit{assoc}_2$, and $\mathit{assoc}_3$ be the
very simple $\Pi$ combinators with the following signatures:
\[\begin{array}{r@{\,\,\!}cl}
\mathit{assoc}₁ &:& \tau₁ + (\tau₂ + \tau₃) \leftrightarrow (\tau₂ + \tau₁) + \tau₃ \\
\mathit{assoc}₂ &:& (\tau₁ + \tau₂) + \tau₃ \leftrightarrow (\tau₂ + \tau₃) + \tau₁ \\
\mathit{assoc}₃ &:& (\tau₁ + \tau₂) + \tau₃ \leftrightarrow \tau₁ + (\tau₃ + \tau₂) \\
\end{array}\]
Composition is then defined as follows:
\[\begin{array}{r@{\,\,\!}cl}
(\fatsemi) &:& 
  (\cubt_1 \isoone \cubt_2) \rightarrow 
  (\cubt_2 \isoone \cubt_3) \rightarrow 
  (\cubt_1 \isoone \cubt_3) \\
 \mathit{seq} &:& 
   (\nodet{\tau_1}{\tau_2} \isoone \nodet{\tau_3}{\tau_4}) \rightarrow
   (\nodet{\tau_3}{\tau_4} \isoone \nodet{\tau_5}{\tau_6}) \\
   && \qquad\rightarrow  (\nodet{\tau_1}{\tau_2} \isoone \nodet{\tau_5}{\tau_6}) \\
   &\eqdef& 
   ((\tau_1+\tau_4) \iso (\tau_2+\tau_3)) \rightarrow
   ((\tau_3+\tau_6) \iso (\tau_4+\tau_5)) \\
  && \qquad\rightarrow  ((\tau_1+\tau_6) \iso (\tau_2+\tau_5)) \\
f \fatsemi g &=& \mathit{trace}~(\mathit{assoc}_1 \fatsemi 
  (f \oplus \idc) \fatsemi \mathit{assoc}_2 \fatsemi (g \oplus \idc) 
  \fatsemi \mathit{assoc}_3)
\end{array}\]
At the level of 1d-types, the first computation produces
$\nodet{\tau_3}{\tau_4}$ which is consumed by the second
computation. Expanding these types, we realize that the $\tau_4$
produced from the first computation is actually a demand for a value of
that type and that the $\tau_4$ consumed by the second computation can
satisfy a demand by an earlier computation. This explains the need for
a feedback mechanism to send future values back to earlier
computations. 

\paragraph*{Higher-order functions.} Given values that flow in both
directions, it is fairly straightforward to encode functions. At the
type level, we have:
\[\begin{array}{rcl}
\boxminus(\nodet{\tau_1}{\tau_2}) &\eqdef& \nodet{\tau_2}{\tau_1} \\
\nodet{\tau_1}{\tau_2} \lolli \nodet{\tau_3}{\tau_4} &\eqdef& 
           \boxminus(\nodet{\tau_1}{\tau_2}) \boxplus \nodet{\tau_3}{\tau_4} \\
  &\eqdef& \nodet{\tau_2+\tau_3}{\tau_1+\tau_4}
\end{array}\]
The $\boxminus$ flips producers and consumers and the $\lolli$ states
that a function is just a transformer demanding values of the input
type and producing values of the output type. As shown below, it now
becomes possible to manipulate functions as values by currying and uncurrying:
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

\begin{figure*}
\[\begin{array}{c}
\nodet{\tau_1}{\tau_2}
\quad\nboxtimes{1}{2}\quad
\nodet{(\nodet{\tau_3}{\tau_4})}{(\nodet{\tau_5}{\tau_6})} \quad= \\
\\
\nodet{(\nodet{{(\nodet{\tau_1 * \tau_3}{\tau_1 * \tau_4})}}
              {{(\nodet{\tau_1 * \tau_5}{\tau_1 * \tau_6})}})}
      {(\nodet{{(\nodet{\tau_2 * \tau_3}{\tau_2 * \tau_4})}}
              {{(\nodet{\tau_2 * \tau_5}{\tau_2 * \tau_6})}})}
\end{array}\]
\\
\\
\begin{center}
\begin{tikzpicture}
\node[left] at (-0.4,0) {$\pp$};
\node[below] at (-0.4,0) {$\tau_1$};
\draw[fill] (-0.4,0) circle [radius=0.05];
\node[right] at (0.6,0) {$\mm$};
\node[below] at (0.6,0) {$\tau_2$};
\draw[fill] (0.6,0) circle [radius=0.05];
\draw[-,dotted] (-0.4,0) -- (0.6,0);
\node at (1.6,0) {$\nboxtimes{1}{2}$}; 

%%
\node[below] at (2.5,-0.5) {$\tau_3$};
\node[left] at (2.5,-0.5) {$\pp\pp$};
\draw[fill] (2.5,-0.5) circle [radius=0.05];
\node[below] at (3.5,-0.5) {$\tau_4$};
\node[right] at (3.5,-0.5) {$\pp\mm$};
\draw[fill] (3.5,-0.5) circle [radius=0.05];
\draw[-,dotted] (2.5,-0.5) -- (3.5,-0.5);
\draw[-,dotted] (2.5,-0.5) -- (2.5,0.5);
\node[above] at (2.5,0.5) {$\tau_5$};
\node[left] at (2.5,0.5) {$\mm\pp$};
\draw[fill] (2.5,0.5) circle [radius=0.05];
\node[above] at (3.5,0.5) {$\tau_6$};
\node[right] at (3.5,0.5) {$\mm\mm$};
\draw[fill] (3.5,0.5) circle [radius=0.05];
\draw[-,dotted] (2.5,0.5) -- (3.5,0.5);
\draw[-,dotted] (3.5,-0.5) -- (3.5,0.5);
%% 
\node at (5,0) {$=$};
%% 
\node[left] at (7.5,0.75) {$(\tau_2 * \tau_3)\mm\pp\pp$};
\draw[fill] (7.5,0.75) circle [radius=0.05];
\node[right] at (9.5,0.75) {$\mm\pp\mm(\tau_2 * \tau_4)$};
\draw[fill] (9.5,0.75) circle [radius=0.05];
\node[above right] at (10.2,1.2) {$\mm\mm\mm(\tau_2 * \tau_6)$};
\draw[fill] (10.2,1.2) circle [radius=0.05];
\node[above left] at (8.2,1.2) {$(\tau_2 * \tau_5)\mm\mm\pp$};
\draw[fill] (8.2,1.2) circle [radius=0.05];
%%
\node[left] at (7.5,-0.75) {$(\tau_1 * \tau_3)\pp\pp\pp$};
\draw[fill] (7.5,-0.75) circle [radius=0.05];
\node[right] at (9.5,-0.75) {$\pp\pp\mm(\tau_1 * \tau_4)$};
\draw[fill] (9.5,-0.75) circle [radius=0.05];
\node[above right] at (10.2,-0.3) {$\pp\mm\mm(\tau_1 * \tau_6)$};
\draw[fill] (10.2,-0.3) circle [radius=0.05];
\node[left] at (8.2,-0.3) {$(\tau_1 * \tau_5)\pp\mm\pp$};
\draw[fill] (8.2,-0.3) circle [radius=0.05];
%%
\draw[-,dotted] (7.5,0.75) -- (9.5,0.75);
\draw[-,dotted] (9.5,0.75) -- (10.2,1.2);
\draw[-,dotted] (10.2,1.2) -- (8.2,1.2);
\draw[-,dotted] (8.2,1.2) -- (7.5,0.75);
%%
\draw[-,dotted] (7.5,-0.75) -- (9.5,-0.75);
\draw[-,dotted] (9.5,-0.75) -- (10.2,-0.3);
\draw[-,dotted,dashed] (10.2,-0.3) -- (8.2,-0.3);
\draw[-,dotted,dashed] (8.2,-0.3) -- (7.5,-0.75);
%%
\draw[-,dotted] (7.5,0.75) -- (7.5,-0.75);
\draw[-,dotted] (9.5,0.75) -- (9.5,-0.75);
\draw[-,dotted] (10.2,1.2) -- (10.2,-0.3);
\draw[-,dotted,dashed] (8.2,1.2) -- (8.2,-0.3);
\end{tikzpicture}
\end{center}
\caption{\label{mult}Example of multiplication of two cartesian types.}
\end{figure*}

\paragraph*{Products.} The \textbf{Int} construction works perfectly
well as a technique to define higher-order functions if we just have
\emph{one} monoidal structure: the additive one as we have assumed so
far. We will now try to extend the construction to encompass the other
(multiplicative) monoidal structure. Recall that natural definition
for the product of 1d types used above was:
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
multiplication is not functorial which would mean that the
\textbf{Int} construction only provides a limited notion of
higher-order functions at the cost of losing the multiplicative
structure at higher-levels. Further investigation reveals that this
observation is intimately related to a well-known problem in algebraic
topology and homotopy theory that was identified thirty years ago as
the \textbf{``phony'' multiplication}~\citep{thomason} in a special
class categories related to ours. This observation, \emph{that the
  \textbf{Int} construction on the additive monoidal structure does
  \emph{not} allow one to lift multiplication in a straightforward
  manner} is less well-known than it should be. This problem was
however recently solved~\citep{ringcompletion} using a technique whose
fundamental ingredients are to add more dimensions and then take
homotopy colimits.

The process of adding more dimensions is relatively straightforward:
if the original intuition was that 1d types like
$\nodet{\tau_1}{\tau_2}$ represent $\tau_1 - \tau_2$, i.e., two types
one in the $\pp$ direction and one in the $\mm$ direction, then
multiplication of two such 1d types ought to produce components in the
$\pp\pp$, $\pp\mm$, $\mm\pp$, and $\mm\mm$ directions and so on. The
idea is illustrated with a simple example in Fig.~\ref{mult}. It
remains to investigate whether this idea could lead to a
generalization of our results to incorporate higher-order functions
while retaining the multiplicative structure. Another intriguing point
to consider is the connection between this idea and the recently
proposed cubical models of type theory that also aim at producing
computational interpretations of univalence~\citep{cubical}.

% \jc {I would (syntactically) highlight that the Int construction does
%   NOT allow one to lift multiplication in a straightforward manner.
%   Put it in a "box" or something?}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}
\label{sec:conc}
\label{sec:8}

We have developed a tight integration between \emph{reversible
  circuits} with \emph{symmetric rig weak groupoids} based on the following
elements:
\begin{itemize}
\item reversible circuits are represented as terms witnessing
  morphisms between finite types in a symmetric rig groupoid;
\item the term language for reversible circuits is universal; it could
  be used as a standalone point-free programming language or as a
  target for a higher-level language with a more conventional syntax;
\item the symmetric rig groupoid structure ensures that programs can
  be combined using sums and products satisfying the familiar laws of
  these operations; 
\item the \emph{weak} versions of the categories give us a second
  level of morphisms that relate programs to equivalent programs and
  is exactly captured in the coherence conditions of the categories;
  this level of morphisms also comes equipped with sums and products
  with the familiar laws and the coherence conditions capture how
  these operations interact with sequential composition;
\item a sound and complete optimizer for reversible circuits can be
  represented as terms that rewrite programs in small steps witnessing
  this second level of morphisms.
\end{itemize}
Our calculus provides a semantically well-founded approach to
representation, manipulation, and optimization of reversible
circuits. In principle, subsets of the optimization rules can be
selected to rewrite programs to several possible canonical forms as
desired. We aim to investigate such frameworks in the future. 

From a much more general perspective, our result can be viewed as part
of a larger programme aiming at a better integration of several
disciplines most notably computation, topology, and physics. Computer
science has traditionally been founded on models such as the
$\lambda$-calculus which are at odds with the increasingly relevant
physical principle of conservation of information as well as the
recent foundational proposal of HoTT that identifies equivalences
(i.e., reversible, information-preserving, functions) as a primary
notion of interest.\footnote{The $\lambda$-calculus is not even
suitable for keeping track of computational resources; linear
logic~\citep{Girard87tcs} is a much better framework for that purpose
but it does not go far enough as it only tracks ``multiplicative
resources.''~\citep{superstructural}} Currently, these reversible
functions are a secondary notion defined with reference to the full
$\lambda$-calculus in what appears to be a detour. In more detail,
current constructions start with the class of all functions $A
\rightarrow B$, then introduce constraints to filter those functions
which correspond to type equivalences $A \simeq B$, and then attempt
to look for a convenient computational framework for effective
programming with type equivalences. As we have shown, in the case of
finite types, this is just convoluted since the collection of
functions corresponding to type equivalences is the collection of
isomorphisms between finite types and these isomorphisms can be
inductively defined, giving rise to a well-behaved programming
language and its optimizer.

More generally, reversible computational models --- in which all
functions have inverses --- are known to be universal computational
models~\citep{Bennett:1973:LRC} and more importantly they can be
defined without any reference to irreversible functions, which
ironically become the derived notion~\citep{Green:2008:RIC}. It is
therefore, at least plausible, that a variant of HoTT based
exclusively on reversible functions would have better computational
properties. Our current result is a step, albeit preliminary in that
direction as it only applies to finite types. However, it is plausible
that this approach can be generalized to accommodate higher-order
functions. The intuitive idea is that our current development based on
the commutative semiring of the natural numbers might be generalizable
to the ring of integers or even to the field of rational numbers. The
generalization to rings would introduce \emph{negative types} and the
generalization to fields would further introduce \emph{fractional
  types}. As Sec.~\ref{sec:7} suggests, there is good evidence that
these generalizations would introduce some notion of higher-order
functions. It is even possible to conceive of more exotic types such
as types with square roots and imaginary numbers by further
generalizing the work to the field of \emph{algebraic numbers}. These
types have been shown to make sense in computations involving
datatypes such as trees that can be viewed as solutions to polynomials
over type variables~\citep{seventrees,Fiore:2004,Fiore2004707}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\appendix
\section{Commutative Semirings}
\label{sec:commrig}
 
Given that the structure of commutative semirings is central to this
paper, we recall the formal algebraic definition. Commutative
semirings are sometimes called \emph{commutative rigs} as they are
commutative rings without negative elements.

\begin{definition}
  A \emph{commutative semiring} consists of a set $R$, two
  distinguished elements of $R$ named 0 and 1, and two binary
  operations~$+$ and $\cdot$, satisfying the following relations for
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
\label{app:opt}

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
\newpage
\bibliographystyle{abbrvnat}
\softraggedright
\bibliography{cites}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}
