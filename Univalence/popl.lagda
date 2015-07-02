\documentclass[preprint]{sigplanconf}

\usepackage{agda}
\usepackage{alltt}
\usepackage{fancyvrb}
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

%% \DefineVerbatimEnvironment
%%   {code}{Verbatim}
%%  {} % Add fancy options here if you like.

\DeclareUnicodeCharacter{9678}{\ensuremath{\odot}}
\DeclareUnicodeCharacter{9636}{\ensuremath{\Box}}

\newtheorem{theorem}{Theorem}
\newtheorem{conj}{Conjecture}
\newtheorem{definition}{Definition}

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

\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.4\textwidth}\color{red}{Amr says: {#1}}\end{minipage}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

\title{Representing, Manipulating and Optimizing \ \\ Reversible Circuits}
\authorinfo{Jacques Carette}
  {McMaster University}
  {carette@mcmaster.ca}
\authorinfo{Amr Sabry}
  {Indiana University}
  {sabry@indiana.edu}

\maketitle

\begin{abstract}
We show how a typed set of combinators for reversible computations,
corresponding exactly to the semiring of permutations, is a convenient
basis for representing and manipulating reversible circuits.  A
categorical interpretation also leads to optimization combinators, and
we demonstrate their utility through an example.
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

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction} 

\jc{That title was fine for the workshop, but we should think of something 
better for POPL.}

\amr{
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
}

\amr{Define and motivate that we are interested in defining HoTT  
  equivalences of types, characterizing them, computing with them,
  etc.}
  
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
negation-equivalence that were mentionned before. More generally, 
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
  The collection of all permutations $\textsc{perm}_{mn}$ between
  finite sets $\mathsf{Fin}~m$ and $\mathsf{Fin}~n$ forms a
  commutative semiring up to strict equality of the representations of
  the permutations.
\end{theorem}
\begin{proof}
  The proof requires delicate attention to the representation of
  permutations as straightforward attempts turn out not to capture
  enough of the properties of permutations. A permutation of one set
  to another is represented using two sizes: $m$ for the size of the
  input finite set and $n$ for the size of the resulting finite
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

\amr{
In our previous work we had argued that one can program with
permutations on finite sets (many others relate this to reversible
computation and more specifically to reversible combinational
circuits). We proposed a family of languages Pi some with trace; some
with effects; etc. The simplest language is permutations on finite
sets which correspond to finite types.
}

In previous work \cite{James:2012:IE:2103656.2103667}, we introduce
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
that witness the type isomorphism in the middle.\footnote{If recursive
types and a trace operator are added, the language becomes Turing
complete~\cite{James:2012:IE:2103656.2103667,rc2011}.}

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

It is fairly straightforward to verify that $\Pi$-combinators can be
interpreted as either type equivalences or as
permutations. Specifically, given the function $⟦\cdot⟧$ that maps each
type constructor to its Agda denotation, e.g., mapping the type 0 to
$\bot$ etc., we can verify that:

\begin{code}
c2equiv  :  {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → ⟦ t₁ ⟧ ≃ ⟦ t₂ ⟧
c2perm   :  {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → 
            CPerm (size t₂) (size t₁)
\end{code}
\AgdaHide{
\begin{code}
c2perm = {!!}
\end{code}
}

%%%%%%%%%%%%
\subsection{Example Circuits}

\amr{
In our previous work we had argued that one can program with  
permutations on finite sets (many others relate this to reversible  
computation and more specifically to reversible combinational  
circuits). Examples of circuits
}

This language $\Pi$ is universal for hardware combinational
circuits~\cite{James:2012:IE:2103656.2103667}.

\begin{center}
\begin{tikzpicture}[scale=0.3,every node/.style={scale=0.3}]
 \draw (-10,0) -- (-6,0);
 \node at (-8,0) {$\oplus$};

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

\begin{code}
BOOL : U
BOOL = PLUS ONE ONE

n₁ : BOOL ⟷ BOOL
n₁ = swap₊
\end{code}

Example Circuit: Not So Simple Negation. 

\begin{center}
\begin{tikzpicture}[scale=0.3,every node/.style={scale=0.3}]
 \draw (-11,0.5) -- (-10,0.5);
 \draw (-12,-0.5) -- (-10,-0.5);
 \draw (-10,-1) -- (-10,1) -- (-8,1) -- (-8,-1) -- cycle;
 \node at (-9,0) {swap};
 \draw (-8,0.5) -- (-6,0.5);
 \node at (-7,0.5) {$\oplus$};
 \draw (-8,-0.5) -- (-6,-0.5);
 \draw (-6,-1) -- (-6,1) -- (-4,1) -- (-4,-1) -- cycle;
 \node at (-5,0) {swap};
 \draw (-4,0.5) -- (-3,0.5);
 \draw (-4,-0.5) -- (-2,-0.5);


  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {*};

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}

\begin{code}
n₂ : BOOL ⟷ BOOL
n₂ =  uniti⋆ ◎
      swap⋆ ◎
      (swap₊ ⊗ id⟷) ◎
      swap⋆ ◎
      unite⋆
\end{code}

A few more circuits...

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Semantics}

\amr{
How do we reason about equivalence of circuits? Previous work:
  operational semantics; extensional tools; we relate to permutations
  and try to prove permutations equal also extensional. No sound and
  complete set of rules for us to reason about equivalence.

Because we live in this HoTT-like world where we have
  equivalences of equivalences, we could move up one level to get the
  right rules.
}

%%%%%%%%%%%%
\subsection{Operational Semantics}

Give operational semantics

%%%%%%%%%%%%
\subsection{Extensional Reasoning about Equivalence}

%%%%%%%%%%%%
\subsection{Rewriting Approach} 

pi combinators are a nice syntax for programming with finite types,
for talking about the commutative semiring of equivalences between
finite types, and for talking about the commutative semiring of
permutations between finite sets. But is it really a programming
language: semantics, optimization rules, etc. and how does the
connection to type equivalences and permutations help us?

Motivation: the two circuits for negation are equivalent: can we
design a sound and complete set of optimization rules that can be used
to prove such an equivalence? Reasoning about Example
Circuits. Algebraic manipulation of one circuit to the other:

\begin{code}

negEx : n₂ ⇔ n₁
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

Manipulating circuits. Nice framework, but:
\begin{itemize}
\item We don't want ad hoc rewriting rules.
\begin{itemize}
\item Our current set has \textcolor{red}{76 rules}!
\end{itemize}
\item Notions of soundness; completeness; canonicity in some sense.
\begin{itemize}
\item Are all the rules valid? (yes)
\item Are they enough? (next topic)
\item Are there canonical representations of circuits? (open)
\end{itemize}
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Categorification}

\amr{
This has been done generically: coherence conditions for
  commutative rig groupoids. These generalize type equivalences and permutations;
}

%%%%%%%%%%%%
\subsection{Monoidal Categories} 

%%%%%%%%%%%%
\subsection{Coherence Conditions} 

%%%%%%%%%%%%
\subsection{Commutative Rig Groupoids} 

This is where the idea of path and path of paths becomes critical. But
that does not give us a computational framework because univalence is
a postulate. The connection to permutations is the one that will give
us an effective procedure by categorification. Quote from
Proof-Theoretical Coherence, Kosta Dosen and Zoran Petric,
\url{http://www.mi.sanu.ac.rs/~kosta/coh.pdf}:

\begin{quote}
In Mac Lane’s second coherence result of [99], which has to do with
symmetric monoidal categories, it is not intended that all equations
be- tween arrows of the same type should hold. What Mac Lane does can
be described in logical terms in the following manner. On the one
hand, he has an axiomatization, and, on the other hand, he has a model
category where arrows are permutations; then he shows that his
axiomatization is complete with respect to this model. It is no wonder
that his coherence problem reduces to the completeness problem for the
usual axiomatization of symmetric groups.
\end{quote}

We get forward and backward evaluators

\begin{code}
eval : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
evalB : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
\end{code}

which really do behave as expected

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
\end{code}
}

From the perspective of category theory, the language $\Pi$ models
what is called a \emph{symmetric bimonoidal groupoid} or a
\emph{commutative rig groupoid}. These are categories in which every
morphism is an isomorphism and with two binary operations and
satisfying the axioms of a commutative semiring up to coherent
isomorphisms. And indeed the types of the $\Pi$-combinators are
precisely the commutative semiring axioms. A formal way of saying this
is that $\Pi$ is the \emph{categorification}~\cite{math/9802029} of
the natural numbers. A simple (slightly degenerate) example of such
categories is the category of finite sets and permutations in which we
interpret every $\Pi$-type as a finite set, interpret the values as
elements in these finite sets, and interpret the combinators as
permutations.

\amr{We haven't said anything about the categorical structure: it is
not just a commutative semiring but a commutative rig; this is crucial
because the former doesn't take composition into account. Perhaps that
is the next section in which we talk about computational
interpretation as one of the fundamental things we want from a notion
of computation is composition (cf. Moggi's original paper on monads).}

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

\amr{
  The refactoring of Pi from the inspiration of symmetric
  rig groupoids.  The added combinators are redundant (from an
  operational perspective) exactly because of the coherences.  But
  some of these higher combinators have rather non-trivial relations
  to each other [ex: pentagon, hexagon, and some of the weirder
  Laplaza rules].  Plus the 'minimalistic' Pi leads to much larger
  programs with LOTS of extra redexes.
}

%%%%%%%%%%%%
\subsection{Optimization Rules}

\amr{
What we need now is Pi plus another layer to top to optimize Pi
  programs; no ad hoc rules; principled rules; 
}

%%%%%%%%%%%%
\subsection{Examples}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Emails}

Reminder of
\url{http://mathoverflow.net/questions/106070/int-construction-traced-monoidal-categories-and-grothendieck-group}

Also,
\url{http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.163.334}
seems relevant

I had checked and found no traced categories or Int constructions in
the categories library. I'll think about that and see how best to
proceed.

The story without trace and without the Int construction is boring as
a PL story but not hopeless from a more general perspective.

I don't know, that a "symmetric rig" (never mind higher up) is a
programming language, even if only for "straight line programs" is
interesting! ;)

But it really does depend on the venue you'd like to send this to.  If
POPL, then I agree, we need the Int construction.  The more generic
that can be made, the better.

It might be in 'categories' already!  Have you looked?

In the meantime, I will try to finish the Rig part.  Those coherence
conditions are non-trivial.

I am thinking that our story can only be compelling if we have a hint
that h.o. functions might work. We can make that case by “just”
implementing the Int Construction and showing that a limited notion of
h.o. functions emerges and leave the big open problem of high to get
the multiplication etc. for later work. I can start working on that:
will require adding traced categories and then a generic Int
Construction in the categories library. What do you think? 

I have the braiding, and symmetric structures done.  Most of the
RigCategory as well, but very close.

Of course, we're still missing the coherence conditions for Rig.

Can you make sense of how this relates to us?

\url{https://pigworker.wordpress.com/2015/04/01/warming-up-to-homotopy-type-theory/}

Unfortunately not.  Yes, there is a general feeling of relatedness, but I can't pin it down.

I do believe that all our terms have computational rules, so we can't get stuck.

Note that at level 1, we have equivalences between Perm(A,B) and
Perm(A,B), not Perm(C,D) [look at the signature of <=>]. That said, we
can probably use a combination of levels 0 and 1 to get there.

Yes, we should dig into the Licata/Harper work and adapt to our
setting.

Though I think we have some short-term work that we simply need to do
to ensure our work will rest on a solid basis.  If that crumbles, all
the rest of the edifice will too.

Trying to get a handle on what we can transport or more precisely if
we can transport things that HoTT can only do with univalence.

(I use permutation for level 0 to avoid too many uses of 'equivalence'
which gets confusing.)

Level 0: Given two types A and B, if we have a permutation between
them then we can transport something of type P(A) to something of type
P(B).

For example: take P = . + C; we can build a permutation between A+C
and B+C from the given permutation between A and B

Level 1: Given types A, B, C, and D. let Perm(A,B) be the type of
permutations between A and B and Perm(C,D) be the type of permutations
between C and D. If we have a 2d-path between Perm(A,B) and Perm(C,D)
then we can transport something of type P(Perm(A,B)) to something of
type P(Perm(C,D)).

This is more interesting. What's a good example though of a property P
that we can implement?

In think that in HoTT the only way to do this transport is via
univalence. First you find an equivalence between the spaces of
permutations, then you use univalence to postulate the existence of a
path, and then you transport along that path. Is that right?

In HoTT this is exhibited by the failure of canonicity: closed terms
that are stuck. We can't get closed terms that are stuck: we don't
have any axioms with no computational rules, right?

Perhaps we can adapt the discussion/example in
\url{http://homotopytypetheory.org/2011/07/27/canonicity-for-2-dimensional-type-theory/}
to our setting and build something executable?

I hope not! [only partly joking]

Actually, there is a fair bit about this that I dislike: it seems to
over-simplify by arbitrarily saying some things are equal when they
are not.  They might be equivalent, but not equal.

This came up in a different context but looks like it might be useful
to us too.

\url{http://arxiv.org/pdf/gr-qc/9905020}

Separate.  The Grothendieck construction in this case is about
fibrations, and is not actually related to the "Grothendieck Group"
construction, which is related to the Int construction.

Yes. The categories library has a Grothendieck construction. Not sure
if we can use that or if we need to define a separate Int
construction? 

Reminder of
\url{http://mathoverflow.net/questions/106070/int-construction-traced-monoidal-categories-and-grothendieck-group}

Also,
\url{http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.163.334}
seems relevant

I had checked and found no traced categories or Int constructions in
the categories library. I'll think about that and see how best to
proceed.

The story without trace and without the Int construction is boring as
a PL story but not hopeless from a more general perspective.

I don't know, that a "symmetric rig" (never mind higher up) is a
programming language, even if only for "straight line programs" is
interesting! ;)

But it really does depend on the venue you'd like to send this to.  If
POPL, then I agree, we need the Int construction.  The more generic
that can be made, the better.

It might be in 'categories' already!  Have you looked?

In the meantime, I will try to finish the Rig part.  Those coherence
conditions are non-trivial.

I am thinking that our story can only be compelling if we have a hint
that h.o. functions might work. We can make that case by “just”
implementing the Int Construction and showing that a limited notion of
h.o. functions emerges and leave the big open problem of high to get
the multiplication etc. for later work. I can start working on that:
will require adding traced categories and then a generic Int
Construction in the categories library. What do you think? —Amr

I have the braiding, and symmetric structures done.  Most of the
RigCategory as well, but very close.

Of course, we're still missing the coherence conditions for Rig.

solutions to quintic equations proof by arnold is all about hott…
paths and higher degree path etc.

I thought we'd gotten at least one version, but could never prove it
sound or complete.

Didn’t we get stuck in the reverse direction. We never had it fully,
or am I misremembering? 

Right.  We have one direction, from Pi combinators to FinVec
permutations -- c2perm in PiPerm.agda.

Note that quite a bit of the code has (already!!) bit-rotted.  I
changed the definition of PiLevel0 to make the categorical structure
better, and that broke many things.  I am in the process of fixing --
which means introducing combinators all the way back in FinEquiv!!!  I
split the 0 absorption laws into a right and left law, and so have to
do the right version; turns out they are non-trivial, because Agda
only reduces the left law for free. Should be done this morning.

We do not have the other direction currently in the code.  That may
not be too bad, as we do have LeftCancellation to allow us to define
things by recursion.

That’s obsolete for now.

By the way, do we have a complement to thm2 that connects to
Pi. Ideally what we want to say is what I started writing: thm2 gives
us a semantic bridge between equivalences and FinVec permutations; we
also need a bridge between FinVec permutations and Pi combinators,
right? 

Is that going somewhere, or is it an experiment that should be put
into Obsolete/ ?  

Thanks.  I like that idea ;).

I have a bunch of things I need to do, so I won't really put my head
into this until the weekend.

I understand the desire to not want to rely on the full coherence
conditions.  I also don't know how to really understand them until
we've implemented all of them, and see what they actually say!

As I was trying really hard to come up with a single story, I am a
little confused as to what "my" story seems to be...  Can you give me
your best recollection of what I seem to be pushing, and how that is
different?  Then I would gladly flesh it out for us to do a second
paper on that.

Instead of discussing this over and over, I think it is clear that
thm2 will be an important part of any story we will tell. So I think
what I am going to start doing is to write an explanation of thm2 in a
way that would be usable in a paper.

I wasn't too worried about the symmetric vs. non-symmetric notion of
equivalence. The HoTT book has various equivalent definitions of
equivalence and the one below is one of them.

I do recall the other discussion about extensionality. That discussion
concluded with the idea that the strongest statement that can be made
is that HoTT equivalence between finite *enumerated* types is
equivalent to Vec-based permutations. This is thm2 and it is
essentially univalence as we noted earlier. My concern however is what
happens at the next level: once we start talking about equivalences
between equivalences. We should be to use thm2 to say that this the
same as talking about equivalences between Vec-based permutations,
which as you noted earlier is equivalence of categories.

I just really want to avoid the full reliance on the coherence
conditions. I also noted you have a different story and I am willing
to go along with your story if you sketch a paper outline for say one
of the conferences/workshops at
\url{http://cstheory.stackexchange.com/questions/7900/list-of-tcs-conferences-and-workshops}

Did you see my "HoTT-agda" question on the Agda mailing list on March
11th, and Dan Licata's reply?

What you wrote reduces to our definition of *equivalence*, not
permutation.  To prove that equivalence, we would need funext -- see
my question of February 18th on the Agda mailing list.

Another way to think about it is that this is EXACTLY what thm2
provides: a proof that for finite A and B, equivalence between A and B
(as below) is equivalent to permutations implemented as (Vect, Vect,
pf, pf).

Now, we may want another representation of permutations which uses
functions (qua bijections) internally instead of vectors.  Then the
answer to your question would be "yes", modulo the question/answer
about which encoding of equivalence to use.

Thought a bit more about this. We need a little bridge from HoTT to
our code and we’re good to go I think.

In HoTT we have several notions of equivalence that are equivalent (in
the technical sense). The one that seems easiest to work with is the
following:

A ≃ B if exists f : A → B such that:
  (exists g : B → A with g o f ~ idA) X
  (exists h : B → A with f o h ~ idB)

Does this definition reduce to our semantic notion of permutation if A
and B are finite sets?

I'm ok with a HoTT bias, but concerned that our code does not really
match that.  But since we have no specific deadline, I guess taking a
bit more time isn't too bad.

Since propositional equivalence is really HoTT equivalence too, then I
am not too concerned about that side of things -- our concrete
permutations should be the same whether in HoTT or in raw Agda.  Same
with various notions of equivalence, especially since most of the code
was lifted from a previous HoTT-based attempt at things.

I would certainly agree with the not-not-statement: using a notion of
equivalence known to be incompatible with HoTT is not a good idea.

I think that I should start trying to write down a more technical
story so that we can see how things fit together. I am biased towards
a HoTT-related story which is what I started. If you think we should
have a different initial bias let me know.

What is there is just one paragraph for now but it already opens a
question: if we are pursuing that HoTT story we should be able to
prove that the HoTT notion of equivalence when specialized to finite
types reduces to permutations. That should be a strong foundation to
the rest and the precise notion of permutation we get (parameterized
by enumerations or not should help quite a bit).

More generally always keeping our notions of equivalences (at higher
levels too) in sync with the HoTT definitions seems to be a good
thing to do.

... and if these coherence conditions are really complete then it
should be the case the two pi-combinators are equal iff their
canonical forms are identical.

So to sum up we would get a nice language for expressing equivalences
between finite types and a normalization process that transforms each
equivalence to a canonical form. The latter yield a simple decision
procedure for comparing equivalences.

Here is a nice idea: we need a canonical form for every
pi-combinator. Our previous approach gave us something but it was hard
to work with. I think we can use the coherence conditions to reach a
canonical form by simply picking a convention that chooses one side of
every commuting diagram. What do you think? —Amr

Indeed!  Good idea.

However, it may not give us a normal form.  This is because quite a
few 'simplifications' require to use 'the other' side of a commuting
diagram first, to expose a combination which simplifies.  Think
$(x . y^-1) . (y . z) ~~ x . z$.

In other words, because we have associativity and commutativity, we
need to deal with those specially.  Diagram with sides not all the
same length are easy to deal with.

However, I think it is not that bad: we can use the objects to help.
We also had put the objects [aka types] in normal form before (i.e. 1
+ (1 + (1 + ... )))) ).  The good thing about that is that there are
very few pi-combinators which preserve that shape, so those ought to
be the only ones to worry about?  We did get ourselves in the mess
there too, so I am not sure that's right either!

Here is another thought: 1. think of the combinators as polynomials in
3 operators, +, * and . (composition).  2. expand things out, with +
being outer, * middle, . inner.  3. within each . term, use
combinators to re-order things [we would need to pick a canonical
order for all single combinators] 4. show this terminates

the issue is that the re-ordering could produce new * and/or + terms.
But with a well-crafted term order, I think this could be shown
terminating.

Here is a nice idea: we need a canonical form for every
pi-combinator. Our previous approach gave us something but it was hard
to work with. I think we can use the coherence conditions to reach a
canonical form by simply picking a convention that chooses one side of
every commuting diagram. What do you think? —Amr

I've been thinking about this some more.  I can't help but think that,
somehow, Laplaza has already worked that out, and that is what is
actually in the 2nd half of his 1972 paper!  [Well, that Rig-Category
'terms' have a canonical form, but that's what we need]

Pi-combinators might be simpler, I don't know.

Another place to look is in Fiore (et al?)'s proof of completeness of
a similar case.  Again, in their details might be our answer.

What’s the proof strategy for establishing that a CPerm implies a
Pi-combinator. The original idea was to translate each CPerm to a
canonical Pi-combinator and then show that every combinator is equal
to its canonical representative. Is that still the high-level idea?

Well enough.  Last talk on the last day, so people are tired.  Doubt
we've caused a revolution in reversible computing...  Though when I
mentioned that the slides were literate Agda, Peter Selinger made a
point of emphasizing what that meant.

I think the idea that (reversible circuits == proof terms) is just a
little too wild for it to sink in quickly.  Same with the idea of
creating a syntactic language (i.e. Pi) out of the semantic structure
of the desired denotational semantics (i.e. permutations).  People
understood, I think, but it might be too much to really 'get'.

If we had a similar story for Caley+T (as they like to call it), it
might have made a bigger splash.  But we should finish what we have
first.

Note that I've pushed quite a few things forward in the code.  Most
are quite straightforward, but they help explain what we are doing,
and the relation between some of the pieces.  Ideally, there would be
more of those easy ones [i.e. that evaluation is the same as the
action of an equivalence which in turn is the same as the action of a
permutation].  These are all 'extensional' in nature, but still an
important sanity check.

Yes, I think this can make a full paper -- especially once we finish
those conjectures.  It depends a little bit on which audience we would
want to pitch it to.

I think the details are fine.  A little bit of polishing is probably
all that's left to do.  Some of the transitions between topics might
be a little abrupt.  And we need to reinforce the message of
"semantics drive the syntax + syntactic theory is good", which is
there, but a bit lost in the sea of details.  And the 'optimizing
circuits' aspect could also be punched up a bit.

Writing it up actually forced me to add PiEquiv.agda to the repository
-- which is trivial (now), but definitely adds to the story.  I think
there might be some easy theorems relating PiLevel0 as a programming
language, the action of equivalences, and the action of permutations.
In other words, we could get that all 3 are the same 'extensionally'
fairly easily.  What we are still missing is a way to go back from
either an equivalence or a permutation to a syntactic combinator.

Firstly, thanks Spencer for setting this up.

This is partly a response to Amr, and partly my own take on (computing
with) graphical languages for monoidal categories.

One of the key ingredients to getting diagrammatic languages to do
work for you is to actually take the diagrams seriously. String
diagrams now have very strong coherence theorems which state that an
equation holds by the axioms of (various kinds of) monoidal categories
if and only if the diagrams are equal. The most notable of these are
the theorems of Joyal \& Street in Geometry of Tensor Calculus for
monoidal, symmetric monoidal, and braided monoidal categories.

If you ignore these theorems and insist on working with the syntax of
monoidal categories (rather than directly with diagrams), things
become, as you put it "very painful".

Of course, when it comes to computing with diagrams, the first thing
you have to make precise is exactly what you mean by "diagram". In
Joyal \& Street's picture, this literally a geometric object,
i.e. some points and lines in space. This works very well, and pretty
much exactly formalises what happens when you do a pen-and-paper proof
involving string diagrams. However, when it comes to mechanising
proofs, you need some way to represent a string diagram as a data
structure of some kind. From here, there seem to be a few approaches:

(1: combinatoric) its a graph with some extra bells and whistles
(2: syntactic) its a convenient way of writing down some kind of term
(3: "lego" style) its a collection of tiles, connected together on a 2D plane

Point of view (1) is basically what Quantomatic is built on. "String
graphs" aka "open-graphs" give a combinatoric way of working with
string diagrams, which is sound and complete with respect to (traced)
symmetric monoidal categories. See arXiv:1011.4114 for details of how
we did this.

Naiively, point of view (2) is that a diagram represents an
equivalence class of expressions in the syntax of a monoidal category,
which is basically back to where we started. However, there are more
convenient syntaxes, which are much closer in spirit to the
diagrams. Lately, we've had a lot of success in connected with
abstract tensor notation, which came from Penrose. See
g. arXiv:1308.3586 and arXiv:1412.8552.

Point of view (3) is the one espoused by the 2D/higher-dimensional
rewriting people (e.g. Yves Lafont and Samuel Mimram). It is also
(very entertainingly) used in Pawel Sobocinski's blog:
http://graphicallinearalgebra.net .

This eliminates the need for the interchange law, but keeps pretty
much everything else "rigid". This benefits from being able to
consider more general categories, but is less well-behaved from the
point of view of rewriting. For example as Lafont/Mimram point out,
even finite rewrite systems can generate infinite sets of critical
pairs.

This is a very good example of CCT. As I am sure that you and others
on the list (e.g., Duncan Ross) know monoidal cats have been suggested
for quantum mechanics, they are closely related to Petri nets, linear
logic, and other “net-based” computational systems. There is
considerable work on graphic syntax.  It would be interesting to know
more details on your cats and how you formalize them.
 
My primary CCT interest, so far, has been with what I call
computational toposes. This is a slight strengthening of an elementary
topos to make subobject classification work in a computational
setting. This is very parallel to what you are doing, but aimed at
engineering modeling. The corresponding graphical syntax is an
enriched SysML syntax. SysML is a dialect of UML. These toposes can be
used to provide a formal semantics for engineering modeling.

There's also the perspective that string diagrams of various flavors
are morphisms in some operad (the composition law of which allows you
to nest morphisms inside of morphisms).

From that perspective, the string diagrams for traced monoidal
categories are little more than just bijections between sets. This
idea, and its connection to rewriting (finding normal forms for
morphisms in a traced or compact category), is something Jason Morton
and I have been working on recently.

Yes, I am sure this observation has been made before.  We'd have to
verify it for all the 2-paths before we really claim this.

[And since monoidal categories are involved in knot theory, this is
un-surprising from that angle as well]

looking at that 2path picture… if these were physical wires and boxes,
we could twist the wires, flipping the c1-c2 box and having them cross
on the other side. So really as we have noted before I am sure, these
2paths are homotopies in the sense of smooth transformations between
paths. Not sure what to do with this observation at this point but I
thought it is worth noting. 

There are some slightly different approaches to implementing a
category as a computational system which make more intrinsic use of
logic, than the ones mentioned by Aleks.  As well there is a different
take on the relationship of graphical languages to the category
implementation.

A category can be formalized as a kind of elementary axiom system
using a language with two sorts, map and type (object), with equality
for each sort.  The signature contain the function symbols, Domain and
Range. The arguments of both are a map and whose value is a type. The
abbreviation

                f:X to Y equiv Domain(f) = X and Range(f) = Y

is used for the three place predicate. 

The operations such as the binary composition of maps are represented
as first order function symbols. Of course the function constructions
are not interpreted as total functions in the standard first order
model theory. So, for example, one has axioms such as the typing
condition

f:Z to Y, g:Y to X implies g(f):Z to X

A function symbol that always produces a map with a unique domain and
range type, as a function of the arguments, is called a
constructor. For example, id(X) is a constructor with a type argument.
This same kind of logic can be used to present linear logics.

For most of the systems that I have looked at the axioms are often “
rules”, such as the category axioms. Sometimes one needs axioms which
have rules as consequences.  One can use standard first order
inference together with rewrite technology to compute.  The axioms for
a category imply that the terms generate a directed graph. Additional
axioms provide congruence relations on the graph.

A morphism of an axiom set using constructors is a functor.  When the
axioms include products and powers, the functors map to sets, this
yields is a form of Henkin semantics. Thus, while it is not standard
first order model theory, is well-known.  For other kinds of axiom
systems a natural semantics might be Hilbert spaces.

With this representation of a category using axioms in the
“constructor” logic, the axioms and their theory serve as a kind of
abstract syntax.  The constructor logic approach provides
standardization for categories which can be given axioms in this
logic.  Different axiom sets can be viewed as belonging to different
profiles. The logic representation is independent of any particular
graphical syntax. A graphical syntax would, of course have to
interpret that axioms correctly.  Possibly the Joyal and Street
theorems can be interpreted as proving the graphical representation
map is a structure preserving functor. Possibly the requirements for a
complete graphical syntax is that it is an invertible functor.

'm writing you offline for the moment, just to see whether I am
understanding what you would like. In short, I guess you want a
principled understanding of where the coherence conditions come from,
from the perspective of general 2-category theory perhaps (a la work
of the Australian school headed by Kelly in the 1970's).

We are in some sense categorifying the notion of "commutative
rig". The role of commutative monoid is categorified by symmetric
monoidal category, which roughly is the next notion past commutative
monoid in the stable range on the periodic table.

I believe there is a canonical candidate for the categorification of
tensor product of commutative monoids. In other words, given symmetric
monoidal categories A, B, C, the (symmetric monoidal) category of
functors A x B --> C that are strong symmetric monoidal in separate
arguments should be equivalent to the (sm) category of strong
symmetric monoidal functors $A \otimes B --> C$, for this canonical
tensor product $A \otimes B$. Actually, I don't think we absolutely
need this construction -- we could phrase everything in terms of
"multilinear" (i.e. multi-(strong sm)) functors
$A_1 x ... x A_n --> B$, but it seems a convenience worth taking
advantage of. In fact, let me give this tensor product a more neutral
name -- I'll write @, and I for the tensor unit -- because I'll want
to reserve $\otimes$ for something else (consistent with Laplaza's
notation).

If S is the 2-category of symmetric monoidal categories, strong
symmetric monoidal functors, and monoidal natural transformations,
then this @ should endow S with a structure of (symmetric) monoidal
2-category, with some other pleasant properties (such as S's being
symmetric monoidal closed in the appropriate 2-categorical sense). All
of these facts should be deducible on abstract grounds, by
categorifying the notion of commutative monad (such as the free
commutative monoid monad on Set) to an appropriate categorification to
commutative 2-monad on Cat, and categorifying the work of Kock on
commutative monads.

In any symmetric monoidal 2-category, we have a notion of
"pseudo-commutative pseudomonoid", which generalizes the notion of
symmetric monoidal category in the special case of the monoidal
2-category (Cat, x). Anyhow, if ($C, \oplus, N)$ is a symmetric
monoidal category, then I my guess (I've checked some but not all
details) is that a symmetric rig category is precisely a
pseudo-commutative pseudomonoid object
($\otimes: C @ C --> C, U: I --> C$, etc.)

in (S, @). I would consider this is a reasonable description stemming
from general 2-categorical principles and concepts.

Would this type of thing satisfy your purposes, or are you looking for something else? 

Quite related indeed.  But much more ad hoc, it seems [which they acknowledge].

Something closer to our work \url{http://www.informatik.uni-bremen.de/agra/doc/konf/rc15_ricercar.pdf}

More related work (as I encountered them, but later stuff might be more important):

Diagram Rewriting and Operads, Yves Lafont
\url{http://iml.univ-mrs.fr/~lafont/pub/diagrams.pdf}

A Homotopical Completion Procedure with Applications to Coherence of Monoids
\url{http://drops.dagstuhl.de/opus/frontdoor.php?source_opus=4064}

A really nice set of slides that illustrates both of the above
\url{http://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_kbs.pdf}

I think there is something very important going on in section 7 of 
\url{http://comp.mq.edu.au/~rgarner/Papers/Glynn.pdf}
which I also attach.  [I googled 'Knuth Bendix coherence' and these all came up]

There are also seems to be relevant stuff buried (very deep!) in
chapter 13 of Amadio-Curiens' Domains and Lambda Calculi.

Also, Tarmo Uustalu's "Coherence for skew-monoidal categories",
available on \url{http://cs.ioc.ee/~tarmo/papers/}

[Apparently I could have saved myself some of that searching time by
going to \url{http://ncatlab.org/nlab/show/rewriting} !  At the
bottom, the preprint by Mimram seems very relevant as well]

Somehow, at the end of the day, it seems we're looking for a
confluent, terminating term-rewriting system for commutative semirings
terms!

\includegraphics[scale=0.07]{IMAG0342.jpg}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Future Work and Conclusion}
\label{sec:conc}

\amr{
\begin{itemize}
\item add trace to make language Turing complete
\item generalize from commutative rig to field as a way to get some
  notion of h.o. functions
\end{itemize}
}

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
\end{document}
         
\absorbr :&~ 0 * \tau & \iso & 0 &: \factorzl \\
\absorbl :&~ \tau * 0 & \iso & 0 &: \factorzr \\

\dist :&~ (\tau_1 + \tau_2) * \tau_3 & \iso & (\tau_1 * \tau_3) + (\tau_2 * \tau_3)~ &: \factor \\
\distl :&~ \tau_1 * (\tau_2 + \tau_3) & \iso & (\tau_1 * \tau_2) + (\tau_1 * \tau_3)~ &: \factorl 
      
