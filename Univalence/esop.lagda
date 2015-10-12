\documentclass[oribibl]{llncs}

\usepackage{savesym}
\usepackage{amssymb}
\usepackage{amsmath}
\savesymbol{vec}
\usepackage{flushend}
\usepackage{agda}
\usepackage{alltt}
%\usepackage{fancyvrb}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{tikz}
\usetikzlibrary{cd}
\usetikzlibrary{quotes}
\usepackage{adjustbox}
%% \usepackage{amsthm}
% \usepackage{latexsym}
\usepackage{MnSymbol}
\usepackage{courier}
\usepackage{thmtools}
\usepackage{bbold}
\usepackage[hyphens]{url}
\usepackage{bbm}
\usepackage{proof}
%% \usepackage{amstext}
\usepackage{comment}
\usepackage{stmaryrd}
\usepackage{listings}
\usepackage{graphicx}
\usepackage{textgreek}
\usepackage{extarrows}
\usepackage{textcomp}
\usepackage{multicol}
\usepackage{natbib}

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
%\newcommand{\lid}{\textsf{lid}}
\newcommand{\alt}{~|~}
%\newcommand{\rid}{\textsf{rid}}
\newcommand{\linv}{l!}
\newcommand{\rinv}{r!}
\newcommand{\invinv}{!!}
\newcommand{\assoc}{\circ}
\newcommand{\identlp}{\mathit{unite}_+}
\newcommand{\identrp}{\mathit{uniti}_+}
\newcommand{\identlsp}{\mathit{unites}_+}
\newcommand{\identrsp}{\mathit{unitis}_+}
\newcommand{\swapp}{\mathit{swap}_+}
\newcommand{\assoclp}{\mathit{assocl}_+}
\newcommand{\assocrp}{\mathit{assocr}_+}
\newcommand{\identlt}{\mathit{unite}_*}
\newcommand{\identrt}{\mathit{uniti}_*}
\newcommand{\identlst}{\mathit{unites}_*}
\newcommand{\identrst}{\mathit{unitis}_*}
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
\DeclareUnicodeCharacter{8779}{\ensuremath{\triplesim}}
\DeclareUnicodeCharacter{9679}{\textbullet}

%\newtheorem{theorem}{Theorem}
%\newtheorem{conj}{Conjecture}
%\newtheorem{definition}{Definition}

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

%% \newcommand{\amr}[1]{}
%% \newcommand{\jc}[1]{}

\newcommand{\jc}[1]{\authornote{purple}{JC}{#1}}
\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.4\textwidth}\color{red}{Amr says: {#1}}\end{minipage}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

%\title{A Curry-Howard Isomorphism between \\
%  Reversible Programming Languages \\
%  and Semirings}
%\titlerunning{Reversible Languages and Semirings}
\title{Computing with Semirings and Weak Rig Groupoids}
\titlerunning{Computing with Rig Groupoids}
\author{Jacques Carette \and Amr Sabry}
\institute{McMaster University\\
\email{carette@mcmaster.ca}
\and
Indiana Uiversity
\email{sabry@indiana.edu}
}
\maketitle

\begin{abstract}

The original formulation of the Curry-Howard isomorphism relates
propositional logic to the simply-typed $\lambda$-calculus at three
levels: the syntax of propositions corresponds to the syntax of types;
the proofs of propositions correspond to programs of the corresponding
types; and the normalization of proofs corresponds to the evaluation
of programs. This rich correspondence has inspired our community for
half a century, and has been updated to deal with more modern ideas
such as resource conservation and the homotopy theoretic approach to
type isomorphisms.  We propose a variant of this correspondence that
very naturally relates semirings to reversible programming languages:
the syntax of semiring elements corresponds to the syntax of types;
the proofs of semiring identities correspond to (reversible) programs
of the corresponding types;  and equivalences between algebraic proofs
corresponds to meaning-preserving program transformations and optimizations.
These latter equivalences are not ad hoc: the same way semirings arise
naturally out of the structure of types, a categorical look at the
structure of proof terms gives rise to (at least) a weak rig groupoid
structure, and the coherence laws are exactly the program transformations
we seek. 
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
a physical process, every computation is, at the physical level, an
equivalence that preserves information.  The idea that computation, at
the logical and programming level, should also be based on
``equivalences'' (i.e., invertible processes) was originally motivated
by such physical
considerations~\citep{Landauer:1961,Bennett:1973:LRC,Toffoli:1980,springerlink:10.1007/BF02650179,fredkin1982conservative,PhysRevA.32.3266}. More
recently, the rising importance of energy conservation for both tiny
mobile devices and supercomputers, the shrinking size of technology at
which quantum effects become noticeable, and the potential for quantum
computation and communication, are additional physical considerations
adding momentum to such reversible computational
models~\citep{Frank:1999:REC:930275,DeBenedictis:2005:RLS:1062261.1062325}. From
a more theoretical perspective, the recently proposed
\citet{hottbook}, based on Homotopy Type Theory (HoTT), greatly
emphasizes computation based on \emph{equivalences} that are satisfied
up to equivalences that are themselves satisfied up to equivalence,
etc.

To summarize, we are witnessing a convergence of ideas from several
distinct research communities, including physics, mathematics, and
computer science, towards basing computations on
equivalences~\citep{baez2011physics}. A first step in that direction
is the development of many \emph{reversible programming
  languages}~(e.g., \citep{Kluge:1999:SEMCD,Mu:2004:ILRC,
  abramsky2005structural, DiPierro:2006:RCL:1166042.1166047,
  Yokoyama:2007:RPL:1244381.1244404, Mackie2011}.)  Typically,
programs in these languages correspond to some notion of
equivalence. But reasoning \emph{about} these programs abandons the
notion of equivalence and uses conventional irreversible functions to
specify evaluators and the derived notions of program
equivalence. This unfortunately misses the beautiful combinatorial
structure of equivalences at higher-levels that was first exposed in
the historical paper by \citet{Hofmann96thegroupoid} and that is
currently the center of attention of HoTT.

This paper addresses --- and completely solves --- a well-defined part
of the general problem of programming with equivalences up to
equivalences. Our approach, we argue, might also be suitable for the
more general problem. The particular problem we focus on is that of
programming with equivalences between the finite types built from the
empty type, the unit type, and closed under sums and products, and
reasoning about equivalences between these programs between finite
types, i.e., the problem of equivalences between finite types and
equivalences between such equivalences. Although limited in their
expressive power, these types are rich enough to express all
combinational (with no state or feedback) hardware circuits and, as we
show, already exhibit substantial combinatorial structure at the
``next level,'' i.e., at the level of equivalences about equivalences
of types. What emerges from our study are the following results:
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
$\Pi$ program to a type equivalence or equivalently a permutation. The
section also gives a small example showing how a few rules that are
sound with respect to equivalence of permutations can be used to
transform $\Pi$ programs without reliance on any extensional
reasoning. Sec.~\ref{sec:5} then reveals that these rules are
intimately related to the coherence conditions of the categorified
analogues of the commutative semiring structures underlying type
equivalences and permutations, namely, the so-called \emph{symmetric
  rig weak groupoids}. Sec.~\ref{sec:6} contains that ``punchline'': a
sound and complete set of rules that can be used to reason about
equivalences of $\Pi$ programs. Before concluding, we devote
Sec.~\ref{sec:7} to a detailed analysis of the problem with extending
our approach to accommodate higher-order functions, suggesting a
possible path towards a solution. We note that because the issues
involved are quite subtle, the paper is the ``unformalization'' of an
executable \texttt{Agda 2.4.2.3} package with the global
\AgdaComment{without-K} option enabled.\footnote{We will publish the
  link to the code repository after the double-blind review process.}

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
semirings, whose definition we recall below. 

\begin{definition}
  A \emph{commutative semiring} (sometimes called a \emph{commutative
    rig} (commutative ri\emph{n}g without negative elements) consists of a
  set $R$, two distinguished elements of $R$ named 0 and 1, and two
  binary operations~$+$ and $\cdot$, satisfying the following
  relations for any $a,b,c \in R$:
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

We emphasize that, in the definition above, the axioms are satisfied
up to strict equality $=$. The most famous instance of commutative
semirings if, of course, the natural numbers. Intuitively, Fiore
et. al's result states that one can interpret each type by its size,
and that this identification validates the familiar properties of the
natural numbers, and is in fact isomorphic to the commutative semiring
of the natural numbers.

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

\noindent For example, for arbitrary types $A$, $B$, and $C$, we have
equivalences such as:
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
  equivalence of equivalences \AgdaSymbol{≋}.
\end{theorem}
\begin{proof}
  The most important insight is the definition of equivalence of
  equivalences. Two equivalences $e_1, e_2 : \textsc{eq}_{A,B}$ with
  underlying functions $f_1$ and $f_2$ and underlying quasi-inverses
  $g_1$ and $g_2$ are themselves equivalent $e₁ ≋ e₂$ if we have that
  both $f₁ = f₂$ and $g₁ = g₂$ extensionally. Given this notion of
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
relationship between finite types and finite sets by formalizing that
equivalent finite types must have the same size.

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
  enough of the properties of permutations.\footnote{None of the
    formalizations of permutations in Agda or Coq known to us supports
    the full range of operations that we need including sequential
    compositions, disjoint unions, and products of permutations.}
  After several attempts, we settled on formalizing a permutation
  using the conventional one-line notation, e.g., giving a preferred
  enumeration 1 2 3 of a set with three elements, the one-line notion
  2 3 1 denotes the permutation sending 1 to 2, 2 to 3, and 3 to 1. To
  make sure the sequence of numbers is of the right length and that
  each number is in the right range, we use Agda vectors
  $\AgdaPrimitiveType{Vec}~(\AgdaPrimitiveType{Fin}~m)~n$ (abbreviated
  $\AgdaFunction{FinVec}~m~n$). To further ensure that the vector
  elements have no repetitions (i.e., represent 1-1 functions), we
  include in the representation of each permutation, an inverse vector
  $\AgdaFunction{FinVec}~n~m$ as well as two proofs asserting that the
  compositions in both directions produce the identity permutation
  (which naturally forces $m$ and $n$ to be equal). Given this
  representation, we can prove that two permutations are equal if the
  one-line vector representations are strictly equal \emph{and} we can
  support the full range of operations on permutations. The main proof
  then proceeds using the vacuous permutation $\mathsf{CPerm}~0~0$ for
  the additive unit and the trivial permutation $\mathsf{CPerm}~1~1$
  for the multiplicative unit. The binary operations on permutations
  map $\mathsf{CPerm}~m₁~m₂$ and $\mathsf{CPerm}~n₁~n₂$ to
  $\mathsf{CPerm}~(m₁+n₁)~(m₂+n₂)$ and
  $\mathsf{CPerm}~(m₁*n₁)~(m₂*n₂)$ respectively. Their definition
  relies on the properties that the unions and products of the
  one-line vectors denoting permutations distribute over the
  sequential compositions of permutations.
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
  The equivalence of Thm.~\ref{thm:eqeqperm} is an \emph{isomorphism}
  between the commutative semiring of equivalences of finite types and
  the commutative semiring of permutations.
\end{theorem}
\begin{proof}
  In the process of this proof, we show that every axiom of semirings
  of types is an equivalence and a permutation.  Some of the axioms
  like the associativity of sums gets mapped to the trivial identity
  permutation.  However, some axioms reveal interesting structure when
  expressed as permutations; the most notable is that the
  commutativity of products maps to a permutation solving the
  classical problem of in-place matrix transposition:
  \[
    \AgdaFunction{swap⋆cauchy}~:~(m~n~:~ℕ)~→~\AgdaFunction{FinVec}~(n~*~m)~(m~*~n)
  \]
\end{proof}

Before concluding this section, we recall that, the conventional
formulation of the univalence \emph{axiom} is:
\[
(A ≡ B) ≃ (A ≃ B)
\]
where $≡$ is the propositional equality relation and hence $(A ≡ B)$
is the collection of all identities between types $A$ and $B$. With
the proper Agda definitions, Thm.~\ref{thm:eqeqperm} can be rephrased
in a more evocative way as follows.

\begin{theorem}
\[
\mathsf{Perm}~|A|~|B|  ≃ (A ≃ B)
\]
\end{theorem}

\noindent 
where $\mathsf{Perm}~|A|~|B|$ is the collection of all permutations
between the finite sets of the given sizes. This reformulation shows
that, for the restricted finite types, the theorem proves, and gives a
computational interpretation of, the univalence axiom. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Programming with Permutations}
\label{sec:3}

In the previous section, we argued that, up to equivalence, the
equivalence of types reduces to permutations on finite sets. We recall
background work which proposed a term language for permutations and
adapt it in later sections to be used to express, compute with, and
reason about type equivalences between finite types.

\begin{figure*}[ht]
\[
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
\]
\caption{$\Pi$-terms~\citep{rc2011,James:2012:IE:2103656.2103667}.
\label{pi-terms}}
\end{figure*}

\begin{figure*}[ht]
\[
\begin{minipage}{0.8\textwidth}
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
\end{minipage}
\]
\caption{$\Pi$-combinators.}
\label{pi-combinators}
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

The first example is simply boolean encoding and negation which can be
defined as shown on the left and visualized as a permutation on finite
sets on the right:

\smallskip 

\begin{tabular}{@{\kern-3em}cc}
\begin{minipage}[t]{0.25\textwidth}
\end{minipage}
& 
\adjustbox{valign=t}{\begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
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
\end{tikzpicture}}
\end{tabular}

\smallskip  
 
Naturally there are many ways of encoding boolean negation. The
following combinator implements a more convoluted circuit that
computes the same function, which is also visualized as a permutation
on finite sets:

\smallskip 

\begin{tabular}{@{\kern-3em}c@{\!\!\!}c}
\begin{minipage}[t]{0.25\textwidth}
\end{minipage}
& 
\adjustbox{valign=t}{\begin{tikzpicture}[scale=0.53,every node/.style={scale=0.53}]
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

\end{tikzpicture}}
\end{tabular}

\smallskip

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

\begin{tabular}{@{\kern-3em}l}
\begin{minipage}{0.5\textwidth}
\end{minipage}
\end{tabular}

\bigskip

\begin{tabular}{@{\kern-3em}l}
\begin{minipage}{0.5\textwidth}
\end{minipage}
\end{tabular}

\begin{tabular}{@{\kern-3em}l}
\begin{minipage}{0.5\textwidth}
\end{minipage}
\end{tabular}

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

\smallskip

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

\noindent The advantage is that permutations have a concrete
representation which can be effectively compared for equality as
explained in the proof of Thm.~\ref{thm:permrig}.

%%%%%%%%%%%%
\subsection{Rewriting Approach}
\label{sec:rewriting}

Having mapped each combinator to a permutation, we can reason about
valid optimizations mapping a combinator to another by studying the
equivalence of permutations on finite sets. Strict equality of
permutations would distinguish the permutations corresponding to
$\AgdaBound{c}$ and
$\AgdaInductiveConstructor{id⟷}~\AgdaInductiveConstructor{◎}~\AgdaBound{c}$
for a combinator $c$ and hence is inappropriate for reasoning about
optimizations and equivalences of circuits. Of course, we could easily
justify this particular equivalence, and many others, by calculating
the actions of the two permutations on arbitrary incoming sets and
checking that the results are identical; this extensional reasoning is
however \emph{not} our stated goal. We need instead, proof
\emph{terms} witnessing \emph{all} possible equivalences on
permutations.

Before we embark on the categorification program that will allow us to
find this complete collection of rules in the next section, we show
that, with some ingenuity, one can develop a reasonable set of rewrite
rules that is rich enough to prove that the two negation circuits from
the previous section are actually equivalent:

\smallskip 

\begin{tabular}{@{\kern-3em}l}
\begin{minipage}{0.5\textwidth}
\end{minipage}
\end{tabular}

\begin{tabular}{@{\kern-3em}l}
\begin{minipage}{0.5\textwidth}
\end{minipage}
\end{tabular}

\smallskip

The rules used in the derivation (and which are defined in the Agda
code) are based on the following important property: reasoning about
permutations is \emph{compositional} in the sense that a permutation
can be decomposed into parts (using sequential composition, sums, and
products as constructors) and then one can simplify the parts
individually. The simplifications used in the derivation correspond to
the following properties of permutations: the sequential composition
of permutations is associative; the identity permutation is a left and
right unit of sequential composition; the composition of a permutation
with its inverse produces the identity permutation; permutations on
the set with one element are trivial and can be omitted; and swapping
and parallel composition commute as follows:
\[
\AgdaInductiveConstructor{swap⋆}~\AgdaInductiveConstructor{◎}~(\AgdaBound{c₁}~\AgdaInductiveConstructor{⊗}~\AgdaBound{c₂})~\AgdaInductiveConstructor{⇔}~(\AgdaBound{c₂}~\AgdaInductiveConstructor{⊗}~\AgdaBound{c₁})~\AgdaInductiveConstructor{◎}~\AgdaInductiveConstructor{swap⋆}
\]
The accompanying material includes a short slide deck animating the
sequence of rewrites showing that they are all indeed intuitive
transformations on the diagrams representing the circuits.

The important question that remains is what other properties of 
permutations are needed for a complete set of rewrite rules?

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
monads). Thus, from a programmer's perspective, this categorification
process is about understanding how type equivalences evolve under
compositions, e.g., how two different paths of type equivalences
sharing the same source and target relate two each other.

\begin{figure*}
\begin{center}
\begin{tikzcd}[column sep=tiny]
((A \otimes B) \otimes C) \otimes D
  \arrow[rr, "\alpha"]
  \arrow[d, "\alpha \otimes \mathrm{id}_D"']
&& (A \otimes B) \otimes (C \otimes D)
   \arrow[d, "\alpha"]
\\
(A \otimes (B \otimes C)) \otimes D
  \arrow[dr, "\alpha"']
&& A \otimes (B \otimes (C \otimes D))
   \arrow[dl, "\mathrm{id}_A \otimes \alpha"]
& A \otimes ((B \otimes C) \otimes D)
\end{tikzcd}
\end{center}
%\qquad\qquad\qquad
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
\caption{\label{fig:mon}Pentagon and triangle diagrams.}
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
categories. This is not the case but will be once we capture the full
structure of commutative semirings categorically. 

%%%%%%%%%%%%
\subsection{Symmetric Rig Weak Groupoids}

Symmetric monoidal categories discussed in the previous section are
the categorifications of commutative monoids. The categorification of
a commutative semiring is called a \emph{symmetric rig category}.  It
is built from a \emph{symmetric bimonoidal category} to which
distributivity and absorption natural isomorphisms are added, and
accompanying coherence laws added.  Since we can easily set things up
so that every morphism is an isomorphism, the category will also be a
groupoid. Since the laws of the category only hold up to a higher
equivalence, the entire setting is that of weak categories.

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
and absorption/annihilation isomorphisms $a_ℓ : x ⊗ 0 \isoarrow 0$ and
$a_r : 0 ⊗ x \isoarrow 0$ satisfying coherence conditions worked out
by \citet{laplaza} and discussed below.
\end{definition}

\begin{definition}[Symmetric Rig Category]
A \emph{symmetric rig category} is a rig category in which the 
multiplicative structure is symmetric. 
\end{definition}

\begin{definition}[Symmetric Rig Groupoid]
A \emph{symmetric rig groupoid} is a symmetric rig category in which
every morphism is invertible.
\end{definition}

The coherence conditions for rig categories were worked out by
\citet{laplaza}. Pages 31-35 of his paper report 24 coherence
conditions numbered I to XXIV that vary from simple diagrams to quite
complicated ones including a diagram with 9 nodes showing that two
distinct ways of simplifying $(A ⊕ B) ⊗ (C ⊕ D)$ to
$(((A ⊗ C) ⊕ (B ⊗ C)) ⊕ (A ⊗ D)) ⊕ (B ⊗ D)$ commute. The 24 coherence
conditions are however not independent and it is sufficient to verify
one of various smaller subsets, to be chosen depending on the
situation.  Generally speaking, the coherence laws appear rather
obscure but, as shown below for many of them, they can be
``unformalized'' to relatively understandable statements:
\begin{itemize}
\item[I] given $A ⊗ (B ⊕ C)$, swapping $B$ and $C$ then distributing
  (on the left) is the same as first distributing, then swapping the
  two summands;
\item[II] given $(A ⊕ B) ⊗ C$, first switching the order of the
  products then distributing (on the left) is the same as distributing
  (on the right) and then switching the order of both products;
\item[IV] given $(A ⊕ (B ⊕ C)) ⊗ D$, we can either distribute then
  associate, or associate then distribute;
\item[VI] given $A ⊗ (B ⊗ (C ⊕ D))$, we can either associate then
  distribute, or first do the inner distribution, then the outer, and
  map associativity on each term;
\item[IX] given $(A ⊕ B) ⊗ (C ⊕ D)$, we can either first distribute on
  the left, map right-distribution and finally associate, or we can go
  ``the long way around'' by right-distributing first, then mapping
  left-distribution, and then a long chain of administrative shuffles
  to get to the same point;
\item[X] given $0 ⊗ 0$, left or right absorption both give $0$ in
  equivalent ways;
\item[XI] given $0 ⊗ (A ⊕ B)$, left absorption or distribution, then
  mapping left absorption, followed by (additive) left unit are
  equivalent;
\item[XIII] given $0 * 1$, left absorption or (multiplicative) right
  unit are equivalent;
\item[XV] given $A ⊗ 0$, we can either absorb $0$ on the left, or
  commute and absorb $0$ on the right;
\item[XVI] given $0 ⊗ (A ⊗ B)$, we can either absorb $0$ on the left,
  or associate, and then absorb twice;
\item[XVII] given $A ⊗ (0 ⊗ B)$, the two obvious paths to $0$ commute;
\item[XIX] given $A ⊗ (0 ⊕ B)$, we can either eliminate the (additive)
  identity in the right term, or distribute, right absorb $0$ in the
  left term, then eliminate the resulting (additive) identity to get
  to $A ⊗ B$;
\item[XXIII] Given $1 ⊗ (A ⊕ B)$, we can either eliminate the
  (multiplicative) identity on the left or distribute the map
  left-elimination.
\end{itemize}

Going through the details of the proof of the coherence theorem
in~\citet{laplaza} with a ``modern'' eye, one cannot help but think of
Knuth-Bendix completion.  Although it is known that the coherence laws
for some categorical structures can be systematically derived in this
way~\cite{Beke2011728}, it is also known that in the presence of
certain structures (such as symmetry), Knuth-Bendix completion will
not terminate.  It would be interesting to know if there is indeed a
systematic way to obtain these laws from the rewriting perspective
but, as far as we know, there are no published results to that
effect. The connections to homotopy theory cited by
\citet{math/9802029} (and mentioned in the previous section) appear to
be the best hope for a rational reconstruction of the coherence laws.

%% \textrm{math}\textbf{\textit{overflow}} about this idea are left
%% unanswered.


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
equivalence are indeed related to the same diagram:
\[
\AgdaFunction{laplazaI} =
  \AgdaInductiveConstructor{eq}~\AgdaFunction{distl-swap₊-lemma}~\AgdaFunction{factorl-swap₊-lemma}
\]
where \AgdaInductiveConstructor{eq} is the constructor for the
equivalence of equivalences used in the proof of Thm.~\ref{thm:eqeq}.
\end{proof}

More directly relevant to our purposes, is the next theorem which
applies to reversible circuits (represented as $\Pi$-combinators).

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
  combinators (see Sec.~\ref{fig:more}) and then to add a whole new
  layer of 2-combinators witnessing enough equivalences of~$\Pi$
  combinators to prove the coherence laws (see
  Fig.~\ref{fig:more2}). The new $\Pi$ 1-combinators, also discussed in
  more detail in the next section, are redundant (from an operational
  perspective) exactly because of the coherence conditions; they are
  however important as they have rather non-trivial relations to each
  other that are captured in the more involved coherence laws.
\end{proof}

Putting the result above together with Laplaza's coherence result
about rig categories, we conclude with our main result, which will be
detailed in the next section by giving the full details of the second
level of combinators.

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

\AgdaHide{
\begin{code}
open import TypeEquivCat
\end{code}
}

%%%%%%%%%%%%
\subsection{Revised Syntax: 1-Paths}
\label {fig:more}

The inspiration of symmetric rig groupoids suggested a refactoring of
$\Pi$ with the following additional level-1 combinators:  

\[\begin{array}{rrcll}
\identlsp :&  \tau + 0 & \iso & \tau &: \identrsp \\
\identlst :&  \tau * 1 & \iso & \tau &: \identrst \\

\absorbr :&~ 0 * \tau & \iso & 0 &: \factorzl \\
\absorbl :&~ \tau * 0 & \iso & 0 &: \factorzr \\

\distl :&~ \tau_1 * (\tau_2 + \tau_3) & \iso & (\tau_1 * \tau_2) 
                                               +~ (\tau_1 * \tau_3) &: \factorl
\end{array}\]      

The added combinators are redundant (from an operational perspective)
exactly because of the coherence conditions. They are however critical
to the proofs, and in addition, they are often useful when
representing circuits, leading to smaller programs with fewer redexes.

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
\\
\swapp \fatsemi (c₁ ⊕ c₂) & \isoone &  (c₂ ⊕ c₁) \fatsemi \swapp \\
\swapt \fatsemi (c₁ ⊗ c₂) & \isoone &  (c₂ ⊗ c₁) \fatsemi \swapt \\
\\
\\
\identlp \fatsemi c₂ & \isoone & (c₁ ⊕ c₂) \fatsemi \identlp \\
\identrp \fatsemi (c₁ ⊕ c₂) & \isoone &  c₂ \fatsemi \identrp \\
\identlsp \fatsemi c₂ & \isoone & (c₂ ⊕ c₁) \fatsemi \identlsp \\
\identrsp \fatsemi (c₂ ⊕ c₁) & \isoone &  c₂ \fatsemi \identrsp \\
\identlsp ⊕ \idc & \isoone & \assocrp \fatsemi (\idc ⊕ \identlp) \\
\\
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
\\
\identlp & \isoone & \distl \fatsemi (\identlp ⊕ \identlp) \\
(\idc ⊗ \swapp) \fatsemi \distl & \isoone & \distl \fatsemi \swapp \\
\dist \fatsemi (\swapt ⊕ \swapt) & \isoone & \swapt \fatsemi \distl \\
\idc \fatsemi \factorzl & \isoone & \factorzl \fatsemi (\idc ⊗ c) \\
\idc \fatsemi \factorzr & \isoone & \factorzr \fatsemi (c ⊗ \idc) 
\end{array}
\end{array}\]
\\
\\
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
\\
\\
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
\end{center}
\end{minipage}
\\
\\
\\
\begin{minipage}{\textwidth}
\begin{center} 
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
\\
\\
\caption{\label{fig:more2}Signatures of level-2 $\Pi$-combinators.}
\end{figure*}

%%%%%%%%%%%%
\subsection{Revised Syntax: 2-Paths}
 
The big addition to $\Pi$ is the level-2 combinators which are
collected in Fig.~\ref{fig:more2}. To avoid clutter we omit the names
of the combinators (which are arbitrary) and only show the
\emph{untyped} signatures. The signatures themselves are of course
typed and in some cases the types add critical information. For
example, $\identlt \fatsemi c₂ \isoone (c₁ ⊗ c₂) \fatsemi \identlt$
hides the fact that $c₁$ here is restricted to have signature
$c₁ : \AgdaInductiveConstructor{ZERO} ⟷
\AgdaInductiveConstructor{ZERO}$.
The reader should consult the code for full details.

Generally speaking, the 2-level combinators arise for the following
reasons. About a third of the combinators come from the definition of
the various natural isomorphisms $\alpha_{A,B,C}$, $\lambda_{A}$,
$\rho_{A}$, $\sigma_{A,B}$, $dₗ$, $dᵣ$, $aₗ$ and $aᵣ$.  The first $4$
natural isomorphisms actually occur twice, once for each of the
symmetric monoidal structures at play.  Each natural isomorphism is
composed of 2 natural transformations (one in each direction) that
must compose to the identity.  This in turn induces $4$ coherences
laws: two \emph{naturality laws} which indicate that the combinator
commutes with structure construction, and two which express that the
resulting combinators are left and right inverses of each other.  We
note that the mere desire that $\oplus$ be a bifunctor induces 3
coherence laws.  And then of course each ``structure'' (monoidal,
braided, symmetric) comes with more, as outlined in the previous
section, culminating with 13 additional coherence laws for the rig
structure.

It is worth noting that most (but not all) of the properties involving
only $⊕$ were already in Agda's standard library (in
\AgdaModule{Data.Sum.Properties} to be precise), whereas all
properties involving only $⊗$ were immediately provable due to $\eta$
expansion.  None of the mixed properties involved with distributivity
and absorption were present, although the proof of all of them was
straightforward.

% \amr{However, it did let me observe one thing: we have 2! which says
%  that given (c <-> d), we can get (d <-> c).  What we don't have, and
%  SHOULD, is 2flip which would say that given (c <-> d), we can get (!
%  c <-> ! d).  This is "obviously true".  More, we also ought to be
%  able to prove (easily!) that all (e : c <-> d) 2! (2flip e) == 2flip
%  (2! e) where I really mean == there.}
%
% \amr{One of the interesting conclusions of the coherence laws (see the
%   comments in the file above) is that it forces all (putative)
%   elements of bot to be equal.  This comes from the coherence law for
%   the two ways of proving that 0 * 0 = 0.}

%% \amr{swapfl* and swapfr* were never used, so I removed them (commented
%% them out of PiLevel1).I’d lean towards leaving it and saying that the
%% axioms are not independent, just like Laplaza’s conditions.}

% \amr{Note that a few of those "id" in there are actually "id<-> {ZERO}
%  {ZERO}", that is very important.  Most of the laws having to do with
%  absorb0 have some occurrences of both kinds of id in their
%  signature, which made figuring them out very challenging!  Same with
%  laws involving factor0}
%
%\amr{Similarly, the c1 in the identl* exchange law MUST map between ONE
%  (same with identr*).  In the same vein, c1 in the identl+ and
%  identr+ laws must involve ZERO.}

%%%%%%%%%%%%
\subsection{Soundness}
 
Each 2-level combinator whose signature is in Fig.~\ref{fig:more2}
gives rise to an equivalence of equivalences of types. The formal Agda
statement is:

\smallskip 

\noindent where \AgdaSymbol{≋} is the equivalence of equivalences with
constructor \AgdaInductiveConstructor{eq} defined in the proof of
Thm.~\ref{thm:eqeq}. Given all the infrastructure, most of the cases
are fairly straightforward to prove except for the two cases in which
we need to prove that the left and right composition of the
equivalence arising from a combinator \AgdaBound{c} and the
equivalence arising from the inverse \AgdaSymbol{!}~\AgdaBound{c} are
equivalent to the identity equivalence. Formally:

\smallskip 

\noindent and symmetrically for the flipped case.

%%%%%%%%%%%%
\subsection{A Syntactic 2-Paths Circuit Optimizer}
  
As Fig.~\ref{fig:more2} illustrates, we have rules to manipulate code
fragments rewriting them in a small-step fashion. The rules apply only
when both sides are well-typed. In their textual form, the rules are
certainly not intuitive. They however become ``evidently correct''
transformations on circuits when viewed diagrammatically.

Consider two arbitrary $\Pi$-combinators representing circuits of the
given types:

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

\noindent Now consider the circuits \AgdaFunction{p₁} and
\AgdaFunction{p₂} which use \AgdaFunction{c₁} and \AgdaFunction{c₂}
as shown below:

\[\begin{array}{l}
\AgdaFunction{p₁}~\AgdaFunction{p₂} ~\AgdaSymbol{:} ~\AgdaSymbol{\{}~\AgdaBound{A} ~\AgdaBound{B} ~\AgdaBound{C} ~\AgdaBound{D} ~\AgdaSymbol{:} ~\AgdaDatatype{U}~\AgdaSymbol{\}} ~\AgdaSymbol{→} ~\AgdaInductiveConstructor{PLUS} ~\AgdaBound{A} ~\AgdaBound{B} ~\AgdaDatatype{⟷} ~\AgdaInductiveConstructor{PLUS} ~\AgdaBound{C} ~\AgdaBound{D}
\\
\AgdaFunction{p₁} ~\AgdaSymbol{=} ~\AgdaInductiveConstructor{swap₊} ~\AgdaInductiveConstructor{◎} ~\AgdaSymbol{(}~\AgdaPostulate{c₁} ~\AgdaInductiveConstructor{⊕} ~\AgdaPostulate{c₂}~\AgdaSymbol{)}
\\
\AgdaFunction{p₂} ~\AgdaSymbol{=} ~\AgdaSymbol{(}~\AgdaPostulate{c₂} ~\AgdaInductiveConstructor{⊕} ~\AgdaPostulate{c₁}~\AgdaSymbol{)} ~\AgdaInductiveConstructor{◎} ~\AgdaInductiveConstructor{swap₊}
\end{array}\]

\noindent As reversible circuits, \AgdaFunction{p₁} and
\AgdaFunction{p₂} evaluate as follows. If \AgdaFunction{p₁} is given
the value $\inl{a}$, it first transforms it to $\inr{a}$, and then
passes it to \AgdaFunction{c₂}. If \AgdaFunction{p₂} is given the
value $\inl{a}$, it first passes it to \AgdaFunction{c₂} and then
flips the tag of the result. Since \AgdaFunction{c₂} is functorial, it
must act polymorphically on its input and hence, it must be the case
that the two evaluations produce the same result. The situation for
the other possible input value is symmetric. This extensional
reasoning is embedded once and for all in the proofs of coherence and
distilled in a 2-level combinator:

\[\begin{array}{rcl}
\AgdaInductiveConstructor{swapl₊⇔} & \AgdaSymbol{:} &
  \AgdaSymbol{\{}\AgdaBound{t₁}~\AgdaBound{t₂}~
  \AgdaBound{t₃}~\AgdaBound{t₄}~\AgdaSymbol{:}~\AgdaDatatype{U}\AgdaSymbol{\}}~ 
  \AgdaSymbol{\{}\AgdaBound{c₁}~\AgdaSymbol{:}~\AgdaBound{t₁}~\AgdaDatatype{⟷}~\AgdaBound{t₂}\AgdaSymbol{\}}~ 
  \AgdaSymbol{\{}\AgdaBound{c₂}~\AgdaSymbol{:}~\AgdaBound{t₃}~\AgdaDatatype{⟷}~\AgdaBound{t₄}\AgdaSymbol{\}}~
  \AgdaSymbol{→} \\
&& \AgdaSymbol{(}
  \AgdaInductiveConstructor{swap₊}~\AgdaInductiveConstructor{◎}~
  \AgdaSymbol{(}\AgdaBound{c₁}~\AgdaInductiveConstructor{⊕}~\AgdaBound{c₂}\AgdaSymbol{))}~
  \AgdaDatatype{⇔}~ 
  \AgdaSymbol{((}
  \AgdaBound{c₂}~\AgdaInductiveConstructor{⊕}~\AgdaBound{c₁}\AgdaSymbol{)}~
  \AgdaInductiveConstructor{◎}~\AgdaInductiveConstructor{swap₊}\AgdaSymbol{)}
\end{array}\]

Categorically speaking, this combinator expresses exactly that the
braiding $\sigma_{A,B}$ is a natural transformation, in other words
that $\sigma_{A,B}$ must commute with $\oplus$. Pictorially, this
2-level combinator is a 2-path showing how the two paths can be
transformed to one another. The proof of equivalence can be visualized
by simply imagining the connections as wires whose endpoints are
fixed: holding the wires on the right side of the top path and
flipping them produces the connection in the bottom path:

\begin{center}
\begin{tikzpicture}[scale=0.9,every node/.style={scale=0.9}]
  \draw[<->,double,red,thick] (2.25,-1.5) -- (2.25,-2.5) ;
  \node at (3.3,-2) {$\AgdaInductiveConstructor{swapl₊⇔}$} ;
  \node at (2.5,-1.3) {$\AgdaSymbol{((}
    \AgdaBound{c₂}~\AgdaInductiveConstructor{⊕}~\AgdaBound{c₁}\AgdaSymbol{)}~
     \AgdaInductiveConstructor{◎}~\AgdaInductiveConstructor{swap₊}\AgdaSymbol{)}$};
  \node at (2.5,-2.7) {$\AgdaSymbol{(}
  \AgdaInductiveConstructor{swap₊}~\AgdaInductiveConstructor{◎}~
  \AgdaSymbol{(}
  \AgdaBound{c₁}~\AgdaInductiveConstructor{⊕}~\AgdaBound{c₂}\AgdaSymbol{))}$};

  \draw (-2,-2) ellipse (0.5cm and 1cm);
  \draw[fill] (-2,-1.5) circle [radius=0.025];
  \node[below] at (-2.1,-1.5) {$A$};
  \draw[fill] (-2,-2.5) circle [radius=0.025];
  \node[below] at (-2.1,-2.5) {$B$};

  \draw (6.5,-2) ellipse (0.5cm and 1cm);
  \draw[fill] (6.5,-1.5) circle [radius=0.025];
  \node[below] at (6.7,-1.5) {$C$};
  \draw[fill] (6.5,-2.5) circle [radius=0.025];
  \node[below] at (6.7,-2.5) {$D$};

  \draw (-2,-1.5) to[bend left] (1,0.5) ;
  \draw (-2,-2.5) to[bend left] (1,-0.5) ;
  \draw[->] (3.5,0.5) to[bend left] (6.5,-1.45) ;
  \draw[->] (3.5,-0.5) to[bend left] (6.5,-2.45) ;

  \draw (-2,-1.5) to[bend right] (1,-3.5) ;
  \draw (-2,-2.5) to[bend right] (1,-4.5) ;
  \draw[->] (3.5,-3.5) to[bend right] (6.5,-1.55) ;
  \draw[->] (3.5,-4.5) to[bend right] (6.5,-2.55) ;

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

\begin{comment}
fully-distribute⇔l : {t₁ t₂ t₃ t₄ : U} → 
  (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊ ⇔
  ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎ ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷) 

  (distl ◎ (dist ⊕ dist)) ⇔
  ((dist ◎ (distl ⊕ distl)) ◎ ((id ⊕ swap₊) ⊕ id))
      
LHS : 
  (TIMES (PLUS t₁ t₂) (PLUS t₃ t₄)) ⟷
  (PLUS (PLUS (PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)) (TIMES t₁ t₄))) (TIMES t₂ t₄)

LHS : (t1+t2)(t3+t4) ⟷ ((t1t3 + t2t3) + t1t4) + t2t4

t1  
--
t2  
        t1
        --
        t2

        t3
        ==
        t1
        --
        t2 

        t4
t3  
--
t4  


\end{comment}

% \amr{Viewing 2 path are transformations on permutations on finite
% sets or as transformations of circuits drawn in a diagrammatic way
% like in 2path figure swap makes them very intuitive: if you see
% wires etc. connection to topology etc.

%   Of course, when it comes to computing with diagrams, the first
%   thing you have to make precise is exactly what you mean by
%   "diagram". In Joyal \& Street's picture, this literally a
%   geometric object, i.e. some points and lines in space. This works
%   very well, and pretty much exactly formalises what happens when
%   you do a pen-and-paper proof involving string diagrams. However,
%   when it comes to mechanising proofs, you need some way to
%   represent a string diagram as a data structure of some kind. From
%   here, there seem to be a few approaches:

% (1: combinatoric) its a graph with some extra bells and whistles (2:
% syntactic) its a convenient way of writing down some kind of term
% (3: "lego" style) its a collection of tiles, connected together on a
% 2D plane

% Point of view (1) is basically what Quantomatic is built on. "String
% graphs" aka "open-graphs" give a combinatoric way of working with
% string diagrams, which is sound and complete with respect to
% (traced) symmetric monoidal categories. See arXiv:1011.4114 for
% details of how we did this.

% Naiively, point of view (2) is that a diagram represents an
% equivalence class of expressions in the syntax of a monoidal
% category, which is basically back to where we started. However,
% there are more convenient syntaxes, which are much closer in spirit
% to the diagrams. Lately, we've had a lot of success in connected
% with abstract tensor notation, which came from Penrose. See
% g. arXiv:1308.3586 and arXiv:1412.8552.

% Point of view (3) is the one espoused by the 2D/higher-dimensional
% rewriting people (e.g. Yves Lafont and Samuel Mimram). It is also
% (very entertainingly) used in Pawel Sobocinski's blog:
% http://graphicallinearalgebra.net .

% This eliminates the need for the interchange law, but keeps pretty
% much everything else "rigid". This benefits from being able to
% consider more general categories, but is less well-behaved from the
% point of view of rewriting. For example as Lafont/Mimram point out,
% even finite rewrite systems can generate infinite sets of critical
% pairs.}

In contrast to the formal coherence conditions from Laplaza, the
2-combinators have more of a ``small-step'' nature which, from
experience with compilers for functional
languages~\citep{PeytonJones:1998:TOH:299619.299621}, makes them more
suitable for designing efficient optimizers. From our small
experiments, an effective way to use the rules is to fix a canonical
representation of circuits that has some desired properties (see many
such properties in the survey paper of
\citet{Saeedi:2013:SOR:2431211.2431220}) and use the rules in a
directed fashion to produce that canonical representation. Of course,
finding a rewriting procedure that makes progress towards the
canonical representation is generally far from trivial. Also the
current syntax is far from intuitive, and it might be critical to have
either a diagrammatic interface similar to
Quantomatic~\citep{quantomatic} (which only works for traced symmetric
monoidal categories) or a radically different syntactic notation such
as Penrose's abstract tensor notation~\citep{tensor1,tensor2}.

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
Our calculus provides a semantically well-founded approach to the
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
resources''~\citep{superstructural}.} Currently, these reversible
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
exclusively on reversible functions that directly correspond to
equivalences would have better computational properties. Our current
result is a step, albeit preliminary in that direction as it only
applies to finite types. However, it is plausible that this
categorification approach can be generalized to accommodate
higher-order functions. The intuitive idea is that our current
development based on the categorification of the commutative semiring
of the natural numbers might be generalizable to the categorification
of the ring of integers or even to the categorification of the field
of rational numbers. The generalization to rings would introduce
\emph{negative types} and the generalization to fields would further
introduce \emph{fractional types}. As Sec.~\ref{sec:7} suggests, there
is good evidence that these generalizations would introduce some
notion of higher-order functions. It is even possible to conceive of
more exotic types such as types with square roots and imaginary
numbers by further generalizing the work to the field of
\emph{algebraic numbers}. These types have been shown to make sense in
computations involving recursive datatypes such as trees that can be
viewed as solutions to polynomials over type
variables~\citep{seventrees,Fiore:2004,Fiore2004707}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% \clearpage
\bibliographystyle{abbrvnat}
%\softraggedright
\bibliography{cites}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}
