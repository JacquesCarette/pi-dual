\documentclass[11pt]{beamer}
\usetheme{Boadilla}

% make the spacing less generous
\ifdefined\mathindent
  \newcommand{\oldmathindent}{\mathindent}
  \renewcommand{\mathindent}{0mm}
  \usepackage{agda}
  % \renewcommand{\mathindent}{\oldmathindent}
\else
  \newcommand{\mathindent}{0mm}
  \usepackage{agda}
\fi

% \usepackage{agda}
% \usepackage{fancyvrb}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{tikz}
\usepackage{amsthm}
\usepackage{latexsym}
\usepackage{courier}
\usepackage{thmtools}
\usepackage{bbold}
% \usepackage{url}
\usepackage{bbm}
\usepackage{proof}
\usepackage{amstext}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{comment}
\usepackage{stmaryrd}
% \usepackage{listings}
\usepackage{graphicx}
\usepackage{textgreek}
\usepackage{extarrows}

\newenvironment{proenv}{\only{\setbeamercolor{local structure}{fg=green}}}{}
\newenvironment{conenv}{\only{\setbeamercolor{local structure}{fg=red}}}{}

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
\newcommand{\factorzl}{\mathit{factorl}_0}
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

% for the slides
\newcommand{\true}{\mathit{true}}
\newcommand{\false}{\mathit{false}}

%% \DefineVerbatimEnvironment
%%   {code}{Verbatim}
%%  {} % Add fancy options here if you like.

\DeclareUnicodeCharacter{9678}{\ensuremath{\odot}}
\DeclareUnicodeCharacter{9636}{\ensuremath{\Box}}

\newtheorem{conj}{Conjecture}

\setbeamertemplate{theorems}[ams style]
\setbeamertemplate{blocks}[rounded][shadow=false]
\setbeamertemplate{navigation symbols}{}%remove navigation symbols

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
\title[Computing with Rigs]{Computing with Semirings and Weak Rig Groupoids}
\author[Carette-Sabry]{\textcolor{blue}{Jacques Carette} \and Amr Sabry}
\institute[McMaster-IU]{McMaster University \and Indiana University}
\date{7 April 2016}
\begin{document}
\maketitle

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Outline}
\begin{itemize}
\item[\checkmark] Usual Curry-Howard (true, false, or, and)
\item[\checkmark] enriched: symmetry, true and X, false or X
\item[\checkmark] unusual? X or X iff X.  X and X iff X. true or X iff true
\item[\checkmark] reversibility enters the picture: only isos
\item[\checkmark] define isos.  give tricky examples?
\item[\checkmark] give type isos.
\item[\checkmark] recognize this... proof terms for semirings
\item[\checkmark] observations:
1. the inhabitants of isos are the proof terms of basic semiring identities
2. the proof terms for a semiring make a nice base language
3. both are missing combinators
4. A x A ~ A x A has two proofs, which are not equal
\item[\checkmark] idea: make a PL whose types are isos and terms are iso combinators
\item[\checkmark] give combinators
\item example programs, proofs, nice prop: syntactic reversibility
\item semantics of Pi
\item Q: when are Pi programs equivalent? (motivates looking at equiv of equiv)
\item but do note that Pi programs do NOT form a semiring, even if we have combinators
  (types don't match).  Need to categorify.
\item and keep going

\end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Simple Curry-Howard}
\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Function using (_∘_; id)
\end{code}
}
\begin{minipage}[t]{.22\textwidth}
Constructors

\begin{tabular}{c|c}
Logic & Types \\ \hline
$\true$ & $\top$ \\
$\false$ & $\bot$ \\
$∧$ & $×$ \\
$∨$ & $⊎$ \\
$\Rightarrow$ & $\rightarrow$ \\
$\forall$ & Π \\
$\exists$ & Σ \\
\end{tabular}
\end{minipage}
\pause
\renewcommand{\arraystretch}{1.2}
\begin{minipage}[t]{0.74\textwidth}
Digging deeper:

\renewcommand{\AgdaCodeStyle}{\footnotesize}
\begin{tabular}{p{3.3cm}|l}
Logical Implication & Inhabiting Term \\ \hline
$ A∧B ⇒ B∧A $ & $\lambda \{(a , b) → (b , a)\}$ \\
$ \true ∧ A ⇒ A $ & $\lambda \{(\mathit{tt} , a) → a\}$ \\
$ A ⇒ \true ∧ A $ & $\lambda a → \mathit{tt} , a$ \\
$ \false ∨ A ⇒ A $ &
\begin{minipage}{0.4\textwidth}
\begin{code}
⊥e₊ : {A : Set} → ⊥ ⊎ A → A
⊥e₊ (inj₁ ())
⊥e₊ (inj₂ y) = y
\end{code}
\end{minipage} \\
$A ⇒ \false ∨ A $ &
\begin{minipage}{0.3\textwidth}
\begin{code}
⊥i₊ : {A : Set} → A → ⊥ ⊎ A
⊥i₊ a = inj₂ a
\end{code}
\end{minipage} \\
\end{tabular}
\pause
\vspace{3mm}
\renewcommand{\arraystretch}{1.5}
\begin{tabular}{p{3.3cm}|l}
Logical Equivalence & Type Isomorphism \\ \hline
$ A ∧ B ⇔ B ∧ A $ & $A × B ≃ B × A$ \\
$ \true ∧ A ⇔ A$ & $⊤ × A ≃ A$ \\
$ \false ∨ A ⇔ A$ & $⊥ ⊎ A ≃ A$ \\
\end{tabular}
\end{minipage}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Classical Curry-Howard: Inhabitation}
\renewcommand{\arraystretch}{1.5}
\begin{tabular}{p{3.3cm}|l}
Logical Equivalence & Type \textcolor{red}{non-}Isomorphism \\ \hline
$ A ∨ A ⇔ A $ & $A ⊎ A ≄ A$ \\
$ A ∧ A ⇔ A $ & $A × A ≄ A$ \\
$ \true ∨ A ⇔ \true$ & $⊤ ⊎ A ≄ ⊤$ \\
\end{tabular}
\vfill
There \emph{are} functions which witness inhabitation in each direction, but these
\textcolor{red}{forget information}, i.e. are not inverses.
\vfill
\pause
Desideratum: only isomorphisms in the right column.\\
Motivation and inspiration:
\begin{itemize}
\item Reversible computing.  Quantum computing.
\item Homotopy Type Theory.
\end{itemize}
\vfill
\pause
Q: What would the table look like then?
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Type isomorphisms I}
\renewcommand{\AgdaCodeStyle}{\footnotesize}

\begin{definition}[Homotopy]\label{def:homotopy}
Two functions $f,g:A \rightarrow B$ are \emph{homotopic}, written $f ∼
g$, if $\forall x:A. f(x) = g(x)$.
\medskip 
\begin{code}
_∼_ : ∀ {A : Set} {P : A → Set} → (f g : (x : A) → P x) → Set
_∼_ {A} f g = (x : A) → f x ≡ g x
\end{code}
\end{definition}
\pause
\begin{definition}[Quasi-inverse]
\label{def:quasi}
For a function $f : A \rightarrow B$, a \emph{quasi-inverse} of~$f$ is a
triple $(g, \alpha, \beta)$, consisting of a function
$g : B \rightarrow A$ and two homotopies
$\alpha : f \circ g \sim \mathrm{id}_B$ and
$\beta : g \circ f \sim \mathrm{id}_A$.

\medskip
\begin{code}
record isqinv {A : Set} {B : Set} (f : A → B) : Set where
  constructor qinv
  field
    g : B → A
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id
\end{code}
\end{definition}
\end{frame}

\begin{frame}{Type isomorphisms II}
\begin{definition}[Equivalence of types]\label{def:eq}
  Two types $A$ and $B$ are equivalent $A ≃ B$ if there exists a
  function $f : A \rightarrow B$ together with a quasi-inverse for
  $f$. 
\medskip 
\begin{code}
_≃_ : Set → Set → Set
A ≃ B = Σ (A → B) isqinv
\end{code}
\end{definition}
\pause
(Tricky) Example\\
\begin{code}
left0e : {A : Set} → ⊥ × A → ⊥
left0e (b , _) = b
left0i : {A : Set} → ⊥ → ⊥ × A
left0i ()

left0ei : {A : Set} → (left0e {A} ∘ left0i) ∼ id
left0ei ()
left0ie : {A : Set} → (left0i {A} ∘ left0e) ∼ id
left0ie (() , _)
\end{code}
\end{frame}

\begin{frame}{Type isomorphisms III}
\begin{minipage}{0.49\textwidth}
{Type isomorphisms}
\[\begin{array}{rcl}
⊥ ⊎ A               & ≃ & A                  \\
A ⊎ B               & ≃ & B ⊎ A             \\
A ⊎ (B ⊎ C)         & ≃ & (A ⊎ B) ⊎ C    \\
                                              \\
⊤ × A           & ≃ & A                  \\
A × B           & ≃ & B × A         \\
A × (B × C) & ≃ & (A × B) × C \\
                                              \\
⊥ × A           & ≃ & ⊥                   \\
(A ⊎ B) × C     & ≃ & (A × C) ⊎ (B × C)
\end{array}\]
\end{minipage}
\pause
\begin{minipage}{0.49\textwidth}
{Semiring Equalities}
\[\begin{array}{rcl}
0 + a               & = & a                  \\
a + b               & = & b + a             \\
a + (b + c)         & = & (a + b) + c    \\
                                              \\
1 \cdot a           & = & a                  \\
a \cdot b           & = & b \cdot a         \\
a \cdot (b \cdot c) & = & (a \cdot b) \cdot c \\
                                              \\
0 \cdot a           & = & 0                   \\
(a + b) \cdot c     & = & (a \cdot c) + (b \cdot c)
\end{array}\]
\end{minipage}
\end{frame}

\begin{frame}{Observations}
\begin{enumerate}
\item<pro@1-> the inhabitants of type isomorphisms are \textcolor{red}{exactly}
the proof terms of basic commutative semiring identities
\item<pro@1-> \uncover<2->{the proof terms for a commutative semiring make a nice base programming language}
\item<con@1-> \uncover<3->{both are missing combinators
\begin{itemize}
\item how would I prove $(0 ⊎ A) × (B × C) ≃ (A × B) × C$ ?
\end{itemize}
}
\item<con@1-> \uncover<4->{$A x A ≃ A x A$ has two proofs, \textcolor{red}{which are not equal}
\begin{itemize}
\item identity
\item swap (commutativity)
\end{itemize}
}
\end{enumerate}

\pause
\large Let's make a programming language out of semiring identities / type isomorphisms!
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Reifying isomorphisms}
First, a universe of (finite) types

\vspace*{0.4cm}
\begin{code}
data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

\end{code}
and its interpretation \vspace*{0.4cm}

\begin{code}
⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
\end{code}

For notational brevity, we will denote these $0, 1, + and *$ respectively.
\end{frame}

\begin{frame}{The $\Pi$ Language}
\vspace*{ -2em}
\[
\begin{array}{rrcll}
\idc :& \tau & \iso & \tau &: \idc \\
\identlp :&  0 + \tau & \iso & \tau &: \identrp \\
\swapp :&  \tau_1 + \tau_2 & \iso & \tau_2 + \tau_1 &: \swapp \\
\assoclp :&  \tau_1 + (\tau_2 + \tau_3) & \iso & (\tau_1 + \tau_2) + \tau_3 &: \assocrp \\
\identlt :&  1 * \tau & \iso & \tau &: \identrt \\
\swapt :&  \tau_1 * \tau_2 & \iso & \tau_2 * \tau_1 &: \swapt \\
\assoclt :&  \tau_1 * (\tau_2 * \tau_3) & \iso & (\tau_1 * \tau_2) * \tau_3 &: \assocrt \\
\distz :&~ 0 * \tau & \iso & 0 ~ &: \factorzl \\
\dist :&~ (\tau_1 + \tau_2) * \tau_3 & \iso & (\tau_1 * \tau_3) + (\tau_2 * \tau_3)~ &: \factor
\end{array}
\]
\[
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_2 \iso \tau_3}
{\jdg{}{}{c_1 \odot c_2 : \tau_1 \iso \tau_3}}
{}
\qquad
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \oplus c_2 : \tau_1 + \tau_3 \iso \tau_2 + \tau_4}}
{}
\]
\[
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \otimes c_2 : \tau_1 * \tau_3 \iso \tau_2 * \tau_4}}
{}
\]
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{And in Agda}

\AgdaHide{
\begin{code}
infix  30 _⟷_
infixr 50 _◎_
\end{code}
}
\renewcommand{\AgdaCodeStyle}{\tiny}

\begin{code}
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
\end{code}
\AgdaHide{
\begin{code}
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
\end{code}
}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Example Circuit: Simple Negation}

\begin{center}
\begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
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

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Example Circuit: Not So Simple Negation}

\begin{center}
\begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
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

\end{frame}

\end{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Reasoning about Example Circuits}

Algebraic manipulation of one circuit to the other:

\AgdaHide{
\begin{code}

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
\end{code}
}

\renewcommand{\AgdaCodeStyle}{\tiny}
\begin{code}

negEx : n₂ ⇔ n₁
negEx = uniti⋆ ◎ (swap⋆ ◎ ((swap₊ ⊗ id⟷) ◎ (swap⋆ ◎ unite⋆)))
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
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Visually}

\only<1>{
Original circuit:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
}

\only<2>{
Making grouping explicit:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (4.8,-1.5) -- cycle; 
  \draw[red,dashed] (3.3,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (3.3,-1.7) -- cycle; 
  \draw[red,dashed] (1.8,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.8,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
}

\only<3>{
By associativity:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (4.8,-1.5) -- cycle; 
  \draw[red,dashed] (3.3,2.8) -- (4.4,2.8) -- (4.4,-1.3) -- (3.3,-1.3) -- cycle; 
  \draw[red,dashed,thick] (1.8,3.0) -- (4.6,3.0) -- (4.6,-1.5) -- (1.8,-1.5) -- cycle; 
  \draw[red,dashed] (1.6,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (1.6,-1.7) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
}

\only<4>{
By pre-post-swap:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (4.8,-1.5) -- cycle; 
  \draw[red,dashed] (3.3,2.8) -- (4.4,2.8) -- (4.4,-1.3) -- (3.3,-1.3) -- cycle; 
  \draw[red,dashed,thick] (1.8,3.0) -- (4.6,3.0) -- (4.6,-1.5) -- (1.8,-1.5) -- cycle; 
  \draw[red,dashed] (1.6,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (1.6,-1.7) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
}

\only<5>{
By associativity:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (4.8,-1.5) -- cycle; 
  \draw[red,dashed] (3.3,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (3.3,-1.7) -- cycle; 
  \draw[red,dashed] (1.6,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.6,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
}

\only<6>{
By associativity:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (4.8,2.6) -- (5.8,2.6) -- (5.8,-1.1) -- (4.8,-1.1) -- cycle; 
  \draw[red,dashed,thick] (3.5,2.8) -- (6.0,2.8) -- (6.0,-1.3) -- (3.5,-1.3) -- cycle; 
  \draw[red,dashed] (3.3,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (3.3,-1.7) -- cycle; 
  \draw[red,dashed] (1.6,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.6,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
}

\only<7>{
By swap-swap:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed,thick] (3.5,2.8) -- (6.0,2.8) -- (6.0,-1.3) -- (3.5,-1.3) -- cycle; 
  \draw[red,dashed] (3.3,3.2) -- (9.4,3.2) -- (9.4,-1.7) -- (3.3,-1.7) -- cycle; 
  \draw[red,dashed] (1.6,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.6,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
}

\only<8>{
By id-compose-left:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (1.6,3.4) -- (9.6,3.4) -- (9.6,-1.9) -- (1.6,-1.9) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
}

\only<9>{
By associativity:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (1.6,2.6) -- (5.8,2.6) -- (5.8,-1.1) -- (1.6,-1.1) -- cycle; 
  \draw[red,dashed] (-0.5,2.8) -- (6.0,2.8) -- (6.0,-1.3) -- (-0.5,-1.3) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
}

\only<10>{
By swap-unit:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (3.6,2.6) -- (5.8,2.6) -- (5.8,-1.1) -- (3.6,-1.1) -- cycle; 
  \draw[red,dashed] (-0.5,2.8) -- (6.0,2.8) -- (6.0,-1.3) -- (-0.5,-1.3) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (4.2,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (4.2,2) circle [radius=0.025];
  \node[below] at (4.2,2) {*};

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
}

%%        swap₊ ◎ (uniti⋆ ◎ unite⋆)

\only<11>{
By associativity:
\begin{center}
\begin{tikzpicture}
  \draw[red,dashed] (6.2,2.8) -- (9.0,2.8) -- (9.0,-1.3) -- (6.2,-1.3) -- cycle; 
  \draw[red,dashed] (3.6,3.0) -- (9.2,3.0) -- (9.2,-1.5) -- (3.6,-1.5) -- cycle; 
  \draw[red,dashed] (-0.7,3.6) -- (9.8,3.6) -- (9.8,-2.1) -- (-0.7,-2.1) -- cycle; 

  \draw (4.2,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (4.2,2) circle [radius=0.025];
  \node[below] at (4.2,2) {*};

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
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
}

\only<12>{
By unit-unit:
\begin{center}
\begin{tikzpicture}
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
}

\only<13>{
By id-unit-right:
\begin{center}
\begin{tikzpicture}
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
}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{But is this a programming language?}

\AgdaHide{
\begin{code}
open import Equiv using (_●_; _⊎≃_; _×≃_; id≃)
import TypeEquiv as TE
\end{code}
}

We get forward and backward evaluators
\begin{code}
eval : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
evalB : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
\end{code}
\pause

which really do behave as expected
\begin{code}
c2equiv : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → ⟦ t₁ ⟧ ≃ ⟦ t₂ ⟧
\end{code}

\AgdaHide{
\begin{code}
eval p v = {!!}
evalB p v = {!!}
c2equiv cc = {!!}
\end{code}
}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Manipulating circuits}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Categorification I}
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
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{2-morphism of circuits}

\begin{center}
\begin{tikzpicture}
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

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Categorification II}
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
\end{frame}

\begin{frame}{Categorification III}
\begin{conj}
The following are \textcolor{red}{Symmetric Rig Groupoids}:
\begin{itemize}
\item The class of all types (\AgdaDatatype{Set})
\item The set of all finite types, of permutations, of equivalences between finite types
\item Our syntactic combinators
\end{itemize}
\end{conj}
\pause
and of course the punchline:
\begin{theorem}[Laplaza 1972]
There is a sound and complete set of \textcolor{red}{coherence rules} for 
Symmetric Rig Categories.
\end{theorem}
\begin{conj}
The set of coherence rules for Symmetric Rig Groupoids are a sound
and complete set for \textcolor{red}{circuit equivalence}.
\end{conj}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{?}
\end{frame}
