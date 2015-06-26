\documentclass[preprint]{sigplanconf}

\usepackage{agda}
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

%% \DefineVerbatimEnvironment
%%   {code}{Verbatim}
%%  {} % Add fancy options here if you like.

\DeclareUnicodeCharacter{9678}{\ensuremath{\odot}}
\DeclareUnicodeCharacter{9636}{\ensuremath{\Box}}

\newtheorem{theorem}{Theorem}
\newtheorem{conj}{Conjecture}
\newtheorem{definition}{Definition}

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

\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.4\textwidth}\color{red}{Amr says: #1}\end{minipage}}}

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction} 

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

Our starting point is the notion of HoTT equivalence of types. We then
connect this notion to several semiring structures on finite types and
on permutations with the goal of reducing the notion of finite type
equivalence to a calculus of permutations.

%%%%%%%%%%%%
\subsection{HoTT Equivalences of Types} 

There are several equivalent definitions of the notion of equivalence
of types. For concreteness, we use the following definition as it
appears to be the most intuitive in our setting.

\begin{definition}[Equivalence of types]
  Two types $A$ and $B$ are equivalent $A ≃ B$ if there exists a
  \emph{bi-invertible} $f : A \rightarrow B$, i.e., if there exists an
  $f$ that has both a left-inverse and a right-inverse. A function
  $f : A \rightarrow$ has a left-inverse if there exists a function
  $g : B \rightarrow A$ such that $g \circ f = \mathrm{id}_A$. A
  function $f : A \rightarrow$ has a right-inverse if there exists a
  function $g : B \rightarrow A$ such that
  $f \circ g = \mathrm{id}_B$.
\end{definition}
Note that the function $g$ used for the left-inverse may be different
from the function $g$ used for the right-inverse.

As the definition of equivalence is parameterized by a function~$f$,
we are concerned with, not just the fact that two types are equivalent,
but with the precise way in which they are equivalent. For example,
there are two equivalences between the type \AgdaDatatype{Bool} and
itself: one that uses the identity for $f$ (and hence for $g$) and one
uses boolean negation for $f$ (and hence for $g$). These two
equivalences are themselves \emph{not} equivalent: each of them can be
used to ``transport'' properties of \AgdaDatatype{Bool} in a different
way.

%%%%%%%%%%%%
\subsection{Instance I: Universe of Types}

The first commutative semiring instance we examine is the universe of
types (\AgdaDatatype{Set} in Agda terminology). The additive unit is
the empty type $\bot$; the multiplicative unit is the unit type
$\top$; the two binary operations are disjoint union $\uplus$ and
cartesian product $\times$. The axioms are satisfied up to equivalence
of types~$\simeq$. For example, we have equivalences such as:
\[\begin{array}{rcl}
\bot ⊎ A &\simeq& A \\
\top \times A &\simeq& A \\
A \times (B \times C) &\simeq& (A \times B) \times C \\
A \times \bot &\simeq& \bot \\
A \times (B \uplus C) &\simeq& (A \times B) \uplus (A \times C) 
\end{array}\]

Formally we have the following fact. 

\begin{theorem}
The collection of all types (\AgdaDatatype{Set}) forms a commutative 
semiring (up to $\simeq$). 
\end{theorem}

%%%%%%%%%%%%
\subsection{Instance II: Finite Sets}
 
The collection of all finite sets (\AgdaDatatype{Fin}~$m$ for natural
number $m$ in Agda terminology) is another commutative semiring
instance. In this case, the additive unit is \AgdaDatatype{Fin}~$0$,
the multiplicative unit is \AgdaDatatype{Fin}~$1$, the two binary
operations are still disjoint union~$\uplus$ and cartesian
product~$\times$, and the axioms are also satisfied up to equivalence
of types~$\simeq$.

The reason finite sets are interesting is that each finite type~$A$
constructed from~$\bot$, $\top$, $\uplus$, and $\times$ is equivalent
(in $|A|~!$ ways) to \AgdaDatatype{Fin}~$|A|$ where $|A|$ is
the size of $A$ defined as follows:
\[\begin{array}{rcl}
|\bot| &=& 0 \\
|\top| &=& 1 \\
|A \uplus B| &=& |A| + |B| \\
|A \times B| &=& |A| * |B| 
\end{array}\]
Each of the $|A|~!$ equivalences of $A$ with \AgdaDatatype{Fin}~$|A|$
corresponds to a \emph{particular} enumeration of the elements of
$A$. For example, we have two equivalences:
\[\begin{array}{rcl}
\top \uplus \top &\simeq& \mathsf{Fin}~2
\end{array}\]
corresponding to the identity and boolean negation.

Thus, as we prove next, up to equivalence, the only interesting
property of a finite type is its size. In other words, given two
equivalent types $A$ and $B$ of completely different structure, e.g.,
$A = (\top \uplus \top) \times (\top \uplus (\top \uplus \top))$ and
$B = \top \uplus (\top \uplus (\top \uplus (\top \uplus (\top \uplus
(\top \uplus \bot)))))$, we can find equivalences from either type to
the finite set $\mathsf{Fin}~6$ and use the latter for further
reasoning. Indeed, as the next section demonstrate, this result allows
us to characterize equivalences between finite types in a canonical
way as permutations between finite sets.

The following theorem precisely characterizes the relationship between
finite types and finite sets.

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
element of $\mathsf{Fin}~(\mathit{suc}~m')$ and analyze every position
this element could be mapped to by the larger equivalence and in each
case construct an equivalence that excludes this element.
\end{proof}

In the remainder of the paper, we will refer to the type of all
equivalences between types $A$ and $B$ as $\textsc{eq}_{AB}$. As
explained above, this type is inhabited only if $|A|=|B|$ in which
case it has $|A|~!$ elements witnessing the various ways in which we
can have $A \simeq B$.

%%%%%%%%%%%%
\subsection{Permutations on Finite Sets} 

Given the correspondence between finite types and finite sets, we will
prove that equivalences on finite types are equivalent to permutations
on finite sets. Formalizing the notion of permutations is delicate
however: straightforward attempts turn out not to capture enough of
the properties of permutations for our purposes. We therefore
formalize a permutation using two sizes: $m$ for the size of the input
finite set and $n$ for the size of the resulting finite set. Naturally
in any well-formed permutations, these two sizes are equal but the
presence of both types allows us to conveniently define permutations
as follows. A permutation $\mathsf{CPerm}~m~n$ consists of four
components. The first two components are:
\begin{itemize}
\item a vector of size $n$ containing elements drawn from the finite 
  set $\mathsf{Fin}~m$; 
\item a dual vector of size $m$ containing elements drawn from the finite 
  set $\mathsf{Fin}~n$; 
\end{itemize}
Each of the above vectors can be interpreted as a map $f$ that acts on
the incoming finite set sending the element at index $i$ to position
$f !! i$ in the resulting finite set. To guarantee that these maps
define an actual permutation, the last two components are proofs that
the sequential composition of the maps in both direction produce the
identity.

In the remainder of the paper, we will refer to the type of all
permutations between finite sets $\mathsf{Fin}~m$ and $\mathsf{Fin}~n$
as $\textsc{perm}_{mn}$. This type is only inhabited if $m=n$ in which
case it has $m!$ elements, each of which witnesses one of the possible
permutations $\mathsf{CPerm}~m~n$.

%%%%%%%%%%%%
\subsection{Equivalences of Equivalences} 

The main result of this section is that the type of all equivalences
between finite types $A$ and $B$, $\textsc{eq}_{AB}$, is equivalent to
the type of all permutations $\textsc{perm}_{mn}$ where $m = |A|$ and
$n = |B|$.\footnote{In fact we have the following stronger theorem:
\begin{theorem}
The equivalence of Theorem~\ref{Perm} is an \emph{isomorphism} between the
semirings of equivalences of finite types, and of permutations.
\end{theorem}
}

\begin{theorem}\label{Perm}
If $A ≃ \mathsf{Fin}~m$ and $B ≃ \mathsf{Fin}~n$, then the type of all
equivalences $\textsc{eq}_{AB}$ is equivalent to the type of all
permutations $\textsc{perm}~m~n$.
\end{theorem}
\begin{proof}
...
\end{proof}

With the proper Agda definitions, we can rephrase the theorem in a way
that is more evocative of the phrasing of the \emph{univalence} axiom.

\begin{theorem}
$$ (A ≃ B) ≃ \mathsf{Perm} |A| |B| $$
\end{theorem}

To summarize the result of this section: if we are interested in
studying type equivalences, up to equivalence, it suffices to study
permutations on finite sets. This will prove quite handy as, unlike
the former, the latter notion can be inductively defined which gives
it a natural computational interpretation. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{A Calculus of Permutations}

A Calculus of Permutations.
Syntactic theories only rely on transforming source programs to other           
programs, much like algebraic calculation. Since only the                       
\emph{syntax} of the programming language is relevant to the syntactic          
theory, the theory is accessible to non-specialists like programmers            
or students.                                                                    

In more detail, it is a general problem that, despite its fundamental           
value, formal semantics of programming languages is generally                   
inaccessible to the computing public. As Schmidt argues in a recent             
position statement on strategic directions for research on programming          
languages~\cite{popularsem}:                                                    
\begin{quote}                                                                   
\ldots formal semantics has fed upon increasing complexity of concepts          
and notation at the expense of calculational clarity. A newcomer to             
the area is expected to specialize in one or more of domain theory,             
intuitionistic type theory, category theory, linear logic, process              
algebra, continuation-passing style, or whatever. These                         
specializations have generated more experts but fewer general users.            
\end{quote}                                                                     

\emph{Typed} Isomorphisms

First, a universe of (finite) types

\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
\end{code}
}

\begin{code}
data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

\end{code}
and its interpretation
\begin{code}

⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
\end{code}

A Calculus of Permutations. First conclusion: it might be useful to
\emph{reify} a (sound and complete) set of equivalences as
combinators, such as the fundamental ``proof rules'' of semirings:

\AgdaHide{
\begin{code}
infix  30 _⟷_
infixr 50 _◎_
\end{code}
}

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Example Circuit: Simple Negation}

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

Example Circuit: Not So Simple Negation. 

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

Reasoning about Example Circuits. Algebraic manipulation of one circuit to the other:

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

Visually.

{
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

{
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

{
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

{
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

{
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

{
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

{
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

{
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

{
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

{
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

{
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

{
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

{
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{But is this a programming language?}

\AgdaHide{
\begin{code}
open import Equiv using (_≃_; _●_; path⊎; path×)
import TypeEquiv as TE
\end{code}
}

We get forward and backward evaluators
\begin{code}
eval : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
evalB : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
\end{code}

which really do behave as expected
\begin{code}
c2equiv : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → ⟦ t₁ ⟧ ≃ ⟦ t₂ ⟧
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
\section{Categorification I}

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
\section{Emails}

\begin{verbatim}
Reminder of
http://mathoverflow.net/questions/106070/int-construction-traced-monoidal-categories-and-grothendieck-group

Also,
http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.163.334
seems relevant

Indeed, this does not seem to be in the library.

On 2015-04-10 10:52 AM, Amr Sabry wrote:
I had checked and found no traced categories or Int constructions in the categories library. I'll think about that and see how best to proceed.

The story without trace and without the Int construction is boring as a PL story but not hopeless from a more general perspective. --Amr

On 04/10/2015 09:06 AM, Jacques Carette wrote:
I don't know, that a "symmetric rig" (never mind higher up) is a
programming language, even if only for "straight line programs" is
interesting! ;)

But it really does depend on the venue you'd like to send this to.  If
POPL, then I agree, we need the Int construction.  The more generic that
can be made, the better.

It might be in 'categories' already!  Have you looked?

In the meantime, I will try to finish the Rig part.  Those coherence
conditions are non-trivial.
Jacques

On 2015-04-10, 06:06 , Sabry, Amr A. wrote:
I am thinking that our story can only be compelling if we have a hint
that h.o. functions might work. We can make that case by “just”
implementing the Int Construction and showing that a limited notion of
h.o. functions emerges and leave the big open problem of high to get
the multiplication etc. for later work. I can start working on that:
will require adding traced categories and then a generic Int
Construction in the categories library. What do you think? —Amr

On Apr 9, 2015, at 10:59 PM, Jacques Carette <carette@mcmaster.ca>
wrote:

I have the braiding, and symmetric structures done.  Most of the
RigCategory as well, but very close.

Of course, we're still missing the coherence conditions for Rig.

Jacques

On 2015-04-09 11:41 AM, Sabry, Amr A. wrote:
Can you make sense of how this relates to us?

https://pigworker.wordpress.com/2015/04/01/warming-up-to-homotopy-type-theory/

Unfortunately not.  Yes, there is a general feeling of relatedness, but I can't pin it down.

I do believe that all our terms have computational rules, so we can't get stuck.

Note that at level 1, we have equivalences between Perm(A,B) and Perm(A,B), not Perm(C,D) [look at the signature of <=>]. That said, we can probably use a combination of levels 0 and 1 to get there.

Yes, we should dig into the Licata/Harper work and adapt to our setting.

Though I think we have some short-term work that we simply need to do to ensure our work will rest on a solid basis.  If that crumbles, all the rest of the edifice will too.

Jacques

On 2015-04-09 12:05 PM, Amr Sabry wrote:
Trying to get a handle on what we can transport or more precisely if we can transport things that HoTT can only do with univalence.

(I use permutation for level 0 to avoid too many uses of 'equivalence' which gets confusing.)

Level 0: Given two types A and B, if we have a permutation between them then we can transport something of type P(A) to something of type P(B).

For example: take P = . + C; we can build a permutation between A+C and B+C from the given permutation between A and B

-- 

Level 1: Given types A, B, C, and D. let Perm(A,B) be the type of permutations between A and B and Perm(C,D) be the type of permutations between C and D. If we have a 2d-path between Perm(A,B) and Perm(C,D) then we can transport something of type P(Perm(A,B)) to something of type P(Perm(C,D)).

This is more interesting. What's a good example though of a property P that we can implement?

In think that in HoTT the only way to do this transport is via univalence. First you find an equivalence between the spaces of permutations, then you use univalence to postulate the existence of a path, and then you transport along that path. Is that right?

In HoTT this is exhibited by the failure of canonicity: closed terms that are stuck. We can't get closed terms that are stuck: we don't have any axioms with no computational rules, right?

Perhaps we can adapt the discussion/example in http://homotopytypetheory.org/2011/07/27/canonicity-for-2-dimensional-type-theory/ to our setting and build something executable?

--Amr

I hope not! [only partly joking]

Actually, there is a fair bit about this that I dislike: it seems to over-simplify by arbitrarily saying some things are equal when they are not.  They might be equivalent, but not equal.

On 2015-04-09 12:36 PM, Amr Sabry wrote:
This came up in a different context but looks like it might be useful to us too.

http://arxiv.org/pdf/gr-qc/9905020

Separate.  The Grothendieck construction in this case is about fibrations, and is not actually related to the "Grothendieck Group" construction, which is related to the Int construction.

Jacques

On 2015-04-10 11:56 AM, Sabry, Amr A. wrote:
Yes. The categories library has a Grothendieck construction. Not sure if we can use that or if we need to define a separate Int construction? —Amr

On Apr 10, 2015, at 11:04 AM, Jacques Carette <carette@mcmaster.ca> wrote:

Reminder of
http://mathoverflow.net/questions/106070/int-construction-traced-monoidal-categories-and-grothendieck-group

Also,
http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.163.334
seems relevant

Indeed, this does not seem to be in the library.

On 2015-04-10 10:52 AM, Amr Sabry wrote:
I had checked and found no traced categories or Int constructions in the categories library. I'll think about that and see how best to proceed.

The story without trace and without the Int construction is boring as a PL story but not hopeless from a more general perspective. --Amr

On 04/10/2015 09:06 AM, Jacques Carette wrote:
I don't know, that a "symmetric rig" (never mind higher up) is a
programming language, even if only for "straight line programs" is
interesting! ;)

But it really does depend on the venue you'd like to send this to.  If
POPL, then I agree, we need the Int construction.  The more generic that
can be made, the better.

It might be in 'categories' already!  Have you looked?

In the meantime, I will try to finish the Rig part.  Those coherence
conditions are non-trivial.
Jacques

On 2015-04-10, 06:06 , Sabry, Amr A. wrote:
I am thinking that our story can only be compelling if we have a hint
that h.o. functions might work. We can make that case by “just”
implementing the Int Construction and showing that a limited notion of
h.o. functions emerges and leave the big open problem of high to get
the multiplication etc. for later work. I can start working on that:
will require adding traced categories and then a generic Int
Construction in the categories library. What do you think? —Amr

On Apr 9, 2015, at 10:59 PM, Jacques Carette <carette@mcmaster.ca>
wrote:

I have the braiding, and symmetric structures done.  Most of the
RigCategory as well, but very close.

Of course, we're still missing the coherence conditions for Rig.

Jacques

solutions to quintic equations proof by arnold is all about hott… paths and higher degree path etc.

I thought we'd gotten at least one version, but could never prove it sound or complete.

On 2015-04-25 8:37 AM, Sabry, Amr A. wrote:
Didn’t we get stuck in the reverse direction. We never had it fully, or am I misremembering? —Amr

On Apr 25, 2015, at 8:27 AM, Jacques Carette <carette@mcmaster.ca> wrote:

Right.  We have one direction, from Pi combinators to FinVec permutations -- c2perm in PiPerm.agda.

Note that quite a bit of the code has (already!!) bit-rotted.  I changed the definition of PiLevel0 to make the categorical structure better, and that broke many things.  I am in the process of fixing -- which means introducing combinators all the way back in FinEquiv!!!  I split the 0 absorption laws into a right and left law, and so have to do the right version; turns out they are non-trivial, because Agda only reduces the left law for free. Should be done this morning.

We do not have the other direction currently in the code.  That may not be too bad, as we do have LeftCancellation to allow us to define things by recursion.

Jacques

On 2015-04-25 7:28 AM, Sabry, Amr A. wrote:
That’s obsolete for now.

By the way, do we have a complement to thm2 that connects to Pi. Ideally what we want to say is what I started writing: thm2 gives us a semantic bridge between equivalences and FinVec permutations; we also need a bridge between FinVec permutations and Pi combinators, right? —Amr


On Apr 24, 2015, at 5:25 PM, Jacques Carette <carette@mcmaster.ca> wrote:

Is that going somewhere, or is it an experiment that should be put into Obsolete/ ?
Jacques

Thanks.  I like that idea ;).

I have a bunch of things I need to do, so I won't really put my head into this until the weekend.

I understand the desire to not want to rely on the full coherence conditions.  I also don't know how to really understand them until we've implemented all of them, and see what they actually say!

As I was trying really hard to come up with a single story, I am a little confused as to what "my" story seems to be...  Can you give me your best recollection of what I seem to be pushing, and how that is different?  Then I would gladly flesh it out for us to do a second paper on that.

On 2015-04-23 9:07 PM, Sabry, Amr A. wrote:
Instead of discussing this over and over, I think it is clear that thm2 will be an important part of any story we will tell. So I think what I am going to start doing is to write an explanation of thm2 in a way that would be usable in a paper. —Amr

On Apr 23, 2015, at 6:07 PM, Amr Sabry <sabry@indiana.edu> wrote:

I wasn't too worried about the symmetric vs. non-symmetric notion of equivalence. The HoTT book has various equivalent definitions of equivalence and the one below is one of them.

I do recall the other discussion about extensionality. That discussion concluded with the idea that the strongest statement that can be made is that HoTT equivalence between finite *enumerated* types is equivalent to Vec-based permutations. This is thm2 and it is essentially univalence as we noted earlier. My concern however is what happens at the next level: once we start talking about equivalences between equivalences. We should be to use thm2 to say that this the same as talking about equivalences between Vec-based permutations, which as you noted earlier is equivalence of categories.

I just really want to avoid the full reliance on the coherence conditions. I also noted you have a different story and I am willing to go along with your story if you sketch a paper outline for say one of the conferences/workshops at http://cstheory.stackexchange.com/questions/7900/list-of-tcs-conferences-and-workshops

--Amr

On 04/23/2015 12:23 PM, Jacques Carette wrote:
Did you see my "HoTT-agda" question on the Agda mailing list on March
11th, and Dan Licata's reply?

What you wrote reduces to our definition of *equivalence*, not
permutation.  To prove that equivalence, we would need funext -- see my
question of February 18th on the Agda mailing list.

Another way to think about it is that this is EXACTLY what thm2
provides: a proof that for finite A and B, equivalence between A and B
(as below) is equivalent to permutations implemented as (Vect, Vect, pf,
pf).

Now, we may want another representation of permutations which uses
functions (qua bijections) internally instead of vectors.  Then the
answer to your question would be "yes", modulo the question/answer about
which encoding of equivalence to use.

Jacques

On 2015-04-23 10:32 AM, Sabry, Amr A. wrote:
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

—Amr


On Apr 21, 2015, at 11:03 AM, Jacques Carette <carette@mcmaster.ca>
wrote:

I'm ok with a HoTT bias, but concerned that our code does not really
match that.  But since we have no specific deadline, I guess taking a
bit more time isn't too bad.

Since propositional equivalence is really HoTT equivalence too, then
I am not too concerned about that side of things -- our concrete
permutations should be the same whether in HoTT or in raw Agda.  Same
with various notions of equivalence, especially since most of the
code was lifted from a previous HoTT-based attempt at things.

I would certainly agree with the not-not-statement: using a notion of
equivalence known to be incompatible with HoTT is not a good idea.

Jacques

On 2015-04-21 10:38 AM, Sabry, Amr A. wrote:
I think that I should start trying to write down a more technical
story so that we can see how things fit together. I am biased
towards a HoTT-related story which is what I started. If you think
we should have a different initial bias let me know.

What is there is just one paragraph for now but it already opens a
question: if we are pursuing that HoTT story we should be able to
prove that the HoTT notion of equivalence when specialized to finite
types reduces to permutations. That should be a strong foundation to
the rest and the precise notion of permutation we get (parameterized
by enumerations or not should help quite a bit).

More generally always keeping our notions of equivalences (at higher
levels too) in sync with the HoTT definitions seems to be a good
thing to do. —Amr

... and if these coherence conditions are really complete then it should be the case the two pi-combinators are equal iff their canonical forms are identical.

So to sum up we would get a nice language for expressing equivalences between finite types and a normalization process that transforms each equivalence to a canonical form. The latter yield a simple decision procedure for comparing equivalences.

--Amr

On 04/27/2015 06:16 AM, Sabry, Amr A. wrote:
Here is a nice idea: we need a canonical form for every pi-combinator. Our previous approach gave us something but it was hard to work with. I think we can use the coherence conditions to reach a canonical form by simply picking a convention that chooses one side of every commuting diagram. What do you think? —Amr

Indeed!  Good idea.

However, it may not give us a normal form.  This is because quite a few 'simplifications' require to use 'the other' side of a commuting diagram first, to expose a combination which simplifies.  Think (x . y^-1) . (y . z)  ~~ x . z.

In other words, because we have associativity and commutativity, we need to deal with those specially.  Diagram with sides not all the same length are easy to deal with.

However, I think it is not that bad: we can use the objects to help.  We also had put the objects [aka types] in normal form before (i.e. 1 + (1 + (1 + ... )))) ).  The good thing about that is that there are very few pi-combinators which preserve that shape, so those ought to be the only ones to worry about?  We did get ourselves in the mess there too, so I am not sure that's right either!

Here is another thought:
1. think of the combinators as polynomials in 3 operators, +, * and . (composition).
2. expand things out, with + being outer, * middle, . inner.
3. within each . term, use combinators to re-order things [we would need to pick a canonical order for all single combinators]
4. show this terminates

the issue is that the re-ordering could produce new * and/or + terms.  But with a well-crafted term order, I think this could be shown terminating.

Jacques

On 2015-04-27 6:16 AM, Sabry, Amr A. wrote:
Here is a nice idea: we need a canonical form for every pi-combinator. Our previous approach gave us something but it was hard to work with. I think we can use the coherence conditions to reach a canonical form by simply picking a convention that chooses one side of every commuting diagram. What do you think? —Amr

I've been thinking about this some more.  I can't help but think that, somehow, Laplaza has already worked that out, and that is what is actually in the 2nd half of his 1972 paper!  [Well, that Rig-Category 'terms' have a canonical form, but that's what we need]

Pi-combinators might be simpler, I don't know.

Another place to look is in Fiore (et al?)'s proof of completeness of a similar case.  Again, in their details might be our answer.

On 2015-04-26 6:34 AM, Sabry, Amr A. wrote:
What’s the proof strategy for establishing that a CPerm implies a Pi-combinator. The original idea was to translate each CPerm to a canonical Pi-combinator and then show that every combinator is equal to its canonical representative. Is that still the high-level idea? —Amr

Well enough.  Last talk on the last day, so people are tired.  Doubt we've caused a revolution in reversible computing...  Though when I mentioned that the slides were literate Agda, Peter Selinger made a point of emphasizing what that meant.

I think the idea that (reversible circuits == proof terms) is just a little too wild for it to sink in quickly.  Same with the idea of creating a syntactic language (i.e. Pi) out of the semantic structure of the desired denotational semantics (i.e. permutations).  People understood, I think, but it might be too much to really 'get'.

If we had a similar story for Caley+T (as they like to call it), it might have made a bigger splash.  But we should finish what we have first.

Note that I've pushed quite a few things forward in the code.  Most are quite straightforward, but they help explain what we are doing, and the relation between some of the pieces.  Ideally, there would be more of those easy ones [i.e. that evaluation is the same as the action of an equivalence which in turn is the same as the action of a permutation].  These are all 'extensional' in nature, but still an important sanity check.

Yes, I think this can make a full paper -- especially once we finish those conjectures.  It depends a little bit on which audience we would want to pitch it to.

I think the details are fine.  A little bit of polishing is probably all that's left to do.  Some of the transitions between topics might be a little abrupt.  And we need to reinforce the message of "semantics drive the syntax + syntactic theory is good", which is there, but a bit lost in the sea of details.  And the 'optimizing circuits' aspect could also be punched up a bit.

Writing it up actually forced me to add PiEquiv.agda to the repository -- which is trivial (now), but definitely adds to the story.  I think there might be some easy theorems relating PiLevel0 as a programming language, the action of equivalences, and the action of permutations.  In other words, we could get that all 3 are the same 'extensionally' fairly easily.  What we are still missing is a way to go back from either an equivalence or a permutation to a syntactic combinator.

Firstly, thanks Spencer for setting this up.

This is partly a response to Amr, and partly my own take on (computing with) graphical languages for monoidal categories.

One of the key ingredients to getting diagrammatic languages to do work for you is to actually take the diagrams seriously. String diagrams now have very strong coherence theorems which state that an equation holds by the axioms of (various kinds of) monoidal categories if and only if the diagrams are equal. The most notable of these are the theorems of Joyal & Street in Geometry of Tensor Calculus for monoidal, symmetric monoidal, and braided monoidal categories.

If you ignore these theorems and insist on working with the syntax of monoidal categories (rather than directly with diagrams), things become, as you put it "very painful".

Of course, when it comes to computing with diagrams, the first thing you have to make precise is exactly what you mean by "diagram". In Joyal & Street's picture, this literally a geometric object, i.e. some points and lines in space. This works very well, and pretty much exactly formalises what happens when you do a pen-and-paper proof involving string diagrams. However, when it comes to mechanising proofs, you need some way to represent a string diagram as a data structure of some kind. From here, there seem to be a few approaches:

(1: combinatoric) its a graph with some extra bells and whistles
(2: syntactic) its a convenient way of writing down some kind of term
(3: "lego" style) its a collection of tiles, connected together on a 2D plane

Point of view (1) is basically what Quantomatic is built on. "String graphs" aka "open-graphs" give a combinatoric way of working with string diagrams, which is sound and complete with respect to (traced) symmetric monoidal categories. See arXiv:1011.4114 for details of how we did this.

Naiively, point of view (2) is that a diagram represents an equivalence class of expressions in the syntax of a monoidal category, which is basically back to where we started. However, there are more convenient syntaxes, which are much closer in spirit to the diagrams. Lately, we've had a lot of success in connected with abstract tensor notation, which came from Penrose. See g. arXiv:1308.3586 and arXiv:1412.8552.

Point of view (3) is the one espoused by the 2D/higher-dimensional rewriting people (e.g. Yves Lafont and Samuel Mimram). It is also (very entertainingly) used in Pawel Sobocinski's blog: http://graphicallinearalgebra.net .

This eliminates the need for the interchange law, but keeps pretty much everything else "rigid". This benefits from being able to consider more general categories, but is less well-behaved from the point of view of rewriting. For example as Lafont/Mimram point out, even finite rewrite systems can generate infinite sets of critical pairs.

This is a very good example of CCT. As I am sure that you and others on the list (e.g., Duncan Ross) know monoidal cats have been suggested for quantum mechanics, they are closely related to Petri nets, linear logic, and other “net-based” computational systems. There is considerable work on graphic syntax.  It would be interesting to know more details on your cats and how you formalize them.
 
My primary CCT interest, so far, has been with what I call computational toposes. This is a slight strengthening of an elementary topos to make subobject classification work in a computational setting. This is very parallel to what you are doing, but aimed at engineering modeling. The corresponding graphical syntax is an enriched SysML syntax. SysML is a dialect of UML. These toposes can be used to provide a formal semantics for engineering modeling.

There's also the perspective that string diagrams of various flavors are morphisms in some operad (the composition law of which allows you to nest morphisms inside of morphisms). 

From that perspective, the string diagrams for traced monoidal categories are little more than just bijections between sets. This idea, and its connection to rewriting (finding normal forms for morphisms in a traced or compact category), is something Jason Morton and I have been working on recently.

Yes, I am sure this observation has been made before.  We'd have to verify it for all the 2-paths before we really claim this.

[And since monoidal categories are involved in knot theory, this is un-surprising from that angle as well]

On 2015-06-02 7:53 PM, Sabry, Amr A. wrote:
looking at that 2path picture… if these were physical wires and boxes, we could twist the wires, flipping the c1-c2 box and having them cross on the other side. So really as we have noted before I am sure, these 2paths are homotopies in the sense of smooth transformations between paths. Not sure what to do with this observation at this point but I thought it is worth noting. —Amr

There are some slightly different approaches to implementing a category as a computational system which make more intrinsic use of logic, than the ones mentioned by Aleks.  As well there is a different take on the relationship of graphical languages to the category implementation.

A category can be formalized as a kind of elementary axiom system using a language with two sorts, map and type (object), with equality for each sort.  The signature contain the function symbols,  Domain and Range. The arguments of both are a map and whose value is a type. The abbreviation

                f:X to Y equiv Domain(f) = X and Range(f) = Y

is used for the three place predicate. 

The operations such as the binary composition of maps are represented as first order function symbols. Of course the function constructions are not interpreted as total functions in the standard first order model theory. So, for example, one has axioms such as the typing condition

f:Z to Y, g:Y to X implies g(f):Z to X

A function symbol that always produces a map with a unique domain and range type, as a function of the arguments, is called a constructor. For example, id(X) is a constructor with a type argument.  This same kind of logic can be used to present linear logics.

For most of the systems that I have looked at the axioms are often “ rules”, such as the category axioms. Sometimes one needs axioms which have rules as consequences.  One can use standard first order inference together with rewrite technology to compute.  The axioms for a category imply that the terms generate a directed graph. Additional axioms provide congruence relations on the graph.

A morphism of an axiom set using constructors is a functor.  When the axioms include products and powers,  the functors map to sets, this yields is a form of Henkin semantics. Thus, while it is not standard first order model theory, is well-known.  For other kinds of axiom systems a natural semantics might be Hilbert spaces.

With this representation of a category using axioms in the “constructor” logic, the axioms and their theory serve as a kind of abstract syntax.  The constructor logic approach provides standardization for categories which can be given axioms in this logic.  Different axiom sets can be viewed as belonging to different profiles. The logic representation is independent of any particular graphical syntax. A graphical syntax would, of course have to interpret that axioms correctly.  Possibly the Joyal and Street theorems can be interpreted as proving the graphical representation map is a structure preserving functor. Possibly the requirements for a complete graphical syntax is that it is an invertible functor.

'm writing you offline for the moment, just to see whether I am understanding what you would like. In short, I guess you want a principled understanding of where the coherence conditions come from, from the perspective of general 2-category theory perhaps (a la work of the Australian school headed by Kelly in the 1970's). 

We are in some sense categorifying the notion of "commutative rig". The role of commutative monoid is categorified by symmetric monoidal category, which roughly is the next notion past commutative monoid in the stable range on the periodic table. 

I believe there is a canonical candidate for the categorification of tensor product of commutative monoids. In other words, given symmetric monoidal categories A, B, C, the (symmetric monoidal) category of functors A x B --> C that are strong symmetric monoidal in separate arguments should be equivalent to the (sm) category of strong symmetric monoidal functors A \otimes B --> C, for this canonical tensor product A \otimes B. Actually, I don't think we absolutely need this construction -- we could phrase everything in terms of "multilinear" (i.e. multi-(strong sm)) functors A_1 x ... x A_n --> B, but it seems a convenience worth taking advantage of. In fact, let me give this tensor product a more neutral name -- I'll write @, and I for the tensor unit -- because I'll want to reserve \otimes for something else (consistent with Laplaza's notation). 

If S is the 2-category of symmetric monoidal categories, strong symmetric monoidal functors, and monoidal natural transformations, then this @ should endow S with a structure of (symmetric) monoidal 2-category, with some other pleasant properties (such as S's being symmetric monoidal closed in the appropriate 2-categorical sense). All of these facts should be deducible on abstract grounds, by categorifying the notion of commutative monad (such as the free commutative monoid monad on Set) to an appropriate categorification to commutative 2-monad on Cat, and categorifying the work of Kock on commutative monads. 

In any symmetric monoidal 2-category, we have a notion of "pseudo-commutative pseudomonoid", which generalizes the notion of symmetric monoidal category in the special case of the monoidal 2-category (Cat, x). Anyhow, if (C, \oplus, N) is a symmetric monoidal category, then I my guess (I've checked some but not all details) is that a symmetric rig category is precisely a pseudo-commutative pseudomonoid object 

(\otimes: C @ C --> C, U: I --> C, etc.) 

in (S, @). I would consider this is a reasonable description stemming from general 2-categorical principles and concepts. 

Would this type of thing satisfy your purposes, or are you looking for something else? 

Quite related indeed.  But much more ad hoc, it seems [which they acknowledge].
Jacques

On 2015-05-17 8:01 AM, Sabry, Amr A. wrote:
Something closer to our work http://www.informatik.uni-bremen.de/agra/doc/konf/rc15_ricercar.pdf

—Amr

More related work (as I encountered them, but later stuff might be more important):

Diagram Rewriting and Operads, Yves Lafont
http://iml.univ-mrs.fr/~lafont/pub/diagrams.pdf

A Homotopical Completion Procedure with Applications to Coherence of Monoids
http://drops.dagstuhl.de/opus/frontdoor.php?source_opus=4064

A really nice set of slides that illustrates both of the above
http://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_kbs.pdf

I think there is something very important going on in section 7 of 
http://comp.mq.edu.au/~rgarner/Papers/Glynn.pdf
which I also attach.  [I googled 'Knuth Bendix coherence' and these all came up]

There are also seems to be relevant stuff buried (very deep!) in chapter 13 of Amadio-Curiens' Domains and Lambda Calculi.

Also, Tarmo Uustalu's "Coherence for skew-monoidal categories", available on http://cs.ioc.ee/~tarmo/papers/

[Apparently I could have saved myself some of that searching time by going to http://ncatlab.org/nlab/show/rewriting !  At the bottom, the preprint by Mimram seems very relevant as well]

Somehow, at the end of the day, it seems we're looking for a confluent, terminating term-rewriting system for commutative semirings terms!


\end{verbatim}

\includegraphics{IMAG0342.jpg}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\appendix
\section{Commutative Semirings}
 
Given that the structure of commutative semirings is central to this
paper, we recall the formal algebraic definition.

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

In the paper, we are interested into various commutative semiring
structures up to some congruence relation instead of strict
equality~$=$.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}

