\documentclass[authoryear,preprint]{sigplanconf}
\usepackage{agda}
\usepackage{tikz}
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

\newcommand{\AgdaArgument}[1]{#1}
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
\begin{document}
\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\title{A Computational Interpretation of \\ Univalence for Finite Types}
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
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Function 
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
a proposition, and hence that this proposition must correspond to a type. In
Agda notation, we can formally express this as follows:

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

It is important to note that the notion of proposition equality $\equiv$
relates any two terms that are \emph{definitionally equal} as shown in
example $i1$ above. In general, there may be \emph{many} proofs (i.e., paths)
showing that two particular values are identical and that proofs are not
necessarily identical. This gives rise to a structure of great combinatorial
complexity.

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

\begin{code}
data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

-- Points 

⟦_⟧ : U → Set
⟦ ZERO ⟧       = ⊥
⟦ ONE ⟧        = ⊤
⟦ PLUS t t' ⟧  = ⟦ t ⟧ ⊎ ⟦ t' ⟧
⟦ TIMES t t' ⟧ = ⟦ t ⟧ × ⟦ t' ⟧

BOOL : U
BOOL = PLUS ONE ONE

BOOL² : U
BOOL² = TIMES BOOL BOOL

TRUE : ⟦ BOOL ⟧
TRUE = inj₁ tt

FALSE : ⟦ BOOL ⟧
FALSE = inj₂ tt

NOT : ⟦ BOOL ⟧ → ⟦ BOOL ⟧
NOT (inj₁ tt) = FALSE
NOT (inj₂ tt) = TRUE

CNOT : ⟦ BOOL ⟧ → ⟦ BOOL ⟧ → ⟦ BOOL ⟧ × ⟦ BOOL ⟧
CNOT (inj₁ tt) b = (TRUE , NOT b)
CNOT (inj₂ tt) b = (FALSE , b)

p₁ : FALSE ≡ FALSE
p₁ = refl FALSE

p₂ : _≡_ {A = ⟦ BOOL² ⟧} (FALSE , TRUE) (FALSE , (NOT FALSE))
p₂ = refl (FALSE , TRUE) 

p₃ : ⟦ BOOL ⟧ ≡ ⟦ BOOL ⟧
p₃ = refl ⟦ BOOL ⟧
\end{code}

In addition to all these trivial paths, there are structured paths. In
particular, paths in product spaces can be viewed as pair of paths. So in
addition to the path above, we also have:

\begin{code}
p₂' : (FALSE ≡ FALSE) × (TRUE ≡ TRUE) 
p₂' = (refl FALSE , refl TRUE) 

--α : p₂ ≡ p₂' not quite but something like that
--α = ? by some theorem in book

-- then talk about paths between bool and bool based on id / not;not
-- etc.
\end{code}

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
