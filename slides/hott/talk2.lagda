\documentclass[11pt]{beamer}
\usetheme{Boadilla}

\usepackage{agda}
\usepackage{tikz}
\usepackage{bbm}
\usepackage{animate}
\usepackage{hyperref}
\usepackage{graphicx}
\usepackage{longtable}
\usepackage{amsmath}
\usepackage{mdwlist}
\usepackage{txfonts}
\usepackage{xspace}
\usepackage{amstext}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{proof}
\usepackage{multicol}
\usepackage[nodayofweek]{datetime}
\usepackage{etex}
\usepackage{textgreek}
\usepackage[all, cmtip]{xy}

\newcommand{\red}[1]{{\color{red}{#1}}}
\newcommand{\blue}[1]{{\color{blue}{#1}}}

\newenvironment{floatrule}
    {\hrule width \hsize height .33pt \vspace{.5pc}}
    {\par\addvspace{.5pc}}

\title{An Introduction to \\
Homotopy Type Theory}
\author{Amr Sabry}
\institute{
  School of Informatics and Computing \\
  Indiana University
}

\date{October 31, 2013} 

\begin{document}

\maketitle

\AgdaHide{
\begin{code}
-- {-# OPTIONS --without-K #-}
module talk2 where
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product
import Level
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Recursion and induction principles}
\vfill

Each type has a recursion and an induction principle. 

\begin{code}
-- for natural numbers

recN : (C : Set) → C → (ℕ → C → C) → ℕ → C
recN C c f 0        = c
recN C c f (suc n)  = f n (recN C c f n)

indN :  (C : ℕ → Set) → 
        C 0 → ((n' : ℕ) → C n' → C (suc n')) → (n : ℕ) → C n
indN C c f 0        = c
indN C c f (suc n)  = f n (indN C c f n)
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Recursion and induction principles}
\vfill

Examples:

\AgdaHide{
\begin{code}
module X where
  open import Relation.Binary.PropositionalEquality
\end{code}
}

\begin{code}
  double : ℕ → ℕ
  double = recN ℕ 0 (λ n r → suc (suc r))

  add : ℕ → ℕ → ℕ
  add = recN (ℕ → ℕ) (λ n → n) (λ m g n → suc (g n))

  assocAdd : (i j k : ℕ) → add i (add j k) ≡ add (add i j) k
  assocAdd = 
    indN 
      (λ i → (j : ℕ) → (k : ℕ) → add i (add j k) ≡ add (add i j) k)
      (λ j k → ?)
      (λ i h j k → ?)
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Propositions as types}
\vfill
\begin{itemize}
\vfill\item A proposition is a statement that is \red{susceptible} to proof

\vfill\item A proposition \blue{$P$} is modeled as a type;

\vfill\item If the proposition is true, the corresponding type is inhabited,
i.e., it is possible to provide evidence for \blue{$P$} using one of the
elements of the type \blue{$P$}; 

\vfill\item If the proposition is false, the corresponding type is empty,
i.e., it is impossible to provide evidence for \blue{$P$};

\vfill\item Dependent functions give us $\forall$; dependent pairs give us
$\exists$.

\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Propositions as types (ctd.)}

\begin{code}
¬ : Set → Set
¬ A = A → ⊥

taut1 : {A B : Set} → ¬ A → ¬ B → ¬ (A ⊎ B)
taut1 na nb (inj₁ a) = na a
taut1 na nb (inj₂ b) = nb b

taut2 : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
taut2 nnna = λ a → nnna (λ na → na a)

taut3 : {A : Set} → ¬ (¬ (A ⊎ ¬ A))
taut3 = λ nana → nana (inj₂ (λ a → nana (inj₁ a)))
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Identity types}
\vfill
\begin{itemize}

\vfill\item The question of whether two elements of a type are equal is
clearly a \red{proposition}

\vfill\item This proposition corresponds to a type:

\end{itemize}

\begin{code}
data _≡_ {A : Set} : (a b : A) → Set where
  refl : (a : A) → (a ≡ a)

i0 : 3 ≡ 3
i0 = refl 3

i1 : (1 + 2) ≡ (3 * 1)
i1 = refl 3
\end{code}


\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Identity types and paths}
\begin{itemize}
\vfill\item We will interpret $x ≡ y$ as a \red{path} from $x$ to $y$
\vfill\item If $x$ and $y$ are themselves paths, then $x ≡ y$ as a \red{path
between paths}, i.e., a homotopy
\vfill\item We can continue this game to get paths between paths between
paths between paths etc.
\vfill\item What are the recursion and induction principle for these paths?
\end{itemize}

\begin{code}
-- recursion principle
indiscernability : {A : Set} {C : A → Set} {x y : A} → 
  (p : x ≡ y) → C x → C y
indiscernability (refl x) c = c
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{K vs. J}

Bad version:

\begin{code}
K : {A : Set} (C : {x : A} → x ≡ x → Set) →
    (∀ x → C (refl x)) →
    ∀ {x} (p : x ≡ x) → C p
K C c (refl x) = c x

proof-irrelevance : {A : Set} {x y : A} (p q : x ≡ y) →  p ≡ q
proof-irrelevance (refl x) (refl .x) = refl (refl x)
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Path induction}

Good version (goes back to Leibniz)

\begin{code}
-- J
pathInd : {A : Set} → (C : {x y : A} → x ≡ y → Set) → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

-- for comparison
K' : {A : Set} (C : {x : A} → x ≡ x → Set) →
     (∀ x → C (refl x)) →
     ∀ {x} (p : x ≡ x) → C p
K' C c (refl x) = c x
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Intensionality}
\begin{itemize}
\vfill\item If two terms $x$ and $y$ are \red{definitionally equal}, 
  then $x \equiv y$
\vfill\item The converse is \red{not true}
\vfill\item This gives rise to a structure of great combinatorial complexity
\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Homotopy Type Theory}
\vfill
\begin{itemize}
\vfill\item Martin-L\"of type theory
\vfill\item Identity types with path induction
\vfill\item \red{Univalence}
\vfill\item \red{Higher-Order Inductive Types}
\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Types as spaces or groupoids}

We are used to think of types as sets of values. So we think of the type Bool
as:

\begin{center}
\begin{tikzpicture}
  \draw (0,0) ellipse (2cm and 1cm);
  \draw[fill] (-1,0) circle [radius=0.025];
  \node[below] at (-1,0) {false};
  \draw[fill] (1,0) circle [radius=0.025];
  \node[below] at (1,0) {true};
\end{tikzpicture}
\end{center}

In HoTT, we should instead think about it as:

\begin{center}
\begin{tikzpicture}
  \draw (0,0) ellipse (2cm and 1cm);
  \draw[fill] (-1,0) circle [radius=0.025];
  \draw[->,thick,cyan] (-1,0) arc [radius=0.2, start angle=0, end angle=320];
  \node[above right] at (-1,0) {false};
  \draw[fill] (1,-0.2) circle [radius=0.025];
  \draw[->,thick,cyan] (1,-0.2) arc [radius=0.2, start angle=0, end angle=320];
  \node[above right] at (1,-0.2) {true};
\end{tikzpicture}
\end{center}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Types as spaces or groupoids}

In this particular case, it makes no difference, but in general we might have
something like:

\begin{center}
\begin{tikzpicture}
  \draw (0,0) ellipse (5cm and 2.5cm);
  \draw[fill] (-4,0) circle [radius=0.025];
  \draw[->,thick,cyan] (-4,0) arc [radius=0.2, start angle=0, end angle=320];
  \draw[fill] (0,0) circle [radius=0.025];
  \draw[->,thick,cyan] (0,0) arc [radius=0.2, start angle=-180, end angle=140];
  \draw[fill] (4,0) circle [radius=0.025];
  \draw[->,double,thick,blue] (-2.3,0.8) to [out=225, in=135] (-2.3,-0.8);
  \draw[->,double,thick,blue] (-1.7,0.8) to [out=-45, in=45] (-1.7,-0.8);
  \draw[->,thick,red] (-2.4,0.1) -- (-1.6,0.1);
  \draw[->,thick,red] (-2.4,0) -- (-1.6,0);
  \draw[->,thick,red] (-2.4,-0.1) -- (-1.6,-0.1);
  \draw[->,thick,cyan] (-4,0) to [out=60, in=120] (0,0);
  \draw[->,thick,cyan] (0,0) to [out=-120, in=-60] (-4,0);
  \draw[->,thick,cyan] (4,0) arc [radius=0.2, start angle=0, end angle=320];
  \draw[->,thick,cyan] (4,0) arc [radius=0.7, start angle=0, end angle=330];
  \draw[->,thick,cyan] (4,0) arc [radius=1.2, start angle=0, end angle=350];
  \draw[->,double,thick,blue] (1.8,0) -- (2.4,0);
\end{tikzpicture}
\end{center}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Additional structure}
\begin{itemize}

\vfill\item For every path $p : x \equiv y$, there exists a path $! p : y
\equiv x$;

\vfill\item For every paths $p : x \equiv y$ and $q : y \equiv z$, there
exists a path $p \circ q : x \equiv z$;

\vfill\item Subject to the following conditions:
  \begin{itemize}
  \vfill\item $p \circ \mathit{refl}~y \equiv p$
  \vfill\item $p \equiv \mathit{refl}~x \circ p$
  \vfill\item $!p \circ p \equiv \mathit{refl}~y$
  \vfill\item $p ~\circ~ !p \equiv \mathit{refl}~x$
  \vfill\item $!~(!p) \equiv p$
  \vfill\item $p \circ (q \circ r) \equiv (p \circ q) \circ r$
  \end{itemize}

\vfill\item With similar conditions one level up and so on and so forth.

\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Pause}

\vfill
\begin{center}
\LaTeX\ crash \ldots \\
Switch to third talk
\end{center}
\vfill

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{}
\vfill
\begin{itemize}
\vfill\item
\vfill\item
\vfill\item
\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{}

\begin{code}

\end{code}

\end{frame}

