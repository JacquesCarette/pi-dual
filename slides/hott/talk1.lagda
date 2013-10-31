\documentclass[11pt]{beamer}
\usetheme{Boadilla}

\usepackage{agda}
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
module talk1 where
import Level
infixr 5 _∷_
infixl 6 _+_ 
infixl 7 _*_ 
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]

\begin{center}
\scalebox{0.5}{
\includegraphics{pics/scientific-american.png}
}
\end{center}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Homotopy Type Theory (HoTT)}

\begin{itemize}
\vfill\item Foundational;

\vfill\item New perspectives on old problems;

\vfill\item Connections to computer science, logic, algebra, geometry,
topology, and physics;

\vfill\item Bridges between communities;

\vfill\item What is it about exactly?

\end{itemize}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Steve Awodey's introduction (Feb. 2012)}

\begin{center}
\scalebox{0.9}{
\includegraphics{pics/awodey.pdf}
}
\end{center}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{In English (bigger informal picture)}
\vfill
\begin{itemize}
\vfill\item We are discovering that \red{every} process around us has
computational content (even the design of outlines of 18th century string
instruments as developed in \blue{Functional geometry and the Trait\'e de
  Lutherie}, ICFP 2013)

\vfill\item We have known for quite a while (by the Curry-Howard
correspondence) that \red{mathematical proofs have computational content}
(\blue{type theory}, \blue{mechanized logic}, \blue{computational logic},
etc. are all well-established)

\vfill\item Feynman, Minsky, Landauer, Fredkin, and others have pushed the
thesis that \red{physical laws have computational content}. Here is one of my
favorite quotes:
\begin{quote}
  \ldots the real world is unlikely to supply us with unlimited memory or
  unlimited Turing machine tapes. Therefore, continuum mathematics is not
  executable, and physical laws which invoke that can not really be
  satisfactory \ldots
\end{quote}

\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Common Themes: Physics perspective}

\begin{itemize}

\vfill\item From the physical perspective: the laws of conservation of energy
and information translate to ``laws'' requiring computation to \red{preserve
  resources}. 

\vfill\item Linear logic is a step in that direction but more generally one
might argue that Computer Science is all about managing resources.

\vfill\item The natural way of expressing computations that preserve
resources is via \red{type isomorphisms}.

\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Common Themes: Mathematics perspective}

\begin{itemize}

\vfill\item From the mathematical side: it is important to understand the
computational content of \blue{propositional equality} $\equiv$ as opposed to
\blue{definitional equality} $=$.

\vfill\item If we claim that we have a proof that the proposition $x \equiv
y$ is true, then it is interesting to be able to produce at least one such
proof and to understand how various proofs might be connected.

\vfill\item The natural way of expressing proofs of propositional equality is
again via \red{isomorphisms between propositions}, which by the Curry-Howard
correspondence is the same as \red{type isomorphisms}.

\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{HoTT, informally}
\vfill

\begin{center}

``Mathematics or Type Theory or Computation etc. with \\ 
  \ \\
  all equalities replaced by isomorphisms, \\ 
  \ \\
  i.e., with equalities given computational content.''

\end{center}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Isomorphisms}

\begin{itemize}
\vfill\item When are two structures isomorphic?

\vfill\item Example: are these two graphs isomorphic?

\begin{center}
\scalebox{0.3}{\includegraphics{pics/i-60.png}}
\scalebox{0.3}{\includegraphics{pics/i-72.png}}
\end{center}

\end{itemize}

\vfill\footnotesize{In general, you don't have nice colors and numbers to
tell you which nodes correspond to which nodes.}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Isomorphisms}

\vfill

Here is the proof that these two graphs are isomorphic.

\begin{center}
\scalebox{0.3}{\animategraphics[controls]{3}{pics/i-}{60}{72}}
\scalebox{0.3}{\includegraphics{pics/i-72.png}}
\end{center}

\vfill\footnotesize{[Credit to Pablo Angulo, using Sage software
    \url{http://commons.wikimedia.org/wiki/File:Kuratowski.gif}]}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Isomorphisms}
\vfill

Two structures are isomorphic if we can \blue{morph} one to the
other by:
\begin{itemize}
\vfill\item \blue{bending},
\vfill\item \blue{shrinking}, and
\vfill\item \blue{expanding}.
\vfill\item \red{No cutting; no gluing}
\vfill\item Formally, a \red{homotopy}.
\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Homotopy}
\vfill
\begin{itemize}

\vfill\item Given two continuous functions from one topological space to
another, a homotopy is a deformation of one function into the other.

\vfill\item In homotopy type theory, we think of $x \equiv y$ as a \red{path}
from point $x$ to point $y$.

\vfill\item Different proofs lead to different paths. 

\vfill\item A homotopy is a 2-path (a path between paths) that deforms one
path to the other:
\begin{center}
\scalebox{0.5}{\animategraphics[controls]{10}{pics/Homotopy-}{0}{50}}
\end{center}

\end{itemize}

\vfill\footnotesize{[Credit: Wikipedia
    \url{http://en.wikipedia.org/wiki/Homotopy}.]}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Mugs and donuts}

\begin{itemize}
\vfill\item No talk that mentions topology can be complete without the
obligatory coffee mug and donut.

\vfill\item This is a homotopy of one space into another:
\begin{center}
\scalebox{0.5}{\animategraphics[controls]{10}{pics/Mug-}{0}{57}}
\end{center}

\end{itemize}

\vfill\footnotesize{[Credit: Wikipedia
    \url{http://en.wikipedia.org/wiki/Homotopy}.]}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Applications to Concurrency Theory}

\begin{itemize}

\vfill\item Different computation schedules correspond to different
\red{paths}.

\vfill\item A homotopy between two paths means that the two corresponding
schedules produce the same answers.

\vfill\item Critical regions correspond to \red{forbidden} regions. A
\red{continuous} deformation of paths \red{cannot} cross the forbidden
region:

\begin{center}
\scalebox{0.15}{\includegraphics{pics/conc.png}}
\end{center}

\vfill\item The schedules on each side of the forbidden region might lead to
different observable answers.

\end{itemize}

\vfill\footnotesize{[Credit: Algebraic Topology and Concurrency, Fajstrup,
    Goubault, and Raussen, TCS 1998]}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{HoTT, a bit more formally}

\begin{itemize}
\vfill\item (Martin-L\"of) type theory
\vfill\item Interpret types as topological spaces (or weak $\infty$-groupoids)
\vfill\item Interpret identities as paths
\end{itemize}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Martin-L\"of type theory}

\vfill
\begin{center}
Universes $+$ \\
\  \\
Dependent functions $+$ \\
\  \\
Inductive data types \\
\  \\
\uncover<2->{\red{in an executable framework}. [We use Agda for this talk.]}
\end{center}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Basic inductive types} 

\begin{code}
-- the empty type; the proposition FALSE
data ⊥ : Set where 

-- the type with one element
data ⊤ : Set where
  tt : ⊤

data Bool : Set where
  false  : Bool
  true   : Bool
\end{code}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Basic inductive types (ctd.)}

\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ

-- disjoint unions or coproducts
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
\end{code}
\AgdaHide{
\begin{code}
{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}
\end{code}
}
\begin{code}
nb₁ : ℕ ⊎ Bool
nb₁ = inj₁ 3

nb₂ : ℕ ⊎ Bool
nb₂ = inj₂ true
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Universes} 

\begin{itemize}
\vfill\item A \red{universe} is a ``set'' whose elements are ``sets''.
\vfill\item A \red{universe} is a ``type'' whose elements are ``types''.
\vfill\item There is no set of all sets, obviously.
\vfill\item There is a \blue{hierarchy} of universes
\end{itemize}
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Universes (ctd.)} 

\begin{code}
n : ℕ
n = 5

t : Set₀ -- or just Set
t = ℕ

t' : Set₁
t' = Set₀

t'' : Set₂
t'' = Set₁
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Universes and families of sets} 

\red{Families of sets} or \red{type families} or \red{dependent types}:

\begin{code}
P : ℕ → Set
P 0        = {!!}
P (suc n)  = {!!}

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _∷_  : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

v₁ : Vec Bool 3
v₁ = false ∷ true ∷ false ∷ []
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Dependent functions} 

\AgdaHide{
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n
\end{code}
}

\begin{code}
_++_ : ∀ {m n} {A : Set} → Vec A m → Vec A n → Vec A (m + n)
[]        ++ ys = ys
(x ∷ xs)  ++ ys = x ∷ (xs ++ ys)

concat : ∀ {m n} {A : Set} → Vec (Vec A m) n → Vec A (n * m)
concat []          = []
concat (xs ∷ xss)  = xs ++ concat xss

c₁ : Vec Bool 6
c₁ = concat (  (false ∷ false ∷ [])  ∷ 
               (true ∷ true ∷ [])    ∷
               (false ∷ false ∷ [])  ∷ [] )
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Dependent pairs}

\begin{code}
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
\end{code}

\AgdaHide{
\begin{code}
open Σ public
\end{code}
}

\begin{code}
exT : Set
exT = Σ ℕ (λ n → Vec Bool n)

ex₁ : exT
ex₁ = (3 , (false ∷ true ∷ false ∷ []))

ex₂ : exT
ex₂ = (0 , [])
\end{code}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}{Pause}

\vfill
\begin{center}
\LaTeX\ crash \ldots \\
Switch to second talk
\end{center}
\vfill

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}

