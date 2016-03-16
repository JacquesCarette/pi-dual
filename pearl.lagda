\documentclass[authoryear,preprint]{sigplanconf}

\usepackage{flushend}
\usepackage{agda}
\usepackage{alltt}
\usepackage{fancyvrb}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{tikz}
\usetikzlibrary{cd}
\usetikzlibrary{quotes}
\usepackage{adjustbox}
\usepackage{amsthm}
\usepackage{latexsym}
\usepackage{MnSymbol}
\usepackage{courier}
\usepackage{thmtools}
\usepackage{bbold}
\usepackage[hyphens]{url}
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
\newcommand{\C}{\mathbf{\mathcal{C}}}

%% \DefineVerbatimEnvironment
%%   {code}{Verbatim}
%%  {} % Add fancy options here if you like.

\DeclareUnicodeCharacter{8345}{\ensuremath{{}_n}}
\DeclareUnicodeCharacter{8347}{\ensuremath{{}_s}}
\DeclareUnicodeCharacter{8718}{\ensuremath{\qed}}
\DeclareUnicodeCharacter{120792}{\ensuremath{\mathbb{0}}}
\DeclareUnicodeCharacter{120793}{\ensuremath{\mathbb{1}}}
\DeclareUnicodeCharacter{9678}{\ensuremath{\odot}}
\DeclareUnicodeCharacter{9636}{\ensuremath{\Box}}
%% shorten the longarrow
\DeclareUnicodeCharacter{10231}{\ensuremath{\leftrightarrow}}
\DeclareUnicodeCharacter{2097}{\ensuremath{{}_l}}
\DeclareUnicodeCharacter{7523}{\ensuremath{{}_r}}
\DeclareUnicodeCharacter{8343}{\ensuremath{{}_l}}
\DeclareUnicodeCharacter{8779}{\ensuremath{\triplesim}}
\DeclareUnicodeCharacter{9679}{\textbullet}

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

%% \newcommand{\amr}[1]{}
%% \newcommand{\jc}[1]{}

\newcommand{\jc}[1]{\authornote{purple}{JC}{#1}}
\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.4\textwidth}\color{red}{Amr says: {#1}}\end{minipage}}}

%% agda code indent
\setlength{\mathindent}{0.1cm}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

\title{HoTT Effects}
\subtitle{Functional Pearl}
\authorinfo{}{}{}

\maketitle

\begin{abstract}

  Homotopy type theory is much more complex than plain type
  theory. The additional complexity can be justified if one is
  concerned with applications to homotopy theory. But can this
  complexity be justified from a purely type theoretic perspective?
  This pearl gives an intuitive answer building on the observation
  that proofs are effectful objects.

\end{abstract}

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

open import Data.Nat hiding (_⊔_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
import Relation.Binary.Core as C
open import Relation.Binary.PropositionalEquality hiding (_≡_; refl)
open ≡-Reasoning

infix  4  _≡_   

_≡_ : ∀ {ℓ} {A : Set ℓ} → (x y : A) → Set ℓ
_≡_ {ℓ} {A} x y = C._≡_ {ℓ} {A} x y

refl : ∀ {ℓ} {A} → (x : A) → x ≡ x
refl {ℓ} {A} x = C.refl {ℓ} {A} {x}

infixr 8 _∘_ 

_∘_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} →
      (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ = trans      

! : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (y ≡ x)
! = sym

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL {x = x} C.refl = refl (refl x)
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction} 

\begin{quote}

Indeed, such questions bring us rapidly to problems such as
calculating the homotopy groups of spheres, a long-standing problem in
algebraic topology for which no simple formula is known. Homotopy type
theory brings a new and powerful viewpoint to bear on such questions,
but it also requires type theory to become as complex as the answers
to these questions~\cite[Sec.~6.1]{hottbook}

\end{quote}

When attempting to explain Homotopy Type Theory (HoTT) to colleagues
or students with a background in functional programming, dependent
types, type theory, proof theory, proof assistants, etc. it is quite
difficult to motivate the sheer explosion in complexity that comes
with the HoTT perspective. Eventually, often after weeks of study, one
may start to appreciate the rich and beautiful combinatorial structure
of proofs in HoTT but only if one learns enough topology or higher
category theory. Is there really no other way to appreciate and
understand the HoTT infrastructure?

Instead of trying to say more in this introduction, we invite the
reader to read this relatively short pearl written from the
perspective of an explanation essay. We assume familiarity with the
basics of dependent type theory and we use Agda as our canonical proof
assistant.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Identity Types: The $=$ Interpretation}
\label{sec2}

In Martin-L\"of type theory, given a type $A$ and two elements $x : A$
and $y : A$, the proposition of whether $x$ and $y$ are equal can be
turned into a type $x ≡ y$. If the proposition is false, the type must
be empty:

\medskip 

\begin{code}
p₁ : 4 ≡ 3  
p₁ = {!!}      -- impossible  
\end{code}

\medskip 

If however the proposition is true, the type $x ≡ y$ must contain at
least one element so that we can provide proofs of the proposition
that $x$ and $y$ are equal. The minimum we might expect is to be able
to prove the proposition if the two objects $x$ and $y$ are actually
identical. In our Agda package, we write $\AgdaFunction{refl}~x$
for that proof object:

\medskip 

\begin{code}
p₂ : 4 ≡ 4
p₂ = refl 4

p₃ : 2 * 3 ≡ 5 + 1
p₃ = refl (2 + 4)
\end{code}

\medskip 

As customary, we implicitly rely on Agda's evaluator to simplify
certain expressions and we treat these as identical. The constructor
\AgdaFunction{refl} establishes that our equality relation $≡$ which
relies on Agda evaluation is reflexive; we naturally also expect it to
be symmetric and transitive (which it is). We also expect at least two
principles which will be crucial for the rest of the paper:
\begin{itemize}
\item congruence: Given a proof of $x ≡ y$ called $p$,
  \AgdaFunction{cong} allows us to infer a proof of $F x ≡ F y$ for
  any $F$. The latter proof is called $\AgdaFunction{cong}~F~p$. For example:

\medskip 

\begin{code} 
p₄ : ∀ {m n} → (m ≡ n) → (suc m ≡ suc n) 
p₄ p = cong suc p 

p₅ : ∀ {m n} → (m ≡ n) → (m * m + 2 * m ≡ n * n + 2 * n)
p₅ p = cong (λ x → x * x + 2 * x) p 
\end{code}

\item Leibniz's principle of the \emph{identity of indiscernibles:}
  Given a proof of $x ≡ y$ called $p$, any proof of $P(x)$ for some
  property~$P$ can be transformed to a proof of $P(y)$. Put
  differently, no property $P$ can distinguish two identical
  objects. For example:

\medskip 

\begin{code} 
p₆ : ∀ {m n} → (m ≡ n) → (m ≥ 0) → (n ≥ 0)
p₆ p gm = subst (λ x → x ≥ 0) p gm

p₇ : ∀ {m n} → (m ≡ n) → (∀ z → m ≥ z)→ (∀ z → n ≥ z)
p₇ p bm = subst (λ x → ∀ z → x  ≥ z) p bm
\end{code}

\medskip\noindent The second example illustrates that the property $P$
may be false without affecting the principle: if an absurdity holds
for $m$ it also holds for $n$.

\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Univalence} 
\label{sec3}

Given the notion of identity types, a natural question arises. Do we
want to be able to prove propositions like $ℕ ≡ ℕ × ℕ$? Clearly the
sets $ℕ$ and $ℕ × ℕ$ are not identical and are not simplifiable to one
another by the Agda evaluator. However, because there exists a
bijection between them, the sets are often treated as identical. To
capture this richer notion of identity in a formal system, one might
postulate that whenever two sets $A$ and $B$ are related by a
bijection~$≃$, they can be treated as identical $≡$:

\AgdaHide{
\begin{code}
open import Function renaming (_∘_ to _○_)
open import Data.Product using (Σ; _,_)
open import Level using (_⊔_)
open import Data.Bool 
open import Algebra
open import Algebra.Structures
open import Data.Unit

infix  4  _∼_     -- homotopy between two functions 
infix  4  _≃_     -- type of equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ
       
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv
\end{code}
}

\medskip 

\begin{code}
postulate 
  univalence : ∀ {ℓ} {A B : Set ℓ} → (A ≃ B) → (A ≡ B)
\end{code} 

\medskip\noindent This is essentially the \emph{univalence axiom} of
HoTT\footnote{\textbf{Warning:} We are glossing over several
  subtleties but without affecting the substance of the message.}. In
this paper, we do not focus on the univalence axiom itself except to
note that it has enriched our notion of equality giving us the
possibility of having proofs of $≡$ that are not just plain
\AgdaFunction{refl}. 

\paragraph*{Example.} We assume one of the standard notions of
equivalence from the HoTT book with a constructor
\AgdaInductiveConstructor{mkisequiv} and we construct two equivalences
(bijections) between the type \AgdaDatatype{Bool} and itself.  The
first bijection \AgdaFunction{b≃₁} uses the identity function in both
directions and the second bijection \AgdaFunction{b≃₂} uses boolean
negation in both directions. The proofs that these functions
constitutes an isomorphism are trivial. Univalence then allows to
postulate of the existence of two, a priori different, elements of the
type $\AgdaDatatype{Bool} ≡ \AgdaDatatype{Bool}$:

\medskip 

\begin{code}
b≃₁ : Bool ≃ Bool
b≃₁ = (id , mkisequiv id refl id refl)

notinv : (b : Bool) → not (not b) ≡ b
notinv true = refl true
notinv false = refl false 

b≃₂ : Bool ≃ Bool
b≃₂ = (not , mkisequiv not notinv not notinv)

b≡₁ : Bool ≡ Bool
b≡₁ = univalence b≃₁

b≡₂ : Bool ≡ Bool
b≡₂ = univalence b≃₂
\end{code}

\medskip

The two elements \AgdaFunction{b≡₁} and \AgdaFunction{b≡₂} of type
$\AgdaDatatype{Bool} ≡ \AgdaDatatype{Bool}$ that we have produced must
actually be kept distinct. Collapsing them allows us in a few short
steps to identify \AgdaInductiveConstructor{false} and
\AgdaInductiveConstructor{true} which renders the entire logic
inconsistent. This distinction must be diligently maintained as we use
\AgdaFunction{b≡₁} and \AgdaFunction{b≡₂} to build larger and larger
proofs and establish richer and richer properties. Consider the
following examples:

\medskip 

\begin{code}
bb₁ : (Bool ≡ Bool) → ((Bool × Bool) ≡ (Bool × Bool))
bb₁ p = cong (λ a → a × a) p 

bb₂ : (Bool ≡ Bool) → ((Bool × Bool) ≡ (Bool × Bool))
bb₂ p = cong (λ a → a × Bool) p 

nonEmpty : (A : Set) → Set
nonEmpty A = Σ[ a ∈ A ] ⊤

ne : (Bool ≡ Bool) → nonEmpty Bool → nonEmpty Bool
ne p b• = subst (λ t → nonEmpty t) p b• 

ne₁ : nonEmpty Bool
ne₁ = ne b≡₁ (false , tt) -- witness is false

ne₂ : nonEmpty Bool
ne₂ = ne b≡₂ (false , tt) -- witness becomes true
\end{code}

\medskip 

We have built various proofs on pairs of booleans that must be kept
distinct. We have also established properties like
\AgdaFunction{nonEmpty} using different witnesses. All this points to
the beginning of a complex combinatorial structure on proofs. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Homotopy Interpretation: Paths}

One way to understand and reason about the structure of proofs alluded
to in the previous section is to bring in the perspective of homotopy
theory. Informally speaking, types become topological spaces and
identity proofs become ``elastic continuous deformations'' of one
space to another. We are led to abandon the conventional computational
intuitions of type theory and consider something novel. To help that
change of perspective, comes a new language. Instead of proofs, we
will speak of paths; instead of congruence of equality we will speak
of functions acting on paths; and instead of Leibniz's principle of
the identity of indiscernibles, we will speak of transporting
properties along paths.

%%%%%%%%%
\subsection{Paths}
\label{sub:paths}

Switching language, instead of viewing an element of $A ≡ B$ as a
proof of equality, we view it as a path from the space $A$ to the
space~$B$. This is not a priori a symmetric notion but paths come
equipped with additional combinatorial structure:

\begin{itemize}
\item For every path $p : x \equiv y$, there exists an inverse path
  $! p : y \equiv x$ 

\item For every paths $p : x \equiv y$ and $q : y \equiv z$, there
exists a path $p \circ q : x \equiv z$;

\item Compositions and inverses satisfy the following conditions:
  \begin{itemize}
  \item $p \circ \AgdaFunction{refl}~y \equiv p$
  \item $p \equiv \AgdaFunction{refl}~x \circ p$
  \item $!p \circ p \equiv \AgdaFunction{refl}~y$
  \item $p ~\circ~ !p \equiv \AgdaFunction{refl}~x$
  \item $!~(!p) \equiv p$
  \item $p \circ (q \circ r) \equiv (p \circ q) \circ r$
  \end{itemize}

\item The conditions above generate new paths like $\alpha : p \circ
\AgdaFunction{refl}~y \equiv p$ which are themselves subject to the
same conditions one level higher, e.g., $!~(!\alpha) \equiv \alpha$.

\end{itemize}

%%%%%%%%%
\subsection{\AgdaFunction{cong} to \AgdaFunction{ap}}

Continuing the path interpretation, a function from space $A$ to space
$B$ must map the points of $A$ to the points of $B$ as usual but it
must also \emph{respect the path structure}. Topologically, this
corresponds to saying that every function is \emph{continuous}, i.e.,
functions act on paths by continuously deforming them to new paths. We
relabel \AgdaFunction{cong} to \AgdaFunction{ap} convey this new
meaning:

\medskip 

\begin{code}
ap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
     (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
ap = cong     
\end{code}

\medskip\noindent and visualize the situation as follows: 

\begin{center}
\begin{tikzpicture}[scale=0.6, every node/.style={scale=0.6}]
  \draw (-3,0) ellipse (1.5cm and 3cm);
  \draw (3,0) ellipse (1.5cm and 3cm);
  \draw[fill] (-3,1.5) circle [radius=0.025];
  \draw[fill] (-3,-1.5) circle [radius=0.025];
  \node[above] at (-3,1.5) {$x$};
  \node[below] at (-3,-1.5) {$y$};
  \draw[fill] (3,1.5) circle [radius=0.025];
  \draw[fill] (3,-1.5) circle [radius=0.025];
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

%%%%%%%%%
\subsection{\AgdaFunction{subst} to \AgdaFunction{tranport} and \AgdaFunction{apd}}

To understand the new meaning of \AgdaFunction{subst}, we must
consider how dependent functions act on paths as visualized below:

\begin{center}
\begin{tikzpicture}[scale=0.6, every node/.style={scale=0.6}]
  \draw (-3,0) ellipse (1.5cm and 3cm);
  \draw (3,2) ellipse (0.5cm and 1cm);
  \draw (3,-1.5) ellipse (2cm and 2cm);
  \node[blue,ultra thick,above] at (3,3) {$P(x)$};
  \node[blue,ultra thick,below] at (3,-3.5) {$P(y)$};
  \draw[fill] (-3,1.5) circle [radius=0.025];
  \draw[fill] (-3,-1.5) circle [radius=0.025];
  \node[above] at (-3,1.5) {$x$};
  \node[below] at (-3,-1.5) {$y$};
  \draw[fill] (3,1.5) circle [radius=0.025];
  \draw[fill] (3,-0.5) circle [radius=0.025];
  \draw[fill] (3,-2.5) circle [radius=0.025];
  \node[above] at (3,1.5) {$f(x)$};
  \node[above] at (3,-0.5) {$\mathit{transport}~P~p~f(x)$};
  \node[below] at (3,-2.5) {$f(y)$};
  \draw[left,cyan,thick] (-3,1.5) -- (-3,-1.5);
  \node[left,cyan] at (-3,0) {$p$};
  \draw[->,cyan,thick] (3,-0.5) -- (3,-2.5);
  \node[right,cyan] at (3,-1.5) {$\mathit{apd}~f~p$};
  \draw[->,red,dashed,ultra thick] (-2,2.5) to [out=45, in=135] (2.3,2.5);
  \node[red,below] at (0,3) {$f$ (to fiber $P(x)$)};
  \draw[->,red,dashed,ultra thick] (-2,-2.5) to [out=-45, in=-135] (1.2,-2.5);
  \node[red,above] at (-0.5,-2.5) {$f$ (to fiber $P(y)$)};
  \draw[->,red,dashed,ultra thick] (3.6,2.3) to [out=-45, in=45] (3.5,0.6);
  \node[red,right] at (3.9,1.45) {$\mathit{transport}~P~p$};
\end{tikzpicture}
\end{center}

Because $f$ is a dependent function, the endpoints of path $p$ which
are $f(x)$ and $f(y)$ end up in separate spaces $P(x)$ and $P(y)$
respectively.  Thus the way $f$ acts on $p$ is more complicated as we
require that one of the endpoints be \emph{transported} to the other
space first. The transport is exactly what we used to call \AgdaFunction{subst}:

\medskip

\begin{code}
transport : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) →
            {x y : A} → (x ≡ y) → B x → B y
transport = subst

apd : ∀ {ℓ₁ ℓ₂} → {A : Set ℓ₁} {B : A → Set ℓ₂} →
      (f : (x : A) → B x) → {x y : A} → (p : x ≡ y) →
      transport B p (f x) ≡ f y
apd f C.refl = C.refl
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Topological Circle} 

With the topological perspective in mind, the combinatorial complexity
of proofs (paths) becomes justified. Indeed, understanding the basic
shape of a topological space (its holes) amounts to understanding the
higher-order structure of paths in a concrete way. We explain this
point in detail using one example: the topological circle. This space
refers to the one-dimensional circumference of the two-dimensional
disk in the plane. Abstractly speaking, the space can be specified as
follows:\footnote{Agda is not designed for modeling higher-inductive
  types that include points and paths. A proper encoding of the circle
  is possible but would be distracting. We present the main
  ingredients as postulates for clarity.}

\medskip 

\begin{code}
module S¹ where 
  postulate
    S¹ : Set₁
    base : S¹
    loop : base ≡ base
\end{code}

\medskip 

We postulate the existence of a point \AgdaFunction{base} lying on the
circle and a way to go from this point to itself using a path called
\AgdaFunction{loop}. A priori there is another path from
\AgdaFunction{base} to itself,
$\AgdaFunction{refl}~\AgdaFunction{base}$, which involves not
moving at all. Because paths are closed under composition, there is
yet another way to go from \AgdaFunction{base} to itself that involves
going around the loop twice and hence evidently $n$ times for
arbitrary $n$. Also because paths are closed under inverses, there is
path $!~\AgdaFunction{loop}$ that involves going in the reverse
direction of \AgdaFunction{loop}; this also induces $n$-fold
iterations of this reverse path. In fact there are now many more paths
like
$(\AgdaFunction{loop} ∘ \AgdaFunction{loop}) ∘ ~!~\AgdaFunction{loop}$
but as explained in Sec.~\ref{sub:paths}, we can reason as follows:
\[\begin{array}{rcl}
&& (\AgdaFunction{loop} ∘ \AgdaFunction{loop}) ∘ ~!~\AgdaFunction{loop} \\
&≡& \AgdaFunction{loop} ∘ (\AgdaFunction{loop} ∘ ~!~\AgdaFunction{loop}) \\
&≡& \AgdaFunction{loop} ∘ (\AgdaFunction{refl}~\AgdaFunction{base}) \\
&≡& \AgdaFunction{loop} 
\end{array}\]
to eliminate these paths. It does turn out that the resulting
non-trivial structure of paths in the case of the circle is as
depicted below:

\begin{center}
\begin{tikzpicture}[scale=0.6, every node/.style={scale=0.6}]
  \draw (0,0) ellipse (5.5cm and 2.5cm);
  \draw[fill] (0,0) circle [radius=0.025];
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

\noindent Generally speaking, calculating the precise structure of
such path spaces is a difficult problem in algebraic topology. The
quote at the beginning of the paper argues that the complications to
type theory brought on by the homotopy interpretation are not
gratuitous: they reflect genuine mathematical structure of topological
spaces. To appreciate this, it is necessary to look at how one would
prove anything about the circle or more generally about topological
spaces as represented in HoTT. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Recursion and Induction Principles}

As is customary in type theory, reasoning about the properties of a
type $A$ is expressed using an appropriate recursion or induction
principle for $A$. We first review the situation for the familiar type
of the natural numbers and then move on to the more interesting
situation of a topological space.

%%%
\subsection{Recursion and Induction for the Natural Numbers}

The recursion and induction principles for the natural numbers are expressed as follows:

\medskip

\begin{code}
recℕ : ∀ {ℓ} → (C : Set ℓ) →
  C → (ℕ → C → C) → ℕ → C
recℕ C c f 0 = c
recℕ C c f (suc n) = f n (recℕ C c f n)

indℕ : ∀ {ℓ} → (C : ℕ → Set ℓ) →
  C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indℕ C c f 0 = c
indℕ C c f (suc n) = f n (indℕ C c f n)
\end{code}

\medskip

First note that only the types differ; the implementation is
identical. In fact, the only difference between the two principles is
that the induction principle uses dependent functions whereas the
recursion principle uses non-dependent functions. To gain some
intuition we show two simple functions defined using the recursion
principle and one property established using the induction principle:

\medskip

\begin{code}
double : ℕ → ℕ
double = recℕ ℕ 0 (λ n r → suc (suc r))

add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ n → n) (λ m r n → suc (r n))

add-assoc : (i j k : ℕ) →
  add i (add j k) ≡ add (add i j) k
add-assoc =
  indℕ
    (λ i → (j k : ℕ) → add i (add j k) ≡ add (add i j) k)
    (λ j k → refl (add j k))
    (λ i p j k → cong suc (p j k))
\end{code}

%%%
\subsection{Recursion and Induction for the Circle}

Defining the recursion and induction principles for interesting
topological spaces is more challenging. We list the recursion and
induction principles for the circle and then spend the remainder of
this section to explain them.

\medskip 

\begin{code}
module S¹reasoning where
  open S¹

  record rec (B : Set₁) (b : B) (p : b ≡ b) : Set₁ where
    field
      f : S¹ → B
      α : f base ≡ b
      β : ! α ∘ ap f loop ∘ α ≡ p 

  record ind  (P : S¹ → Set) (b : P base)
              (p : transport P loop b ≡ b) : Set₁ where
    field
      f :  (x : S¹) → P x
      α :  f base ≡ b
      β :  ! (ap (transport P loop) α) ∘ apd f loop ∘ α ≡ p 
\end{code}

\medskip 

Both the recursion and induction principles allow us to write
functions from $S¹$ to some other space with enough structure, i.e., a
space with at least a point and a loop on that point. The defined
function is non-dependent in the case of the recursion principle and
is dependent in the case of the induction principle. Both the
recursion and induction principles postulate the existence of the
function and how it acts on the point \AgdaFunction{base} and path
\AgdaFunction{loop}. In both cases, the function sends the point
\AgdaFunction{base} to the point \AgdaFunction{b} as captured by
$\alpha$.\footnote{Our presentation is slightly more complicated than
  the one in the book~\cite{hottbook} because $\alpha$ is expressed as
  a propositional equality. This is harmless.} To understand the type
of $\beta$, first in the case of the recursion principle, it is
helpful to visualize the situation:

\begin{center}
\begin{tikzpicture}[scale=0.6, every node/.style={scale=0.6}]
  \draw (-3,0) ellipse (1.5cm and 3cm);
  \draw (3,0) ellipse (3cm and 3cm);
  \node[blue,ultra thick,above] at (-3,3) {$S¹$};
  \node[blue,ultra thick,above] at (3,3) {$B$};
  \draw[fill] (-3,1.5) circle [radius=0.025];
  \draw[fill] (-3,-1.5) circle [radius=0.025];
  \node[above] at (-3,1.5) {\AgdaFunction{base}};
  \node[below] at (-3,-1.5) {\AgdaFunction{base}};
  \draw[fill] (1.5,1.5) circle [radius=0.025];
  \node[above] at (1.5,1.5) {$f(\AgdaFunction{base})$};
  \draw[fill] (1.5,-1.5) circle [radius=0.025];
  \node[below] at (1.5,-1.5) {$f(\AgdaFunction{base})$};
  \draw[->,left,cyan,thick] (1.5,1.5) -- (1.5,-1.5);
  \node[left] at (1.5,0) {$\AgdaFunction{ap}~f~\AgdaFunction{loop}$};
  \draw[fill] (4.5,1.5) circle [radius=0.025];
  \node[above] at (4.5,1.5) {$b$};
  \draw[->,left,cyan,thick] (1.5,1.5) -- (4.5,1.5);
  \node[above] at (3,1.5) {$\alpha$};
  \draw[->,left,cyan,thick] (1.5,-1.5) -- (4.5,-1.5);
  \node[below] at (3,-1.5) {$\alpha$};
  \node[below] at (4.5,-1.5) {$b$};
  \draw[->,left,cyan,thick] (4.5,1.5) to [out=-45, in=45] (4.5,-1.5);
  \node[right] at (5.1,0) {$p$};
  \draw[->,left,dashed,cyan,thick] (4.5,1.5) to [out=-135, in=135] (4.5,-1.5);
%%  \node[left] at (3.9,0) {$\AgdaFunction{transport}\ldots$};
  \draw[->,double,red,thick] (4,0) -- (5,0);
  \node[below,red] at (4.5,0) {$\beta$};  
  \node[above] at (3,1.5) {$\alpha$};
  \draw[->,left,cyan,thick] (-3,1.5) -- (-3,-1.5);
  \node[left,cyan] at (-3,0) {\AgdaFunction{loop}};
  \draw[->,red,dashed,ultra thick] (-2,2.5) to [out=45, in=135] (2,2.8);
  \node[red,below] at (0,3.2) {$f$};
\end{tikzpicture}
\end{center}

Intuitively, in order to define the ``recursive'' function $f$ from
$S¹$ to some space $B$, the user must provide a point in $B$
corresponding to $f(\AgdaFunction{base})$ and a path
$\AgdaFunction{ap}~f~\AgdaFunction{loop}$ of type
$f(\AgdaFunction{base}) ≡ f(\AgdaFunction{base})$. We also have in the
space $B$ two known paths: $\alpha$ which relates
$f(\AgdaFunction{base})$ to $\AgdaFunction{b}$ and the path
$\AgdaFunction{p} : \AgdaFunction{b} ≡ \AgdaFunction{b}$ which is
assumed to exist as the target space must have enough structure. What
$\beta$ asserts is that this path~$\AgdaFunction{p}$ cannot be an
arbitrary path in $B$: it must incorporate whatever the action of $f$
on \AgdaFunction{loop} was. In the figure, it is apparent that the
obvious way to relate $\AgdaFunction{ap}~f~\AgdaFunction{loop}$ and
\AgdaFunction{p} is to insist that $p$ be equivalent to $! \alpha ∘
\AgdaFunction{ap}~\AgdaFunction{f}~\AgdaFunction{loop} ∘ \alpha$ which
is represented by the dashed path that follows the path from the top
occurrence of $b$ to the bottom one in the counterclockwise direction.

There is another presentation of the dashed path that provides
additional insight. This dashed path can be written as:
\[
\AgdaFunction{transport}~(\lambda x → x ≡ x)~\alpha~(\AgdaFunction{ap}~f~\AgdaFunction{loop})
\]
which, in the terminology of homotopy theory, means that it
corresponds to transporting the path
$(\AgdaFunction{ap}~f~\AgdaFunction{loop})$ along $\alpha$. The two
perspectives are equivalent as the following lemma shows.

%% β : transport (λ x → x ≡ x) α (ap f loop) ≡ p 
%% β : transport 
%%       (λ x → transport P loop x ≡ x) α (apd f loop) 
%%     ≡ p 

\medskip 

\begin{code}
transportId :  ∀ {ℓ} {A : Set ℓ} {y z : A} →
  (p : y ≡ z) → (q : y ≡ y) → 
  transport (λ x → x ≡ x) p q ≡ ! p ∘ q ∘ p
transportId {y = y} C.refl q =
  begin  (transport (λ x → x ≡ x) C.refl q
           ≡⟨ refl q ⟩
         q
           ≡⟨ unitTransR q ⟩ 
         q ∘ refl y
           ≡⟨ refl (q ∘ refl y) ⟩ 
         ! C.refl ∘ q ∘ C.refl ∎)
  where
    unitTransR :  ∀ {ℓ} {A : Set ℓ} {x y : A} →
      (p : x ≡ y) → (p ≡ p ∘ refl y) 
    unitTransR {x = x} C.refl = refl (refl x)
\end{code}

\medskip 

There is a third perspective regarding the dashed path and its
connection to \AgdaFunction{loop} and \AgdaFunction{p} that is useful
to keep in mind and that is a programming language theory
perspective. Both \AgdaFunction{refl}~\AgdaFunction{base} and
\AgdaFunction{loop} are paths in the space $\AgdaFunction{base} ≡
\AgdaFunction{base}$. The first is a trivial path and we will think of
it as a pure function with no side effects and the second is a path
that cannot be identified with the trivial \AgdaFunction{refl} path and
we will think of it as a function with possible side effects. The
function~$f$ is arbitrary but given that \AgdaFunction{loop} is viewed
as an object with side effects, its action on \AgdaFunction{loop} may
also have side effects. Therefore, when moving from the space $S¹$ to
another space $B$, the side effects in the action of $f$ on
\AgdaFunction{loop} must be taken into account and the path
$\AgdaFunction{p}$ can neither discard nor duplicate these side
effects. We will develop this perspective further in the next section.

The induction principle for $S¹$ differs from the recursion principle
in two aspects: first the dependent version \AgdaFunction{apd} is used
instead of \AgdaFunction{ap}; second the path $p$ is not just of type
$\AgdaFunction{b} ≡ \AgdaFunction{b}$ but rather of type
$\AgdaFunction{transport}~P~\AgdaFunction{loop}~\AgdaFunction{b} ≡
\AgdaFunction{b}$.
To understand this subtlety we reason as follows. Recall that the
circle is constructed from a point \AgdaFunction{base} and a path
\AgdaFunction{loop} on which we can travel starting from
\AgdaFunction{base} all the way around back to \AgdaFunction{base}. A
property $P$ of $S¹$ must consider both the point and the action of
traveling along \AgdaFunction{loop}. In the induction principle,
$\AgdaFunction{b}$ is a proof that the property holds for
$\AgdaFunction{base}$ and $\AgdaFunction{p}$ is a proof that the
property of \AgdaFunction{base} established by \AgdaFunction{b}
remains true when transported along \AgdaFunction{loop}. Note that
Agda does not care about this subtlety and would happily typecheck an
``induction principle" in which \AgdaFunction{p} had the type
$\AgdaFunction{b} ≡ \AgdaFunction{b}$. Thinking again of the effects
perspective, the proof of $P(\AgdaFunction{base})$ must be robust and
hold even if the side effects represented by \AgdaFunction{loop} are
taken into account.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Effectful Paths and Proofs}
 
The above material, except perhaps for its exposition, is
standard. The goal was to show enough of HoTT to get an appreciation
of its complexity and understand that the main reason for this
complexity is the existence of non-trivial paths which, in some
intuitive sense, can be though of as operations with side effects. To
sum it up, given a space~$A$, two points $x$ and $y$ in $A$, and two
proofs $p$ and $q$ of type $x ≡ y$, we, in general, know nothing about
the relationship between $p$ and~$q$. It is true that there are both
proofs of the identity $x ≡ y$ but these proofs may be different in a
critical way that would make it inconsistent to identify them. In the
topological world, it is easy to visualize such a situation:

\begin{center}
\begin{tikzpicture}[scale=0.6, every node/.style={scale=0.6}]
  \draw (0,0) rectangle (5,5);
  \node[left] at (0,0) {$x$};
  \node[right] at (5,5) {$y$};
  \fill[blue!40!white] (2,2) rectangle (3,3);
  \draw[->,cyan,thick] (0,0) to [out=10, in=-100] (5,5);
  \draw[->,cyan,thick] (0,0) to [out=80, in=-170] (5,5);
\end{tikzpicture}
\end{center}

The idea is that the large space $A$ (the square) has a hole (in
blue). The two paths connect $x$ and $y$ but are separated by the hole
and hence there is no way to perform a continuous deformation (without
cutting and gluing) of one path to the other. The question is whether
a similar intuition can be develop in a conventional computational
setting?

%%%
\subsection{Concurrency}

A first hint comes from a paper
by~\citet{Gunawardena:2001:HC:377786.377845} which views the diagram
above as representing the concurrent execution of two processes. One
process $H$ makes progress depicted along the horizontal dimension and
the other $V$ makes progress depicted along the vertical
dimension. The paths from $x$ and $y$ correspond to all the legal
interleavings of the two processes. Now assume that during their
computation, the processes need to acquire exclusive access to a
shared resource. As soon as process $H$ acquires the resource, all
interleavings moving up in the vertical direction are forbidden until
the resource is released and symmetrically if process $V$ acquires the
resource all interleavings moving to the right in the horizontal
direction are forbidden until the resource is released. In other
words, the blue square represents a forbidden zone. Furthermore, all
interleavings to the right of the blue square are equivalent
executions in which process $H$ acquires the resource first and
similarly all interleavings going to the left of the blue square are
equivalent executions in which process $V$ acquires the resource
first. It would clearly be incorrect to equate executions that are on
different sides of the blue square.

The connection to concurrency outlined above suggests that paths can
be viewed as embodying conventional computational effects related to
acquiring and releasing locks and not just the special effects arising
from the homotopy theoretic interpretation (if one may call the
trajectory of a path around holes in the space as a form of
computational effect). Even more generally, and abstracting from the
particular example of concurrency theory, we argue that paths may be
viewed as embodying some general notion of computational effects.

%%%
\subsection{Effectful Proofs}

Forgetting about the homotopy theoretic interpretation and returning
to the terminology of Secs.~\ref{sec2} and~\ref{sec3}, objects of type
$x ≡ y$ are proofs of the equivalence of $x$ and $y$. If we postulate
for a moment that these proofs may embody computational effects then
all the special treatment of paths arising from the homotopy
interpretation can be justified on purely computational grounds by
appealing to the familiar reasoning laws governing computational
effects using monads, type-and-effect systems, effect handlers,
etc. For example, if we imagine that \AgdaFunction{loop} in the
definition of $S¹$ represents a proof with a computational effect,
then given an arbitrary function from $S¹$ to some space $B$, it is
natural to expect the proof object
$\AgdaFunction{ap}~f~\AgdaFunction{loop}$ to also have a computational
effect in which case this proof cannot in general be equivalent to
another proof with no effects or with different computational
effects. Similarly following \AgdaFunction{loop} twice thus
experiencing the computational effect twice would not necessarily be
the same as experiencing it once. However, in order to be consistent
with the tenets of HoTT it should be possible to experience the
computational effect in the opposite direction in a way that cancels
out.\footnote{This reversibility of computational effects does not
  apply to acquiring and releasing locks which is why the connections
  between homotopy and concurrency were been further developed using
  \emph{directed} homotopy theory~\cite{Fajstrup2006241}.} The
question therefore is what kind of such reversible computational
effects could be embodied in proof objects? We address this last point
in the next section.

%%%
\subsection{Reversible Monads} 

Putting the previous observations together, the type of proofs $x ≡ y$
in some space $A$ should be treated as a monadic type involving a
reversible effect. Note that the monad laws together with the
reversibility requirement give us the combinational structure of paths
in Sec.~\ref{sub:paths}. The presence of monadic effects ensures that
path equivalence is treated delicately: we certainly cannot identify
all paths and must accept the complex combinatorial structure that
arises from the desire to keep certain paths distinct. 

So what is a ``reversible monadic effect''? This precise question is
answered in a paper by~\citet{Heunen:2015:RMC:2875516.2875606} which
argues that effectful computations are reversible \emph{precisely}
when the monad in question is Frobenius as specified in the following
two definitions.

\begin{definition}[Dagger Category]
A \emph{dagger} is a functor $\dagger : \C^{\mathrm{op}} \rightarrow
\C$ satisfying $A^\dagger = A$ on objects and $f^{\dagger\dagger} = f$
on morphisms. A \emph{dagger category} is a category equipped with a
dagger. 
\end{definition}

Note that any groupoid is a dagger category. 

\begin{definition}[Frobenius Monad~\cite{Heunen:2015:RMC:2875516.2875606}]
A \emph{Frobenius monad} on a dagger category $\C$ is a monad
$(T,\mu,\eta)$ on $\C$ with $T(f^\dagger) = T(f)^\dagger$ and: 
\[
  T(\mu_A) \circ \mu^\dagger_{T(A)} = \mu_{T(A)} \circ T(\mu^\dagger_{A}).
\]
\end{definition}

Note that daggers make any monad give rise to a comonad and hence that
the definition of a Frobenius monad is essentially about the
interaction between the monad and its comonad counterpart.

%% If some effects commute for example, then a 2 level path can express 
%% that etc. properties of effects represented as 2-paths 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

The pearl leaves many unanswered questions but we believe it meets the
first criterion for pearls by providing a new and thought-provoking
way of looking at an old idea (HoTT). Specifically, the complex
structure of HoTT is not specific to homotopy theory but arises
naturally from the consideration of proofs embodying reversible
computational effects.

%% all the stuff with subst we did before may be was the right thing from
%% the hott perspective ???

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% \clearpage
\bibliographystyle{abbrvnat}
\softraggedright
\bibliography{cites}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}

\item This satisfies the following properties:
  \begin{itemize}
  \item $\mathit{ap}~f~(p \circ q) \equiv 
                (\mathit{ap}~f~p) \circ (\mathit{ap}~f~q)$;
  \item $\mathit{ap}~f~(!~p) \equiv ~!~(\mathit{ap}~f~p)$;
  \item $\mathit{ap}~g~(\mathit{ap}~f~p) \equiv 
                \mathit{ap}~(g \circ f)~p$;
  \item $\mathit{ap}~\mathit{id}~p \equiv p$.
  \end{itemize}
\end{itemize}

One can visualize the example in the previous section as
follows:

\begin{center}
\begin{tikzpicture}[scale=0.6, every node/.style={scale=0.6}]
  \draw (-3,0) ellipse (2cm and 3cm);
  \draw (3,0) ellipse (2cm and 3cm);
  \draw[fill] (-3,1.5) circle [radius=0.025];
  \draw[fill] (-3,-1.5) circle [radius=0.025];
  \node[above] at (-3,1.5) {\AgdaDatatype{Bool}};
  \node[below] at (-3,-1.5) {\AgdaDatatype{Bool}};
  \draw[fill] (3,1.5) circle [radius=0.025];
  \draw[fill] (3,-1.5) circle [radius=0.025];
  \node[above] at (3,1.5) {$\AgdaDatatype{Bool} × \AgdaDatatype{Bool}$};
  \node[below] at (3,-1.5) {$\AgdaDatatype{Bool} × \AgdaDatatype{Bool}$};
  \draw[->,cyan,thick] (-3,1.5) to [out=-45, in=45] (-2.85,-1.5);
  \draw[->,cyan,thick] (-3,1.5) to [out=225, in=135] (-3.15,-1.5);
  \node[left,cyan] at (-3.7,0) {\AgdaFunction{b≡₁}};
  \node[left,cyan] at (-1.6,0) {\AgdaFunction{b≡₂}};
  \draw[->,cyan,thick] (3,1.5) to [out=-45, in=45] (3.15,-1.5);
  \draw[->,cyan,thick] (3,1.5) to [out=225, in=135] (2.85,-1.5);
  \node[right,cyan] at (1.3,-1.1) {$\AgdaFunction{bb₁}~\AgdaFunction{b≡₁}$}; 
  \node[right,cyan] at (3.4,1.1) {$\AgdaFunction{bb₁}~\AgdaFunction{b≡₂}$}; 
  \draw[->,red,dashed,ultra thick] (-2,2.5) to [out=45, in=135] (2,2.5);
  \node[red,below] at (0,3) {$\lambda a → a × a$};
\end{tikzpicture}
\end{center}

\medskip 

Revisiting the example at the end of last section in this light we have:

\begin{itemize}

\item The points $x$ and $y$ are both \AgdaDatatype{Bool} and there
are two different paths between them corresponding to the identity
function and the boolean negation function.

\item The property $P(x)$ is $\AgdaFunction{nonEmpty}(x)$. Assume we
know the top version of \AgdaDatatype{Bool} has an element
\AgdaInductiveConstructor{false} and assume we are considering the
boolean negation path: \emph{transporting the non-emptiness property
witnessed by \AgdaInductiveConstructor{false} along that boolean
negation path should produce a new proof of non-emptiness using
\AgdaInductiveConstructor{true} as the witness.}

\end{itemize}

\begin{center}
\begin{tikzpicture}[scale=0.6, every node/.style={scale=0.6}]
  \draw (-3,0) ellipse (1.5cm and 3cm);
  \draw (3,0) ellipse (3cm and 3cm);
  \node[blue,ultra thick,above] at (-3,3) {$S¹$};
  \node[blue,ultra thick,above] at (3,3) {$P(\AgdaFunction{base})$};
  \draw[fill] (-3,1.5) circle [radius=0.025];
  \draw[fill] (-3,-1.5) circle [radius=0.025];
  \node[above] at (-3,1.5) {\AgdaFunction{base}};
  \node[below] at (-3,-1.5) {\AgdaFunction{base}};
  \draw[fill] (1.5,1.5) circle [radius=0.025];
  \node[above] at (1.5,1.5) {$\AgdaFunction{transport}~P~\AgdaFunction{loop}~f(\AgdaFunction{base})$};
  \draw[fill] (1.5,-1.5) circle [radius=0.025];
  \draw[->,left,cyan,thick] (1.5,1.5) -- (4.5,1.5);
  \node[below] at (1.5,-1.5) {$f(\AgdaFunction{base})$};
  \draw[->,left,cyan,thick] (1.5,1.5) -- (1.5,-1.5);
  \node[below] at (3,1.5) {$\AgdaFunction{ap}~(\AgdaFunction{transport}~P~\AgdaFunction{loop})~α$};
  \node[left] at (1.5,0) {$\AgdaFunction{apd}~f~\AgdaFunction{loop}$};
  \draw[fill] (4.5,1.5) circle [radius=0.025];
  \node[above] at (5,1.5) {$\AgdaFunction{transport}~P~\AgdaFunction{loop}~b$};
  \node[below] at (4.5,-1.5) {$b$};
  \draw[->,left,cyan,thick] (4.5,1.5) to [out=-45, in=45] (4.5,-1.5);
  \node[right] at (5.1,0) {$p$};
  \draw[->,dashed,left,cyan,thick] (4.5,1.5) to [out=-135, in=135] (4.5,-1.5);
%%  \node[left] at (3.9,0) {$\AgdaFunction{transport}\ldots$};
  \draw[->,double,red,thick] (4,0) -- (5,0);
  \node[below,red] at (4.5,0) {$\beta$};  
  \draw[->,left,cyan,thick] (1.5,-1.5) -- (4.5,-1.5);
  \node[below] at (3,-1.5) {$\alpha$};
  \draw[->,left,cyan,thick] (-3,1.5) -- (-3,-1.5);
  \node[left,cyan] at (-3,0) {\AgdaFunction{loop}};
  \draw[->,red,dashed,ultra thick] (-2,2.5) to [out=45, in=135] (2,2.8);
  \node[red,below] at (0,3.2) {$f$};
\end{tikzpicture}
\end{center}

-- \begin{code} 
-- ap² : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
--       (f : A → B) → {x y : A} {p q : x ≡ y} → (r : p ≡ q) → 
--       (ap f p ≡ ap f q)
-- ap² f C.refl = C.refl      

-- transport² : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂) →
--       {x y : A} {p q : x ≡ y} → (r : p ≡ q) → (u : P x) →
--       (transport P p u ≡ transport P q u)
-- transport² P {p = C.refl} C.refl u = refl u

-- apd² : ∀ {ℓ₁ ℓ₂} → {A : Set ℓ₁} {B : A → Set ℓ₂} →
--       (f : (x : A) → B x) → {x y : A} {p q : x ≡ y} → (r : p ≡ q) →
--       apd f p ≡ (transport² B r (f x)) ∘ (apd f q)
-- apd² f {p = C.refl} C.refl = C.refl 
--
-- module I where
--   postulate
--     I : Set
--     𝟘 : I
--     𝟙 : I
--     seg : 𝟘 ≡ 𝟙

--   record rec (B : Set) (b₀ b₁ : B) (s : b₀ ≡ b₁) : Set₁ where
--     postulate
--       f : I → B
--       α₀ : f 𝟘 ≡ b₀
--       α₁ : f 𝟙 ≡ b₁
--       β : transport₂ (λ x y → x ≡ y) α₀ α₁ (ap f seg) ≡ s

--   record ind (P : I → Set) (b₀ : P 𝟘) (b₁ : P 𝟙)
--              (s : transport P seg b₀ ≡ b₁) : Set₁ where
--     postulate
--       f :   (x : I) → P x
--       α₀ :  f 𝟘 ≡ b₀
--       α₁ :  f 𝟙 ≡ b₁
--       β :   transport₂ (λ x y → transport P seg x ≡ y)
--                 α₀ α₁ (apd f seg) 
--             ≡ s

--  module S² where 
--   postulate
--     S² : Set
--     base : S²
--     surf : refl base ≡ refl base

--   record rec (B : Set) (b : B) (s : refl b ≡ refl b) : Set₁ where
--     postulate
--       f : S² → B
--       α : f base ≡ b
--       β : transport (λ p → refl p ≡ refl p) α (ap² f surf) ≡ s

--   record ind (P : S² → Set) (b : P base) 
--              (s : refl b ≡ transport² P surf b ∘ (refl b)) : Set₁ where
--     postulate
--       f :  (x : S²) → P x
--       α :  f base ≡ b
--       β :  transport
--                  (λ p → refl p ≡ transport² P surf p ∘ refl p) α
--                  (apd² f surf)
--            ≡ s

-- module T² where
--   postulate
--     T² : Set
--     b  : T²
--     p  : b ≡ b
--     q  : b ≡ b
--     t  : p ∘ q ≡ q ∘ p
-- \end{code}

%%%
\subsection{Suspensions}

To express the recursion and induction principles for other spaces,
things get more complicated. We need binary versions of
\AgdaFunction{transport} and then higher order versions of
\AgdaFunction{ap}, \AgdaFunction{transport}, and \AgdaFunction{apd}:

\medskip 

-- \begin{code}
-- transport₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} 
--   (P : A → B → Set ℓ₃) →
--   {x₁ x₂ : A} {y₁ y₂ : B} → (x₁ ≡ x₂) → (y₁ ≡ y₂) →
--   P x₁ y₁ → P x₂ y₂
-- transport₂ = subst₂

-- module Susp (A : Set) where
--   postulate
--     Susp : Set → Set₁
--     N : Susp A
--     S : Susp A
--     merid : A → (N ≡ S)

--   record rec (B : Set) (n : B) (s : B) (m : A → (n ≡ s)) : Set₁ where 
--     field
--       f : Susp A → B
--       αₙ : f N ≡ n
--       αₛ : f S ≡ s
--       β : (a : A) → transport₂ (λ x y → x ≡ y) αₙ αₛ (ap f (merid a)) ≡ m a

--   record ind  (P : Susp A → Set) (n : P N) (s : P S)
--               (m : (a : A) → transport P (merid a) n ≡ s) : Set₁
--     where
--       field
--         f : (x : Susp A) → P x
--         αₙ : f N ≡ n
--         αₛ : f S ≡ s
--         β : (a : A) →  transport₂
--                          (λ x y → transport P (merid a) x ≡ y)
--                          αₙ αₛ (apd f (merid a))
--                        ≡ m a
-- \end{code}

\medskip 

Things get progressively more and more complicated as we must
carefully account for non-trivial paths and maintain them. 

%% Not one to one with holes: can trade holes

%% fcircle (base) = south
%% fcircle (loop) = east ∘ ! west
%%
%% gcircle (south) = base
%% gcircle (north) = base
%% gcircle (east)  = loop
%% gcircle (west)  = refl base

live in a world of reversible functions (equivalences) which may have
side effects (also reversible); functions with non-trivial effects
must transport properly; 2-paths could express different sequences of
effects are the same (read and write commute) etc. 

\medskip 

\begin{code}

postulate
  seq : ∀ {A B : Set} → A → B → B
  inc : ⊤ 
  dec : ⊤
  pure : ∀ {A B C : Set} {x : A} {y : B} {f : B → C} →
         f (seq x y) ≡ seq x (f y)
  incdec : ∀ {B : Set} {y : B} → seq inc (seq dec y) ≡ y
  decinc : ∀ {B : Set} {y : B} → seq dec (seq inc y) ≡ y

notε : Bool → Bool
notε b = seq inc (not b)

notε⁻¹ : Bool → Bool
notε⁻¹ b = seq dec (not b)

fg≡ : ∀ b → notε⁻¹ (notε b) ≡ b
fg≡ b = begin
          seq dec (not (seq inc (not b)))
        ≡⟨ cong (λ x → seq dec x) (pure {x = inc} {f = not}) ⟩
          seq dec (seq inc (not (not b)))
        ≡⟨ decinc ⟩
          not (not b)
        ≡⟨ notinv b ⟩
          b ∎

gf≡ : ∀ b → notε (notε⁻¹ b) ≡ b
gf≡ b = begin
          seq inc (not (seq dec (not b)))
        ≡⟨ cong (λ x → seq inc x) (pure {x = dec} {f = not}) ⟩
          seq inc (seq dec (not (not b)))
        ≡⟨ incdec ⟩
          not (not b)
        ≡⟨ notinv b ⟩
          b ∎

bε≃ : Bool ≃ Bool
bε≃ = (notε , mkisequiv notε⁻¹ gf≡ notε⁻¹ fg≡)

bε≡ : Bool ≡ Bool
bε≡ = univalence bε≃
\end{code}

\medskip 

Now if I have \AgdaDatatype{Bool} and the path \AgdaFunction{bε≡} and
I want to write an eliminator for that type. In more mundane terms, we
have an object in the OO sense with a method \textsf{not} that has a
side effect and we want to write a function from that object to some
other equivalent type, i.e., we want a new representation for the
abstract data type. Consider a function from M to M that also
increments a global counter; that's also a loop but a non-trivial
loop; compositions n times are possible are all different; the
function has inverse which decrements the global counter. Now how do I
write functions from M together with that loop that increments to
another space: the points have to map to points and that incrementing
operation has to map to some self-operation on the new points but we
have to maintain the effect. We CANNOT choose to map the operation to
refl on the new points.

Say I want to write a function from \AgdaDatatype{Bool} to the type
$\top \uplus \top$. I am interested, not just, in mapping the points
but also in mapping the effectful function \AgdaFunction{notε} on
\AgdaDatatype{Bool} to an ``equivalent'' function on the target type.

\medskip 

\begin{code}
postulate
  b2u   : Set → Set
  u2b   : Set → Set
  b2u≡  : b2u Bool ≡ (⊤ ⊎ ⊤)

notε⊤ : (⊤ ⊎ ⊤) → (⊤ ⊎ ⊤)
notε⊤ = {!!} 
\end{code}

\medskip 

The HoTT perspective will tell us how to do it and will give us for
free that all the properties we proved about the original
representation can be transported to the new representation.

\begin{center}
\begin{tikzpicture}[scale=0.6, every node/.style={scale=0.6}]
  \draw (-3,0) ellipse (1.5cm and 3cm);
  \draw (3,0) ellipse (3cm and 3cm);
  \draw[fill] (-3,1.5) circle [radius=0.025];
  \draw[fill] (-3,-1.5) circle [radius=0.025];
  \node[above] at (-3,1.5) {\AgdaDatatype{Bool}};
  \node[below] at (-3,-1.5) {\AgdaDatatype{Bool}};
  \draw[fill] (1.5,1.5) circle [radius=0.025];
  \node[above] at (1.5,1.5) {$\AgdaFunction{b2u}(\AgdaDatatype{Bool})$};
  \draw[fill] (1.5,-1.5) circle [radius=0.025];
  \node[below] at (1.5,-1.5) {$\AgdaFunction{b2u}(\AgdaDatatype{Bool})$};
  \draw[->,left,cyan,thick] (1.5,1.5) -- (1.5,-1.5);
  \node[left] at (1.5,0) {$\AgdaFunction{ap}~\AgdaFunction{b2u}~\AgdaFunction{notε}$};
  \draw[fill] (4.5,1.5) circle [radius=0.025];
  \node[above] at (4.5,1.5) {$⊤ ⊎ ⊤$};
  \draw[->,left,cyan,thick] (1.5,1.5) -- (4.5,1.5);
  \node[above] at (3,1.5) {$\AgdaFunction{b2u≡}$};
  \draw[->,left,cyan,thick] (1.5,-1.5) -- (4.5,-1.5);
  \node[below] at (3,-1.5) {$\AgdaFunction{b2u≡}$};
  \node[below] at (4.5,-1.5) {$⊤ ⊎ ⊤$};
  \draw[->,left,cyan,thick] (4.5,1.5) to [out=-45, in=45] (4.5,-1.5);
  \node[right] at (5.1,0) {$\AgdaFunction{notε⊤}$};
  \draw[->,left,dashed,cyan,thick] (4.5,1.5) to [out=-135, in=135] (4.5,-1.5);
  \node[left] at (3.9,0) {$\AgdaFunction{transport}\ldots$};
  \draw[->,double,red,thick] (4,0) -- (5,0);
  \draw[->,left,cyan,thick] (-3,1.5) -- (-3,-1.5);
  \node[left,cyan] at (-3,0) {\AgdaFunction{notε}};
  \draw[->,red,dashed,ultra thick] (-2,2.5) to [out=45, in=135] (2,2.8);
  \node[red,below] at (0,3.2) {$\AgdaFunction{b2u}$};
\end{tikzpicture}
\end{center}

So the HoTT framework tells us that \AgdaFunction{notε⊤} is:
\[
!~\AgdaFunction{b2u≡} ∘
(\AgdaFunction{ap}~\AgdaFunction{b2u}~\AgdaFunction{notε}) ∘
\AgdaFunction{b2u≡} 
\]

This function is \emph{induced} by the HoTT infrastructure. In the
conventional setting, this infrastructure consists of identity types
with refl as a constructor, J as the induction principle, and one
mechanism to postulate non-trivial paths (univalence or
higher-inductive types).

In our setting we replace the latter mechanism with a pervasive notion
of reversible effectful functions which we treat as non-trivial
paths. Thus given reversible effectful functions, identity types and
their constructor and induction principle, we can write programs that
are guaranteed to respect the effects; more importantly we can derive
effectful programs from other programs; easy example? space of
matrices with two loops: refl and transpose; so we have program
transformations that respect effects

restricted for now to functions that are reversible but can do side
effects; not really a restriction but distracting to deal with this
now; see conclusion

Let us make one global assumption: that we have a reversible
programming language with effects. It could the one in extended with
an arbitrary effect, say reading and writing a global location.

Let's go through Chapter 2 of the book which provides the foundation
for the HoTT interpretation and re-interpret everything from the
perspective this reversible language with effects. 

\begin{itemize}
\item Types like Bool, Nat, etc. are just plain sets
\item The universe of types has types as points and has functions
  going between these types; these functions are reversible and
  potentially effectful
\item When we say that $A ≡ B$ we mean that there is a reversible map
  $f : A → B$ that is an equivalence (isomorphism). This map may be
  effectful, reading and writing the global location. 
\item subst says that for given such a map between $A$ and $B$ and
\item path induction says that every time we want to construct an
  object or prove a statement which depends on an inhabitant of
  $A ≡ B$ then it suffices to perform the construction in the special
  case $A$ and $B$ are the same and the inhabitant of $A ≡ B$ is
  \AgdaFunction{refl}. This is remarkable: we don't need to reason
  about every possible inhabitant of $A ≡ B$ that may have an effect;
  those things get transported automatically in a way that respects
  the effects. 
\item Eckmann-Hilton: Consider a type $\AgdaDatatype{A}$ and consider two arbitrary
  inhabitants $\alpha$ and $\beta$ of
  $\AgdaFunction{refl}~\AgdaDatatype{A} ≡
  \AgdaFunction{refl}~\AgdaDatatype{A}$. These maps $\alpha$ and
  $\beta$ could be effectful functions and yet the theorem guarantees
  that $\alpha ∘ \beta ≡ \beta ∘ \alpha$ ???
\item Connections to monads: effects have a right unit, left unit, and
  an associative composition operation; these are lemmas that we can
  prove for arbitrary effects using J.

\end{itemize}

\begin{code}
right-unit+ : (n : ℕ) → (n + 0 ≡ n)
right-unit+ 0 = refl 0
right-unit+ (suc m) = cong suc (right-unit+ m) 
\end{code}

\medskip

In Martin-L\"of type theory, proofs are typically represented as
dependent functions. For example, the following proof is a function
from the set of natural numbers to propositions; the result type of
this function depends on the \emph{value} of the input:

In conventional type theory, such functions are \emph{pure}. Is it,
however, possible to conceive of situations in which such functions
may have computational effects?

Connections to monads: effects have a right unit, left unit, and an
associative composition operation; these are lemmas that we can prove
for arbitrary effects using J.

Instead of homotopy etc how about a purely type theoretic
interpretation of proofs. In an actual proof assistant proofs are not
just pure functions: they have holes at various times exceptions etc. 

\cite{MR2666883}

So if we consider proofs with effects then we don't need the homotopy
interpretation; we get the same complex combinatorial structure!!!

One might argue that this is the only interesting proof of this
property and that any proof of the same property will be essentially
equivalent. This can formalized as follows:

\medskip

\begin{code}
nat-irr : {n : ℕ} → (p : n + 0 ≡ n) → (q : n + 0 ≡ n) → (p ≡ q)
nat-irr p q = proof-irrelevance p q
\end{code}

\medskip

But now consider the following incomplete proof:

\medskip

\begin{code}
right-unit+I : (n : ℕ) → (n + 0 ≡ n)
right-unit+I 0 = refl 0
right-unit+I (suc m) = {!!}
\end{code}

\medskip

\begin{code}
ppI : {n : ℕ} → (right-unit+ n) ≡ (right-unit+I n)
ppI {n} = nat-irr (right-unit+ n) (right-unit+I n)
\end{code}

\medskip

Now just looking at the above two lines and not knowing the rest of
the rest of the context, one might argue that we are in a precarious
situation. We have equated a complete proof with an incomplete proof
that may or may not ever be completed but \AgdaFunction{ppI} does not
record that distinction. Now imagine the situation with complex proofs
that may have holes in different parts, manipulating proofs with no
formal account of dependencies is dangerous. One solution is to
arbitrarily forbid such incomplete proofs from propagating beyond the
boundaries of a module. Another is to use HoTT!

As we argue, the quite complex machinery develop to deal with
topological spaces is exactly the machinery needed to deal with such
incomplete proofs.

