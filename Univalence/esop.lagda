%% \documentclass[oribibl]{llncs}
\documentclass{llncs}

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

\newcommand{\tc}{\AgdaInductiveConstructor{tt}}
\newcommand{\fun}[1]{\AgdaFunction{#1}}
\newcommand{\injl}[1]{\AgdaInductiveConstructor{inj₁}~#1}
\newcommand{\injr}[1]{\AgdaInductiveConstructor{inj₂}~#1}
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
\frac{\begin{array}{l}#2 \\\end{array}}
{\begin{array}{l}#3      \\\end{array}}$
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
%% Hyphenation
\hyphenation{e-vi-dent}
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
%  Reversible Programming Languages        \\
%  and Semirings}
%\titlerunning{Reversible Languages and Semirings}
\title{Computing with                      \\ Semirings and Weak Rig Groupoids}
\titlerunning{Computing with Rig Groupoids}
\author{Jacques Carette \and Amr Sabry}
\institute{McMaster University (\email{carette@mcmaster.ca})
\and
Indiana University (\email{sabry@indiana.edu})
}
\maketitle

\begin{abstract}

  The original formulation of the Curry-Howard correspondence relates
  propositional logic to the simply-typed $\lambda$-calculus at three
  levels: the syntax of propositions corresponds to the syntax of
  types; the proofs of propositions correspond to programs of the
  corresponding types; and the normalization of proofs corresponds to
  the evaluation of programs. This rich correspondence has inspired
  our community for half a century and has been generalized to deal
  with more advanced logics and programming models. 
  % We propose a
  % variant of this correspondence for physically-inspired logics and
  % models with a focus on conservation of information, and for recent homotopy
  % theoretic approaches to type theory. 
  We propose a variant of this correspondence which is inspired by
  conservation of information and recent homotopy theoretic approaches
  to type theory.

  Our proposed correspondence naturally relates semirings to
  reversible programming languages: the syntax of semiring elements
  corresponds to the syntax of types; the proofs of semiring
  identities correspond to (reversible) programs of the corresponding
  types; and equivalences between algebraic proofs correspond to
  meaning-preserving program transformations and optimizations.  These
  latter equivalences are not ad hoc: the same way semirings arise
  naturally out of the structure of types, a categorical look at the
  structure of proof terms gives rise to (at least) a weak rig
  groupoid structure, and the coherence laws are exactly the program
  transformations we seek.  Thus it is algebra, rather than logic,
  which finally leads us to our correspondence.
\end{abstract}

\AgdaHide{
\begin{code} 
import Level
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Algebra using (CommutativeSemiring)
open import Algebra.Structures using (IsCommutativeSemiring)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code} 
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}\label{sec:intro}

The elementary building blocks of type theory are the empty type
($\bot$), the unit type ($\top$), the sum type ($\uplus$), and the
product type ($\times$). The traditional Curry-Howard correspondence
which goes back to at least 1969 relates these types to logical
propositions as follows: the type $\bot$ corresponds to the absurd
proposition with no proof; the type $\top$ corresponds to the
trivially true proposition; the type $\tau_1 \uplus \tau_2$
corresponds to the disjunction of the corresponding propositions, and
the type $\tau_1 \times \tau_2$ corresponds to the conjunction of the
corresponding propositions. The following tautologies of propositional
logic therefore give rise to functions witnessing the back-and-forth
transformations:
\[\begin{array}{rcl}
\tau \uplus \tau                      & \Leftrightarrow & \tau \\
 \tau \times \tau                     & \Leftrightarrow & \tau \\
 (\tau_1 \times \tau_2) \uplus \tau_3 & \Leftrightarrow & 
  (\tau_1 \uplus \tau_3) \times (\tau_2 \uplus \tau_3) 
\end{array}\]

This connection to logic, as inspiring as it is, only cares whether a
type is inhabited or not. For example, when translated to the world of
types, the first tautology above states that the type $\tau \times
\tau$ is inhabited iff the type $\tau$ is inhabited. Furthermore, the
proofs of the two implications give rise to two functions that produce
an element from one type given an element of the other. This framework
is however of no direct help if one is concerned with other, richer
properties of types and their relationships. For example, type
isomorphisms are an important relation between types that is more refined
than mere inhabitance of types as they clearly distinguishes $\tau
\times \tau$ and $\tau$.

The study of type isomorphisms became recently popular during at least
two short periods: in the early 1990s when they were used to search
large libraries~\citep{Rittri:1989:UTS:99370.99384}, and in the mid
2000s when they were studied from a categorical
perspective~\citep{Fiore:2004,fiore-remarks,Fiore2004707}. In the last
few years, type isomorphisms became one of the central concepts in
homotopy type theory (HoTT)~\citep{hottbook}, where type equivalences
feature prominently in the \emph{univalence axiom}.  These connections
exposed that there is even more interesting structure arising from
type isomorphisms at higher levels. For example, consider the two
isomorphisms between the type $\top + \top$ and itself. One of these
is the identity and the other is the twist map. These isomorphisms are
themselves ``not equivalent'' one level up in a sense to be
formalized. And the chain of reasoning continues.

The question we therefore ask is whether there is a natural
correspondence, in the style of the Curry-Howard correspondence,
between types and some existing mathematical entities, which would
bring forth the structure of type isomorphisms and their equivalences
at higher levels. We argue that commutative semirings and their categorification
are exactly these entities. In a broader sense, such a correspondence
connects computation with mathematical structures common in topology
and physics thus opening the door for deeper and more fruitful
interactions among these disciplines~\citep{rosetta}. In more detail,
because physical laws obey various conservation principles (including
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
models~\citep{Frank:1999:REC:930275,DeBenedictis:2005:RLS:1062261.1062325}.

\begin{comment}
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
\citet {hottbook}, based on Homotopy Type Theory (HoTT), greatly
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

\end{comment}

%% \todo{Restore some of the link to physics-based computation and
%% reversible computation.  Detail what our contributions are.}  

%% \todo{The outline will need to be tweaked once it settles}

%% \todo{Every single theorem should have, in a comment above it, the
%% name of a source file and an Agda statement which has a proof.}

\paragraph*{Outline.} The next section discusses the correspondence
between semirings and types at an intuitive informal
level. Sec.~\ref{sec:equiv} formalizes the notions of equivalences of
types and equivalences of equivalences which are the semantic building
blocks for the computational side of the Curry-Howard style
correspondence we aim for. Sec.~\ref{sec:prog} introduces a reversible
programming language which exactly captures type
equivalences. Sec.~\ref{sec:categorification} lays the categorical
foundation for developing a second language that exactly captures
equivalences between equivalences. Sec.~\ref{sec:revised} introduces such
a language. The remaining sections put our work in perspective, point
out its limitations and directions for future work, and conclude.

% The next section reviews equivalences between finite types and relates
% them to various commutative semiring structures. The main message of
% that section is that, up to equivalence, the concept of equivalence of
% finite types is equivalent to permutations between finite sets. The
% latter is computationally well-behaved with existing reversible
% programming languages developed for programming with permutations and
% finite-type isomorphisms. This family of languages, called $\Pi$, is
% universal for describing combinational reversible circuits (see
% Sec.~\ref{sec:3}). The infrastructure of the HoTT-inspired type
% equivalences enriches these languages by viewing their original design
% as 1-paths and systematically producing 2-paths (equivalences between
% equivalences) manifesting themselves as syntactic rules for reasoning
% about equivalences of programs representing reversible
% circuits. Sec.~\ref{sec:sem} starts the semantic investigation of the
% $\Pi$ languages emphasizing the denotational approach that maps each
% $\Pi$ program to a type equivalence or equivalently a permutation. The
% section also gives a small example showing how a few rules that are
% sound with respect to equivalence of permutations can be used to
% transform $\Pi$ programs without reliance on any extensional
% reasoning. Sec.~\ref{sec:5} then reveals that these rules are
% intimately related to the coherence conditions of the categorified
% analogues of the commutative semiring structures underlying type
% equivalences and permutations, namely, the so-called \emph{symmetric
%   rig weak groupoids}. Sec.~\ref{sec:categorification} contains that
% ``punchline'': a sound and complete set of rules that can be used to
% reason about equivalences of $\Pi$ programs.  

We note that because the
issues involved are quite subtle, the paper is the ``unformalization''
of an executable \texttt{Agda 2.4.2.3} package with the global
\AgdaComment{without-K} option enabled.\footnote{Available at
  \url{http://github.com//JacquesCarette/pi-dual/Univalence}.}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Informal Development}\label{sec:informal}

We explore the main ingredients that would constitute a Curry-Howard
like correspondence between (commutative) semirings and (constructive)
type theory.

%%%
\subsection{Semirings}\label{sec:semirings}

We begin with the familiar definition of the algebraic structure of
commutative semirings.

\begin{definition}\label{defn:csr}
  A \emph{commutative semiring} (sometimes called a \emph{commutative
    rig} (commutative ri\emph{n}g without negative elements) consists of a
  set $R$, two distinguished elements of $R$ named 0 and 1, and two
  binary operations~$+$ and $\cdot$, satisfying the following
  relations for any $a,b,c \in R$:
\[\begin{array}{rcl@{\qquad}l}
0 + a               & = & a                   & (\mbox{+-unit}) \\
a + b               & = & b + a             & (\mbox{+-sym})  \\
a + (b + c)         & = & (a + b) + c    & (\mbox{+-assoc}) \\
                                              \\
1 \cdot a           & = & a                   & (\mbox{$\cdot$-unit}) \\
a \cdot b           & = & b \cdot a         & (\mbox{$\cdot$-sym})  \\
a \cdot (b \cdot c) & = & (a \cdot b) \cdot c & (\mbox{$\cdot$-assoc}) \\
                                              \\
0 \cdot a           & = & 0                   & (\mbox{$\cdot$-0}) \\
(a + b) \cdot c     & = & (a \cdot c) + (b \cdot c) & (\mbox{$\cdot$-+})
\end{array}\]
\end{definition}

If one were to focus on the \emph{syntax} of the semiring elements,
they would be described using the following grammar:
\[\begin{array}{rcl}
a & ::= & 0 \alt 1 \alt a + b \alt a \cdot b
\end{array}\]

This grammar evidently corresponds to the grammar for the finite types in
type theory:
\[\begin{array}{rcl}
\tau & ::= & \bot \alt \top \alt \tau_1 \uplus \tau_2 \alt \tau_1 \times \tau_2 
\end{array}\]

We will show that this --- so far --- superficial correspondence
scratches the surface of a beautiful correspondence of rich
combinatorial structure.

%%% 
\subsection{Semiring Identities and Isomorphisms}
\label{subsec:isos}

Having matched the syntax of semiring elements and the syntax of
types, we examine the computational counterpart of the semiring
identities. When viewed from the type theory side, each semiring
identity asserts that two types are ``equal.'' For example, the
identity $\cdot$-unit, i.e., $1 \cdot a = a$ asserts that the types
$\top \times A$ and $A$ are ``equal.'' One way to express such an
``equality'' computationally is to exhibit two functions mediating
between the two types and prove that these two functions are
inverses. Specifically, we define:
\[\begin{array}{l@{\qquad}l}
\fun{f} ~:~ \top \times A \to A & \fun{f⁻} : A \to \top \times A \\
\fun{f}~(\tc , x) = x & \fun{f⁻}~x = (\tc, x) 
\end{array}\] 
and prove
$\fun{f} \circ \fun{f⁻} = \fun{f⁻} \circ \fun{f} = \fun{id}$. One
could use this proof to ``equate'' the two types, but computationally
speaking it is more appropriate to keep the identity of the types
separate and speak of \emph{isomorphisms}.

%%%
\subsection{Proof Relevance}
\label{subsec:proofrelev}

In the world of semirings, there are many proofs of $a + a = a +
a$. Consider the following two proofs:
\[\begin{array}{l@{\qquad}rcl@{\qquad}l}
\fun{pf₁} : & a + a &=& a + a & \mbox{(because $=$ is reflexive)} \\
\fun{pf₂} : & a + a &=& a + a & \mbox{(using $+$-sym)}
\end{array}\]
In some cases, we might not care \emph{how} a semiring identity was
proved and it might then be acceptable to treat $\fun{pf₁}$ and
$\fun{pf₂}$ as ``equal.'' But although these two proofs of
$a + a = a + a$ look identical, they use different ``justifications''
and these justifications are clearly \emph{not} ``equal.''

When viewed from the computational side, the situation is as
follows. The first proof gives rise to one isomorphism using the
self-inverse function $\fun{id}$. The second proof gives rise to
another isomorphism using another self-inverse function
$\fun{swap}$ defined as:
\[\begin{array}{l}
\fun{swap} ~:~ A \uplus B \to B \uplus A \\
\fun{swap}~(\injl{x}) = \injr{x} \\
\fun{swap}~(\injr{x}) = \injl{x} 
\end{array}\]
Now it is clear that even though both $\fun{id}$ and
$\fun{swap}$ can be used to establish an isomorphism between $A
\uplus A$ and itself, their actions are different. Semantically
speaking, these two functions are different and no program
transformation or optimization should ever identify them.

% \jc{both proofs below implicitly use 'naturality', or
% \AgdaFunction{cong} in Agda parlance;  Also, I don't see
% where symmetry of = comes in?}
The discussion above should not however lead one to conclude that
programs resulting from different proofs are always semantically
different. Consider for example, the following two proofs of
$(a + 0) + b = a + b$. To avoid clutter in this informal presentation,
we omit the justifications that refer to the fact that $=$ is a congruence
relation:
\[\begin{array}{l@{\qquad}rcl@{\qquad}l}
\fun{pf₃} : & (a + 0) + b &=& (0 + a) + b & \mbox{(using $+$-sym}) \\
& &=& a + b & \mbox{(using $+$-unit)}  \\
\\
\fun{pf₄} : & (a + 0) + b &=& a + (0 + b) & \mbox{(using $+$-assoc)} \\
& &=& a + b & \mbox{(using $+$-unit)}
\end{array}\]
On the computational side, the proofs induce the following two isomorphisms between 
$(A \uplus \bot) \uplus B$ and $A \uplus B$. The first isomorphism \fun{pf₃}
takes the values in $(A \uplus \bot) \uplus B$ using the composition
of the following two isomorphisms:
\[\begin{array}{l@{\qquad}l}
\fun{f₁} ~:~ (A \uplus \bot) \uplus B \to (\bot \uplus A) \uplus B 
  & \fun{f₁⁻} ~:~ (\bot \uplus A) \uplus B \to (A \uplus \bot) \uplus B \\
\fun{f₁} (\injl{(\injl{x})}) = \injl{(\injr{x})} & 
  \fun{f₁⁻} (\injl{(\injr{x})}) = \injl{(\injl{x})}) \\
\fun{f₁} (\injr{x}) = \injr{x} & 
  \fun{f₁⁻} (\injr{x}) = \injr{x}) \\
\\
\fun{f₂} ~:~ (\bot \uplus A) \uplus B \to A \uplus B & 
  \fun{f₂⁻} ~:~ A \uplus B \to (\bot \uplus A) \uplus B \\  
\fun{f₂} (\injl{(\injr{x})}) = \injl{x} & 
  \fun{f₂⁻} (\injl{x}) = \injl{(\injr{x})} \\
\fun{f₂} (\injr{x}) = \injr{x} & 
  \fun{f₂⁻} (\injr{x}) = \injr{x}
\end{array}\]
We calculate that composition corresponding to \fun{pf₃} is:
\[\begin{array}{l@{\qquad}l}
\fun{f₁₂} ~:~ (A \uplus \bot) \uplus B \to A \uplus B & 
  \fun{f₁₂⁻} ~:~ A \uplus B \to (A \uplus \bot) \uplus B \\
\fun{f₁₂} (\injl{(\injl{x})}) = \injl{x} & 
  \fun{f₁₂⁻} (\injl{x}) = \injl{(\injl{x})}) \\
\fun{f₁₂} (\injr{x}) = \injr{x} & 
  \fun{f₁₂⁻} (\injr{x}) = \injr{x}) 
\end{array}\]
We can similarly calculate the isomorphism corresponding to \fun{pf₄}
and verify that it is identical to the one above. 

% along the following ``paths'' to values in $A \uplus B$:
% \[\begin{array}{l}
% \texttt{inj}_1~(\texttt{inj}_1~x) \mapsto \texttt{inj}_1~(\texttt{inj}_2~x) \mapsto \texttt{inj}_1~x \\
% \texttt{inj}_2~x \mapsto \texttt{inj}_2~x 
% \end{array}\] 
% The second isomorphism carries the values along different ``paths'':
% \[\begin{array}{l}
% \texttt{inj}_1~(\texttt{inj}_1~x) \mapsto \texttt{inj}_1~x \\
% \texttt{inj}_2~x \mapsto \texttt{inj}_2~(\texttt{inj}_2~x) \mapsto \texttt{inj}_2~x
% \end{array}\]
% These two computations are, unlike the case of \textit{id} and
% \textit{swap} from the previous example, semantically equivalent. This
% is not immediately obvious but one can get some intuition by viewing
% the two computations diagrammatically as shown below. The diagram
% shows the two top paths can be continuously transformed to the two
% bottom paths:

% \begin{center}
% \begin{tikzpicture}[scale=0.9,every node/.style={scale=0.9}]
%   \draw (-2,-2) ellipse (0.5cm and 1cm);
%   \draw[fill] (-2,-1.5) circle [radius=0.025];
%   \node[below] at (-2.1,-1.5) {$A$};
%   \draw[fill] (-2,-2.5) circle [radius=0.025];
%   \node[below] at (-2.1,-2.5) {$\bot$};
%   \draw (-2,-2.5) ellipse (1cm and 1.7cm);
%   \draw[fill] (-2,-3.35) circle [radius=0.025];
%   \node[below] at (-2.1,-3.35) {$B$};

%   \draw (6.5,-2) ellipse (0.5cm and 1cm);
%   \draw[fill] (6.5,-1.5) circle [radius=0.025];
%   \node[below] at (6.65,-1.5) {$A$};
%   \draw[fill] (6.5,-2.5) circle [radius=0.025];
%   \node[below] at (6.65,-2.5) {$B$};

%   \draw (1.5,0.5) ellipse (0.5cm and 1cm);
%   \draw[fill] (1.5,1) circle [radius=0.025];
%   \node[below] at (1.4,1) {$\bot$};
%   \draw[fill] (1.5,0) circle [radius=0.025];
%   \node[below] at (1.4,0) {$A$};
%   \draw (1.5,0) ellipse (1cm and 1.7cm);
%   \draw[fill] (1.5,-0.85) circle [radius=0.025];
%   \node[below] at (1.4,-0.85) {$B$};

%   \draw (2.5,-4) ellipse (0.5cm and 1cm);
%   \draw[fill] (2.5,-2.5) circle [radius=0.025];
%   \node[below] at (2.4,-2.5) {$A$};
%   \draw[fill] (2.5,-3.5) circle [radius=0.025];
%   \node[below] at (2.4,-3.5) {$\bot$};
%   \draw (2.5,-3.5) ellipse (1cm and 1.7cm);
%   \draw[fill] (2.5,-4.35) circle [radius=0.025];
%   \node[below] at (2.4,-4.35) {$B$};

%   \draw[->] (-2,-1.5) to[bend left] (1.5,0) ;
%   \draw[->] (-2,-3.35) to[bend left] (1.5,-0.85) ;
%   \draw[->] (1.5,0) to[bend left] (6.5,-1.45) ;
%   \draw[->] (1.5,-0.85) to[bend left] (6.5,-2.45) ;

%   \draw[->] (-2,-1.5) to[bend right] (2.5,-2.5) ;
%   \draw[->] (-2,-3.35) to[bend right] (2.5,-4.35) ;
%   \draw[->] (2.5,-2.5) to[bend right] (6.5,-1.55) ;
%   \draw[->] (2.5,-4.35) to[bend right] (6.5,-2.55) ;

% \end{tikzpicture}
% \end{center}

%%% 
\subsection{Summary} 

To summarize this high-level presentation, there is a natural
computational model that emerges from viewing types as syntax for
semiring elements and semiring identities as type isomorphisms. The
correspondence continues further between justifications for semiring
identities and valid program transformations and optimizations. There
is a long way however from noticing such a correspondence to
formalizing it in such way that a well-founded reversible programming
language along with its accompanying program transformations and
optimizations can be naturally extracted from the algebraic semiring
structure. Furthermore, the correspondence between the algebraic
manipulations in semirings and program transformations is so tight
that it should be possible to conveniently move back and forth between
the two worlds transporting results that are evident in one domain to
the other. The remainder of the paper is about such a formalization
and its applications. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% \section{Equivalences and Commutative Semirings, formally} 
\section{Equivalences}
\label{sec:equiv}

The previous section used two informal notions of equivalence: 
equivalences between types (corresponding to semiring identities), and
equivalences between programs corresponding to proofs of semiring
identities. We give precise definitions to these notions. 

% We now redo the material of the previous section, but with formal
% definitions throughout.  When the Agda code is just as clear as
% informal ``paper mathematics'', we choose formality.

%%%
\subsection{Type Equivalences}

As a first approximation, Sec.~\ref{subsec:isos} identifies two types
when there is an isomorphism between them.  The next section
(Sec.~\ref{subsec:proofrelev}) however reveals that we want to reason
at a higher-level about equivalences of such isomorphisms. We
therefore follow the HoTT approach and expose one of the functions
forming the isomorphism in order to explicitly encode the precise way
in which the two types are equivalent. Thus, for example, as mentioned
earlier, there are two equivalences between the type
\AgdaDatatype{Bool} and itself: one that uses the identity map and one
that uses boolean negation. These two equivalences have enough
information to prove that they are \emph{not} themselves equivalent.

Our definition is presented next.\footnote{For reasons beyond the
scope of this paper, we do not use any of the definitions of
equivalence which make it a \emph{mere proposition}, as we want a
definition which is syntactically symmetric.}
 
\begin{definition}[Homotopy]
\label{def:homotopy}
Two functions $f,g:A \rightarrow B$ are \emph{homotopic} if
$\forall x:A. f(x) = g(x)$. In Agda, we write:

\medskip 
\begin{code}
_∼_ : ∀ {A : Set} {P : A → Set} → (f g : (x : A) → P x) → Set
_∼_  {A} f g = (x : A) → f x ≡ g x
\end{code}
\end{definition}

\begin{definition}[Quasi-inverse]
\label{def:quasi}
For a function $f : A \rightarrow B$, a \emph{quasi-inverse} is a
triple $(g, \alpha, \beta)$, consisting of a function
$g : B \rightarrow A$ and two homotopies
$\alpha : f \circ g \sim \mathrm{id}_B$ and
$\beta : g \circ f \sim \mathrm{id}_A$. In Agda, we write:

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

\begin{definition}[Equivalence of types]\label{def:eq}
  Two types $A$ and $B$ are equivalent $A ≃ B$ if there exists a
  function $f : A \rightarrow B$ together with a quasi-inverse for
  $f$. In Agda, we write:

\medskip 
\begin{code}
_≃_ : Set → Set → Set
A ≃ B = Σ (A → B) isqinv
\end{code}
\end{definition}

\noindent It is easy to prove that homotopies (for any given function
space $A \rightarrow B$) are an equivalence relation. It is also straightforward to
show that $≃$ is an equivalence relation by defining:
\[\begin{array}{rcl}
\AgdaFunction{id≃} &:& A ≃ A \\
\AgdaFunction{sym≃} &:& (A ≃ B) → (B ≃ A) \\
\AgdaFunction{trans≃} &:& (A ≃ B) → (B ≃ C) → (A ≃ C)
\end{array}\]

The definition of equivalence allows us to formalize the presentation
of Sec.~\ref{subsec:isos} by proving that every commutative semiring
identity is satisfied by types in the universe (\AgdaDatatype{Set}) up
to~$≃$.

% TypeEquiv:typesCSR
\begin{theorem}\label{thm:typesCSR}
The collection of all types (\AgdaDatatype{Set}) forms a commutative 
semiring (up to $\simeq$). 
\end{theorem}
\begin{proof}
The relevant structure is:
\AgdaHide{
\begin{code}
postulate
  typesIsCSR : IsCommutativeSemiring _≃_ _⊎_ _×_ ⊥ ⊤
\end{code}
}

\medskip 
\begin{code} 
typesCSR : CommutativeSemiring (Level.suc Level.zero) Level.zero
typesCSR = record {
  Carrier = Set ;
  _≈_ = _≃_ ;
  _+_ = _⊎_ ;
  _*_ = _×_ ;
  0#  = ⊥ ;
  1#  = ⊤ ;
  isCommutativeSemiring = typesIsCSR
  }
\end{code}
\medskip  

\noindent The functions, homotopies, and quasi-inverses witnessing the explicit
equivalences are defined within \AgdaFunction{typesIsCSR} and are
straightforward. For future reference, we list some of these equivalences:
\[\begin{array}{rcl}
\AgdaFunction{unite₊≃} &:& (⊥ ⊎ A) ≃ A \\
\AgdaFunction{swap₊≃} &:& (A ⊎ B) ≃ (B ⊎ A) \\
\AgdaFunction{assoc₊≃} &:& ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C)) \\
\_\AgdaSymbol{⊎≃}\_ &:&  (A ≃ C) → (B ≃ D) → ((A ⊎ B) ≃ (C ⊎ D))
\end{array}\]
\qed
\end{proof}

%%%
\subsection{Equivalences of Equivalences}

In the terminology of Sec.~\ref{subsec:proofrelev}, an equivalence $≃$
denotes a proof of a semiring identity. Thus the proofs
\AgdaFunction{pf₁}, \AgdaFunction{pf₂}, \AgdaFunction{pf₃}, and
\AgdaFunction{pf₄} can be written formally as:
\AgdaHide{
\begin{code}
module A where

  id≃ : ∀ {A : Set} → A ≃ A
  id≃ = (id , qinv id (λ _ → refl) (λ _ → refl))

  sym≃ : ∀ {A B : Set} → (A ≃ B) → B ≃ A
  sym≃ (A→B , equiv) = e.g , qinv A→B e.β e.α
    where module e = isqinv equiv

  postulate
    trans≃ :  ∀ {A B C : Set} → (A ≃ B) → (B ≃ C) → (A ≃ C)

  swap₊ : {A B : Set} → A ⊎ B → B ⊎ A
  swap₊ (inj₁ a) = inj₂ a
  swap₊ (inj₂ b) = inj₁ b

  swapswap₊ : {A B : Set} → (swap₊ ∘ (swap₊ {A} {B})) ∼ id
  swapswap₊ (inj₁ a) = refl
  swapswap₊ (inj₂ b) = refl

  postulate
    unite₊≃ : {A : Set} → (⊥ ⊎ A) ≃ A

  postulate
    swap₊≃ : {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)

  postulate
    assoc₊≃ : {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))

  postulate
    _⊎≃_ :  ∀ {A B C D} → A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)

\end{code}
}

\medskip 
\begin{code}
  pf₁ : {A : Set} → (A ⊎ A) ≃ (A ⊎ A)
  pf₁ = id≃ 

  pf₂ : {A : Set} → (A ⊎ A) ≃ (A ⊎ A)
  pf₂ = swap₊≃

  pf₃ : {A B : Set} → ((A ⊎ ⊥) ⊎ B) ≃ (A ⊎ B)
  pf₃ = trans≃ (swap₊≃ ⊎≃ id≃) (unite₊≃ ⊎≃ id≃) 

  pf₄ : {A B : Set} → ((A ⊎ ⊥) ⊎ B) ≃ (A ⊎ B)
  pf₄ = trans≃ assoc₊≃ (id≃ ⊎≃ unite₊≃) 
\end{code}

\medskip  
 In order to argue that \AgdaFunction{pf₃} and \AgdaFunction{pf₄} are
equivalent, we therefore need a notion of equivalence of
equivalences. Our definition is fairly straightforward: two
equivalences are equivalent if there exist homotopies between their
underlying functions.

\begin{definition}[Equivalence of equivalences]
Two equivalences $e_1, e_2 : A ≃ B$ are themselves equivalent $e_1.f ∼
  e_2.f$ and $e_1.g ∼ e_2.g$. In Agda, we write:

\AgdaHide{
\begin{code}
  infix 4 _≋_
\end{code}
}

\medskip 
\begin{code}
  record _≋_ {A B : Set} (eq₁ eq₂ : A ≃ B) : Set where
    constructor eq
    open isqinv
    field
      f≡ : proj₁ eq₁ ∼ proj₁ eq₂
      g≡ : g (proj₂ eq₁) ∼ g (proj₂ eq₂)
\end{code}
\end{definition}

Note that we cannot use the type $\left(A \simeq B\right) \simeq
\left(A \simeq B\right)$ as ``equivalence of equivalence'' (even
though it is well formed).  The problem is that the homotopies
in such a type ($\alpha$ and $\beta$) would equate two elements
of type $A \simeq B$ using $\equiv$, but the components of
$\simeq$ contain functions -- and such an equality would require
extensionality.  But since equating two equivalences essentially
boils down to equating those functions, we simply need to do the
same as we did before, and move to homotopies.  Thus our
definition\footnote{Strictly speaking, the $g\equiv$ component
is redundant, from a logical perspective, as it is derivable.  From 
a computational perspective, it is very convenient.}.

We could now verify that \AgdaFunction{pf₃} is indeed equivalent to
\AgdaFunction{pf₄} by proving
\AgdaFunction{pf₃}~\AgdaSymbol{≋}~\AgdaFunction{pf₄}. Such a proof
exists in the accompanying code in \AgdaModule{TypeEquivEquiv} but
requires a surprisingly tedious infrastructure to present. We explore
a much more direct and intuitive to reason about such equivalences of
equivalences in the next sections. Of major importance will be
ensuring that our definition of equivalence of equivalence satisfies
some notion of soundness and completeness relative to proof
equivalence in the world of semirings.

% \noindent For example, for arbitrary types $A$, $B$, and $C$, we have
% equivalences such as:
% \[\begin{array}{rcl}
% \bot ⊎ A &\simeq& A \\
% \top \times A &\simeq& A \\
% A \times (B \times C) &\simeq& (A \times B) \times C \\
% A \times \bot &\simeq& \bot \\
% A \times (B \uplus C) &\simeq& (A \times B) \uplus (A \times C) 
% \end{array}\]

% One of the advantages of using equivalence $\simeq$ instead of strict
% equality $=$ is that we can form a type of all equivalences
% $\textsc{eq}_{A,B}$, and then investigate its structure.  In particular,
% for a given $A$ and $B$, the
% elements of $\textsc{eq}_{A,B}$ are all the ways in which we can prove
% $A \simeq B$. For example,
% $\textsc{eq}_{\AgdaDatatype {Bool},\AgdaDatatype  {Bool}}$ has two
% elements corresponding to the $\mathrm{id}$-equivalence and to the
% negation-equivalence that were mentioned before. More generally, 
% for finite types $A$ and $B$,
% the type $\textsc{eq}_{A,B}$ is only inhabited if $A$ and~$B$ have the
% same size in which case the type has $|A|~!$ (factorial of the size of
% $A$) elements witnessing the various possible identifications of $A$
% and $B$. The type of all equivalences has some non-trivial structure,
% which will be examined in detail in section~\ref{sec:categorification}.

% Note that finite types \emph{do not} form a commutative semiring: the
% extra ``size'' information is incompatible with the universally 
% quantified nature of the semiring axioms.

% \todo{find a good home for the definition of equivalence-of-equivalence.}
% \todo{figure out when to first mention $\Pi$ and cite.}

% \subsection{Linking Finite Types and Semirings}

% A result by \citet{Fiore:2004,fiore-remarks} completely characterizes
% the isomorphisms between finite types using the axioms of commutative
% semirings, whose definition we now turn to. The result which is proved
% in Lemma 2.2 of~\citet{fiore-remarks} is repeated below along with all
% supporting definitions.

% \begin{definition}[$\mathcal{D}$] The equational theory $\mathcal{D}$
%   consists of the following identities:
% \[\begin{array}{l}
% 1 \cdot x = x \qquad 
%   x \cdot y = y \cdot x \qquad
%   (x \cdot y) \cdot z = x \cdot (y \cdot z) \\
% x + 0 = x \qquad 
%   x + y = y + x \qquad 
%   (x + y) + z = x + (y + z) \\
% x \cdot 0 = 0 \qquad 
%   x \cdot (y + z) = x \cdot y + x \cdot z 
% \end{array}\]
% \end{definition}

% \begin{definition}
% We let $\mathcal{D}[T]$ be the
%   category with objects given by types over base types in $T$ and
%   morphisms $\tau_1 \to \tau_2$ given by equivalence classes $[ x : \tau_1 
%   \vdash t : \tau_2]$ of well-typed terms under the equivalence
%   identifying $(x : \tau_1 \vdash t : \tau_2)$ and $(x' : \tau_1
%   \vdash t' : \tau_2)$ iff the judgement $x : \tau_1 \vdash t =
%   t'[x/x'] : \tau_2$ is derivable. Composition is by substitution
% \[ 
%   [ x' : \tau_2 \vdash t' : \tau_3] \circ [ x : \tau_1 \vdash t : \tau_2] = 
%   [ x : \tau_1 \vdash t'[t/x'] : \tau_3] 
% \]
% with identities given by $[x : \tau \vdash x : \tau]$.
% \end{definition}

% \begin{definition}
% The category $\mathbf{F}$ is the
%   category of finite sets and functions. The translation
%   $\overline{\cdot}$ is:
% \[\begin{array}{l}
% \overline{x} = x \mbox{~($x$ is a variable)} \qquad
%   \overline{1} = 1 \qquad 
%   \overline{e_1 \cdot e_2} = \overline{e_1} \times \overline{e_2} \qquad 
%   \overline{0} = 0 \qquad 
%   \overline{e_1 + e_2} = \overline{e_1} + \overline{e_2} 
% \end{array}\]
% \end{definition}

% \begin{proposition} For arithmetic expressions $e_1$ and $e_2$ in the 
%   language given by 1, 0, $\cdot$, and + and with unknowns in a set
%   $U$, the following statements are equivalent. The notation $\cong$ is type isomorphism.
% \begin{enumerate}
% \item $\mathcal{D} \vdash e_1 = e_2$.
% \item $\overline{e_1} \cong \overline{e_2} \mbox{~in~} \mathcal{D}[U]$.
% \item $\mathbf{F} \vdash \overline{e_1} = \overline{e_2}$.
% \item $N_0 \models e_1 = e_2$.
% \end{enumerate}
% \end{proposition}

% Intuitively, Fiore et. al's result states that one can interpret each 
% finite type by its size, and that this identification validates the 
% familiar properties of the natural numbers, and is in fact isomorphic 
% to the commutative semiring of the natural numbers.

% \begin{comment}
% \begin{theorem}
% \label{thm:eqeq}
%   The type of all equivalences $\textsc{eq}_{A,B}$ for finite types
%   $A$ and $B$ forms a commutative semiring up to extensional
%   equivalence of equivalences \AgdaSymbol{≋}.
% \end{theorem}
% \begin{proof}
%   The most important insight is the definition of equivalence of
%   equivalences. Two equivalences $e_1, e_2 : \textsc{eq}_{A,B}$ with
%   underlying functions $f_1$ and $f_2$ and underlying quasi-inverses
%   $g_1$ and $g_2$ are themselves equivalent $e₁ ≋ e₂$ if we have that
%   both $f₁ = f₂$ and $g₁ = g₂$ extensionally. Given this notion of
%   equivalence of equivalences, the proof proceeds smoothly with the
%   additive unit being the vacuous equivalence $\bot \simeq \bot$, the
%   multiplicative unit being the trivial equivalence
%   $\top \simeq \top$, and the two binary operations being essentially
%   a mapping of $\uplus$ and $\times$ over equivalences.
% \end{proof}

% We reiterate that the commutative semiring axioms in this case are
% satisfied up to extensional equality of the functions underlying the
% equivalences.  We could, in principle, consider a weaker notion of
% equivalence of equivalences and attempt to iterate the construction
% but for the purposes of modeling circuits and optimizations, it is
% sufficient to consider just one additional level.

% Our work builds on this identification together with work by
% \citet{James:2012:IE:2103656.2103667} which introduced the $\Pi$
% family of languages whose core computations are these isomorphisms
% between finite types. Taking into account the growing-in-importance
% idea that isomorphisms have interesting computational content and
% should not be silently or implicitly identified, we first recast Fiore
% et. al's result in the next section, making explicit that the
% commutative semiring structure can be defined up to the HoTT relation
% of \emph{type equivalence} instead of strict equality~$=$.
% \end{comment}

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \section{Permutations}

% now give names to equivalences ...

% Although permutations do not form a semiring (for the same reason
% that finite types do not), they ``almost'' do.  As they are a 
% crucial ingredient later on, we present some basic results here.
% Informally, a permutation is a bijection between two canonically
% finite sets.  We formalize this as

% \jc{need to define some these things formally.  Maybe give the
% Agda?  Probably not, as we don't want to talk about permutations very
% much here.  In fact, perhaps cut things down instead of add?  This is
% about type equivalences, we can downplay permutations.  Not sure.}

% \begin{definition}
% A \emph{permutation} is a $4$-tuple ...
% \end{definition}

% \jc{the introductory material in the paragraph below is now bogus.
% I have fixed our definitions (to agree with our code), so that we
% don't have that confusion.  We need to figure out what we really 
% want to say here!}
% The idea is that, \emph{up to equivalence}, the only interesting property of
% a finite type is its size, so that type equivalences must be
% size-preserving maps and hence correspond to permutations. For
% example, given two equivalent types $A$ and $B$ of completely
% different structure, e.g.,
% $A = (\top \uplus \top) \times (\top \uplus (\top \uplus \top))$ and
% $B = \top \uplus (\top \uplus (\top \uplus (\top \uplus (\top \uplus
% (\top \uplus \bot)))))$,
% we can find equivalences from either type to the finite set
% $\mathsf{Fin}~6$ and reduce all type equivalences between sets of size
% 6 to permutations.

% We begin with the following theorem which precisely characterizes the
% relationship between finite types and finite sets by formalizing that
% equivalent finite types must have the same size.

% \begin{theorem}
%   If $A\simeq \mathsf{Fin}~m$, $B\simeq \mathsf{Fin}~n$ and
%   $A \simeq B$ then $m = n$.
% \end{theorem}
% \begin{proof}
%   We proceed by cases on the possible values for $m$ and $n$. If they
%   are different, we quickly get a contradiction. If they are both~0 we
%   are done. The interesting situation is when $m = \mathit{suc}~m'$
%   and $n = \mathit{suc}~n'$. The result follows in this case by
%   induction assuming we can establish that the equivalence between $A$
%   and $B$, i.e., the equivalence between
%   $\mathsf{Fin}~(\mathit{suc}~m')$ and
%   $\mathsf{Fin}~(\mathit{suc}~n')$, implies an equivalence between
%   $\mathsf{Fin}~m'$ and $\mathsf{Fin}~n'$. In a constructive setting,
%   we actually need to construct a particular equivalence between the
%   smaller sets given the equivalence of the larger sets with one
%   additional element. This lemma is quite tedious as it requires us to
%   isolate one element of $\mathsf{Fin}~(\mathit{suc}~m')$ and analyze
%   every class of positions this element could be mapped to by the
%   larger equivalence and in each case construct an equivalence that
%   excludes it.
% \end{proof}

% Given the correspondence between finite types and finite sets, we now
% prove that equivalences on finite types are equivalent to permutations
% on finite sets. We proceed in steps: first by proving that finite sets
% for a commutative semiring up to $\simeq$ (Thm.~\ref{thm:finrig});
% second by proving that, at the next level, the type of permutations
% between finite sets is also a commutative semiring up to strict
% equality of the representations of permutations
% (Thm.~\ref{thm:permrig}); third by proving that the type of type
% equivalences is equivalent to the type of permutations
% (Thm.~\ref{thm:eqeqperm}); and finally by proving that the commutative
% semiring of type equivalences is isomorphic to the commutative
% semiring of permutations (Thm.~\ref{thm:isoeqperm}). This series of
% theorems will therefore justify our focus in the next section of
% develop a term language for permutations as a way to compute with type
% equivalences.

% \begin{theorem}\label{thm:finrig}
%   The collection of all finite types ($\AgdaDatatype{Fin}~m$ for
%   natural number $m$) forms a commutative semiring (up to $\simeq$).
% \end{theorem}
% \begin{proof}
%   The additive unit is \AgdaDatatype{Fin}~$0$ and the multiplicative unit
%   is \AgdaDatatype{Fin}~$1$.  For the two binary operations, the proof
%   crucially relies on the following equivalences:
% \end{proof}
 
% \begin{theorem}\label{thm:permrig}
%   The collection of all permutations $\textsc{perm}_{m,n}$ between
%   finite sets $\mathsf{Fin}~m$ and $\mathsf{Fin}~n$ forms a
%   commutative semiring up to strict equality of the representations of
%   the permutations.
% \end{theorem}
% \begin{proof}
%   The proof requires delicate attention to the representation of
%   permutations as straightforward attempts turn out not to capture
%   enough of the properties of permutations.\footnote{None of the
%     formalizations of permutations in Agda or Coq known to us supports
%     the full range of operations that we need including sequential
%     compositions, disjoint unions, and products of permutations.}
%   After several attempts, we settled on formalizing a permutation
%   using the conventional one-line notation, e.g., giving a preferred
%   enumeration 1 2 3 of a set with three elements, the one-line notion
%   2 3 1 denotes the permutation sending 1 to 2, 2 to 3, and 3 to 1. To
%   make sure the sequence of numbers is of the right length and that
%   each number is in the right range, we use Agda vectors
%   $\AgdaPrimitiveType{Vec}~(\AgdaPrimitiveType{Fin}~m)~n$ (abbreviated
%   $\AgdaFunction{FinVec}~m~n$). To further ensure that the vector
%   elements have no repetitions (i.e., represent 1-1 functions), we
%   include in the representation of each permutation, an inverse vector
%   $\AgdaFunction{FinVec}~n~m$ as well as two proofs asserting that the
%   compositions in both directions produce the identity permutation
%   (which naturally forces $m$ and $n$ to be equal). Given this
%   representation, we can prove that two permutations are equal if the
%   one-line vector representations are strictly equal \emph{and} we can
%   support the full range of operations on permutations. The main proof
%   then proceeds using the vacuous permutation $\mathsf{CPerm}~0~0$ for
%   the additive unit and the trivial permutation $\mathsf{CPerm}~1~1$
%   for the multiplicative unit. The binary operations on permutations
%   map $\mathsf{CPerm}~m₁~m₂$ and $\mathsf{CPerm}~n₁~n₂$ to
%   $\mathsf{CPerm}~(m₁+n₁)~(m₂+n₂)$ and
%   $\mathsf{CPerm}~(m₁*n₁)~(m₂*n₂)$ respectively. Their definition
%   relies on the properties that the unions and products of the
%   one-line vectors denoting permutations distribute over the
%   sequential compositions of permutations.
% \end{proof}

% \begin{theorem}\label{thm:eqeqperm}
% If $A ≃ \mathsf{Fin}~m$ and $B ≃ \mathsf{Fin}~n$, then the type of all
% equivalences $\textsc{eq}_{A,B}$ is equivalent to the type of all
% permutations $\textsc{perm}~m~n$.
% \end{theorem}
% \begin{proof}
%   The main difficulty in this proof was to generalize from sets to 
%   setoids to make the equivalence relations explicit. The proof is 
%   straightforward but long and tedious. 
% \end{proof}

% \begin{theorem}\label{thm:isoeqperm}
%   The equivalence of Thm.~\ref{thm:eqeqperm} is an \emph{isomorphism}
%   between the commutative semiring of equivalences of finite types and
%   the commutative semiring of permutations.
% \end{theorem}
% \begin{proof}
%   In the process of this proof, we show that every axiom of semirings
%   of types is an equivalence and a permutation.  Some of the axioms
%   like the associativity of sums gets mapped to the trivial identity
%   permutation.  However, some axioms reveal interesting structure when
%   expressed as permutations; the most notable is that the
%   commutativity of products maps to a permutation solving the
%   classical problem of in-place matrix transposition:
%   \[
%     \AgdaFunction{swap⋆cauchy}~:~(m~n~:~ℕ)~→~\AgdaFunction{FinVec}~(n~*~m)~(m~*~n)
%   \]
% \end{proof}

% Before concluding this section, we recall that, the conventional
% formulation of the univalence \emph{axiom} is:
% \[
% (A ≡ B) ≃ (A ≃ B)
% \]
% where $≡$ is the propositional equality relation and hence $(A ≡ B)$
% is the collection of all identities between types $A$ and $B$. With
% the proper Agda definitions, Thm.~\ref{thm:eqeqperm} can be rephrased
% in a more evocative way as follows.

% \begin{theorem}
% \[
% \mathsf{Perm}~|A|~|B|  ≃ (A ≃ B)
% \]
% \end{theorem}

% \noindent 
% where $\mathsf{Perm}~|A|~|B|$ is the collection of all permutations
% between the finite sets of the given sizes. This reformulation shows
% that, for the restricted finite types, the theorem proves, and gives a
% computational interpretation of, the univalence axiom. 

% \jc{I will first write this using informal mathematics.  Once it
% is correct, it is easy enough to switch to Agda}
% The above definition uses equality of functions (which is why
% we call it \emph{extensional}), which is well-known to be problematic
% for computational purposes.  Instead, we replace the equalities between
% functions with \emph{homotopies}, giving us

% \begin{definition}
% Given an equivalence relation $\simeq$ on a set $R$, a 
% \emph{$\simeq$-semiring} on $R$ is a semiring where $=$ is replaced by
% $\simeq$ in all the defining relations.
% \end{definition}

% We emphasize that, in the definition of commutative semiring 
% (Definition~\ref{defn:csr} in Section~\ref{sec:semirings}), the axioms 
% are satisfied
% up to strict equality $=$. The most famous instance of commutative
% semirings is, of course, the natural numbers $\mathbb{N}$.  We need
% to adapt this definition.

%  It should be noted that, in Agda's standard library, semirings
% are axiomatized as $\simeq$-semirings.  This is because in constructive
% type theory, there is no global equality ($=$) predicate, and thus
% it is more natural to define notions which are relative to an
% equivalence relation.

% % Bad definition!
% \begin{definition}[Quasi-inverse, extensionally]
% \label{def:quasi-ext}
% For a function $f : A \rightarrow B$, an \emph{extensional quasi-inverse} is a
% triple $(g, \alpha, \beta)$, consisting of a function
% $g : B \rightarrow A$ which satisfies the two (named) equalities
% $\alpha : f \circ g = \mathrm{id}_B$ and
% $\beta : g \circ f = \mathrm{id}_A$.
% \end{definition}
 
% \subsection{Proof transformations and equivalence of equivalences}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Programming with Equivalences}
\label{sec:prog}

We have established and formalized a correspondence between semirings
and types which relates semiring identities to the type equivalences
of Def.~\ref{def:eq}. We have further introduced the infrastructure
needed to reason about equivalences of equivalences so that we can
reason about the relation between different proofs of the same
semiring identity. As we aim to refine these relationships to a
Curry-Howard like correspondence, we now turn our attention to
developing an actual programming language. The first step will be to
introduce syntax that denotes type equivalences. Thus instead of
having to repeatedly introduce functions and their inverses and proofs
of homotopies, we would simply use a term language that exactly
expresses type equivalences and nothing else. 

\begin{figure*}[ht]
\[
\begin{array}{rrcll}
\idc :& \tau & \iso & \tau &: \idc \\
\\
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
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_2 \iso \tau_3}
{\jdg{}{}{c_1 \fatsemi c_2 : \tau_1 \iso \tau_3}}
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
\caption{$\Pi$-combinators.}
\label{pi-combinators}
\end{figure*}

%%%%%%%%%%
\subsection{Syntax of $\Pi$}

In previous work, \citet{rc2011,James:2012:IE:2103656.2103667}
introduced the~$\Pi$ family of reversible languages whose only
computations are isomorphisms between types. The simplest of these
languages is exactly the language we seek for capturing type
equivalences arising from semiring identities.

The syntactic components of our language are as follows:
\[\begin{array}{lrcl}
(\textit{Types}) & 
  \tau &::=& 0 \alt 1 \alt \tau_1 + \tau_2 \alt \tau_1 * \tau_2 \\
 (\textit{Values}) & 
  v &::=& () \alt \inl{v} \alt \inr{v} \alt (v_1,v_2) \\
(\textit{Combinator types}) &&& \tau_1 \iso \tau_2 \\
(\textit{Terms and Combinators}) & 
  c &::=& [\textit{see Figs.~\ref{pi-terms} and ~\ref{pi-combinators}}]
\end{array}\]
The values classified by the finite types types are the conventional
ones: $()$ of type 1, $\inl{v}$ and $\inr{v}$ for injections into sum
types, and $(v_1,v_2)$ for product types.

Fig.~\ref{pi-terms} gives the terms which correspond to the identities
of commutative semirings.  Each line of the figure introduces a pair
of dual constants\footnote{where $\idc$, $\swapp$ and $\swapt$ are
  self-dual.}  that witness the type isomorphism in the middle.
Fig.~\ref{pi-combinators} adds to that $3$ combinators, which come
from the requirement that $\iso$ be transitive (giving a sequential
composition operator), and that $\iso$ be a congruence for both $+$
and $*$ (giving a way to take sums and products of combinators).  That
latter congruence requirement is usually invisible in classical
mathematics, but appears when doing proof-relevant mathematics.

The attentive reader will notice that there are many more combinators
here than in Def.~\ref{defn:csr}.  This is because we want the
language to be composed of \emph{equivalences}, and we want the
reversibility of the language to be a theorem, at the level of the
syntax.  In particular, every combinator $c$ has an inverse $!c$
according to the figure. The inverse flips the order of the
combinators in sequential composition, and is homomorphic on sums and
products.

%%%%%%%%%%%%
\subsection{Example Programs}

\AgdaHide{
\begin{code}
open import PiU using (U; ZERO; ONE; PLUS; TIMES) 
open import PiLevel0

infixr 2  _⟷⟨_⟩_   
infix  2  _□       

_⟷⟨_⟩_ : (t₁ : U) {t₂ : U} {t₃ : U} → 
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃) 
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U) → {t : U} → (t ⟷ t)
_□ t = id⟷
\end{code}
}
\begin{code}
BOOL : U
BOOL  = PLUS ONE ONE 

BOOL² : U
BOOL² = TIMES BOOL BOOL

NOT : BOOL ⟷ BOOL
NOT = swap₊

NEG1 NEG2 NEG3 NEG4 NEG5 : BOOL ⟷ BOOL
NEG1 = swap₊
NEG2 = id⟷ ◎ NOT 
NEG3 = NOT ◎ NOT ◎ NOT 
NEG4 = NOT ◎ id⟷
NEG5 = uniti⋆l ◎ swap⋆ ◎ (NOT ⊗ id⟷) ◎ swap⋆ ◎ unite⋆l
NEG6 = uniti⋆r ◎ (NOT ⊗ id⟷) ◎ unite⋆r 

-- CNOT

CNOT : BOOL² ⟷ BOOL²
CNOT = TIMES BOOL BOOL
         ⟷⟨ id⟷ ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ dist ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT) ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ factor ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ id⟷ ⟩
       TIMES BOOL BOOL □
  where x = ONE; y = ONE

-- TOFFOLI

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

%%%%%%%%%%%%
\subsection{Example Proofs}

Write pf1, pf2, pf3, and pf4

%%%%%%%%%%%%
%% \subsection{Semiring of Finite Types}

% Our previous grammar for $\tau$ can be formalized as

% \begin{code}
% data U : Set where
%   ZERO  : U
%   ONE   : U
%   PLUS  : U → U → U
%   TIMES : U → U → U
% \end{code}
% \noindent to define the universe \AgdaDatatype{U} of finite types.
% There is an obvious mapping from \AgdaDatatype{U} to $\mathbb{N}$:

% \begin{code}
% toℕ : U → ℕ
% toℕ ZERO = 0
% toℕ ONE = 1
% toℕ (PLUS t₁ t₂) = toℕ t₁ + toℕ t₂
% toℕ (TIMES t₁ t₂) = toℕ t₁ * toℕ t₂ 
% \end{code}

% We will indeed see that \AgdaDatatype{U} and $\mathbb{N}$ are
% isomorphic (as semirings).  But to do so, we first need to
% formalize when two types are equivalent.

% \subsection{Equivalences of Types}

%%%%%%%%%%%%
\subsection{Semantics}

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

In conventional programming language research, valid optimizations are
specified with reference to the \emph{observational equivalence}
relation which itself is defined with reference to an \emph{evaluator}.
As the language is reversible, a reasonable starting point would then
be to define forward and backward evaluators with the following
signatures:

\[\begin{array}{rcl}
\mathit{eval}  &:&  (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧ \\ 
eval unite₊ (inj₁ ()) \\
eval unite₊ (inj₂ v) &=& v  \\ 
eval uniti₊ v &=& inj₂ v  \\ 
eval swap₊ (inj₁ v) &=& inj₂ v  \\ 
eval swap₊ (inj₂ v) &=& inj₁ v  \\ 
eval assocl₊ (inj₁ v) &=& inj₁ (inj₁ v)  \\ 
eval assocl₊ (inj₂ (inj₁ v)) &=& inj₁ (inj₂ v)  \\ 
eval assocl₊ (inj₂ (inj₂ v)) &=& inj₂ v  \\ 
eval assocr₊ (inj₁ (inj₁ v)) &=& inj₁ v  \\ 
eval assocr₊ (inj₁ (inj₂ v)) &=& inj₂ (inj₁ v)  \\ 
eval assocr₊ (inj₂ v) &=& inj₂ (inj₂ v)  \\ 
eval unite⋆ (tt , v) &=& v  \\ 
eval uniti⋆ v &=& (tt , v)  \\ 
eval swap⋆ (v₁ , v₂) &=& (v₂ , v₁)  \\ 
eval assocl⋆ (v₁ , (v₂ , v₃)) &=& ((v₁ , v₂) , v₃)  \\ 
eval assocr⋆ ((v₁ , v₂) , v₃) &=& (v₁ , (v₂ , v₃))  \\ 
eval absorbr (() , _)  \\ 
eval absorbl (_ , ())  \\ 
eval factorzl ()  \\ 
eval factorzr ()   \\ 
eval dist (inj₁ v₁ , v₃) &=& inj₁ (v₁ , v₃)   \\ 
eval dist (inj₂ v₂ , v₃) &=& inj₂ (v₂ , v₃)   \\ 
eval factor (inj₁ (v₁ , v₃)) &=& (inj₁ v₁ , v₃)   \\ 
eval factor (inj₂ (v₂ , v₃)) &=& (inj₂ v₂ , v₃)   \\ 
eval id⟷ v &=& v   \\ 
eval (c₁ ◎ c₂) v &=& eval c₂ (eval c₁ v)   \\ 
eval (c₁ ⊕ c₂) (inj₁ v) &=& inj₁ (eval c₁ v)   \\ 
eval (c₁ ⊕ c₂) (inj₂ v) &=& inj₂ (eval c₂ v)   \\ 
eval (c₁ ⊗ c₂) (v₁ , v₂) &=& (eval c₁ v₁ , eval c₂ v₂)
\end{array}\]

also say that every combinator $⟷$ maps to $≃$

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
\label{sec:categorification}

The problem of finding a sound and complete set of rules for reasoning
about equivalences is solved by appealing to various
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

Thus what we seek is a structure ``like'' a commutative semiring,
but where the elements of the carrier, equivalences, are typed.
What we seek then is a way to define two monoidal structures
atop our category of types, which respects the commutative
semiring structure of the types.  Because the details matter,
we now turn to monoidal categories.

\begin{figure*}
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
%The informal idea was already silently used in the examples in
%Sec.~\ref{sec:circuits} in which the types were named \AgdaFunction{x}
%and \AgdaFunction{y} during the derivation to distinguish operations
%that would otherwise be ambiguous if all the types were instantiated
%with \AgdaInductiveConstructor{ONE}.

From a different perspective, \citet{math/9802029} explain the source
of these coherence laws as arising from homotopy theory. In this
theory, laws are only imposed up to homotopy, with these homotopies
satisfying certain laws, up again only up to homotopy, with these
higher homotopies satisfying their own higher coherence laws, and so
on. Remarkably, they report, among other results, that the pentagon
identity of Fig.~\ref{fig:mon} arises when studying the algebraic
structure possessed by a space that is homotopy equivalent to a loop
space and that the hexagon identity arises in the context of spaces
homotopy equivalent to double loop spaces.

In our context, we will build monoidal categories where the objects
are finite types and the morphisms are equivalences represented
as $\Pi$-combinators.  As we have mentioned multiple times,
there are two different equivalences between $A+A$ and itself;
the coherence laws should not equate these two morphisms and
they do not. 
%We might also hope that the two versions of boolean
%negation in Sec.~\ref{sec:circuits} and Sec.~\ref{sec:rewriting} could
%be identified using the coherence conditions of monoidal
%categories. This is not the case but will be once we capture the full
%structure of commutative semirings categorically. 

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
equivalence, the entire setting is that of weak categories 
(aka bicategories).

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
way~\citep{Beke2011728}, it is also known that in the presence of
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

Of course, the main structure of study, is indeed a
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

-- \begin{code}
-- distl-swap₊-lemma : {A B C : Set} → (x : (A × (B ⊎ C))) →
--   TE.distl (map× F.id TE.swap₊ x) P.≡
--   (TE.swap₊ (distl x))
-- distl-swap₊-lemma (x , inj₁ y) = P.refl
-- distl-swap₊-lemma (x , inj₂ y) = P.refl
-- \end{code}

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
where \AgdaInductiveConstructor{eq} is the constructor for $\equiv$.
\end{proof}

More directly relevant to our purposes, is the next theorem which
applies to reversible circuits (represented as $\Pi$-combinators).

\begin{theorem}
The universe $U$ and $\Pi$-combinators is a symmetric rig
groupoid.
\end{theorem}
\begin{proof}
  The objects of the category are the syntax of finite types,
  and the morphisms are
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

\begin{comment}
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
\end{comment}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Revised $\Pi$ and its Optimizer}
\label{sec:revised}

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

\smallskip 

\AgdaHide{
\begin{code}
-- postulate
\end{code}
}

\begin{code}
--  c₁ : {B C : U} →  B ⟷ C
--  c₂ : {A D : U} →  A ⟷ D
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
\section{Limitations}
\label{sec:lim}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}
\label{sec:conc}
%\label{sec:8}

The traditional Curry-Howard correspondence is based on
``mere logic''\footnote{to use the HoTT terminology}.  That is, it
is based around \emph{proof inhabitation}: two types, like two
propositions, are regarded as ``the same'' when one is inhabited
if and only if the other is.  In that sense, the propositions
$A$ and $A \wedge A$, are indeed the same, as are the type
$T$ and $T \times T$.  This is all centered around proof
irrelevant mathematics.

What we have shown is that if we shift to proof relevant
mathematics, computationally relevant equivalences,
explicit homotopies, and algebra, something quite new emerges:
an actual isomorphism between proof terms and reversible
computations.  Furthermore, what algebraic structure to use
is not mysterious: it is exactly the algebraic structure of
the semantics.  In the case of finite types (with sums and
products), this turns out to be commutative semirings.

But the Curry-Howard correspondence promises more: that 
proof transformations correspond to program transformations.
However, in a proof irrelevant setting, this is rather awkward;
similarly, in a extensional setting, program equivalence is a
rather coarse concept.

But, in our setting, both of these issues disappear.  The key to
proceed was to realize that there exists combinators which
make equivalences\footnote{and permutations, but
I don't know if we can bring that in} look like a semiring,
but do not actually have a semiring structure.  The next 
insight is to ``remember'' that a monoidal category is
really a model of a \emph{typed monoid}; in a way, a 
monoidal category is a \emph{categorified} monoid.  So
what we needed was a categorified version of commutative
semirings.  Luckily, this had already been done, in the form
of Rig categories.  Modifying this to have a weaker notion
of equivalence and having all morphisms invertible was
quite straightforward.

Again, being proof relevant mattered: it quickly became 
apparent that the \emph{coherence laws} involved in
weak Rig Groupoids were \emph{exactly} the program
equivalences that were needed.  So rather than fumbling 
around finding various equivalences and hoping to 
stumble on enough of them to be complete, a systematic
design emerged: given a 1-algebra of types parametrized
by an equivalence $\simeq$, one should seek a 
$2$-algebra (aka typed algebra, aka categorification
of the given $1$-algebra) that corresponds to it.
The coherence laws then emerge as a complete set of
program transformations.  This, of course, clearly
points the way to further generalizations.

\begin{comment}
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
introduce \emph{fractional types}. 
\end{comment}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% \clearpage
\bibliographystyle{abbrvnat}
%\softraggedright
\bibliography{cites}

\appendix

\section{Code Roadmap}

For those who wish to delve into the code, we give a quick roadmap here,
with links between the results in our paper and where the formalization
can be found.  We put module names in \texttt{typewriter} font below.

Equivalences are defined in \texttt{Equiv}.  This is used in
\texttt{TypeEquiv} to define equivalences between types; these are 
assembled to show that \AgdaPrimitiveType{Set} has the structure of
a $\simeq$-semiring, \AgdaFunction{typesCSR}, which is our
Theorem~\ref{thm:typesCSR}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}
