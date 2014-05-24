\documentclass[authoryear,preprint]{sigplanconf}
\usepackage{agda}
\usepackage{bbm}
\usepackage{amsmath}
\usepackage{textgreek}
\usepackage{listings} 
\usepackage{stmaryrd}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{xcolor}
\usepackage{courier}
\usepackage{url}
\usepackage{thmtools}
\usepackage{bbold}
\usepackage{tikz}
\usepackage{proof}
\usepackage{graphicx}

\newcommand{\refl}[1]{\textsf{refl}_{#1}}
\newcommand{\seg}[1]{\textsf{seg}_{#1}}
\newcommand{\bdim}[1]{\textsf{dim}(#1)}
\newcommand{\Rule}[4]{
\makebox{{\rm #1}
$\displaystyle
\frac{\begin{array}{l}#2\\\end{array}}
{\begin{array}{l}#3\\\end{array}}$
 #4}}
\newcommand{\proves}{\vdash}
\newcommand{\symc}[1]{\mathit{sym}~#1}
\newcommand{\jdg}[3]{#2 \proves_{#1} #3}
\newcommand{\adjoint}[1]{#1^{\dagger}}
\newcommand{\iso}{\leftrightarrow}
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
\newcommand{\idc}{\mathit{id}}
\newcommand{\plus}{\raisebox{.4\height}{\scalebox{.6}{+}}}
\newcommand{\minus}{\raisebox{.4\height}{\scalebox{.8}{-}}}
\newcommand{\mm}{\texttt{-}}
\newcommand{\pp}{\texttt{+}}
\newcommand{\negp}[1]{\textit{neg}(#1)}
\newcommand{\inl}[1]{\textsf{inl}~#1}
\newcommand{\inr}[1]{\textsf{inr}~#1}
\newcommand{\lolli}{\multimap} 
\newcommand{\cubt}{\mathbb{T}}
\newcommand{\den}[1]{\llbracket #1 \rrbracket}
\newcommand{\nodet}[2]{\fcolorbox{black}{white}{$#1$}\fcolorbox{black}{gray!20}{$#2$}}
\newcommand{\hast}{:\mkern -2.5mu:\;}

\begin{document}
\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\newcommand{\alt}{~|~}
\lstnewenvironment{haskellcode}{\lstset{basicstyle={\sffamily\footnotesize}}}{}

\lstset{frame=none,
         language=Haskell,
         basicstyle=\sffamily, 
         numberstyle=\tiny,
         numbersep=5pt,
         tabsize=2,    
         extendedchars=true,
         breaklines=true,   
         breakautoindent=true,
         keywordstyle=\color{black},
         captionpos=b,
         stringstyle=\color{black}\ttfamily,
         showspaces=false,  
         showtabs=false,    
         framexleftmargin=2em,
         framexbottommargin=1ex,
         showstringspaces=false
         basicstyle=\sffamily,
         columns=[l]flexible,
         flexiblecolumns=true,
         aboveskip=\medskipamount,
         belowskip=\medskipamount,
         lineskip=-1pt,
         xleftmargin=1em,
         escapeinside={/+}{+/},
         keywords=[1]{Monad,Just,Nothing,type,data,right,left,id,where,do,
                     if,then,else,let,in},
         literate=
           {+}{{$\;+\;$}}1 
           {/}{{$/$}}1 
           {*}{{$\;*\;$}}1
           {=}{{$=\ $}}1 
           {/=}{{$\not=$}}1
           {[]}{$[\;]$}2
           {<}{{$<$}}1 
           {>}{{$>$}}1 
           {++}{{$+\!\!\!+\;$}}1 
           {::}{{$:\mkern -2.5mu:\;$}}1
           {&&}{{$\&\!\!\!\&$}}2
           {:=:}{{$:\mkern -2mu=\mkern -2mu:\;$}}3
           {:+:}{{$:\mkern -5mu+\mkern -5mu:\;$}}3
           {:-:}{{$:\mkern -5mu-\mkern -5mu:\;$}}3
           {:*:}{{$:\mkern -5mu*\mkern -5mu:\;$}}3
           {$}{{\texttt{\$}\hspace{0.5em}}}1
           {`}{$^\backprime$}1
           {==}{{$=\!=\;$}}2
           {===}{{$\equiv\;$}}2
           {->}{{$\rightarrow\;$}}2 
           {>=}{{$\geq$}}2 
           {<=}{{$\leq$}}2 
           {>=0}{{$\geq_\zerog\;$}}2 
           {<=0}{{$\leq_\zerog\;$}}2 
           {==0}{{$=_\zerog\;$}}2 
           {>0}{{$>_\zerog\;$}}2 
           {<0}{{$<_\zerog\;$}}2 
           {<-}{{$\leftarrow$}}2
           {=>}{{$\Rightarrow\;$}}2
           {<<}{{$\ll$}}2 
           {>>}{{$\gg\;$}}2
           {>>>}{{$\ggg\;$}}3 
           {<<<}{{$\lll\;$}}3
           {>>=}{{$\gg\mkern -2.5mu=\;$}}3
           {=<<}{{$=\mkern -2.5mu\ll\;$}}3
           {<|}{$\lhd\;$}2
           {<||}{$\unlhd\;$}2
           {\ ||\ }{$\|$}1
           {\\}{$\lambda$}1
           {:>}{{$\rhd$}}2
           {||>}{{$\unrhd$}}2
           {_}{{$\_$}}1
           {_B}{{$_b$}}2
           {forall}{{$\forall$}}1
}

\lstset{postbreak=\raisebox{0ex}[0ex][0ex]
        {\ensuremath{\hookrightarrow}}}
\lstset{breaklines=true, breakatwhitespace=true}
\lstset{numbers=none, numbersep=5pt, stepnumber=2, numberstyle=\scriptsize}
\lstset{rangeprefix=/*!\ , rangesuffix=\ !*\/, includerangemarker=false}

%% double-blind reviewing...
\title{Negative Types}
\authorinfo{}{}{}
\maketitle

\begin{abstract}
\ldots
\end{abstract}

\AgdaHide{
\begin{code}
module ring where
open import Level
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Function 
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

The \textbf{Int} construction or the $\mathcal{G}$ construction are neat. As
Neel K. explains~\cite{neelblog}, given first-order types and feedback you
get higher-order functions. But if you do the construction on the additive
structure, you lose the multiplicative structure. It turns out that this is
related to a deep open problem in algebraic topology and homotopy theory that
was recently solved~\cite{ringcompletion}. We ``translate'' that solution to
a computational type-theoretic world. This has evident connections to
homotopy (type) theory that remain to be investigated in more depth.

Make sure we introduce the abbreviation HoTT in the
introduction~\cite{hottbook}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The \textbf{Int} Construction} 

We may or may not want to explain the construction using Haskell. In case we
do, the most relevant code is below. The key insight it to enrich types to
consist of pairs that intuitively represent $(t_1 - t_2)$ where the values of
type $t_1$ flow in the ``normal'' direction (from producers to consumers) and
the values of type $t_2$ flow backwards (representing a \emph{demand} for a
value). This is expressive enough to represent functions which are viewed as
expressions that convert a demand for an argument to the production of a
result. The problem is that the obvious definition of multiplication is not
functorial. This turns out to be intimately related to a well-known open
problem in algebraic topology that goes back at least thirty
years~\cite{thomason}.

\begin{haskellcode}
class GT p where
  type Pos p      :: *  -- a type has a positive component
  type Neg p      :: *  -- and a negative component
  type ZeroG      :: *  -- we want all the usual type 
  type OneG       :: *  -- constructors including 0, 1,
  type PlusG p q  :: *  -- sums, and 
  type ProdG p q  :: *  -- products
  type DualG p    :: *  -- as a bonus we get negation and
  type LolliG p q :: *  -- linear functions

-- A definition of the composite types with a 
-- positive and negative components

data a :- b = a :- b

instance GT (ap :- am) where
  type Pos (ap :- am) = ap
  type Neg (ap :- am) = am
  type ZeroG = Void :- Void
  type OneG = () :- Void
  type PlusG  (ap :- am) (bp :- bm) = 
    (Either ap bp) :- (Either am bm)
  type TimesG (ap :- am) (bp :- bm) = 
    -- the "obvious" but broken multiplication
    (Either (ap,bp) (am,bm)) :- (Either (am,bp) (ap,bm))
  type DualG  (ap :- am) = am :- ap
  type LolliG (ap :- am) (bp :- bm) = 
    (Either am bp) :- (Either ap bm)

-- Functions between composite types with positive 
-- and negative components; implemented using 
-- resumptions (i.e., feedback)
newtype GM a b = 
  GM { rg :: R  (Either (Pos a) (Neg b)) 
                (Either (Neg a) (Pos b)) } 

data R i o = R { r  :: i -> (o, R i o), 
                 rr :: o -> (i, R o i) }

plusG :: (a ~ (ap :- am), b ~ (bp :- bm), 
         c ~ (cp :- cm), d ~ (dp :- dm)) =>
  GM a b -> GM c d -> GM (PlusG a c) (PlusG b d)
plusG (GM f) (GM g) = -- short definition omitted

timesG :: (a ~ (ap :- am), b ~ (bp :- bm), 
          c ~ (cp :- cm), d ~ (dp :- dm)) =>
  GM a b -> GM c d -> GM (TimesG a c) (TimesG b d)
timesG = -- IMPOSSIBLE

\end{haskellcode}

The main ingredient of the recent solution to this problem can intuitively
explained as follows. We regard conventional types as $0$-dimensional
cubes. By adding composite types consisting of two types, the \textbf{Int}
construction effectively creates 1-dimensional cubes (i.e., lines). The key
to the general solution, and the approach we adopt here, is to generalize
types to $n$-dimensional cubes.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Cubes}
\label{cubes}

We first define the syntax and then present a simple semantic model of types
which is then refined.

\begin{figure*}
\[\begin{array}{c}
\nodet{S_1}{S_2}
\quad\otimes\quad
\nodet{(\nodet{S_3}{S_4})}{(\nodet{S_5}{S_6})} \quad= \\
\\
\nodet{(\nodet{{(\nodet{S_1 \times S_3}{S_1 \times S_4})}}
              {{(\nodet{S_1 \times S_5}{S_1 \times S_6})}})}
      {(\nodet{{(\nodet{S_2 \times S_3}{S_2 \times S_4})}}
              {{(\nodet{S_2 \times S_5}{S_2 \times S_6})}})}
\end{array}\]
\\
\\
\begin{center}
\begin{tikzpicture}
\node[above] at (0,0) {\pp};
\node[left] at (0,0) {$S_1$};
\draw[fill] (0,0) circle [radius=0.05];
\node[above] at (0.6,0) {\mm};
\node[right] at (0.6,0) {$S_2$};
\draw[fill] (0.6,0) circle [radius=0.05];
\draw[-,dotted] (0,0) -- (0.6,0);
\node at (1.6,0) {$\otimes$}; 

%%
\node[left] at (2.5,-0.5) {\pp\pp};
\node[below] at (2.5,-0.5) {$S_3$};
\draw[fill] (2.5,-0.5) circle [radius=0.05];
\node[right] at (3.5,-0.5) {\pp\mm};
\node[below] at (3.5,-0.5) {$S_4$};
\draw[fill] (3.5,-0.5) circle [radius=0.05];
\draw[-,dotted] (2.5,-0.5) -- (3.5,-0.5);
\draw[-,dotted] (2.5,-0.5) -- (2.5,0.5);
\node[left] at (2.5,0.5) {\mm\pp};
\node[above] at (2.5,0.5) {$S_5$};
\draw[fill] (2.5,0.5) circle [radius=0.05];
\node[right] at (3.5,0.5) {\mm\mm};
\node[above] at (3.5,0.5) {$S_6$};
\draw[fill] (3.5,0.5) circle [radius=0.05];
\draw[-,dotted] (2.5,0.5) -- (3.5,0.5);
\draw[-,dotted] (3.5,-0.5) -- (3.5,0.5);
%% 
\node at (5,0) {$=$};
%% 
\node[left] at (7.5,0.75) {$(S_2 \times S_3)$\,\mm\pp\pp};
\draw[fill] (7.5,0.75) circle [radius=0.05];
\node[right] at (9.5,0.75) {$(S_2 \times S_4)$\,\mm\pp\mm};
\draw[fill] (9.5,0.75) circle [radius=0.05];
\node[above right] at (10.2,1.2) {$(S_2 \times S_6)$\,\mm\mm\mm};
\draw[fill] (10.2,1.2) circle [radius=0.05];
\node[above left] at (8.2,1.2) {$(S_2 \times S_5)$\,\mm\mm\pp};
\draw[fill] (8.2,1.2) circle [radius=0.05];
%%
\node[left] at (7.5,-0.75) {$(S_1 \times S_3)$\,\pp\pp\pp};
\draw[fill] (7.5,-0.75) circle [radius=0.05];
\node[right] at (9.5,-0.75) {$(S_1 \times S_4)$\,\pp\pp\mm};
\draw[fill] (9.5,-0.75) circle [radius=0.05];
\node[above right] at (10.2,-0.3) {$(S_1 \times S_6)$\,\pp\mm\mm};
\draw[fill] (10.2,-0.3) circle [radius=0.05];
\node[left] at (8.2,-0.3) {$(S_1 \times S_5)$\,\pp\mm\pp};
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
\caption{\label{mult}Example of multiplication of two cubical types.}
\end{figure*}

%%%%%%%%%%%%%%%%%%%%
\subsection{Negative and Cubical Types}

Our types $\tau$ include the empty type 0, the unit type 1, conventional sum
and product types, as well as \emph{negative} types:
\[\begin{array}{rcl}
\tau &::=& 0 \alt 1 \alt \tau_1 + \tau_2 \alt \tau_1 * \tau_2 \alt - \tau
\end{array}\]
We use $\tau_1 - \tau_2$ to abbreviate $\tau_1 + (- \tau_2)$ and more
interestingly $\tau_1 \lolli \tau_2$ to abbreviate $(- \tau_1) + \tau_2$.
The \emph{dimension} of a type is defined as follows:
\[\begin{array}{rcl}
\bdim{\cdot} &\hast& \tau \rightarrow \mathbb{N} \\
\bdim{0} &=& 0 \\
\bdim{1} &=& 0 \\
\bdim{\tau_1 + \tau_2} &=& \max(\bdim{\tau_1},\bdim{\tau_2}) \\
\bdim{\tau_1 * \tau_2} &=& \bdim{\tau_1} + \bdim{\tau_2} \\
\bdim{- \tau} &=& \max(1,\bdim{\tau})
\end{array}\]
The base types have dimension 0. If negative types are not used, all
dimensions remain at 0. If negative types are used but no products of
negative types appear anywhere, the dimension is raised to 1. This is the
situation with the \textbf{Int} or $\mathcal{G}$ construction. Once negative
and product types are freely used, the dimension can increase without bounds.

This point is made precise in the following tentative denotation of types (to
be refined in the next section) which maps a type of dimension $n$ to an
$n$-dimensional cube. We represent such a cube syntactically as a binary tree
of maximum depth~$n$ with nodes of the form $\nodet{\cubt_1}{\cubt_2}$. In
such a node, $\cubt_1$ is the positive subspace and $\cubt_2$ (shaded in
gray) is the negative subspace along the first dimension. Each of these
subspaces is itself a cube of a lower dimension. The $0$-dimensional cubes
are plain sets representing the denotation of conventional first-order
types. We use $S$ to denote the denotations of these plain types. A
1-dimensional cube, $\nodet{S_1}{S_2}$, intuitively corresponds to the
difference $\tau_1 - \tau_2$ of the two types whose denotations are $S_1$ and
$S_2$ respectively. The type can be visualized as a ``line'' with polarized
endpoints connecting the two points~$S_1$ and $S_2$. A full 2-dimensional
cube, $\nodet{(\nodet{S_1}{S_2})}{(\nodet{S_3}{S_4})}$, intuitively
corresponds to the iterated difference of the appropriate types
$(\tau_1-\tau_2)-(\tau_3-\tau_4)$ where the successive ``colors'' from the
outermost box encode the sign. The type can be visualized as a ``square''
with polarized corners connecting the two lines corresponding to
$(\tau_1-\tau_2)$ and $(\tau_3-\tau_4)$. (See Fig.~\ref{mult} which is
further explained after we discuss multiplication below.)

Formally, the denotation of types discussed so far is as follows:
\[\begin{array}{rcl}
\den{0} &=& \emptyset \\
\den{1} &=& \{ \star \} \\
\den{\tau_1 + \tau_2} &=& \den{\tau_1} \oplus \den{\tau_2} \\
\den{\tau_1 * \tau_2} &=& \den{\tau_1} \otimes \den{\tau_2} \\
\den{- \tau} &=& \ominus \den{\tau} \\
\\
\noalign{\mbox{where:}\hfill}
\\
S_1 \oplus S_2 &=& S_1 \uplus S_2 \\
S \oplus (\nodet{\cubt_1}{\cubt_2}) &=& \nodet{S \oplus \cubt_1}{\cubt_2} \\
(\nodet{\cubt_1}{\cubt_2}) \oplus S &=& \nodet{\cubt_1 \oplus S}{\cubt_2} \\
(\nodet{\cubt_1}{\cubt_2}) \oplus (\nodet{\cubt_3}{\cubt_4}) &=& 
  \nodet{\cubt_1 \oplus \cubt_3}{\cubt_2 \oplus \cubt_4} \\
\\
S_1 \otimes S_2 &=& S_1 \times S_2 \\
S \otimes (\nodet{\cubt_1}{\cubt_2}) &=& 
  \nodet{S \otimes \cubt_1}{S \otimes \cubt_2} \\
(\nodet{\cubt_1}{\cubt_2}) \otimes \cubt &=& 
  \nodet{\cubt_1 \otimes \cubt}{\cubt_2 \otimes \cubt} \\
\\
\ominus~S &=& \nodet{\phantom{S}}{S} \\
\ominus~\nodet{\cubt_1}{\cubt_2} &=& \nodet{\ominus~\cubt_2}{\ominus~\cubt_1} 
\end{array}\]
The type 0 maps to the empty set. The type 1 maps to a singleton set. The sum
of $0$-dimensional types is the disjoint union as usual. For cubes of higher
dimensions, the subspaces are recursively added. Note that the sum of
1-dimensional types reduces to the sum used in the \textbf{Int} construction.
The definition of negation is natural: it recursively swaps the positive and
negative subspaces. The product of 0-dimensional types is the cartesian
product of sets. For cubes of higher-dimensions $n$ and $m$, the result is of
dimension $(n+m)$. The example in Fig.~\ref{mult} illustrates the idea using
the product of 1-dimensional cube (i.e., a line) with a 2-dimensional cube
(i.e., a square). The result is a 3-dimensional cube as illustrated.

%%%%%%%%%%%%%%%%%%%%
\subsection{Type Isomorphisms: Paths to the Rescue}

Our proposed semantics of types identifies several structurally different
types such as $(1+(1+1))$ and $((1+1)+1)$. In some sense, this is innocent as
the types are isomorphic. However, in the operational semantics discussed in
Sec.~\ref{opsem}, we make the computational content of such type isomorphisms
explicit. Some other isomorphic types like $(\tau_1*\tau_2)$ and
$(\tau_2*\tau_1)$ map to different cubes and are \emph{not} identified:
explicit isomorphisms are needed to mediate between them. We therefore need
to enrich our model of types with isomorphisms connecting types we deem
equivalent. So far, our types are modeled as cubes which are really sets
indexed by polarities. An isomorphism between $(\tau_1*\tau_2)$ and
$(\tau_2*\tau_1)$ requires nothing more than a pair of set-theoretic
functions between the spaces, and that compose to the identity. What is much
more interesting are the isomorphisms involving the empty type~0. In
particular, if negative types are to be interpreted as their name suggests,
we must have an isomorphism between $(t-t)$ and the empty type
0. Semantically the former denotes the ``line'' $\nodet{\cubt}{\cubt}$ and
the latter denotes the empty set. Their denotations are different and there
is no way, in the world of plain sets, to express the fact that these two
spaces should be identified. What is needed is the ability to \emph{contract}
the \emph{path} between the endpoints of the line to the trivial path on the
empty type. This is, of course, where the ideas of homotopy (type) theory
enter the development.

Consider the situation above in which we want to identify the spaces
corresponding to the types $(1-1)$ and the empty type:
\begin{center}
\begin{tikzpicture}
\node[above] at (0,0) {\pp};
\node[left] at (-0.2,0) {$1$};
\draw[fill] (0,0) circle [radius=0.05];
\node[above] at (2.6,0) {\mm};
\node[right] at (2.8,0) {$1$};
\draw[fill] (2.6,0) circle [radius=0.05];
\draw[->,red] (0.1,0) -- (2.5,0);
\draw[->,red] (-0.1,-0.1) arc (135:405:0.2);
\node[below,red] at (0,-0.4) {$\refl{1}$};
\draw[->,red] (2.5,-0.1) arc (135:405:0.2);
\node[below,red] at (2.6,-0.4) {$\refl{1}$};
\node[above] at (1.3,0) {$\seg{1}$};
\node[right] at (1.3,-0.5) {$q$};
%%
\node[below] at (1.3,-1.5) {$\emptyset$};
\draw[fill] (1.3,-1.5) circle [radius=0.05];
\draw[->,red] (1.4,-1.4) arc (-45:225:0.2);
\node[right,red] at (1.5,-1.3) {$\refl{0}$};
%% 
\draw[->,double,blue] (1.3,-0.1) -- (1.3,-1);
\end{tikzpicture}
\end{center}
The top of the figure is the 1-dimensional cube representing the type $(1-1)$
as before except that we now add a path $\seg{1}$ to connect the two
endpoints. This path identifies the two occurrences of 1. (Note that
previously, the dotted lines in the figures were a visualization aid and were
\emph{not} meant to represent paths.) We also make explicit the trivial
identity paths from every space to itself.  The bottom of the figure is the
0-dimensional cube representing the empty type. To express the equivalence of
$(1-1)$ and 0, we add a 2-path $q$, i.e. a path between paths, that connects
the path $\seg{1}$ to the trivial path $\refl{0}$. That effectively makes the
two points ``disappear.''  Surprisingly, that is everything that we need. The
extension to higher dimensions just ``works'' because paths in HoTT have a
rich structure. We explain the details after we include a short introduction
of the necessary concepts from HoTT.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Condensend Background on HoTT}

Informally, and as a first approximation, one may think of HoTT as
mathematics, type theory, or computation but with all equalities replaced by
isomorphisms, i.e., with equalities given computational content. We explain
some of the basic ideas below.

%%%%%%%%%%%%%%%%%
\subsection{Types as Spaces}

One starts with Martin-L\"of type theory, interprets the types as topological
spaces or weak $\infty$-groupoids, and interprets identities between elements
of a type as \emph{paths}.  In more detail, one interprets the witnesses of
the identity $x \equiv y$ as paths from $x$ to $y$. If $x$ and $y$ are
themselves paths, then witnesses of the identity $x \equiv y$ become paths
between paths, or homotopies in the topological language. In Agda notation,
we can formally express this as follows:

\medskip
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
\medskip

\noindent It is important to note that the notion of proposition
equality~$\equiv$ relates any two terms that are \emph{definitionally equal}
as shown in example \AgdaFunction{i1} above. In general, there may be
\emph{many} proofs (i.e., paths) showing that two particular values are
identical and that proofs are not necessarily identical. This gives rise to a
structure of great combinatorial complexity.

We are used to think of types as sets of values. So we think of the type
\AgdaPrimitiveType{Bool} as the figure on the left but in HoTT we should
instead think about it as the figure on the right:
\[
\begin{tikzpicture}[scale=0.7]
  \draw (0,0) ellipse (2cm and 1cm);
  \draw[fill] (-1,0) circle (0.025);
  \node[below] at (-1,0) {false};
  \draw[fill] (1,0) circle (0.025);
  \node[below] at (1,0) {true};
\end{tikzpicture}
\qquad\qquad
\begin{tikzpicture}[scale=0.7]
  \draw (0,0) ellipse (2cm and 1cm);
  \draw[fill] (-1,0) circle (0.025);
  \draw[->,thick,cyan] (-1,0) arc (0:320:0.2);
  \node[above right] at (-1,0) {false};
  \draw[fill] (1,-0.2) circle (0.025);
  \draw[->,thick,cyan] (1,-0.2) arc (0:320:0.2);
  \node[above right] at (1,-0.2) {true};
\end{tikzpicture}
\]
In this particular case, it makes no difference, but in general we may have a
much more complicated path structure. 


We cannot generate non-trivial groupoids starting from the usual type
constructions. We need \emph{higher-order inductive types} for that purpose.
The classical example is the \emph{circle} that is a space consisting of a
point \AgdaFunction{base} and a path \AgdaFunction{loop} from
\AgdaFunction{base} to itself. As stated, this does not amount to
much. However, because path carry additional structures (explained below),
that space has the following non-trivial structure:

\begin{center}
\begin{tikzpicture}[scale=0.78]
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

%%%%%%%%%%%%%%
\subsection{Functions}

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
\begin{tikzpicture}[scale=0.6]
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
\begin{tikzpicture}[scale=0.82]
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
\item We know that paths in $A \times B$ are pairs of paths, i.e.,
we can prove that $(a_1,b_1) \equiv (a_2,b_2)$ in $A \times B$ iff $a_1 \equiv
a_2$ in $A$ and $b_1 \equiv b_2$ in $B$.
\item We know that paths in $A_1 \uplus A_2$ are tagged, i.e., 
we can prove that $\mathit{inj}_i~x \equiv \mathit{inj}_j~y$ 
in $A_1 \uplus A_2$ iff $i=j$ and $x \equiv y$ in $A_i$.
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Homotopy Types and Univalence}

We describe the construction of our universe of types. 

%%%%%%%%%%%%%%%%%%%%
\subsection{Homotopy Types}

Our starting point is the construction in Sec.~\ref{cubes} which we summarize
again. We start with all finite sets built from the empty set, a singleton
set, disjoint unions, and cartesian products. All these sets are thought of
being indexed by the empty sequence of polarities $\epsilon$. We then
constructs new spaces that consist of pairs of finite sets $\nodet{S_1}{S_2}$
indexed by positive and negative polarities. These are the 1-dimensional
spaces. We iterate this construction to the limit to get $n$-dimensional
cubes for all natural numbers $n$.

At this point, we switch from viewing the universe of types as an
unstructured collection of spaces to a viewing it as a \emph{groupoid} with
explicit \emph{paths} connecting spaces that we want to consider as
equivalent. We itemize the paths we add next:
\begin{itemize}
\item The first step is to identify each space with itself by adding trivial
  identity paths $\refl{\cubt}$ for each space $\cubt$;
\item Then we add paths $\seg{\cubt}$ that connect all occurrences of the
  same type $\cubt$ in various positions in $n$-dimensional cubes. For
  example, the 1-dimensional space corresponding to $(1-1)$ would now include
  a path connecting the two endpoints as illustrated at the end of 
  Sec.~\ref{cubes}.
\item We then add paths for witnessing the usual type isomorphisms between
  finite types such as associativity and commutativity of sums and
  products. The complete list of these isomorphisms is given in the next
  section.
\item Finally, we add \emph{2-paths} between $\refl{0}$ and any path
  $\seg{\cubt}$ whose endpoints are of opposite polarities, i.e., of
  polarities $s$ and $\negp{s}$ where:
  \[\begin{array}{rcl}
  \negp{\epsilon} &=& \epsilon \\
  \negp{+s} &=& -\negp{s} \\
  \negp{-s} &=& +\negp{s}
  \end{array}\]
\item The groupoid structure forces other paths to be added as described in
  the previous section. 
\end{itemize}

Now the structure of path spaces is complicated in general. Let's look at
some examples.

%%%%%%%%%%%%%%%%%%%%
\subsection{Univalence} 

The heart of HoTT is the \emph{univalence axiom}, which informally states
that isomorphic structures can be identified. One of the major open problems
in HoTT is a computational interpretation of this axiom. We propose that, at
least for the special case of finite types, reversible computation \emph{is}
the computational interpretation of univalence. Specifically, in the context
of finite types, univalence specializes to a relationship between type
isomorphisms on the side of syntactic identities and permutations in the
symmetric group on the side of semantic equivalences. 

In conventional HoTT:

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

In the conventional setting, this is not executable!

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{A Reversible Language with Cubical Types} 
\label{opsem}

We first define values then combinators that manipulate the values to witness
the type isomorphisms.

%%%%%%%%%%%%%%%%%%
\subsection{Values} 

Now that the type structure is defined, we turn our attention to the notion
of values. Intuitively, a value of the $n$-dimensional type $\tau$ is an
element of one of the sets located in one of the corners of the
$n$-dimensional cube denoted by $\tau$ (taking into that there are non-trivial
paths relating these sets to other sets, etc.) Thus to specify a value, we must
first specify one of the corners of the cube (or equivalently one of the
leaves in the binary tree representation) which can easily be done using a
sequence $s$ of $+$ and $-$ polarities indicating how to navigate the cube in
each successive dimension starting from a fixed origin to reach the desired
corner. We write $v^{s}$ for the value $v$ located at corner $s$ of the cube
associated with its type. We use $\epsilon$ for the empty sequence of
polarities and identify $v$ with $v^\epsilon$. Note that the polarities
doesn't completely specify the type since different types like $(1+(1+1))$
and $((1+1)+1)$ are assigned the same denotation. What the path $s$ specifies
is the \emph{polarity} of the value, or its ``orientation'' in the space
denoted by its type. Formally:
\[\begin{array}{c}
\infer{() : 1}{} 
\qquad
\infer[\textit{neg}]{v^{\negp{s}} : - \tau}{v^s : \tau} 
\\
\infer[\textit{left}]{(\inl{v})^{s} : \tau_1 + \tau_2}{v^{s} : \tau_1}
\qquad
\infer[\textit{right}]{(\inr{v})^{s} : \tau_1 + \tau_2}{v^{s} : \tau_2} 
\\
\infer[\textit{prod}]{(v_1,v_2)^{s_1 \cdot s_2} : \tau_1 * \tau_2}
      {v_1^{s_1} : \tau_1 & v_2^{s_2} : \tau_2} 
\end{array}\]
The rules \textit{left} and \textit{right} reflect the fact that sums do not
increase the dimension. Note that when $s$ is $\epsilon$, we get the
conventional values for the 0-dimensional sum type. The rule \textit{prod} is
the most involved one: it increases the dimension by \emph{concatenating} the
two dimensions of its arguments. For example, if we pair $v_1^{\pp}$ and
$v_2^{\mm\pp}$ we get $(v_1,v_2)^{\pp\mm\pp}$. (See Fig.~\ref{mult} for the
illustration.) Note again that if both components are 0-dimensional, the pair
remains 0-dimensional and we recover the usual rule for typing values of
product types. The rule \textit{neg} uses the function below which states
that the negation of a value $v$ is the same value $v$ located at the
``opposite'' corner of the cube.

\begin{table*}[t]
\[\begin{array}{cc}
\begin{array}{rrcll}
\identlp :&  0 + b & \iso & b &: \identrp \\
\swapp :&  b_1 + b_2 & \iso & b_2 + b_1 &: \swapp \\
\assoclp :&  b_1 + (b_2 + b_3) & \iso & (b_1 + b_2) + b_3 &: \assocrp \\
\identlt :&  1 * b & \iso & b &: \identrt \\
\swapt :&  b_1 * b_2 & \iso & b_2 * b_1 &: \swapt \\
\assoclt :&  b_1 * (b_2 * b_3) & \iso & (b_1 * b_2) * b_3 &: \assocrt \\
\distz :&~ 0 * b & \iso & 0 &: \factorz \\
\dist :&~ (b_1 + b_2) * b_3 & \iso & (b_1 * b_3) + (b_2 * b_3)~ &: \factor \\
\eta :&~ 0 & \iso & b + (-b)~ & : \epsilon
\end{array}
& 
\begin{minipage}{0.5\textwidth}
\begin{center} 
\Rule{}
{}
{\jdg{}{}{\idc : b \iso b}}
{}
\qquad\qquad
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
\\ \bigskip
\Rule{}
{\jdg{}{}{c_1 : b_1 \iso b_2} \quad c_2 : b_3 \iso b_4}
{\jdg{}{}{c_1 \otimes c_2 : b_1 * b_3 \iso b_2 * b_4}}
{}
\end{center}
\end{minipage}
\end{array}\]
\caption{Combinators\label{pi-combinators}}
\end{table*}

%%%%%%%%%%%%%%%%%%
\subsection{$\Pi$ Combinators} 

The terms of $\Pi$ witness type isomorphisms of the form $b \iso b$. They
consist of base isomorphisms, as defined in Table~\ref{pi-combinators} and
their composition. Each line of the table introduces a pair of dual
constants\footnote{where $\swapp$ and $\swapt$ are self-dual.} that witness
the type isomorphism in the middle.  These are the base (non-reducible) terms
of the second, principal level of $\Pi$. Note how the above has two readings:
first as a set of typing relations for a set of constants. Second, if these
axioms are seen as universally quantified, orientable statements, they also
induce transformations of the (traditional) values. The (categorical or
homotopical) intuition here is that these axioms have computational content
because they witness isomorphisms rather than merely stating an extensional
equality. The isomorphisms are extended to form a congruence relation by
adding constructors that witness equivalence and compatible closure.

It is important to note that ``values'' and ``isomorphisms'' are completely
separate syntactic categories which do not intermix. The semantics of the
language come when these are made to interact at the ``top level'' via
\emph{application}: 
\[\begin{array}{lrcl}
\textit{top level term}, l &::=& c~v
\end{array}\]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work and Context}

A ton of stuff here. 

Connection to our work on univalence for finite types. We didn't have to rely
on sets for 0-dimensional types. We could have used groupoids again. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{abbrvnat}
\softraggedright
\bibliography{cites}

\end{document}




be careful about that 2-path. Are we 
allowed to do that given that the 
empty type is, well, empty.

identical to a single point. It should 
then follow that a square where one edge 
contracts to a point would itself contract 
to a line, and a 3-dimensional cube 
in which one face contracts to a point 
would itself contract to a square, etc. 

Now consider (a-b)-(c-c). We have a 
path to (a-b)-0 that contracts the
path between c and -c. We want to 
reduce the dimension of that space
and map to (a-b). 

original space

    c ------ c
    |        |  
p1  |        | p2
    |        |  
    a ------ b
       p3

after collapsing the two c's

      0
     /\
    /  \
   a -- b

or because path compose

  a ---- b
    ---- 

where the top path is p1;p2
and the bottom path is p3

I think we should have a 2-path
between them to say that these
paths are equivalent which will 
then collapse the square to a 
line as desired.

There are two values of type
1-1

() 
and 
()^-

epsilon should take one and map
to the other because it can
never produce something of type 0

In general, we have several direction
not just left and right like in the
Int construction. In 3D we have
8 directions: +++, ++-, ..., ---
We have an epsilon that 
takes ++- and flips it to --+
and another that flips
+++ to --- and so on

So we should have 8 interpreters
for 3D one for each direction!!!

The ++- interpreter would 
manipulates values like
(v1,v2,v3) and would apply
the normal combinators to v1, v2, 
and the adjoint to v3 and so on.

To complete the story we need to 
define morphisms. (More on this below.)
Once we have a notion of morphism we 
can check whether X + 0 is the same
as X etc. i.e., we can check all the 
ring equivalences. 

Ok so what are the morphisms between 
these cubical objects? We know what
they are for 1-dimensional cubes: 
they are the pi combinabors. We also
know what they are for the 2-dimensional 
cubes: a maps (A-B) ==> (C-D) 
is a Pi map between A+D <=> C+B. 
How to generalize this? 

Why is there no trace in the ring 
completion paper??? What are 
the morphisms in that paper?

The ring completion paper produces
a simplicial category.

p. 3 talks about the group cancellation
as subcubes along the diagonal... 

We shouldn't focus on denotations. We want
an operational semantics for pi with 
negatives. The same way that Neel turned
the G construction into code that does
something neat; we want to turn that 
ring completion construction into code
that produces h.o. functions without
losing the multiplicative structure.

Show how to embed a square in 2D into
each of the faces of the 3D cube.

1D into 2D:

(a-b) => (a-b)-(0-0)
(a-b) => (a-0)-(b-0)
(a-b) => (0-b)-(0-a)
(a-b) => (0-0)-(b-a)


We only have -
which flips ALL the directions simultaneously.
So from ++-+--+ you can only go to
        --+-++-
What if you wanted to go to
        ++++--+
I think we use the * functor to flip the 
direction we want. 

\subsection{Combinators: Example} 

Consider the following simple function on 0-dimensional sum types:
\[\begin{array}{rcl}
\textsf{swapP} &\hast& (\tau_1 + \tau_2) \rightarrow (\tau_2 + \tau_1) \\
\textsf{swapP} (\inl{v}) &=& inr{v} \\
\textsf{swapP} (\inr{v}) &=& inl{v}
\end{array}\]
Given our setup, this just works $n$-dimensional types. And so do most of the
$\Pi$ combinators for that matter. Only $\eta$ and $\epsilon$ seem to need
thinking. How and why would $1-1$ which is a 1-dimensional line be the same
as the empty type which is a 0-dimensional thing. And how do we generalize
for arbitrary group identities at higher dimensions. We need a mechanism for
cubes with subspaces that ``cancel'' to map to equivalent smaller subcubes.

