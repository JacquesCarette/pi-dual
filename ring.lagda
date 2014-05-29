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
\usepackage{tikz-qtree}


\newcommand{\todo}[1]{\textbf{Todo:} #1}
\newcommand{\ignore}[1]{}

\newcommand{\embed}{\mathit{embed}}
\newcommand{\Pin}[1]{\Pi{\textbf{#1}}}
\newcommand{\taun}[1]{\tau\textbf{#1}}
\newcommand{\pn}[1]{\mathcal{P}\textbf{#1}}
\newcommand{\qn}[1]{\mathcal{Q}\textbf{#1}}
\newcommand{\cpath}[2]{\textit{path}~\{#1\}~\{#2\}}
\newcommand{\evalone}[2]{#1~\triangleright~#2}
\newcommand{\evaloneb}[2]{#1~\triangleleft~#2}
\newcommand{\eqdef}{\stackrel{\triangle}{=}}
\newcommand{\onepath}[2]{#1 \rightarrow #2}
\newcommand{\twopath}[2]{#1 \Rightarrow #2}
\newcommand{\threepath}[2]{#1 \Rrightarrow #2}
\newcommand{\trace}[1]{\mathit{trace}~{#1}}
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
\newcommand{\isoone}{\Leftrightarrow}
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
\newcommand{\cubv}{\mathbb{V}}
\newcommand{\cubc}{\mathbb{C}}
\newcommand{\patht}{\mathbb{P}}
\newcommand{\ztone}{\mathbb{0}}
\newcommand{\otone}{\mathbb{1}}
\newcommand{\ptone}[2]{#1 \boxplus #2}
\newcommand{\ttone}[2]{#1 \boxtimes #2}
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
\title{Polarized Cubical Types}
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

In a computational world in which the laws of physics are embraced and
resources are carefully maintained (e.g., quantum
computing~\cite{NC00,Abramsky:2004:CSQ:1018438.1021878}), programs must be
reversible. Although this is apparently a limiting idea, it turns out that
conventional computation can be viewed as a special case of such
resource-preserving reversible programs. This thesis has been explored for
many years from different
perspectives~\cite{fredkin1982conservative,Toffoli:1980,bennett2010notes,bennett2003notes,Bennett:1973:LRC,Landauer:1961,Landauer}.
We build on the work of James and
Sabry~\citeyearpar{James:2012:IE:2103656.2103667} which expresses this thesis
in a type theoretic computational framework, expressing computation via type
isomorphisms.

Make sure we introduce the abbreviation HoTT in the
introduction~\cite{hottbook}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Computing with Type Isomorphisms}
\label{pi}

\begin{table*}[t]
\[\begin{array}{cc}
\begin{array}{rrcll}
\identlp :&  0 + \tau & \iso & \tau &: \identrp \\
\swapp :&  \tau_1 + \tau_2 & \iso & \tau_2 + \tau_1 &: \swapp \\
\assoclp :&  \tau_1 + (\tau_2 + \tau_3) & \iso & (\tau_1 + \tau_2) + \tau_3 &: \assocrp \\
\identlt :&  1 * \tau & \iso & \tau &: \identrt \\
\swapt :&  \tau_1 * \tau_2 & \iso & \tau_2 * \tau_1 &: \swapt \\
\assoclt :&  \tau_1 * (\tau_2 * \tau_3) & \iso & (\tau_1 * \tau_2) * \tau_3 &: \assocrt \\
\distz :&~ 0 * \tau & \iso & 0 &: \factorz \\
\dist :&~ (\tau_1 + \tau_2) * \tau_3 & \iso & (\tau_1 * \tau_3) + (\tau_2 * \tau_3)~ &: \factor 
\end{array}
& 
\begin{minipage}{0.5\textwidth}
\begin{center} 
\Rule{}
{}
{\jdg{}{}{\idc : \tau \iso \tau}}
{}
\qquad
\Rule{}
{\jdg{}{}{c : \tau_1 \iso \tau_2}}
{\jdg{}{}{\symc{c} : \tau_2 \iso \tau_1}}
{}
\\ \bigskip
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_2 \iso \tau_3}
{\jdg{}{}{c_1 \fatsemi c_2 : \tau_1 \iso \tau_3}}
{}
\\ \bigskip
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \oplus c_2 : \tau_1 + \tau_3 \iso \tau_2 + \tau_4}}
{}
\\ \bigskip
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \otimes c_2 : \tau_1 * \tau_3 \iso \tau_2 * \tau_4}}
{}
\\ \bigskip
\Rule{}
{\jdg{}{}{c : \tau+\tau_1 \iso \tau+\tau_2}}
{\jdg{}{}{\trace{c} : \tau_1 \iso \tau_2}}
{}
\end{center}
\end{minipage}
\end{array}\]
\caption{$\Pi$-combinators~\cite{James:2012:IE:2103656.2103667}\label{pi-combinators}}
\end{table*}

The main syntactic vehicle for the developments in this paper is a simple
language called $\Pi$ whose only computations are isomorphisms between finite
types. The set of types $\tau$ includes the empty type 0, the unit type 1,
and conventional sum and product types. The values of these types are the
conventional ones: \lstinline|()| of type 1, $\inl{v}$ and $\inr{v}$ for
injections into sum types, and $(v_1,v_2)$ for product types:
\[\begin{array}{lrcl}
(\textit{Types}) & 
  \tau &::=& 0 \alt 1 \alt \tau_1 + \tau_2 \alt \tau_1 * \tau_2 \\
(\textit{Values}) & 
  v &::=& () \alt \inl{v} \alt \inr{v} \alt (v_1,v_2) \\
(\textit{Combinator types}) &&& \tau_1 \iso \tau_2 \\
(\textit{Combinators}) & 
  c &::=& [\textit{see Table~\ref{pi-combinators}}]
\end{array}\]
The interesting syntactic category of $\Pi$ is that of \emph{combinators}
which are witnesses for type isomorphisms $\tau_1 \iso \tau_2$. They consist
of base combinators (on the left side of Table~\ref{pi-combinators}) and
compositions (on the right side of the same table). Each line of the table on
the left introduces a pair of dual constants\footnote{where $\swapp$ and
  $\swapt$ are self-dual.} that witness the type isomorphism in the
middle. This set of isomorphisms is known to be
complete~\cite{Fiore:2004,fiore-remarks} and the language is universal for
hardware combinational circuits~\cite{James:2012:IE:2103656.2103667}.  The
$\mathit{trace}$ operator provides a bounded iteration facility which adds no
expressiveness in the current context but will be needed in
Sec.~\ref{intc}.\footnote{If recursive types are added, the trace operator
  provides unbounded iteration and the language becomes Turing
  complete~\cite{James:2012:IE:2103656.2103667,rc2011}. We will not be
  concerned with recursive types in this paper.}

As simple illustrative examples of ``programming'' in $\Pi$, here are three
useful combinators that we define here for future reference:
\[\begin{array}{r@{\,\,\!}cl}
\mathit{assoc}_1 &\hast& 
  \tau_1 + (\tau_2 + \tau_3) \iso (\tau_2 + \tau_1) + \tau_3 \\
\mathit{assoc}_1 &=& \assoclp \fatsemi (\swapp \oplus \idc) \\
\\
\mathit{assoc}_2 &\hast& 
  (\tau_1 + \tau_2) + \tau_3 \iso (\tau_2 + \tau_3) + \tau_1 \\
\mathit{assoc}_2 &=& (\swapp \oplus \idc) \fatsemi \assocrp 
  \fatsemi (\idc \oplus \swapp) \fatsemi \assoclp \\
\\
\mathit{assoc}_3 &\hast& 
  (\tau_1 + \tau_2) + \tau_3 \iso \tau_1 + (\tau_3 + \tau_2) \\
\mathit{assoc}_3 &=& \assocrp \fatsemi (\idc \oplus \swapp)
\end{array}\]

From the perspective of category theory, the language $\Pi$ models what is
called a traced \emph{symmetric bimonoidal category} or a \emph{commutative
  rig category}. These are categories with two binary operations $\oplus$ and
$\otimes$ satisfying the axioms of a rig (i.e., a ring without negative
elements also known as a semiring) up to coherent isomorphisms. And indeed
the types of the $\Pi$-combinators are precisely the semiring axioms. A
formal way of saying this is that $\Pi$ is the
\emph{categorification}~\cite{math/9802029} of the natural numbers. A simple
(slightly degenerate) example of such categories is the category of finite
sets and permutations in which we interpret every $\Pi$-type as a finite set,
the values as elements in these finite sets, and the combinators as
permutations. Another common example of such categories is the category of
finite dimensional vector spaces and linear maps over any field. Note that in
this interpretation, the $\Pi$-type~0 maps to the 0-dimensional vector space
which is \emph{not} empty. Its unique element, the zero vector --- which is
present in every vector space --- acts like a ``bottom'' everywhere-undefined
element and hence the type behaves like the unit of addition and the
annihilator of multiplication as desired.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Int Construction}
\label{intc}

Our immediate technical goal is to explore an extension of $\Pi$ with a
notion of higher-order functions. In the context of monoidal categories, it
is known that a notion of higher-order functions emerges from having an
additional degree of \emph{symmetry}. In particular, both the
\textbf{Int} construction of Joyal, Street, and
Verity~\citeyearpar{joyal1996traced} and the closely related $\mathcal{G}$
construction of linear logic~\cite{gcons} construct higher-order
\emph{linear} functions by considering a new category built on top of a given
base traced monoidal category. The objects of the new category are of the
form $(\tau_1-\tau_2)$ where~$\tau_1$ and~$\tau_2$ are objects in the base
category. Intuitively, the component $\tau_1$ is viewed as a conventional
type whose elements represent values flowing, as usual, from producers to
consumers. The component $\tau_2$ is viewed as a \emph{negative type} whose
elements represent demands for values or equivalently values flowing
backwards. Under this interpretation, and as we explain below, a function is
nothing but an object that converts a demand for an argument into production
of a result.

We begin our formal development by extending $\Pi$ with a new universe of
types $\cubt$ that consists of composite types $(\tau_1-\tau_2)$:
\[\begin{array}{lrcl}
(\textit{{1d} types}) & 
  \cubt &::=& (\tau_1-\tau_2) 
\end{array}\]
In anticipation of future developments, we will refer to the original types
$\tau$ as 0-dimensional (0d) types and to the new types $\cubt$ as
1-dimensional (1d) types. It turns out that, except for one case discussed
below, the 1d level is a ``lifted'' instance of $\Pi$ with its own notions of
empty, unit, sum, and product types, and its corresponding notion of
isomorphisms on these 1d types.

Our next step is to define lifted versions of the 0d types:
\[\begin{array}{rcl}
\ztone &\eqdef& (0-0) \\
\otone &\eqdef& (1-0) \\
\ptone{(\tau_1-\tau_2)}{(\tau_3-\tau_4)} &\eqdef& 
  (\tau_1+\tau_3)-(\tau_2+\tau_4) \\
\ttone{({\tau_1}-{\tau_2})}{({\tau_3}-{\tau_4})} &\eqdef&
{((\tau_1*\tau_3)+(\tau_2*\tau_4))}-\\
&& {((\tau_1*\tau_4)+(\tau_2*\tau_3))}
\end{array}\]
Building on the idea that $\Pi$ is a categorification of the natural numbers
and following a long tradition that relates type isomorphisms and arithmetic
identities~\cite{DiCosmo:2005:SSI:1090732.1090734}, one is tempted to think
that the \textbf{Int} construction (as its name suggests) produces a
categorification of the integers. Based on this hypothesis, the definitions
above can be intuitively understood as arithmetic identities. The same
arithmetic intuition explains the lifting of isomorphisms to 1d types:
\[\begin{array}{rcl}
(\tau_1-\tau_2) \isoone (\tau_3-\tau_4) &\eqdef& 
  (\tau_1+\tau_4) \iso (\tau_2+\tau_3)
\end{array}\]
In other words, an isomorphism between 1d types is really an isomorphism
between ``re-arranged'' 0d types where the negative input $\tau_2$ is viewed
as an output and the negative output $\tau_4$ is viewed as an input. Using
these ideas, it is now a fairly standard exercise to define the lifted
versions of most of the combinators in
Table~\ref{pi-combinators}.\footnote{See
  Krishnaswami's~\citeyearpar{neelblog} excellent blog post implementing this
  construction in OCaml.} There are however a few interesting cases whose
appreciation is essential for the remainder of the paper that we discuss
below.

\paragraph*{Easy Lifting.} Many of the 0d combinators lift easily to the 1d
level. For example:
\[\begin{array}{rcl}
\idc &\hast& \cubt \isoone \cubt \\
     &\hast& (\tau_1-\tau_2) \isoone (\tau_1-\tau_2) \\
     &\eqdef& (\tau_1+\tau_2) \iso (\tau_2+\tau_1) \\
\idc &=& \swapp \\
\\
\identlp &\hast& \ztone \boxplus \cubt \isoone \cubt \\
%%         &\eqdef& (0+\tau_1)-(0+\tau_2) \isoone (\tau_1-\tau_2) \\
%%         &\eqdef& ((0+\tau_1)+\tau_2) \iso ((0+\tau_2)+\tau_1) \\
         &=& \assocrp \fatsemi (\idc \oplus \swapp) \fatsemi \assoclp
\end{array}\]

\paragraph*{Composition using $\mathit{trace}$.} 

\[\begin{array}{r@{\,\,\!}cl}
(\fatsemi) &\hast& 
  (\cubt_1 \isoone \cubt_2) \rightarrow 
  (\cubt_2 \isoone \cubt_3) \rightarrow 
  (\cubt_1 \isoone \cubt_3) \\
%% \mathit{seq} &\hast& 
%%   ((\tau_1-\tau_2) \isoone (\tau_3-\tau_4)) \rightarrow
%%   ((\tau_3-\tau_4) \isoone (\tau_5-\tau_6)) \rightarrow
%%   ((\tau_1-\tau_2) \isoone (\tau_5-\tau_6)) \\
%%   &\eqdef& 
%%   ((\tau_1+\tau_4) \iso (\tau_2+\tau_3)) \rightarrow
%%   ((\tau_3+\tau_6) \iso (\tau_4+\tau_5)) \rightarrow
%%   ((\tau_1+\tau_6) \iso (\tau_2+\tau_5)) \\
f \fatsemi g &=& \mathit{trace}~(\mathit{assoc}_1 \fatsemi 
  (f \oplus \idc) \fatsemi \mathit{assoc}_2 \fatsemi (g \oplus \idc) 
  \fatsemi \mathit{assoc}_3)
\end{array}\]

\paragraph*{New combinators $\mathit{curry}$ and $\mathit{uncurry}$ for higher-order functions.}

\[\begin{array}{rcl}
\boxminus(\tau_1-\tau_2) &\eqdef& \tau_2-\tau_1 \\
(\tau_1-\tau_2) \lolli (\tau_3-\tau_4) &\eqdef& 
           \boxminus(\tau_1-\tau_2) \boxplus (\tau_3-\tau_4) \\
  &\eqdef& (\tau_2+\tau_3) - (\tau_1+\tau_4) 
\end{array}\]
\[\begin{array}{rcl}
\mathit{flip} &\hast& (\cubt_1 \isoone \cubt_2)
  \rightarrow (\boxminus\cubt_2 \isoone \boxminus\cubt_1) \\
%% \mathit{flip} &\hast& ((\tau_1-\tau_2) \isoone (\tau_3-\tau_4))
%%   \rightarrow (\boxminus(\tau_3-\tau_4) \isoone \boxminus(\tau_1-\tau_2)) \\
%%   &\eqdef& ((\tau_1-\tau_2) \isoone (\tau_3-\tau_4))
%%   \rightarrow ((\tau_4-\tau_3) \isoone (\tau_2-\tau_1)) \\
%%   &\eqdef& ((\tau_1+\tau_4) \iso (\tau_2+\tau_3))
%%   \rightarrow ((\tau_4+\tau_1) \iso (\tau_3+\tau_2)) \\
\mathit{flip}~f &=& \swapp \fatsemi f \fatsemi \swapp \\
\\
\mathit{curry} &\hast& 
  ((\cubt_1\boxplus\cubt_2) \isoone \cubt_3) \rightarrow
  (\cubt_1 \isoone (\cubt_2 \lolli \cubt_3)) \\
%% \mathit{curry} &\hast& 
%%   (((\tau_1-\tau_2)\boxplus(\tau_3-\tau_4)) \isoone (\tau_5-\tau_6)) \rightarrow
%%   ((\tau_1-\tau_2) \isoone ((\tau_3-\tau_4) \lolli (\tau_5-\tau_6))) \\
%%   &\eqdef& 
%%   (((\tau_1+\tau_3)-(\tau_2+\tau_4)) \isoone (\tau_5-\tau_6)) \rightarrow
%%   ((\tau_1-\tau_2) \isoone ((\tau_4+\tau_5)-(\tau_3+\tau_6))) \\
%%   &\eqdef& 
%%   (((\tau_1+\tau_3)+\tau_6) \iso ((\tau_2+\tau_4)+\tau_5)) \rightarrow
%%   ((\tau_1+(\tau_4+\tau_5)) \iso (\tau_2+(\tau_3+\tau_6))) \\
\mathit{curry}~f &=& \assoclp \fatsemi f \fatsemi \assocrp \\
\\
\mathit{uncurry} &\hast& 
  (\cubt_1 \isoone (\cubt_2 \lolli \cubt_3)) \rightarrow
  ((\cubt_1\boxplus\cubt_2) \isoone \cubt_3) \\
\mathit{uncurry}~f &=& \assocrp \fatsemi f \fatsemi \assoclp 
\end{array}\]


\paragraph*{The ``phony'' multiplication that is not a functor.} 
The definition for the product of 1d types used above is:
\[\begin{array}{l}
\ttone{({\tau_1}-{\tau_2})}{({\tau_3}-{\tau_4})} = \\
{((\tau_1*\tau_3)+(\tau_2*\tau_4))}-
  {((\tau_1*\tau_4)+(\tau_2*\tau_3))}
\end{array}\]
That definition is ``obvious'' in some sense as it matches the usual
understanding of types as modeling arithmetic. Using it, it is possible to
lift all the 0d combinators involving products \emph{except} the functor:
\[ (\otimes) \hast 
  (\cubt_1\isoone\cubt_2) \rightarrow 
  (\cubt_3\isoone\cubt_4) \rightarrow 
  ((\cubt_1\boxtimes\cubt_3) \isoone
   (\cubt_2\boxtimes\cubt_4))
\]
After a few failed attempts, we suspected that this definition of
multiplication is not functorial which would mean that the
\textbf{Int} construction provides a limited notion of higher-order functions
at the expense of losing the multiplicative structure at higher-levels. This
observation is less well-known that it should be. Further investigation
reveals that this observation is intimately related to a well-known problem
in algebraic topology that was identified thirty years ago as the ``phony''
multiplication~\cite{thomason} in a special class categories related to
ours. This problem was recently solved~\cite{ringcompletion} using a
technique whose fundamental ingredient is to add more dimensions. We exploit
this idea in the remainder of the paper.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Cubes}
\label{cubes}

As hinted at in the previous section, one can think of the \textbf{Int}
construction as generalizing conventional (0-dimensional) types to a
higher-dimension. The types in the higher-dimension are indexed by a polarity
which specifies their position in a 1-dimensional space. Generalizing this
idea further, we view types as being indexed by a dimension $n$ and a
position in the corresponding $n$-dimensional space.

%%%%%%%%%%%%%%
\subsection{Indexing}

We will refer to two kinds of $n$-dimensional cubical diagrams with~$2^n$ and
$3^n$ vertices respectively. These diagrams will be indexed by the categories
$\pn{n}$ and $\qn{n}$ defined below. The category $\pn{n}$ has subsets of
$\textbf{n}=\{1,\ldots,n\}$ as objects and set inclusions as morphisms. The
category $\qn{n}$ has subsets of $\{\pm 1,\ldots,\pm n\}$ in which no number
appears with both positive and negative polarities as objects and set
inclusions as morphisms. Both $\pn{0}$ and $\qn{0}$ consist of the category
with one object, the empty set. The category $\qn{1}$ is depicted below:
\begin{center}
\begin{tikzpicture}
\node (Z) at (0,0) {$\emptyset$};
\node (P) [right of=Z] {$\{1\}$};
\node (N) [left of=Z] {$\{-1\}$};
\draw[->] (Z) -- (P);
\draw[->] (Z) -- (N);
\end{tikzpicture}
\end{center}
It consists of 3 objects. The category $\pn{1}$ consists of the right part of
the diagram. The category $\qn{2}$ is depicted below:
\begin{center}
\begin{tikzpicture}[node distance=1.7cm]
\node (ZZ) at (5.5,0) {$\emptyset$};
\node (ZP) [right of=ZZ] {$\{1\}$};
\node (ZN) [left of=ZZ] {$\{-1\}$};
\node (ZNP) [above of=ZN] {$\{-1,2\}$};
\node (ZP2) [above of=ZZ] {$\{2\}$};
\node (ZPP) [above of=ZP] {$\{1,2\}$};
\node (ZNN) [below of=ZN] {$\{-1,-2\}$};
\node (ZN2) [below of=ZZ] {$\{-2\}$};
\node (ZPN) [below of=ZP] {$\{1,-2\}$};
\draw[->] (ZZ) -- (ZP);
\draw[->] (ZZ) -- (ZN);
\draw[->] (ZZ) -- (ZP2);
\draw[->] (ZZ) -- (ZN2);
\draw[->] (ZP2) -- (ZNP);
\draw[->] (ZP2) -- (ZPP);
\draw[->] (ZN) -- (ZNP);
\draw[->] (ZP) -- (ZPP);
\draw[->] (ZN) -- (ZNN);
\draw[->] (ZP) -- (ZPN);
\draw[->] (ZN2) -- (ZPN);
\draw[->] (ZN2) -- (ZNN);
\end{tikzpicture}
\end{center}
The category $\pn{2}$ is the upper right square. 

Our types will be indexed by objects from the categories $\qn{n}$, i.e., by
pairs $(\textbf{n},S)$ specifying the category $\qn{n}$ and the selected
object in it. Examples of such indexing objects are $(\textbf{0},\emptyset)$,
$(\textbf{1},\{-1\})$ which is the object $\{-1\}$ in $\qn{1}$,
$(\textbf{2},\{-1\})$ which is also the object $\{-1\}$ but in $\qn{2}$, and
$(\textbf{2},\{-1,-2\})$ which is the object $\{-1,-2\}$ in $\qn{2}$. By the
Grothendieck construction~\cite[Ch.12]{DBLP:books/daglib/0080381}, these
indexing objects form a category with morphisms from $(\textbf{n},S)$ to
$(\textbf{m},T)$ if there is an injection between the finite sets
$\textbf{n}$ and $\textbf{m}$ that maps $S$ to a subset of~$T$. For example,
there are two ways of embedding $\qn{1}$ into $\qn{2}$ determined by how one
chooses to inject the set $\{1\}$ into the set $\{1,2\}$. One can choose to
send the element 1 in the first set to either the element 1 or the element 2
in the second set. The first map embeds $\qn{1}$ into the top row of $\qn{2}$
while the second map embeds $\qn{1}$ into the right column of $\qn{2}$. Each
of these possibilities gives a morphism between $(\textbf{1},\{-1\})$ and
$(\textbf{2},\{-1,2\})$.

%%%%%%%%%%%%%%
\subsection{The Cube Construction}

Having defined our indexing objects, we now proceed to define the generalized
$n$-dimensional types. We do this in two stages, first for the special case
of indexing objects in $\pn{n}$ and then for general indexing objects in
$\qn{n}$.

Given $(\textbf{n},S)$ for the special case of $S \in \pn{n}$, we construct a
$n$-dimensional extension of $\Pi$ denoted $\Pin{n}(S)$. The types in
$\Pin{n}(S)$ are as many copies as there are subsets of $S$ of the types in
$\Pi$ labeled by the subsets of $S$. For example, a type in
$\Pin{2}(\emptyset)$ is just a plain $\Pi$ type (technically indexed by
$\emptyset$); a type in $\Pin{2}(\{1\})$ is a collection of two $\Pi$-types
indexed by $\emptyset$ and $\{1\}$; a type in $\Pin{2}(\{2\})$ is also a
collection of two $\Pi$-types but indexed by $\emptyset$ and $\{2\}$; and
finally a type in $\Pin{2}(\{1,2\})$ is a collection of four $\Pi$-types
indexed by $\emptyset$, $\{1\}$, $\{2\}$, and $\{1,2\}$. In general, for a
given $\textbf{n}$, there are $2^n$ versions of $\Pin{n}$ viewed as being
spread out over the corners of an $n$-dimensional cube. The various copies of
$\Pin{n}(S)$ can be embedded in one another following the morphisms in the
indexing category. Thus the two $\Pi$-types in $\Pin{2}(\{1\})$ embed in the
four $\Pi$-types in $\Pin{2}(\{1,2\})$ as follows. We get two copies of the
type indexed by $\emptyset$; one indexed by $\emptyset$ and one indexed by
$\{2\}$; and we get two copies of the type indexed by $\{1\}$; one indexed by
$\{1\}$ and one indexed by $\{1,2\}$.

\begin{center}
\begin{tikzpicture}[node distance=3.3cm]
\node[text width=1cm] (A) at (0,0) {$\Pin{2}(\emptyset) = \Pi_{\emptyset}$};
\node[text width=2cm] (B) [right of=A] {$\Pin{2}(\{1\}) = \Pi_{\emptyset}\times\Pi_{\{1\}}$};
\node[text width=1.5cm] (C) [above of=A] {$\Pin{2}(\{2\}) = \Pi_{\emptyset}\times\Pi_{\{2\}}$};
\node[text width=3cm] (D) [right of=C] {$\Pin{2}(\{1,2\}) = \Pi_{\emptyset}\times\Pi_{\{1\}}\times\Pi_{\{2\}}\times\Pi_{\{1,2\}}$};
\draw[->] (A) -- (B);
\draw[->] (A) -- (C);
\draw[->] (C) -- (D);
\draw[->] (B) -- (D);
\end{tikzpicture}
\end{center}



Formally the set of types in $\Pin{n}(S)$ is:
\[\begin{array}{rcl}
\taun{n}(S) &::=& \bigotimes_n \{ \tau_s ~|~ s \textrm{~subset~of~} S \} \\
  &\alt& \taun{n}(S) + \taun{n}(S) \\
  &\alt& \taun{i}(S) * \taun{j}(S) \quad\mbox{where~} n=i+j\\
  &\alt& \embed(\textbf{m}\mapsto\textbf{n}){\taun{m}(T)}
\end{array}\]

indexing by qn

show functors on the pi-n types and then isos

\newpage
~
\newpage

We present the syntax of generalized $n$-dimensional types and isomorphisms
between them.

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

Our types $\cubt$ are ``cubes'' defined as follows:
\[\begin{array}{rcl}
\tau &::=& 0 \alt 1 \alt \tau_1+\tau_1 \alt \tau_1*\tau_2 \\
\cubt &::=& \tau \alt \nodet{\cubt_1}{\cubt_2} \alt
  \cubt_1\boxplus\cubt_2 \alt \cubt_1\boxtimes\cubt_2 \alt 
  \boxminus\cubt
\end{array}\]

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

This point is made precise in the following denotation of types which maps a
type of dimension $n$ to an $n$-dimensional cube. We represent such a cube
syntactically as a binary tree of maximum depth~$n$ with nodes of the form
$\nodet{\cubt_1}{\cubt_2}$. In such a node, $\cubt_1$ is the positive
subspace and $\cubt_2$ (shaded in gray) is the negative subspace along the
first dimension. Each of these subspaces is itself a cube of a lower
dimension. The $0$-dimensional cubes are plain sets representing the
denotation of conventional first-order types. We use $S$ to denote the
denotations of these plain types. A 1-dimensional cube, $\nodet{S_1}{S_2}$,
intuitively corresponds to the difference $\tau_1 - \tau_2$ of the two types
whose denotations are $S_1$ and $S_2$ respectively. The type can be
visualized as a ``line'' with polarized endpoints connecting the two
points~$S_1$ and $S_2$. A full 2-dimensional cube,
$\nodet{(\nodet{S_1}{S_2})}{(\nodet{S_3}{S_4})}$, intuitively corresponds to
the iterated difference of the appropriate types
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work and Context}

A ton of stuff here. 

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
they are the pi combinators. We also
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

Before we define the construction in any detail, let's take one simple
example $\identlp : 0+1 \iso 1$ and see how to represent as a value of type
$1-(0+1)$. We visually represent the type itself as a line with 0-dimensional
types attached at the endpoints (which are distinguished by polarities):
\begin{center}
\begin{tikzpicture}
\node[above] at (0,0) {\pp};
\draw[fill] (0,0) circle [radius=0.05];
\node[above] at (2.6,0) {\mm};
\draw[fill] (2.6,0) circle [radius=0.05];
\draw[-,dotted] (0,0) -- (2.6,0);
\draw (0,-1.1) ellipse (0.5cm and 1cm);
\draw (2.6,-1.1) ellipse (0.5cm and 1cm);
\node at (0,-1.1) {1};
\node at (2.6,-1.1) {0+1};
\end{tikzpicture}
\end{center}
The value representing $\identlp$ is simply:
\begin{center}
\begin{tikzpicture}
\node[above] at (0,0) {\pp};
\draw[fill] (0,0) circle [radius=0.05];
\node[above] at (2.6,0) {\mm};
\draw[fill] (2.6,0) circle [radius=0.05];
\draw[-,dotted] (0,0) -- (2.6,0);
\draw (0,-1.1) ellipse (0.5cm and 1cm);
\draw (2.6,-1.1) ellipse (0.5cm and 1cm);
\draw[->,thick,blue] (2.0,-1.1) -- (0.6,-1.1);
\node[above] at (1.3,-1.1) {$\identlp$};
\node at (0,-1.1) {1};
\node at (2.6,-1.1) {0+1};
\end{tikzpicture}
\end{center}
This entire package is a value, an atomic entity with invisible internal
structure and that can only be manipulated via the level 1 combinators
described next.

Most of the time, the level 1 combinators are oblivious to the fact that they
are manipulating first class functions. Formally, the action of a level 1
combinator of type $(\tau_1-\tau_2) \isoone (\tau_3-\tau_4)$ is derived from
the action of 0 level combinators of type $(\tau_1+\tau_4) \iso
(\tau_3+\tau_2)$. Thus to take a trivial example $\identlp^1 : \ztone
\boxplus \cubt \isoone \cubt$ is realized as $\assocrp \fatsemi (\idc \oplus
\swapp) \fatsemi \assoclp$ which evidently knows nothing specific about
higher order functions. The interesting idea is that it is possible to define
a new level 1 combinator that exposes the internal structure of values as
functions:
\[\begin{array}{rrcll}
\eta :&  0-0 & \isoone & \tau - \tau &: \varepsilon 
\end{array}\]
What this does is essentially provide an input and output port which are
connected by the internal hidden function.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Condensed Background on HoTT}
\label{hott}

Informally, and as a first approximation, one may think of HoTT as
mathematics, type theory, or computation but with all equalities replaced by
isomorphisms, i.e., with equalities given computational content. We explain
some of the basic ideas below.

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

\noindent It is important to note that the notion of propositional
equality~$\equiv$ relates any two terms that are \emph{definitionally equal}
as shown in example \AgdaFunction{i1} above. In general, there may be
\emph{many} proofs (i.e., paths) showing that two particular values are
identical and that proofs are not necessarily identical. This gives rise to a
structure of great combinatorial complexity. To be explicit, we will use
$\equiv_U$ to refer to the space in which the path lives.

We are used to thinking of types as sets of values. So we typically view the
type \AgdaPrimitiveType{Bool} as the figure on the left but in HoTT we should
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
much. However, because paths carry additional structure (explained below),
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

The additional structure of types is formalized as follows. Let $x$, $y$, and
$z$ be elements of some $U$:
\begin{itemize}
\item For every path $p : x \equiv_U y$, there exists a path $! p : y
  \equiv_U x$;
\item For every $p : x \equiv_U y$ and $q : y \equiv_U z$, there exists a
  path $p \circ q : x \equiv_U z$;
\item Subject to the following conditions:
 \[\begin{array}{rcl}
  p \circ \mathit{refl}~y &\equiv_{{x \equiv_U y}} & p \\
  p &\equiv_{{x \equiv_U y}} & \mathit{refl}~x \circ p \\
  !p \circ p &\equiv_{{y \equiv_U y}} & \mathit{refl}~y \\
  p ~\circ~ !p &\equiv_{{x \equiv_U x}} & \mathit{refl}~x \\
  !~(!p) &\equiv_{{x \equiv_U y}} & p \\
  p \circ (q \circ r) &\equiv_{{x \equiv_U z}} & (p \circ q) \circ r
 \end{array}\]
\item With similar conditions one level up and so on and so forth.
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Space of Types}

Instead of modeling the semantics of $\Pi$ using \emph{permutations}, which
are are set-theoretic functions after all, we use \emph{paths} from the HoTT
framework. More precisely, we model the universe of $\Pi$ types as a space
whose points are the individual $\Pi$-types and we will consider that there
is path between two points $\tau_1$ and $\tau_2$ if there is a $\Pi$
combinator $c : \tau_1 \iso \tau_2$. If we focus on 1-paths, this is perfect
as we explain next. 

\paragraph*{Note.} 
But first, we note that this is a significant deviation from the HoTT
framework which fundamentally includes functions, which are specialized to
equivalences, which are then postulated to be paths by the univalence
axiom. This axiom has no satisfactory computational interpretation,
however. Instead we completely bypass the idea of extensional functions and
use paths directly. Another way to understanding what is going on is the
following. In the conventional HoTT framework:
\begin{itemize}
\item We start with two different notions: paths and functions;
\item We use extensional non-constructive methods to identify a
particular class of functions that form isomorphisms;
\item We postulate that this particular class of functions can be
identified with paths.
\end{itemize}
In our case, 
\begin{itemize}
\item We start with a constructive characterization of \emph{reversible
  functions} or \emph{isomorphisms} built using inductively defined
  combinators; 
\item We blur the distinction between such combinators and paths from the
  beginning. We view computation as nothing more than \emph{following paths}!
  As explained earlier, although this appears limiting, it is universal and
  regular computation can be viewed as a special case of that.
\end{itemize}

\paragraph*{Construction.} 
We have a universe $U$ viewed as a groupoid whose points are the types
$\Pi$-types $\tau$. The $\Pi$-combinators of Table~\ref{pi-combinators} are
viewed as syntax for the paths in the space $U$. We need to show that the
groupoid path structure is faithfully represented. The combinator $\idc$
introduces all the $\refl{\tau} : \tau \equiv \tau$ paths in $U$. The adjoint
$\symc{c}$ introduces an inverse path $!p$ for each path $p$ introduced by
$c$. The composition operator $\fatsemi$ introduce a path $p \circ q$ for
every pair of paths whose endpoints match. In addition, we get paths like
$\swapp$ between $\tau_1+\tau_2$ and $\tau_2+\tau_1$. The existence of such
paths in the conventional HoTT developed is \emph{postulated} by the
univalence axiom. The $\otimes$-composition gives a path $(p,q) :
(\tau_1*\tau_2) \equiv (\tau_3*\tau_4)$ whenever we have paths $p : \tau_1
\equiv \tau_3$ and $q : \tau_2 \equiv \tau_4$. A similar situation for the
$\oplus$-composition. The structure of these paths must be discovered and
these paths must be \emph{proved} to exist using path induction in the
conventional HoTT development. So far, this appears too good to be true, and
it is. The problem is that paths in HoTT are subject to rules discussed at
the end of Sec.~\ref{hott}. For example, it must be the case that if $p :
\tau_1 \equiv_U \tau_2$ that $(p \circ \refl{\tau_2})
\equiv_{\tau_1\equiv_U\tau_2} p$.  This path lives in a higher universe:
nothing in our $\Pi$-combinators would justify adding such a path as all our
combinators map types to types. No combinator works one level up at the space
of combinators and there is no such space in the first place. Clearly we are
stuck unless we manage to express a notion of higher-order functions in
$\Pi$. This would allow us to internalize the type $\tau_1\iso\tau_2$ as a
$\Pi$-type which is then manipulated by the same combinators one level higher
and so on.

To make the correspondence between $\Pi$ and the HoTT concepts more apparent
we will, in the remainder of the paper, use \textsf{refl} instead of $\idc$
and $!$ instead of $\mathit{sym}$ when referring to $\Pi$ combinators when
viewed as paths.  Similarly we will use $\rightarrow$ instead of the
$\Pi$-notation $\iso$ or the HoTT notation $\equiv$ to refer to paths.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Homotopy Types and Univalence}
\label{hottypes}

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

-- f is an equivalence if we have g and h 
-- such that the compositions with f in 
-- both ways are ∼ id
record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    h : B → A
    β : (h ∘ f) ∼ id

-- Two spaces are equivalent if we have 
-- functions f, g, and h that compose 
-- to id
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

-- A path between spaces implies their 
-- equivalence
idtoeqv : {A B : Set} → (A ≡ B) → (A ≃ B)
idtoeqv {A} {B} p = {!!}

-- equivalence of spaces implies a path 
postulate 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)
\end{code}

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

Luckily, an impressive amount of work has been
happening in HoTT that builds around the computational content of equalities,
equivalences, and isomorphisms, and this work will enable us to develop a
more accurate model of $\Pi$ that also supports higher-order functions and
that additionally resolves some issues regarding the computational
interpretation of functional extensionality and the univalence axiom of
HoTT. For the readers familiar with the basic ideas of HoTT, a good intuition
to keep in mind --- to be further justified and explained in the remainder of
the paper -- is that the $\Pi$-combinators are syntax for \emph{paths} in
HoTT, and hence that computation in $\Pi$ is nothing more than following
paths in some complex combinatorial space.

\begin{table*}[t]
\[\begin{array}{cc}
\begin{array}{rrcll}
\identlp :&  (0-0) \boxplus \cubt & \isoone & \cubt &: \identrp \\
\swapp :&  \cubt_1 \boxplus \cubt_2 & \isoone & \cubt_2 \boxplus \cubt_1 &: \swapp \\
\assoclp :&  \cubt_1 \boxplus (\cubt_2 \boxplus \cubt_3) & \isoone & (\cubt_1 \boxplus \cubt_2) \boxplus \cubt_3 &: \assocrp 
\end{array}
& 
\begin{minipage}{0.5\textwidth}
\begin{center} 
\Rule{}
{}
{\jdg{1}{}{\idc : \cubt \isoone \cubt}}
{}
\qquad
\Rule{}
{\jdg{1}{}{\cubc : \cubt_1 \isoone \cubt_2}}
{\jdg{1}{}{\symc{\cubc} : \cubt_2 \isoone \cubt_1}}
{}
\\ \bigskip
\Rule{}
{\jdg{1}{}{\cubc_1 : \cubt_1 \isoone \cubt_2} \quad \cubc_2 : \cubt_2 \isoone \cubt_3}
{\jdg{1}{}{\cubc_1 \fatsemi \cubc_2 : \cubt_1 \isoone \cubt_3}}
{}
\\ \bigskip
\Rule{}
{\jdg{1}{}{\cubc_1 : \cubt_1 \isoone \cubt_2} \quad \cubc_2 : \cubt_3 \isoone \cubt_4}
{\jdg{1}{}{\cubc_1 \oplus \cubc_2 : \cubt_1 \boxplus \cubt_3 \isoone \cubt_2 \boxplus \cubt_4}}
{}
\end{center}
\end{minipage}
\end{array}\]
\caption{1d combinators\label{combinators1}}
\end{table*}


Naturally,
this new layer of types should have appropriate notions of sum and product
types to be computationally interesting. As discussed near the end of this
section, product types will require a much more extensive construction to be
developed in the remainder of the paper. Thus, for the moment, we confine our
discussion to sum types in the new universe of types:
The combinators of Table~\ref{pi-combinators} all
work on 0d types. These 0d combinators will be the base \emph{values} of 1d
types and will be manipulated by a new layer of 1d combinators:
\[\begin{array}{lrcl}
(\textit{{1d} values}) & \cubv &::=& 
  c \alt \inl{\cubv} \alt \inr{\cubv} \\
(\textit{{1d} Combinator types}) &&& \cubt_1 \isoone \cubt_2 \\
(\textit{{1d} combinators}) & \cubc &::=& 
  [\textit{see Table~\ref{combinators1}}]
\end{array}\]
We use the same names for the 0d and 1d combinators which should not lead to
confusion as the types will always be clear from context. The new layer of 1d
combinators consists of lifted versions of all the 0d combinators that do not
refer to product types. The lifting of the empty type 0 is the type $(0-0)$
which is no longer empty since we have (at least) $\idc : 0 \iso 0$. We
return to this subtle point below.

The 1d values have the following type rules:

\medskip
\begin{tabular}{c}
\Rule{}
{\jdg{}{}{c : \tau_1 \iso \tau_2}}
{\jdg{1}{}{c : \tau_2 - \tau_1}}
{}
\\
\Rule{}
{\jdg{1}{}{\cubv : \cubt_1}}
{\jdg{1}{}{\inl{\cubv} : \cubt_1 \boxplus \cubt_2}}
{}
\qquad
\Rule{}
{\jdg{1}{}{\cubv : \cubt_2}}
{\jdg{1}{}{\inr{\cubv} : \cubt_1 \boxplus \cubt_2}}
{}
\end{tabular}
\medskip

\noindent A 0d-combinator $\tau_1\iso\tau_2$ is viewed as a function
demanding $\tau_1$ and producing $\tau_2$ which is encoded by putting
$\tau_1$ in the negative position. The values $\inl{\cubv}$ and $\inr{\cubv}$
are the usual injection into the sum type. Before presenting the formal
semantics of the 1d level of $\Pi$, we consider a small example showing we
can reason about equivalence of 0d combinators. Consider a 0d-combinator $c :
\tau_1+\tau_2 \iso \tau_3+\tau_4$. In the 1d world, this combinator has type
$(\tau_3+\tau_4)-(\tau_1+\tau_2)$.




in the int construction the problem with 0 is avoided because boxplus expands
to plus in the base category where the 0 cancels. we don't want to expand in
the base category and lose the structure of paths. instead we add a new 2path
that eliminates the 0-0

we need combinator that use neg and that show that we have firstclass
function (at least 2nd order). we need to show some identities on paths that are validated by the semantics


The semantics consist of a pair of mutually recursive evaluators that take a
1d combinator and a 1d value and either propagate the value in the
``forward'' $\triangleright$ direction or in the ``backwards''
$\triangleleft$ direction:
\[\begin{array}{rlcl}
\evalone{\identlp}{&(\inl{\cubv})} &=& ?? \\
\evalone{\identlp}{&(\inr{\cubv})} &=& \cubv \\
\evalone{\identrp}{&\cubv} &=& \inr{\cubv} \\
\evalone{\swapp}{&(\inl{\cubv})} &=& \inr{\cubv} \\
\evalone{\swapp}{&(\inr{\cubv})} &=& \inl{\cubv} \\
\evalone{\assoclp}{&(\inl{\cubv})} &=& \inl{(\inl{\cubv})} \\
\evalone{\assoclp}{&(\inr{(\inl{\cubv})})} &=& \inl{(\inr{\cubv})} \\
\evalone{\assoclp}{&(\inr{(\inr{\cubv})})} &=& \inr{\cubv} \\
\evalone{\assocrp}{&(\inl{(\inl{\cubv})})} &=& \inl{\cubv} \\
\evalone{\assocrp}{&(\inl{(\inr{\cubv})})} &=& \inr{(\inl{\cubv})} \\
\evalone{\assocrp}{&(\inr{\cubv})} &=& \inr{(\inr{\cubv})} \\
\evalone{\idc}{&\cubv} &=& \cubv \\
\evalone{(\symc{\cubc})}{&\cubv} &=& \evaloneb{\cubc}{\cubv} \\
\evalone{(\cubc_1\fatsemi\cubc_2)}{&\cubv} &=& 
  \evalone{\cubc_2}{(\evalone{\cubc_1}{\cubv})} \\
\evalone{(\cubc_1\oplus\cubc_2)}{&(\inl{\cubv})} &=& 
  \inl{(\evalone{\cubc_1}{\cubv})} \\
\evalone{(\cubc_1\oplus\cubc_2)}{&(\inr{\cubv})} &=& 
  \inr{(\evalone{\cubc_2}{\cubv})} \\
\\
\evaloneb{\identlp}{&\cubv} &=& \inr{\cubv} \\
\evaloneb{\identrp}{&(\inl{\cubv})} &=& ?? \\
\evaloneb{\identrp}{&(\inr{\cubv})} &=& \cubv \\
\evaloneb{\swapp}{&(\inl{\cubv})} &=& \inr{\cubv} \\
\evaloneb{\swapp}{&(\inr{\cubv})} &=& \inl{\cubv} \\
\evaloneb{\assoclp}{&(\inl{(\inl{\cubv})})} &=& \inl{\cubv} \\
\evaloneb{\assoclp}{&(\inl{(\inr{\cubv})})} &=& \inr{(\inl{\cubv})} \\
\evaloneb{\assoclp}{&(\inr{\cubv})} &=& \inr{(\inr{\cubv})} \\
\evaloneb{\assocrp}{&(\inl{\cubv})} &=& \inl{(\inl{\cubv})} \\
\evaloneb{\assocrp}{&(\inr{(\inl{\cubv})})} &=& \inl{(\inr{\cubv})} \\
\evaloneb{\assocrp}{&(\inr{(\inr{\cubv})})} &=& \inr{\cubv} \\
\evaloneb{\idc}{&\cubv} &=& \cubv \\
\evaloneb{(\symc{\cubc})}{&\cubv} &=& \evalone{\cubc}{\cubv} \\
\evaloneb{(\cubc_1\fatsemi\cubc_2)}{&\cubv} &=& 
  \evaloneb{\cubc_1}{(\evaloneb{\cubc_2}{\cubv})} \\
\evaloneb{(\cubc_1\oplus\cubc_2)}{&(\inl{\cubv})} &=& 
  \inl{(\evaloneb{\cubc_1}{\cubv})} \\
\evaloneb{(\cubc_1\oplus\cubc_2)}{&(\inr{\cubv})} &=& 
  \inr{(\evaloneb{\cubc_2}{\cubv})} \\
\end{array}\]

%%%%%%%%%%%%%%%%%%%%
\subsection{Higher-Order Functions}

In the \textbf{Int} construction a function from $T_1=(t_1-t_2)$ to
$T_2=(t_3-t_4)$ is represented as an object of type $-T_1+T_2$. Expanding the
definitions, we get:
\[\begin{array}{rcl}
-T_1+T_2 &=& -(t_1-t_2) + (t_3-t_4) \\
         &=& (t_2-t_1) + (t_3-t_4) \\
         &=& (t_2+t_3) - (t_1+t_4)
\end{array}\]
The above calculation is consistent with our definitions specialized to 
1-dimensional types. Note that the function is represented as an object
of the same dimension as its input and output types. The situation
generalizes to higher-dimensions. For example, consider a function of type
\[
\nodet{\nodet{\tau_1}{\tau_2}}{\nodet{\tau_3}{\tau_4}} 
\lolli
\nodet{\nodet{\tau_5}{\tau_6}}{\nodet{\tau_7}{\tau_8}} 
\]
This function is represent by an object of dimension 2 as the calculation
below shows:
\[\begin{array}{rcl}
&& \nodet{\nodet{\tau_1}{\tau_2}}{\nodet{\tau_3}{\tau_4}} 
\lolli
\nodet{\nodet{\tau_5}{\tau_6}}{\nodet{\tau_7}{\tau_8}} \\
&=& (\ominus \nodet{\nodet{\tau_1}{\tau_2}}{\nodet{\tau_3}{\tau_4}}) 
    \oplus (\nodet{\nodet{\tau_5}{\tau_6}}{\nodet{\tau_7}{\tau_8}}) \\
&=& (\nodet{\ominus(\nodet{\tau_3}{\tau_4})}{\ominus(\nodet{\tau_1}{\tau_2})})
    \oplus (\nodet{\nodet{\tau_5}{\tau_6}}{\nodet{\tau_7}{\tau_8}}) \\
&=&     (\nodet{\nodet{\tau_4}{\tau_3}}{\nodet{\tau_2}{\tau_1}})
 \oplus (\nodet{\nodet{\tau_5}{\tau_6}}{\nodet{\tau_7}{\tau_8}}) \\
&=& \nodet{(\nodet{\tau_4}{\tau_3})\oplus(\nodet{\tau_5}{\tau_6})}
           {(\nodet{\tau_2}{\tau_1})\oplus(\nodet{\tau_7}{\tau_8})} \\
&=& \nodet{(\nodet{\tau_4\oplus\tau_5}{\tau_3\oplus\tau_6})}
          {(\nodet{\tau_2\oplus\tau_7}{\tau_1\oplus\tau_8})} \\
&=& \nodet{(\nodet{\tau_4\uplus\tau_5}{\tau_3\uplus\tau_6})}
          {(\nodet{\tau_2\uplus\tau_7}{\tau_1\uplus\tau_8})}
\end{array}\]
This may be better understood by visualizing each of the argument type and 
result types as two squares. The square representing the argument type
is flipped in both dimensions effectively swapping the labels on both 
diagonals. The resulting square is then superimposed on the square 
for the result type to give the representation of the function as a first-class
object.

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

We will need a way of indexing types by the space they live in and their
position in that space. \ldots

We begin by specifying a way to denote a corner in an $n$-dimensional cube
with $3^n$ corners. Examples are $\cpath{0}{}$, $\cpath{1}{-1}$,
$\cpath{1}{1}$, $\cpath{2}{-1,2}$, and $\cpath{3}{-1,2,3}$ which have the
following meaning:
\begin{itemize}
\item $\cpath{0}{}$ is a specification in a 0d space, i.e., a point. It
  selects that point.
\item $\cpath{1}{-1}$ is a specification in a 1d space, i.e., a line with 3
  possible positions: a center with no label and two endpoints labeled $-1$
  and $1$; it chooses the endpoint labeled $-1$.
\item $\cpath{1}{1}$ is a specification in the same space as above which
  selects the other endpoint.
\item $\cpath{1,2}{-1,2}$ is a specification in a 2d space with 9 points
  arranged in a grid. It selects the point labeled $(-1,2)$ in that grid.
\item $\cpath{1,2,3}{-1,2,3}$ is a specification in a 3d space with 27 points
  which selects the point labeled $(-1,2,3)$ in the space.
\end{itemize}
One way to represent this information is by drawing the space as a tree of
degree 3 with a star at the desired location:
\[
\emptyset
\qquad
\Tree [.$\emptyset$ $-1*$ $\emptyset$ 1 ]
\qquad
\Tree [.$\emptyset$ $-1$ $\emptyset$ $1*$ ]
\qquad
\Tree [.$\emptyset$ [.$-1$ $-2$ $\emptyset$ $2*$ ] 
                  [.$\emptyset$ $-2$ $\emptyset$ $2$ ] 
                  [.1 $-2$ $\emptyset$ $2$ ] ]
\]



