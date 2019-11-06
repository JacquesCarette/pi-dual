\documentclass[sigplan,10pt,review,anonymous]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}
\acmConference[PL'18]{ACM SIGPLAN Conference on Programming Languages}{January 01--03, 2018}{New York, NY, USA}
\acmYear{2018}
\acmISBN{} 
\acmDOI{} 
\startPage{1}
\setcopyright{none}
\bibliographystyle{ACM-Reference-Format}

\usepackage{booktabs}  
\usepackage{subcaption} 
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage[references]{agda} 
\usepackage{newunicodechar}

\newunicodechar{𝕌}{$\mathbb{U}$}
\newunicodechar{𝟙}{$1$}
\newunicodechar{ᵤ}{${}_u$}

\newcommand{\alt}{~|~}
\newcommand{\inlv}[1]{\ensuremath{\mathit{inl}(v)}}
\newcommand{\inrv}[1]{\ensuremath{\mathit{inr}(v)}}
\newcommand{\pointed}[2]{[#1 \bullet #2]}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

\title{Fractional Types}
\author{Chao-Hong Chen}
\affiliation{
  \institution{Indiana University}
}

\author{Vikraman Choudhury}
\affiliation{
  \institution{Indiana University}
}

\author{Jacques Carette}
\affiliation{
  \institution{McMaster University}
}

\author{Amr Sabry}
\affiliation{
  \institution{Indiana University}
}

\begin{abstract}
Text of abstract \ldots.
\end{abstract}

\maketitle

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

\paragraph*{Conservation of Information.} If quantum field theory is
correct (as it so far seems to be) then information, during any
physical process, is neither created nor
destroyed. Landauer~\cite{Landauer:1961,Landauer,bennett1985fundamental},
Bennett~\cite{bennett2010notes,bennett2003notes,Bennett:1973:LRC},
Fredkin~\cite{fredkin1982conservative} and others made compelling
arguments that this physical principle induces a corresponding
computational principle of ``conservation of information.'' This
principle is indeed one of the defining characteristics of quantum
computing and its classical restriction known as reversible computing.

\paragraph*{Quantum and Reversible Computing.} The Toffoli gate is
known to be universal for classical reversible
circuits~\cite{Toffoli:1980}. Adding just one gate (the Hadamard gate)
produces a universal set of primitives for quantum
circuits~\cite{hadtoffuniv}. The ``only'' difference between the two
circuit models is that quantum circuits can process superpositions of
values (waves) in one step whereas classical circuits lack this form
of parallelism. Most importantly, structurally the two circuits models
are identical and one can derive properties valid for both families by
focusing on the simpler classical model. In fact, classical reversible
computations are often used as ``subroutines'' of quantum
computations.

Instead of using the Toffoli gate as a universal primitive for
reversible classical circuits, one can leverage the full force of type
theory and category theory by expressing reversible classical
computations as \emph{isomorphisms over finite
  types}~\cite{Fiore:2004,James:2012:IE:2103656.2103667} or
\emph{equivalences over
  groupoids}~\cite{DBLP:conf/esop/CaretteS16}. This perspective
exposes interesting mathematical structure in reversible computations
that we will exploit to solve the ``ancilla problem'' explained next. 

\paragraph*{Temporary Storage using Ancilla Bits.} The universality of
the Toffoli gate for classical reversible computing and of the
combination of the Toffoli and Hadamard gates for quantum computing
should not distract from efficiency and safety concerns. The theorems
proving universality (i) assume that temporary storage (often called
\emph{ancilla bits}) may be used~\cite{Toffoli:1980}, and (ii) that
this temporary storage is returned to its initial state before
de-allocation. Indeed if no temporary storage is allowed, the Toffoli
gate is not universal~\cite{DBLP:conf/innovations/AaronsonGS17} and as
we demonstrate using space-time tradeoffs in Sec.~\ref{sec:examples},
the more temporary storage is allowed, the more efficient certain
computations could become. The condition requiring that the temporary
storage is only de-allocated when returned to its initial condition is
a safety condition. Violating this condition destroys the symmetry
between input and output making the circuits not reversible and, in
the quantum model, causes irreversible decoherence problems. As
reviewed in Sec.~\ref{sec:examples}, ancilla bits have a number of critical
applications and yet are poorly supported in current reversible and
quantum programming languages making them a common source of bugs.

\paragraph*{Negative Entropy.}  
According to the conventional theory of
communication~\cite{Shannon1948}, a type with $N$ values is viewed as
an abstract system that has $N$ distinguishable states where the
amount of information contained in each state is $\log{N}$. This
entropy is a measure of information which materializes itself in
memory or bandwidth requirements when storing or transmitting elements
of this type. Thus a type with 8 elements needs 3 bits of memory for
storage or 3 bits of bandwidth for communication. The logarithmic map
implies that information contained in a composite state is the sum of
the information contained in its constituents. For example, the type
$A \times B$ where $A$ has two elements and $B$ has three elements can
be thought of a composite system consisting of two independent
unrelated subsystems.  Each state of the composite system therefore
contains $\log{(2*3)} = \log{2} + \log{3}$ bits which is the sum of
the information contained in each subsystem. A \emph{fractional type}
$\frac{1}{A}$ introduces negative entropy. For example, a type with
cardinality $\frac{1}{8}$ has entropy $\log{\frac{1}{8}} = -3$. It is
natural to interpret this negative entropy just like we interpret
``negative money,'' as a resource (space or bandwidth) to be repaid
(reclaimed) by some other part of the system. Indeed, we will
introduce such fractional types and use them to represent ``garbage
collection processes'' that reclaim temporary storage.

\paragraph*{Contributions.} 

\paragraph*{Outline.}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Ancilla Bits}
\label{sec:examples}
 
%%%
\subsection{Applications}
 
Uses of ancillas:
\url{https://quantum.country/search}:

\begin{quote}
  There’s a rough heuristic worth noting here, which is that you can
  often convert if-then style thinking into quantum circuits. You
  introduce an ancilla qubit to store the outcome of evaluating the if
  condition. And then depending on the state of the ancilla, you
  perform the appropriate state manipulation. Finally, when possible
  you reverse the initial computation, resetting the ancilla to its
  original state so you can subsequently ignore it.
\end{quote}

\url{https://www.nap.edu/read/25196/chapter/5#73}
\begin{quote}
  For error correction, one needs to replicate the state of a qubit
  onto a number of qubits. While the no cloning theorem prevents one
  from copying the state of a qubit directly onto another, one can
  create a redundant entangled qubit state of many qubits. The key is
  that the qubits to be entangled must start out in a known
  state. Qubits with a known state (for purposes of this discussion,
  it will be the state \verb.|0>.), called ``ancilla qubits,'' may be
  added to a computation for this purpose. Since the state of ancilla
  qubits are known, it is possible to create a simple circuit that
  makes the output state of all these ancilla qubits match the
  protected qubit: run each ancilla through a controlled-NOT gate,
  where the control is driven by the qubit that needs to be
  replicated. Assume that there is a qubit with state \verb.PSI. that
  we want to protect, where \verb.|PSI>. represents an arbitrary
  superposition state \verb.|PSI> = a0 |0> + a0 |1>. In the CNOT gate,
  the ancilla \verb.|0>. state will remain a \verb.|0>. state by the
  \verb.|0>. component of \verb.|PSI>., but it will be converted to
  \verb.|1>. by the \verb.|1>. component of \verb.|PSI>. The result of
  this operation is the newly entangled two-qubit state
  \verb.a0 |00> + a1 |11>., creating a system in which the ancilla
  qubit is now perfectly entangled with the first qubit. Adding more
  ancillas increases the distance of the repetition code.  \end{quote}

\url{https://www.sigarch.org/the-case-for-quantum-computing/}
\begin{quote}
  Imagine a 3-qubit quantum majority code in which a logical “0” is
  encoded as “000” and a logical “1” is encoded as “111.”  Just as
  with a classical majority code, a single bit-flip error can be
  corrected by restoring to the majority value.  Unlike a classical
  code, however, we can not directly measure the qubits else their
  quantum state will be destroyed.  Instead, we measure syndromes from
  each possible pair of qubits by interacting them with an ancilla,
  then measure each ancilla.  Although the errors to the qubits are
  actually continuous, the effect of measuring the ancilla is to
  discretize the errors, as well as inform us whether an error
  occurred so that it can be corrected.  With this methodology,
  quantum states are restored in a modular way for even a large
  quantum computer.  Furthermore, operations on error-corrected qubits
  can be viewed as digital rather than analog, and only a small number
  of universal operations (H, T, CNOT) are needed for universal
  quantum computation.  Through careful design and engineering, error
  correction codes and this small set of precise operations will lead
  to machines that could support practical quantum computation.
\end{quote}

\url{https://homepages.cwi.nl/~rdewolf/qcnotesv2.pdf}
\begin{quote}
  Using an ancilla qubit, it is possible to avoid doing any
  intermediate measurements in a quantum circuit. Show how this can be
  done.  Hint: instead of measuring the qubit, apply a CNOT that
  “copies” it to a new \verb.|0>.-qubit, which is then left alone
  until the end of the computation. Analyze what happens.
\end{quote}

%%%
\subsection{Language Support}
 
current proposals for reversible
and quantum programming languages
(e.g. Ricercar~\cite{10.1007/978-3-319-20860-2_13},
Quipper~\cite{Green:2013:QSQ:2491956.2462177}), restrict ancilla bits
to be used in nested scopes, have sound but incomplete laws for
reasoning about the safety condition, and only guarantee safety via
runtime checks.

Leads to bugs as analyzed by
\url{http://drops.dagstuhl.de/opus/volltexte/2019/10196/pdf/OASIcs-PLATEAU-2018-4.pdf}:

\begin{quote}

  Bug type 6: Incorrect composition of operations using mirroring Section 4.5 discussed how bugs in deallocating ancillary qubits can happen due to bad parameters. Here we see how bugs in deallocating ancillary qubits can happen due to incorrect composition of operations following a mirroring pattern. For example, in Table 7, the operations in rows 2 and 3 are respectively mirrored and undone in rows 6 and 5. These lines of code need careful reversal of every loop and every operation.

  A common pattern in quantum programs involves performing operations (e.g., add), contingent on a set of qubits known as control qubits. Without language support, this pattern needs many lines of code and manual allocation of ancillary qubits. In the Scaffold code example in Table 7, rows 3 and 5 are just computing the intersection of qubits q, with the help of ancillary qubits initialized in row 1, in order to realize the controlled rotation operation in row 4. Furthermore, quantum algorithms often need varying numbers of control qubits in different parts of the algorithm, leading to replicated code from multiple versions of the same subroutine differing only by the number of control qubits.

\end{quote}

%%%
\subsection{Examples}
 
Toffoli4 using 2 Toffoli3: core of proof of universality; simple
enough. Reversible/Quantum Circuits and Ancilla Wires: Early use of
ancillas in Toffoli's paper to implement arbitrary reversible
functions using a fixed number of 3 input gates
\url{https://link.springer.com/content/pdf/10.1007%2F3-540-10003-2_104.pdf}

In-place matrix transpose: ease of programming, efficiency. Say we
want to transpose a matrix. Wikipedia example
(\url{https://en.wikipedia.org/wiki/In-place_matrix_transposition}):
\begin{verbatim}
11 12 13 14 
21 22 23 24 
\end{verbatim}
transposed to
\begin{verbatim}
11 21
12 22
13 23
14 24
\end{verbatim}
In Pi, the input and output matrices are:
\begin{verbatim}
M   = (11 , 21) , (12 , 22) , (13, 23) , (14 , 24) 

trM = (11 , 12 , 13 , 14) , (21 , 22 , 23 , 23) 
\end{verbatim}
Say we are given a language like Pi that is sound and complete with
respect to permutations on finite types, we would write the
permutation like so.
\begin{verbatim}
WRITE PERMUTATION
\end{verbatim}
This code does not use additional space, i.e., it performs the matrix
transpose in constant space, i.e., performs an in-place matrix
transposition. It is well know that with additional space, one can
write more efficient matrix transpositions (explain and citations).

Example(s) from Quipper etc. with focus on safety condition. Quipper
uses ancilla bits in several places; one use is to compile
irreversible circuits to reversible ones; need ancilla bits; more
generally several quantum algorithms need ancilla bits (see below); in
quipper de-allocation left to programmer.

Is the below a possible example?
\begin{verbatim}
Say we already have a permutation A <-> B
we can implement a permutation X <-> Z 
when there exists Y such that A = X * Y = Z * Y = B

X -> X * Y * 1/Y 
  -> A * 1/Y
  -> B * 1/Y
  -> Y * Z * 1/Y
  -> Z * Y * 1/Y
  -> Z
\end{verbatim}
This basically says, in the language of Lens, that
when $A$ is isomorphic to $X \times Y$ and
$B$ is isomorphic to $Z \times Y$, then
$X$ is isomorphic to $Y$.

Another way to think of it: for all isomorphic
$A$ and $B$, whenever they can be factored with a
common complement ($Y$), then the ``other pieces''
(here $X$ and $Y$) are automatically isomorphic.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Preliminaries}

%%%%%
\subsection{Singleton Types}

Consider the type $\Sigma \mathbb{N} (\lambda n. n \equiv 5)$. Values
of that type are a number $m$ and a proof that this is number is equal
to 5. So we can have $(4 + 1, \textit{refl})$, $(2 + 3 ,
\textit{refl})$, and so on. All these syntactically different values
are identical to 5 and hence we can \emph{contract} the type to a
single point at 5. 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{PiFrac}

%%%%%
\subsection{Pi}

Plain Pi over finite types:
\[\begin{array}{lrcl}
\textit{Value types} & t &::=& 0 \alt 1 \alt t+t \alt t*t \\
\textit{Values}      & v &::=& \star \alt \inlv{v} \alt \inrv{v} \alt (v,v) \\
\textit{Level-1 types} &&& t \leftrightarrow t \\
\textit{Level-1 programs} & c &::=& \cdots \\
\textit{Level-2 types} &&& c \Leftrightarrow c \\
\textit{Level-2 programs} & \alpha &::=& \cdots 
\end{array}\]

%%%%%
\subsection{Adding Fractions}

%%%%%
\subsection{Ancilla}

When ancilla bits are created they are created with a specific
value. This value is encoded in the circuit. We use a Singleton type
to remember this information. We add the following:

\AgdaHide{
\begin{code}
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

infix  70 _×ᵤ_
infix  60 _+ᵤ_
infix  40 _↔_

mutual 

  data 𝕌 : Set where
    𝟘 : 𝕌
    𝟙 : 𝕌
    _+ᵤ_ : 𝕌 → 𝕌 → 𝕌
    _×ᵤ_ : 𝕌 → 𝕌 → 𝕌
    ●_[_] : (t : 𝕌) → ⟦ t ⟧ → 𝕌
    𝟙/●_[_] : (t : 𝕌) → ⟦ t ⟧ → 𝕌

  ⟦_⟧ : 𝕌 → Set
  ⟦ t ⟧ = ⊤

  data _↔_ : 𝕌 → 𝕌 → Set where

Singleton : (A : Set) → (v : A) → Set
Singleton A v = ∃ (λ ● → v ≡ ●)
\end{code}
}

\AgdaHide{
\begin{code}
postulate 
\end{code}
}
\begin{code}
  η : {t : 𝕌}  {v : ⟦ t ⟧} → 𝟙 ↔ ● t [ v ] ×ᵤ 𝟙/● t [ v ]
\end{code}



The value of fractional type represents the ``garbage collector.''
The garbage collector is specialized to collect a single value, which
is the value used to create the ancilla value. At this point, if the
garbage collector encounters a different value, it doesn't know what
to do, and would need to throw an exception. This situation in
\verb|PiFracDyn.agda| is similar to current solutions (e.g. Quipper)
but actually more general as it allows non-scoped ancilla allocation
and de-allocation. Show examples.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Dependently-Typed Garbage Collectors}

The denotation of the fractional type is now:
\begin{code}
Recip : (A : Set) → (v : A) → Set
Recip A v = Singleton A v → ⊤ 
\end{code}

Exploit dependent types to reify proofs in the type system. Type
checking requires (partial) eval. Once we have a proof can we somehow
go back to \verb|PiFracDyn.agda| and remove the runtime check?

Polymorphic type for ancilla?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Trace?}
  
Add multiplicative trace, do SAT solver

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Space Denotational Semantics}
  
Positive rational numbers are a model. Apparently there is a
categorification
\url{https://alistairsavage.ca/pubs/Copelli-Categorification_of_the_Nonnegative_Rational_Numbers.pdf}

Use all the constructions name, coname, etc. and see what they do in this context!

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliography{../../cites.bib}

\end{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%