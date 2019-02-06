\documentclass[a4paper]{article}
\usepackage{graphicx}
\usepackage{onecolceurws}

% Not the final title!
\title{Reversible Programming for the BX enthusiast}

\author{
Jacques Carette\\ Dept. of Computing and Software\\
        (address) \\ carette@mcmaster.ca
\and
Amr Sabry \\ Computer Science Dept.\\
        (address) \\ sabry@indiana.edu
}

\institution{}

\begin{document}
\maketitle

\begin{abstract}
Show how BX is deeply entertwined with RP already,
so that BX enthusiast should really know all about RP too.
\end{abstract}
\vskip 32pt


\section{Introduction}

The inspiration for this paper comes from two sources:
\begin{enumerate}
  \item Oleg Grenrus' \textit{Finding correct (lens) laws}~\cite{oleg-blog}, 
    and
  \item The paper \textit{Synthesizing Bijective Lenses}~\cite{Miltner2018}.
\end{enumerate}

There are many, many different representations for (monomorphic)
lenses. The one that will be the most fruitful for us is the
existential formulation:
\begin{verbatim}
\end{verbatim}
where the type isomorphism is plain to see. That formulation is the
principal source of the relationship.

Paper: bijective lenses, p.5.

\section{Lens and other Optics}

Remember that (A + A + A) ~= 3*A. And that one can lens into the 3
on the right -- so one can lens into it on the left too!
The iso expresses the difference (in languages with proper sum-of-product
types) between implicit tags and explicit tags. On the left, the compiler
chooses how to represent it, on the right, the programmer. But there are
many types that can be ``exploded'' so as to move any discrete portion
to/from tags.

Rememer that the type Lens (A*B*C) (A*C) is inhabited. So is
Lens (A*B*C) (C*A).  Look familiar?

\section{Pi}

Intro to Pi.

\section{Happy together}

Really explore the relationship.

\section{Random thoughts}

What if we took different notions of iso (i.e. contractible or not)
instead of the usual one, would that change things? What about the 
effect no the lens laws?

Possibly this should all be done in Agda? Or Haskell? Some PL for sure.

\section{Conclusion}

\bibliographystyle{alpha} 
\bibliography{cites}
%inline the .bbl file directly for mailing to authors.

\end{document}


