%% \documentclass[a4paper]{article}
\documentclass{article}

\usepackage{onecolceurws}
\usepackage{amssymb,amsthm,amsmath}
\usepackage{graphicx}
\usepackage{agda}
\usepackage{lmodern}
\usepackage{textgreek}
\usepackage[utf8x]{inputenc}
\usepackage[LGR,TS1,T1]{fontenc}
\usepackage{comment}
\usepackage{tikz}
\usepackage{tikz-cd}
\usepackage[nocenter]{qtree}
\usepackage{fullpage}
\usepackage{hyperref}
\usepackage{multicol}
\usepackage{stmaryrd}
\usepackage{proof}
\usepackage{ucs}

%%

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}

\newcommand{\Gpd}{\ensuremath{\mathsf{Groupoid}}}
\newcommand{\nboxtimes}[2]{\,\,~{^{#1}\boxtimes^{#2}}~\,\,}
\newcommand{\mm}{\texttt{\textminus}}
\newcommand{\pp}{\texttt{+}}

\newcommand{\presumtype}{\uplus}
\newcommand{\preprodtype}{*}
\newcommand{\sumtype}{+}
\newcommand{\prodtype}{\times}
\newcommand{\fin}[1]{\ensuremath{\left[#1\right]}}
\newcommand{\Nat}{\ensuremath{\mathbb{N}}}

\newcommand{\inleft}[1]{\textsf{left}~#1}
\newcommand{\inright}[1]{\textsf{right}~#1}
\newcommand{\cp}[3]{#1\stackrel{#2}{\bullet}#3}
\newcommand{\idt}[3]{#2 \equiv_{#1} #3}
\newcommand{\idrt}[3]{#3 \equiv_{#1} #2}
\newcommand{\refl}[1]{\textsf{refl}~#1}
\newcommand{\alt}{~|~}
\newcommand{\linv}{l!}
\newcommand{\rinv}{r!}
\newcommand{\invinv}{!!}
\newcommand{\assoc}{\circ}
\newcommand{\identlp}{\ensuremath{\mathit{unite}_{\sumtype}\mathit{l}}}
\newcommand{\identrp}{\ensuremath{\mathit{uniti}_{\sumtype}\mathit{l}}}
\newcommand{\identlsp}{\ensuremath{\mathit{unite}_{\sumtype}\mathit{r}}}
\newcommand{\identrsp}{\ensuremath{\mathit{uniti}_{\sumtype}\mathit{r}}}
\newcommand{\swapp}{\ensuremath{\mathit{swap}_{\sumtype}}}
\newcommand{\assoclp}{\ensuremath{\mathit{assocl}_{\sumtype}}}
\newcommand{\assocrp}{\ensuremath{\mathit{assocr}_{\sumtype}}}
\newcommand{\identlt}{\ensuremath{\mathit{unite}_{\prodtype}\mathit{l}}}
\newcommand{\identrt}{\ensuremath{\mathit{uniti}_{\prodtype}\mathit{l}}}
\newcommand{\identlst}{\ensuremath{\mathit{unite}_{\prodtype}\mathit{r}}}
\newcommand{\identrst}{\ensuremath{\mathit{uniti}_{\prodtype}\mathit{r}}}
\newcommand{\swapt}{\ensuremath{\mathit{swap}_{\prodtype}}}
\newcommand{\assoclt}{\ensuremath{\mathit{assocl}_{\prodtype}}}
\newcommand{\assocrt}{\ensuremath{\mathit{assocr}_{\prodtype}}}
\newcommand{\absorbr}{\ensuremath{\mathit{absorbr}}}
\newcommand{\absorbl}{\ensuremath{\mathit{absorbl}}}
\newcommand{\factorzr}{\ensuremath{\mathit{factorzr}}}
\newcommand{\factorzl}{\ensuremath{\mathit{factorzl}}}
\newcommand{\dist}{\ensuremath{\mathit{dist}}}
\newcommand{\factor}{\ensuremath{\mathit{factor}}}
\newcommand{\distl}{\ensuremath{\mathit{distl}}}
\newcommand{\factorl}{\ensuremath{\mathit{factorl}}}
\newcommand{\iso}{\leftrightarrow}
\newcommand{\proves}{\vdash}
\newcommand{\idc}{\mathit{id}\!\!\leftrightarrow}
\newcommand{\Rule}[4]{
\makebox{{\rm #1}
$\displaystyle
\frac{\begin{array}{l}#2 \\\end{array}}
{\begin{array}{l}#3      \\\end{array}}$
 #4}}
\newcommand{\jdg}[3]{#2 \proves_{#1} #3}
\newcommand{\sem}[1]{\ensuremath{\llbracket{#1}\rrbracket}}

% Unicode declarations

%% \DeclareUnicodeCharacter{9678}{\ensuremath{\odot}}
%% \DeclareUnicodeCharacter{9636}{\ensuremath{\Box}}
%% shorten the longarrow
%% \DeclareUnicodeCharacter{10231}{\ensuremath{\leftrightarrow}}

\DeclareUnicodeCharacter{9679}{\ensuremath{\bullet}}

\DeclareMathAlphabet{\mymathbb}{U}{bbold}{m}{n}

% TIKZ declarations
\tikzstyle{func}=[rectangle,draw,fill=black!20,minimum size=1.9em,
  text width=2.4em, text centered]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Some needed unicode characters

% Convenient abbreviations
\newcommand{\AIC}[1]{\AgdaInductiveConstructor{#1}}

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
\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.9\textwidth}\color{red}{Amr says: {#1}}\end{minipage}}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Not the final title!
% \title{Reversible Programming for the BX enthusiast}
%\title{Reversible programming applied to bidirectional programming}
\title{Optics and Type Equivalences}

\author{
Jacques Carette\\ Dept. of Computing and Software\\
        McMaster University \\ carette@mcmaster.ca
\and
Amr Sabry \\ Computer Science Dept.\\
        Indiana University \\ sabry@indiana.edu
}

\institution{}

\begin{document}
\maketitle

\begin{abstract}
Bidirectional programming, lenses, prisms, and other optics have connections
to reversible programming which have been explored from several perspectives,
mostly by attempting to recover bidirectional transformations from unidirectional
ones. We offer a novel and foundational perspective in which reversible programming
is expressed using “type equivalences.” This perspective offers several advantages:
first, it is possible to construct sets of sound and complete type equivalences
for certain collections of types; these correspond to canonical optic constructions.
Second, using ideas inspired by category theory and homotopy type theory,
it is possible to construct sound and complete “equivalences between equivalences”
which provide the canonical laws for reasoning about lens and prism equivalences.
\end{abstract}
\vskip 32pt

\AgdaHide{
\begin{code}
 -- {-# OPTIONS --without-K #-}
module RCforBX where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
  renaming (map to map×)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; cong; cong₂; sym; trans; refl; inspect; [_])
open import Function using (id; const; _∘_; case_of_; _∋_)

open import Relation.Binary using (Setoid; Rel)
open import Function.Equality using (_⟨$⟩_; Π)
-- open import Relation.Binary.Product.Pointwise using (_×-setoid_)
-- open import Data.Product.Relation.Pointwise.NonDependent using (_×-inverse_)
open import Function.Inverse using (Inverse)
  renaming (id to idF; _∘_ to _∘F_)
open Inverse using (to; from; left-inverse-of; right-inverse-of)

open import Equiv
open import TypeEquiv

-- Do our own Setoid product, because the built-in one triggers an internal error!
_×S_ : {a b c d : Level} → Setoid a b → Setoid c d → Setoid (a ⊔ c) (b ⊔ d)
S ×S T = record
  { Carrier = Setoid.Carrier S × Setoid.Carrier T
  ; _≈_ = λ {(s₁ , t₁) (s₂ , t₂) → Setoid._≈_ S s₁ s₂ × Setoid._≈_ T t₁ t₂}
  ; isEquivalence = record
    { refl = (Setoid.refl S) , (Setoid.refl T)
    ; sym = λ pf → Setoid.sym S (proj₁ pf) , Setoid.sym T (proj₂ pf)
    ; trans = λ {(i≈Sj , i≈Tj) (j≈Sk , j≈Tk) → Setoid.trans S i≈Sj j≈Sk , Setoid.trans T i≈Tj j≈Tk }
    } }

_≈S_ : {a b : Level} → (A : Setoid a b) → (B : Setoid a b) → Rel (Setoid.Carrier A ⊎ Setoid.Carrier B) b
(S ≈S T) (inj₁ x) (inj₁ x₁) = Setoid._≈_ S x x₁
(_≈S_ {_} {b} S T) (inj₁ x) (inj₂ y) = Lift b ⊥
(_≈S_ {_} {b} S T) (inj₂ y₁) (inj₁ x) = Lift b ⊥
(S ≈S T) (inj₂ y₁) (inj₂ y) = Setoid._≈_ T y₁ y

_⊎S_ : {a b : Level} → Setoid a b → Setoid a b → Setoid a b
_⊎S_ {a} {b} S T = record
  { Carrier = Carrier S ⊎ Carrier T
  ; _≈_ = S ≈S T
  ; isEquivalence = record
    { refl = λ { {inj₁ x} → Setoid.refl S ; {inj₂ y} → Setoid.refl T}
    ; sym = λ { {inj₁ x} {inj₁ x₁} ≈ → Setoid.sym S ≈ ; {inj₁ x} {inj₂ y} (lift ())
              ; {inj₂ y} {inj₁ x} (lift ()) ; {inj₂ y} {inj₂ y₁} ≈ → Setoid.sym T ≈}
    ; trans = λ { {inj₁ x} {inj₁ x₁} {inj₁ x₂} i≈j j≈k → Setoid.trans S i≈j j≈k
                ; {inj₁ x} {inj₁ x₁} {inj₂ y} i≈j (lift ())
                ; {inj₁ x} {inj₂ y} {inj₁ x₁} i≈j (lift ())
                ; {inj₁ x} {inj₂ y} {inj₂ y₁} (lift ()) j≈k
                ; {inj₂ y} {inj₁ x} {k} (lift ()) j≈k
                ; {inj₂ y} {inj₂ y₁} {inj₁ x} i≈j (lift ())
                ; {inj₂ y} {inj₂ y₁} {inj₂ y₂} i≈j j≈k → Setoid.trans T i≈j j≈k } }
  }
  where open Setoid

-- And our own product of Inverses
_×-inverse_ : {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Level}
  {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
  {C : Setoid c₁ c₂} {D : Setoid d₁ d₂} →
  Inverse A B → Inverse C D → Inverse (A ×S C) (B ×S D)
A↔B ×-inverse C↔D = record
  { to = record { _⟨$⟩_ = map× (to A↔B ⟨$⟩_) (to C↔D ⟨$⟩_)
                ; cong = λ { ( _∼₁_ , _∼₂_ ) → Π.cong (to A↔B) _∼₁_ , Π.cong (to C↔D) _∼₂_ } }
  ; from = record { _⟨$⟩_ = map× (from A↔B ⟨$⟩_) (from C↔D ⟨$⟩_)
                  ; cong = λ { ( _∼₁_ , _∼₂_ ) → Π.cong (from A↔B) _∼₁_ , Π.cong (from C↔D) _∼₂_ } }
  ; inverse-of = record
    { left-inverse-of = λ { (a , c) → left-inverse-of A↔B a , left-inverse-of C↔D c}
    ; right-inverse-of = λ { (b , d) → right-inverse-of A↔B b , right-inverse-of C↔D d } } }
  where
    open Inverse
    inv = right-inverse A↔B

×-assoc : {a₁ a₂ b₁ b₂ c₁ c₂ : Level}
  {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} {C : Setoid c₁ c₂} →
  Inverse (A ×S (B ×S C)) ((A ×S B) ×S C)
×-assoc {A = A} {B} {C} = record
  { to = record
    { _⟨$⟩_ = λ {(a , (b , c)) → (a , b) , c}
    ; cong = λ { (≈₁ , ≈₂ , ≈₃) → (≈₁ , ≈₂), ≈₃ }}
  ; from = record
    { _⟨$⟩_ = λ {((a , b), c) → a , b , c}
    ; cong = λ { ((≈₁ , ≈₂) , ≈₃) → ≈₁ , ≈₂ , ≈₃ } }
  ; inverse-of = record { left-inverse-of = λ _ → (Setoid.refl A) , (Setoid.refl B) , (Setoid.refl C)
                        ; right-inverse-of = λ _ → (Setoid.refl A , Setoid.refl B) , Setoid.refl C }
  }
\end{code}
}
\section{Introduction}

The notion of lenses (and its generalizations to optics) is now
established as one of the formalisms for bidirectional
transformations~\cite{eaab8672ebea42538109e9f72ece5ed0}. These optics
are generally studied in the context of conventional programming
languages (e.g., Java, Haskell, etc.) which leaves untapped the
richness of a dependently-typed language, especially one which
directly supports programming with proof-relevant type
equivalences. (See however the characterization of bidirectional
transformations as proof-relevant
bisimulations~\cite{eaab8672ebea42538109e9f72ece5ed0} for a closely
related perspective.)

In this paper, we show that in the context of a programming language
for proof-relevant type equivalences, the many constructions of optics
and more importantly, their correctness and their laws, become simple
consequences of the general properties of proof-relevant type
equivalences. In particular, we formalize the intuitive, but informal,
constructions and laws, in various
sources~\cite{oleg-blog,Miltner:2017:SBL:3177123.3158089,laarhoven}.

We start in the next section with the conventional definition of
lenses using a pair of \emph{very well-behaved} set/get
functions. That definition is only implicitly related to type
equivalences via a hidden \emph{constant-complement}. In order to
expose the underlying type equivalence, we first reformulate the
definition of lenses using an existential record that packages an
unknown but fixed complement type. That definition, however, turns out
to have weak proof-theoretic properties. We therefore introduce our
final definition of lenses using the notion of \emph{setoid} to
formalize the correct equivalence relation on the source type of the
lens. We present a complete formalized proof in Agda that this final
definition is sound and complete with respect to the conventional
set/get definition.

With a formulation of lenses based on proof-relevant type-equivalences
in hand, we aim to show that many variants of lenses, as well as other
optics (prisms, etc.), are directly expressible, and more importantly,
that their laws are immediately derivable. In order to do that,
however, we first need, a language in which to express type
equivalences as well as proofs between type equivalences. In previous
work, we have established that if we restrict ourselves to finite
types constructed from the empty type, the unit type, the sum type,
and the product type, then it is possible to formulate a two-level
language with the following properties. The programs at level-1 in the
language are sound and complete type equivalences, and the programs at
level-2 are sound and complete proofs of equivalences between the
level-1 programs (see Sec. 3). This setting of finite types thus
provides us with a framework in which to define canonical optics with
their properties (see Sec. 4). In the presence of richer types, lenses
and their properties can still be expressed but we generally lose
guarantees of completeness. We conclude with discussions about more
general optics and transformations.

%% * we want to understand lenses in the setting of proof-relevant type isomorphisms
%%
%% * the first question is how to define lenses:
%%      - first guess set/get; no obvious connection to type equivalences
%%      - next guess \exists; type equivalences appear; can show soundness but
%%        no completness
%%      - final def: setoid
%%    [none of the above refers to Pi, so could be presented first, right?]
%%
%% * we now want to explore various optics using our definition; but
%%      first we need a language to talk about proof-relevant type
%%      equivalences; if we restrict ourselves to finite types, we can
%%      have soundness and completeness of type equivalences AND proofs
%%      about such equivalences; that setting will give us nice canonical
%%      results; in principle we could go to richer types (cite other Pi
%%      papers with trace etc) but we lose
%%      soundness/completeness. Introduce relevant pieces of PI as a
%%      language for sound and complete proof relevant type equivalences
%%
%% * a whole bunch of optics emerge with the right laws for free….

%% The inspiration for this paper comes from a number of sources:
%% \begin{enumerate}
%%   \item Oleg Grenrus' \textit{Finding correct (lens) laws}~\cite{oleg-blog},
%%   \item The paper \textit{Synthesizing Bijective Lenses}~\cite{Miltner2018},
%%   \item Twan van Laarhoven's blog \textit{Isomorphism Lenses},
%%   \item (many more, insert citations throughout)
%% \end{enumerate}
%%
%% Example of two lenses that are the same
%% lenses as fractional types; prisms as negative types

\section{Lenses}

A \emph{lens} is a structure that mediates between a source $S$ and
view $A$. Typically a lens comes equipped with two functions
$\mathit{get}$ which projects a view from a source, and $\mathit{set}$
which takes a source and a view and reconstructs an appropriate source with that
view. A monomorphic interface for such lenses is shown below,
including the commonly cited laws for the lens to be very well-behaved:

\begin{code}
record GS-Lens {ℓs ℓa : Level} (S : Set ℓs) (A : Set ℓa) : Set (ℓs ⊔ ℓa) where
  field
    get     : S → A
    set     : S → A → S
    getput  : (s : S) (a : A) → get (set s a) ≡ a
    putget  : (s : S) → set s (get s) ≡ s
    putput  : (s : S) (a a' : A) → set (set s a) a' ≡ set s a'
open GS-Lens
\end{code}

A common theme in the literature on lenses is that the function
$\mathit{get}$ discards some information from the source to create a
view, and that this information can be explicitly represented using
the \emph{constant-complement} technique from the database
literature. In other words, lenses can viewed as elements of $\exists\
C. S \simeq C × A$ where $\simeq$ is type equivalence.

This observation is what connects lenses to type equivalences and
hence to reversible programming. The main contribution of the paper is
to exploit various canonical constructions and completness results in
the world of reversible programming and export them to the world of
bidirectional programming with lenses (and other optics).

Although correct in principle, a straightforward encoding of
\emph{constant-complement lenses} as $\Sigma\ C. S \simeq C × A$ is
not satisfactory: a $\AgdaRecord{GS-Lens}$ does not reveal any sort of
complement $C$; so the constant-complement lenses should not
either. To do this, we should somehow hide our choice of $C$.  We
could use a variety of tricks to do this, but all would rely on
features of Agda which do not have well-understood meta-theory.
Instead, we will rely on \emph{discipline} to not access the actual
$C$. Note that because $\AgdaFunction{Set}~ℓ$ does not allow
introspection, actually getting one's hands on this $C$ still does not
reveal very much!

We can use the formulation $∃\ C. S \simeq C × A$ as the basis for a
first definitions of isomorphism-based lens. We make $C$ implicit, so as to
reduce the temptation to examine it. This formulation will not be
entirely adequate, but is very close to our final definition.
\begin{code}
record Lens₁ {ℓ : Level} (S : Set ℓ) (A : Set ℓ) : Set (suc ℓ) where
  constructor ∃-lens
  field
    {C} : Set ℓ
    iso : S ≃ (C × A)
\end{code}

Given an $\AgdaRecord{Lens₁}$, we can build a \AgdaRecord{GS-Lens}, so
that this is certainly sound:

\begin{code}
sound : {ℓ : Level} {S A : Set ℓ} → Lens₁ S A → GS-Lens S A
sound (∃-lens (f , qinv g α β)) = record
  { get = λ s → proj₂ (f s)
  ; set = λ s a → g (proj₁ (f s) , a)
  ; getput = λ s a → cong proj₂ (α _)
  ; putget = λ s → β s
  ; putput = λ s a a' → cong g (cong₂ _,_ (cong proj₁ (α _)) P.refl) }
\end{code}

\noindent It is important to notice that the conversion above only uses the
\AgdaField{iso} part of the \AgdaRecord{Lens₁}.

The question is, is this \emph{complete}, in the sense that we can
also go in the other direction? To achieve this, we must
manufacture an appropriate constant complement.  We certainly
know what $S$ contains all the necessary information for this but
is in some sense ``too big''.  But it is instructive to see what
happens when we try.

Roughly speaking the forward part of the isomorphism is forced:
given an $s:S$, there is only one way to get an $A$, and that is
via \AgdaFunction{get}. To get an $S$ back, there are two choices:
either use $s$ itself, or call \AgdaFunction{set}; the laws of
\AgdaRecord{GS-Lens} say that either will actually work.
In the backwards direction of the isomorphism,
the laws help in narrowing down the choices: basically, we want the
$s′ : S$ where $\AgdaFunction{get s′} ≡ a$, and so we again
use \AgdaFunction{set} for the purpose:

\begin{code}
incomplete : {ℓ : Level} {S A : Set ℓ} → GS-Lens S A → Lens₁ S A
incomplete {ℓ} {S} {A} l =
  ∃-lens ((λ s → s , get l s) ,
         qinv (λ { (s , a) → set l s a })
              (λ { (s , a) → cong₂ _,_ hole (getput l s a)})
               λ s → putget l s)
\end{code}
That almost gets us there. The one hole we can't fill says
\begin{code}
    where
      hole : {s : S} {a : A} → set l s a ≡ s
      hole = {!!}
\end{code}
But that will only ever happen if $\AgdaFunction{get s}$ was already $a$ (by
\AgdaField{putget}).

Of course, we already knew this would happen: $S$ is too big. Basically, it is
too big by exactly the inverse image of $A$ by \AgdaFunction{get}.

Thus our next move is to make that part of $S$ not matter. In other words,
rather than using the \emph{type} $S$ as a proxy, we want to use a
\AgdaRecord{Setoid} where $s, t : S$ will be regarded as the same if they
only differ in their $A$ component.  It is convenient to also define a
function \AgdaFunction{lens} that lifts type isomorphisms (which work over
propositional equality) to the \AgdaRecord{Setoid} setting.

\begin{code}
record ∃-Lens {a s : Level} (S : Set s) (A : Set a) : Set (suc (a ⊔ s)) where
  constructor ll
  field
    {C} : Setoid s a
    iso : Inverse (P.setoid S) (C ×S (P.setoid A))

lens : {ℓ : Level} {S A C : Set ℓ} → S ≃ (C × A) → ∃-Lens S A
lens {C = C} (f , qinv g α β) = ll {C = P.setoid C} (record
  { to = record { _⟨$⟩_ = f ; cong = λ { P.refl → P.refl , P.refl} }
  ; from = record { _⟨$⟩_ = g ; cong = λ { (P.refl , P.refl) → P.refl } } -- η for × crucial
  ; inverse-of = record
    { left-inverse-of = β
    ; right-inverse-of = λ { (c , a) → (cong proj₁ (α _)) , cong proj₂ (α _)}
    }
  })
\end{code}

One important aspect of the proof is that not only are both laws $\alpha$ and $\beta$
for the isomorphism used, but $\eta$ for pairs is also crucial.

The soundness proof is then essentially identical to the previous one:
\begin{code}
sound′ : {ℓ : Level} {S A : Set ℓ} → ∃-Lens S A → GS-Lens S A
sound′ {S = S} {A} (ll len) =
  let f = to len ⟨$⟩_
      g = from len ⟨$⟩_
      α = right-inverse-of len
      β = left-inverse-of len in
  record
  { get = λ s → proj₂ (f s)
  ; set = λ s a → g (proj₁ (f s) , a)
  ; getput = λ s a → proj₂ (α (proj₁ (f s) , a))
  ; putget = β
  ; putput = λ s a _ → Π.cong (from len) (proj₁ (α (proj₁ (f s) , a)) , P.refl) }
\end{code}

And now the completeness proof goes through. Key is to create an equivalence
relation $\AgdaField{≈}$ between sources $s,t$ which makes them ``the same''
if they only differ in their $A$ component.
\begin{code}
complete : {ℓ : Level} {S A : Set ℓ} → GS-Lens S A → ∃-Lens S A
complete {ℓ} {S} {A} l = ll
  {C = record
    { Carrier = S
    ; _≈_ = λ s t → ∀ (a : A) → set l s a ≡ set l t a
    ; isEquivalence = record { refl = λ _ → P.refl ; sym = λ i≈j a → P.sym (i≈j a)
                             ; trans = λ i≈j j≈k a → P.trans (i≈j a) (j≈k a) } }}
   (record
     { to = record { _⟨$⟩_ = λ s → s , get l s ; cong = λ { refl → (λ _ → P.refl) , P.refl } }
     ; from = record { _⟨$⟩_ = λ {(s , a) → set l s a} ; cong = λ { {_ , a₁} (≈ , P.refl) → ≈ a₁ } }
     ; inverse-of = record
         { left-inverse-of = putget l
         ; right-inverse-of = λ { (s , a) → (λ a' → putput l s a a') , getput l s a}
         }
     })
\end{code}

Grenrus~\cite{oleg-blog} gives a completely different type which also works --- but
the completeness proofs requires both proof irrelevance and function extensionality
(crucially), while our proof works in a much simpler setting.

\section{Proof-relevant type equivalences}

Our principal means of building lenses, \AgdaFunction{lens}, takes as
input a \emph{type equivalence}.  These are called \emph{proof relevant}
because different witnesses (proofs) of an equivalence are
not assumed to be the same.  For example, there are two
non-equivalent ways to prove that $A × A \simeq A × A$, namely
the identity and ``swap''.

Our starting point will be a basic type theory with the empty
type ($\bot$), the unit type ($\top$), the sum type ($\presumtype$), and
the product ($\preprodtype$) type. But rather than focusing on
\emph{functions} between these types, we will instead look at
\emph{equivalences}.

%%%%%%%%%
\subsection{Type Equivalences}

\noindent The Curry-Howard correspondence teaches that logical
expressions form a commutative semiring -- and leads us to
expect that types
too form a commutative semiring. And indeed they do -- at least up to
\emph{type isomorphism}.  The reader unfamiliar with these can
find a leisurely introduction in~\cite{CaretteJamesSabryArxiv}. We
will furthermore assume that the reader is already familiar with
the basic definitions around \emph{type equivalences}.
That types, with ($\bot, \top, \presumtype,
\preprodtype$) interpreted as ($0, 1, +, ×$) and strict
equality replaced with equivalence $\simeq$
form a commutative semiring is a basic result of type theory.

However, we might be misled by the Curry-Howard correspondence:
In logic, it is true that $A \lor A = A$ and
$A \land A = A$. However, neither $A \presumtype A$ nor $A \preprodtype A$ are
equivalent to $A$. They are however \emph{equi-inhabited}. This is
a fancy way of saying
\[ A \presumtype A \ \text{is inhabited} \qquad \Leftrightarrow \qquad A \
  \text{is inhabited} \] The above is the real \textit{essence} of the
Curry-Howard correspondence.  In other words, classical Curry-Howard
tells us about \emph{logical equivalence} of types; there are indeed functions
$f : A \presumtype A \rightarrow A$ and $g : A \rightarrow A \presumtype A$;
however, they are not inverses.

\begin{figure}[t]
\begin{minipage}{0.48\textwidth}
\[\begin{array}{rcl}
a &=& a \\
\\
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
\end{minipage}
\begin{minipage}{0.48\textwidth}
\[
\begin{array}{rrcll}
& A & \simeq & A &\\
\\
&  \bot \presumtype A & \simeq & A &\\
&  A \presumtype B & \simeq & B \presumtype A &\\
&  A \presumtype (B \presumtype C) & \simeq & (A \presumtype B) \presumtype C &\\
\\
&  \top \preprodtype A & \simeq & A &\\
&  A \preprodtype B & \simeq & B \preprodtype A &\\
&  A \preprodtype (B \preprodtype C) & \simeq & (A \preprodtype B) \preprodtype C &\\
\\
& \bot \preprodtype A & \simeq & \bot &\\
& (A \presumtype B) \preprodtype C & \simeq & (A \preprodtype C) \presumtype (B \preprodtype C) &
\end{array}
\]
\end{minipage}
\caption{Semiring equalities and type isomorphisms.}
\label{type-isos}
\end{figure}

The generators for our type isomorphisms will exactly be those
of a semiring --- we place them side-by-side in
Fig.~\ref{type-isos}.  Each is also named --- the details can be found
both in~\cite{Carette2016,Carette2018} and in the online repository
\url{http://github.com/JacquesCarette/pi-dual} (in file
\texttt{Univalence/TypeEquiv.agda}).  There, a programming
language named $\Pi$ is created to denote type isomorphisms.

This set of isomorphisms is known to be sound and
complete~\cite{Fiore:2004,fiore-remarks} for isomorphisms
of finite types.  Furthermore, it is also universal
for hardware combinational
circuits~\cite{James:2012:IE:2103656.2103667}.

\subsection{Examples}
We can express a 3-bit word reversal operation as follows:

\ensuremath{\mathit{reverse} : \mathit{word}_3 \leftrightarrow \mathit{word}_3}

\ensuremath{\mathit{reverse} = \swapt \odot (\swapt  \otimes  \idc)~ \odot \assocrt}

\noindent We can check that \ensuremath{\mathit{reverse}} does the right thing by
applying it to a value \ensuremath{(v_1, (v_2, v_3))} and writing out the full
reduction, which can be visualized as:
\[\begin{array}{rlr}
 & (v_1, (v_2, v_3)) \\
 \swapt & ((v_2, v_3), v_1) \\
 \swapt \otimes  \idc & ((v_3, v_2), v_1) \\
 \assocrt & (v_3, (v_2, v_1)) \\
 \end{array}\]

There are several universal primitives for conventional (irreversible)
hardware circuits, such as \ensuremath{\mathit{nand}} and \ensuremath{\mathit{fanout}}. In the case
of reversible hardware circuits, the canonical universal primitive is
the Toffoli gate~\cite{Toffoli:1980}. The Toffoli gate takes three
boolean inputs: if the first two inputs are \ensuremath{\mathit{true}} then the third
bit is negated. The Toffoli gate, and its simple cousin the $\mathit{cnot}$ gate, are both
expressible in the programming language $\Pi$.

\subsection{Equivalences between Equivalences}
\label{sec:pi2}

Just as types can be shown equivalent, type isomorphisms
also induce a ``higher dimensional'' set of equivalences.
To illustrate, consider two equivalences that both
map between the types $A + B$ and $C+D$:

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.8}]
  \draw[>=latex,<->,double,red,thick] (2.25,-1.2) -- (2.25,-2.9) ;
  \draw[fill] (-2,-1.5) circle [radius=0.025];
  \node[below] at (-2.1,-1.5) {$A$};
  \node[below] at (-2.1,-1.9) {$+$};
  \draw[fill] (-2,-2.5) circle [radius=0.025];
  \node[below] at (-2.1,-2.5) {$B$};

  \draw[fill] (6.5,-1.5) circle [radius=0.025];
  \node[below] at (6.7,-1.5) {$C$};
  \node[below] at (6.7,-1.9) {$+$};
  \draw[fill] (6.5,-2.5) circle [radius=0.025];
  \node[below] at (6.7,-2.5) {$D$};

  \draw[<-] (-2,-1.5) to[bend left] (1,0.5) ;
  \draw[<-] (-2,-2.5) to[bend left] (1,-0.5) ;
  \draw[->] (3.5,0.5) to[bend left] (6.5,-1.45) ;
  \draw[->] (3.5,-0.5) to[bend left] (6.5,-2.45) ;

  \draw[<-] (-2,-1.5) to[bend right] (1,-3.5) ;
  \draw[<-] (-2,-2.5) to[bend right] (1,-4.5) ;
  \draw[->] (3.5,-3.5) to[bend right] (6.5,-1.55) ;
  \draw[->] (3.5,-4.5) to[bend right] (6.5,-2.55) ;


  \draw     (2,0.5)  -- (2.5,0.5)  ;
  \draw     (2,-0.5) -- (2.5,-0.5) ;

  \draw     (2.5,0.5)  -- (3.5,-0.5)  ;
  \draw     (2.5,-0.5) -- (3.5,0.5) ;

  \draw     (1,-3.5)  -- (2,-4.5)    ;
  \draw     (1,-4.5) -- (2,-3.5)   ;

  \draw     (2,-3.5)  -- (2.5,-3.5)    ;
  \draw     (2,-4.5) -- (2.5,-4.5)   ;

  \path (1.5,0.5) node (tc1) [func] {$c_1$};
  \path (1.5,-0.5) node (tc2) [func] {$c_2$};
  \path (3,-4.5) node (bc1) [func] {$c_1$};
  \path (3,-3.5) node (bc2) [func] {$c_2$};
\end{tikzpicture}
\end{center}
The top path is
$(c_1~\oplus~c_2)~\odot~\swapp$ and the bottom path
$\swapp~\odot~(c_2~\oplus~c_1)$. These are equivalent --
and in fact denote the same permutation.
And, of course, not
all programs between the same types are equivalent. The simplest example
are the two automorphisms of $1+1$, namely $\idc$ and $\swapp$.

The language of type isomorphisms and equivalences between
them has a strong connection to \emph{univalent universes} in
HoTT~\cite{Carette2018}. Based on this connection, we refer to the
types as being at level-0, to the equivalences between types as being
at level-1, and to the
equivalences between equivalences of types (i.e., this subsection)
as being at level-2.

The basic type equivalences were defined by using all the
proof terms of commutative semirings. What we need
now is to understand how \emph{proofs} of algebraic identities should be
considered equivalent. Classical algebra does not help, as proofs
are not considered first-class citizens. However,
another route is available to us: since the work of
Hofmann and Streicher~\cite{hofmann96thegroupoid}, we know that
one can model types as \emph{groupoids}.  The additional
structure comes from explicitly modeling the ``identity
types'': instead of regarding all terms which witness
the equality of (say) $a$ and $b$ of type $A$ as being
indistinguishable, we posit that there may in fact be many,
i.e. proof relevance.

Thus, rather than looking at (untyped) commutative semirings, we
should look at a \emph{typed} version. This process frequently goes by
the moniker of ``categorification.''  We want a categorical algebra,
where the basic objects are groupoids (to model our types), and where
there is a natural notion of $+$ and $*$.  At first, we hit what seems
like a serious stumbling block: the category of all groupoids, \Gpd,
have neither co-products nor products. However, we don't want to work
internally in \Gpd -- we want operations \emph{on} groupoids. In other
words, we want something akin to symmetric monoidal categories, but
with two interacting monoidal structures.  Luckily, this already
exists: the categorical analog to (commutative) semirings are
(symmetric) Rig Categories~\cite{laplaza72,kelly74}.  This
straightforwardly generalizes to symmetric Rig Groupoids.

How does this help? Coherence conditions! Symmetric monoidal categories,
to start somewhere simple, do not just introduce natural transformations
like the associator $\alpha$ and the left and right unitors ($\lambda$
and~$\rho$ respectively), but also coherence conditions that these must satisfy.
Looking, for example, at just the additive fragment (i.e. with just $0$,
$1$ and $+$ for the types, $\odot$ and $\oplus$ as combinators, and
only the terms so expressible), the sub-language would correspond,
denotationally, to exactly symmetric monoidal groupoids. And
here we have \emph{equations between equations}, aka
commutative diagrams.  Transporting these coherence conditions, for
example those that express that various transformations are \emph{natural},
to our setting gives a list of equations between isomorphisms.
Furthermore, all the natural transformations
that arise are in fact natural \emph{isomorphisms} -- and thus
reversible.

We can in fact prove that all the coherence conditions
of symmetric Rig Groupoids holds for the groupoid
interpretation of types~\cite{Carette2016}.  This is somewhat tedious
given the sheer numbers involved, but when properly formulated,
relatively straightforward, up to a couple of tricky cases.

But why are these particular coherence laws? Are they all necessary?
Conversely are they, in some appropriate sense, sufficient? This is
the so-called \emph{coherence problem}. Mac Lane, in his farewell address
as President of the American Mathematical Society~\cite{MacLane1976} gives
a good introduction and overview of such problems.  A more modern
interpretation (which can nevertheless be read into Mac Lane's own
exposition) would read as follows: given a set of equalities on abstract
words, regarded as a rewrite system, and two means of rewriting a word
in that language to another, is there some suitable notion of canonical
form that expresses the essential uniqueness of the non-trivial
rewrites?  Note how this word-and-rewrite problem is essentially
independent of the eventual interpretation. But one must take some care,
as there are obvious degenerate cases (involving ``trivial'' equations
involving $0$ or $1$) which lead to non-uniqueness. The landmark
results, first by Kelly-Mac Lane~\cite{KELLY197197} for closed
symmetric monoidal categories, then (independently) Laplaza and
Kelly~\cite{laplaza72,kelly74} for symmetric Rig Categories, is
that indeed there are sound and complete coherence conditions that
insure that all the ``obvious'' equalities between different abstract
words in these systems give rise to commutative diagrams. The
``obvious'' equalities come from \emph{syzygies} or
\emph{critical pairs} of the system of equations.
The problem is far from trivial --- Fiore et al.~\cite{Fiore-2008}
document some publications where the coherence set is in
fact incorrect. They furthermore give a quite general algorithm
to derive such coherence conditions.

\section{Exploring the Lens landscape}

Given that we have a sound and complete set of primitive type equivalences
(and combinators),
we can explore what this means for actually programming lenses. Many papers
have explored the most general settings for lenses, we will instead look
inside the implementations.  This will
reveal the \emph{inner structure} of lenses, rather than focusing on their
macro structure.

\subsection{Simple Lenses}
Let's explore the simplest lenses first.  For a \AgdaRecord{GS-Lens}, the simplest is
when \AgdaField{get} is the identity, which forces the rest:

\begin{code}
module _ (A B D E : Set) where
  open ∃-Lens

  AA-gs-lens : GS-Lens A A
  AA-gs-lens = record { get = id ; set = λ _ → id
    ; getput = λ _ _ → P.refl ; putget = λ _ → P.refl ; putput = λ _ _ _ → P.refl }
\end{code}

What does that correspond to as a \AgdaRecord{∃-Lens}? Here, we can easily
guess the complement by solving the equation $A ≃ C × A$ for $C$: $C$ must
be $\AgdaSymbol{⊤}$. But then the $\AgdaRecord{∃-Lens}$ isn't quite as simple as above:
\begin{code}
  AA-∃-lens : ∃-Lens A A
  AA-∃-lens = lens uniti⋆equiv
\end{code}
\noindent where $\AgdaFunction{uniti⋆equiv}$ has type
$A ≃ (⊤ × A)$. In other words, as the complement is not actually
present in $A$, it must be introduced. $\AgdaFunction{uniti⋆equiv}$
names the ``multiplicative unit introduction equivalence''. From
here on, we will not expand on the names, trusting that they
can be guessed by the reader.

What about in the other direction, what is the \AgdaRecord{∃-Lens} whose
underlying isomorphism is the identity?
\begin{code}
  BAA-∃-lens : ∃-Lens (B × A) A
  BAA-∃-lens = lens id≃
\end{code}
\noindent Since our definition of \AgdaRecord{∃-Lens} is right-biased
(we are looking for isomorphisms of shape $S ≃ C × A$), the above lens
extracts the $A$ on the right.  Of course, there is another lens which
switches the roles of $A$ and $B$ --- and this leaves a trace on the
isomorphism:
\begin{code}
  BAB-∃-lens : ∃-Lens (B × A) B
  BAB-∃-lens = lens swap⋆equiv
\end{code}

Thus, looking at type equivalences, which ones return a type
of shape $C × A$ ?  We have already seen \AIC{uniti⋆l},
\AIC{id⟷} and \AIC{swap⋆} arise. That leaves four:
\AIC{assocl⋆}, \AIC{factorz}, \AIC{factor} and \AIC{×≃}.
These occur as follows:
\begin{code}
  DBA-lens : ∃-Lens (D × (B × A)) A
  DBA-lens = lens assocl⋆equiv

  ⊥-lens : ∃-Lens ⊥ A
  ⊥-lens = lens factorzequiv

  ⊎-lens : ∃-Lens ((D × A) ⊎ (B × A)) A
  ⊎-lens = lens factorequiv

  ⊗-lens : (E ≃ B) → (D ≃ A) → ∃-Lens (E × D) A
  ⊗-lens iso₁ iso₂ = lens (iso₁ ×≃ iso₂)
\end{code}

The first is a basic administrative ``reshaping''. The second
takes a bit more thought, but is easily explained: if we promise
an impossible source, it is easy to promise to return something
arbitrary in return!

The $\AgdaFunction{⊎-lens}$ is interesting, because it allows us
to see a constant complement in a type which itself is not a
product -- it is, however, equivalent to one. The last uses the
full power of equivalences, to see an $A$ where, a priori, one
does not seem to exist at all.

Lastly, we also have lens composition:
\begin{code}
  ∘-lens : ∃-Lens D B → ∃-Lens B A → ∃-Lens D A
  ∘-lens l₁ l₂ = ll ((×-assoc ∘F (idF ×-inverse ∃-Lens.iso l₂)) ∘F ∃-Lens.iso l₁)
\end{code}
The above gives us our first \emph{lens program} consisting of a composition of
four more basic equivalences. However, it is ``lower level'' as we can only
extract $\AgdaRecord{Setoid}$-based equivalences from a $\AgdaRecord{∃-Lens}$.
The necessary code is quite straightforward (and available in the literate
Agda source of this paper).

\subsection{Unusual lenses}

It is possible to create lenses for things which are
not ``in'' a type at all --- an example is most instructive.
For completeness, both \AgdaRecord{GS-Lens} and \AgdaRecord{∃-Lens}
will be given.

Let us consider a type \verb|Colour| with exactly $3$ inhabitants,
\begin{code}
module _ {A : Set} where
  data Colour : Set where red green blue : Colour
\end{code}

First, a \AgdaRecord{∃-Lens} built ``by hand'':
\begin{code}
  ∃-Colour-in-A+A+A : ∃-Lens (A ⊎ A ⊎ A) Colour
  ∃-Colour-in-A+A+A = lens eq
   where
    f : A ⊎ A ⊎ A → A × Colour
    f (inj₁ x) = x , red
    f (inj₂ (inj₁ x)) = x , green
    f (inj₂ (inj₂ x)) = x , blue
    g : A × Colour → A ⊎ A ⊎ A
    g (a , red) = inj₁ a
    g (a , green) = inj₂ (inj₁ a)
    g (a , blue) = inj₂ (inj₂ a)
    eq : (A ⊎ A ⊎ A) ≃ (A × Colour)
    eq = f , qinv g (λ { (a , red) → refl ; (a , green) → refl ; (a , blue) → refl})
                    λ { (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl}
\end{code}
The equivalence is not too painful to establish. But let's do
the same for the \verb|GS-Lens|:
\begin{code}
  GS-Colour-in-A+A+A : GS-Lens (A ⊎ A ⊎ A) Colour
  GS-Colour-in-A+A+A = record
    { get = λ { (inj₁ x) → red ; (inj₂ (inj₁ x)) → green ; (inj₂ (inj₂ y)) → blue}
    ; set = λ { (inj₁ x) red → inj₁ x ; (inj₁ x) green → inj₂ (inj₁ x) ; (inj₁ x) blue → inj₂ (inj₂ x)
              ; (inj₂ (inj₁ x)) red → inj₁ x ; (inj₂ (inj₁ x)) green → inj₂ (inj₁ x) ; (inj₂ (inj₁ x)) blue → inj₂ (inj₂ x)
              ; (inj₂ (inj₂ y)) red → inj₁ y ; (inj₂ (inj₂ y)) green → inj₂ (inj₁ y) ; (inj₂ (inj₂ y)) blue → inj₂ (inj₂ y)}
    ; getput = λ { (inj₁ x) red → refl ; (inj₁ x) green → refl ; (inj₁ x) blue → refl
                 ; (inj₂ (inj₁ x)) red → refl ; (inj₂ (inj₁ x)) green → refl ; (inj₂ (inj₁ x)) blue → refl
                 ; (inj₂ (inj₂ y)) red → refl ; (inj₂ (inj₂ y)) green → refl ; (inj₂ (inj₂ y)) blue → refl}
    ; putget = λ { (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl}
    ; putput = λ { (inj₁ x) red red → refl ; (inj₁ x) green red → refl ; (inj₁ x) blue red → refl
                 ; (inj₁ x) red green → refl ; (inj₁ x) green green → refl ; (inj₁ x) blue green → refl
                 ; (inj₁ x) red blue → refl ; (inj₁ x) green blue → refl ; (inj₁ x) blue blue → refl

                 ; (inj₂ (inj₁ x)) red red → refl ; (inj₂ (inj₁ x)) green red → refl ; (inj₂ (inj₁ x)) blue red → refl
                 ; (inj₂ (inj₁ x)) red green → refl ; (inj₂ (inj₁ x)) green green → refl ; (inj₂ (inj₁ x)) blue green → refl
                 ; (inj₂ (inj₁ x)) red blue → refl ; (inj₂ (inj₁ x)) green blue → refl ; (inj₂ (inj₁ x)) blue blue → refl

                 ; (inj₂ (inj₂ y)) red red → refl ; (inj₂ (inj₂ y)) green red → refl ; (inj₂ (inj₂ y)) blue red → refl
                 ; (inj₂ (inj₂ y)) red green → refl ; (inj₂ (inj₂ y)) green green → refl ; (inj₂ (inj₂ y)) blue green → refl
                 ; (inj₂ (inj₂ y)) red blue → refl ; (inj₂ (inj₂ y)) green blue → refl ; (inj₂ (inj₂ y)) blue blue → refl}
    }
\end{code}

Note how the \AgdaRecord{∃-Lens} is linear in the size of the enumerated type, including
the proofs, whilst \AgdaRecord{GS-Lens} is quadratic for the function size, and cubic in
the proof size!  Naturally in a tactic-based theorem provers, the proof for
\AgdaField{putput} would likely have hidden this; this is misleading as the tactics
nevertheless generate this large term, as it is what needs to be type-checked.

But the deeper points is that $A ⊎ A ⊎ A$ does not ``contain'' a \AgdaSymbol{Colour},
and yet we can create a lens to get and set it.  The \AgdaRecord{GS-Lens} view makes this
quite mysterious but, in our opinion, the \AgdaRecord{∃-Lens} makes it clear that any
type that we can see \emph{up to isomorphism} can be focused on.

In a way, a ``better'' explanation of \AgdaRecord{∃-Colour-in-A+A+A}
is to remark that the types $⊤ ⊎ ⊤ ⊎ ⊤$ (which we'll call
$\mymathbb{3}$) and \AgdaRecord{Colour} are isomorphic, which leads to
the chains of isomorphisms $A \uplus A \uplus A \simeq A × \mymathbb{3}
\simeq A × \AgdaRecord{Colour}$. This is a strength of the combinator-based
approach to type isomorphisms.

An interesting interpretation of $A \uplus A \uplus A \simeq A × \AgdaRecord{Colour}$
is that we can freely move tagging
of data $A$ with \textit{finite information} between type-level tags and value-level
tags at will.

\subsection{Lenses from reversible circuits}

Consider the following lens, built from a generalized \texttt{cnot} gate:
\begin{code}
  gcnot-equiv : {A B C : Set} → ((A ⊎ B) × (C ⊎ C)) ≃ ((A ⊎ B) × (C ⊎ C))
  gcnot-equiv = factorequiv ● id≃ ⊎≃ (id≃ ×≃ swap₊equiv) ● distequiv

  gcnot-lens : {A B C : Set} → ∃-Lens ((A ⊎ B) × (C ⊎ C))  (C ⊎ C)
  gcnot-lens {A} {B} = lens gcnot-equiv
\end{code}
The above lens is rather unusual in that it dynamically chooses between
passing the $C ⊎ C$ value through as-is or swapped, depending on the first
parameter. The corresponding $\AgdaRecord{GS-Lens}$ would be considerably
more complex to write (and prove correct).

The same can be done with a (generalized) Toffoli gate, which ends up being
controlled by the conjunction of two values instead of just one, but otherwise
introduces no new ideas.

There are quite a few ways to witness the equivalence using an
isomorphism: \[ E = ((A ⊎ B) × (C ⊎ C)) ≃ ((A ⊎ B) × (C ⊎ C)) \]
Recall from Sec. 3 that the level-2 programs are equivalences between
isomorphisms. Indeed, these equivalences can be used to show the
equivalence of different implementations of \AgdaFunction{gcnot-lens}
that use different ways of establishing $E$. More generally the
level-2 equivalences can be used to simplify, optimize, and reason
about lens programs.


%% Level 2 of $\Pi$ lets us look at relations between isomorphisms.
%% In particular, we can see when some lens/prims/etc are simplifiable
%% to something simpler.
%%
%% Note that factor/distrib is crucial to move between them all.

\subsection{Completeness}

The $\Pi$ language is \emph{complete} for equivalences, in the sense that
any two type which can be written as a sum-of-products over arbitrarily many
variables are equivalent if and only if there is a term of $\Pi$ which witnesses
this equivalence.  In other words,

\begin{theorem}
Suppose $S$ and $A$ are two types belonging to the language of the
semiring of types $T\left[x_{1},\ldots,x_{n}\right]$ over $n$ variables.
If $∃C. S ≃ C × A$ is inhabited, then there is a term of $\Pi$ witnessing
the equivalence.
\end{theorem}

\section{Optics}

Lenses have been generalized -- and in keeping with the theme, have been
named \emph{optics}. The immediate dual to lens is \emph{prism}, which
we will dig into a little. We will follow this by general remarks on
other optics, as the precise development follows a clear pattern.

\subsection{Prism}

Prisms are dual to lenses in that they arise from exchanging product ($×$)
with coproduct ($⊎$). In other words, a prism is $∃C. S ≃ C ⊎ A$, giving us
\AgdaRecord{Prism₁} (straightforward definition elided). We can mimick
the definitions used for lens for all.

\AgdaHide{
\begin{code}
record Prism₁ {ℓ : Level} (S : Set ℓ) (A : Set ℓ) : Set (suc ℓ) where
  constructor prism₁
  field
    {C} : Set ℓ
    iso : S ≃ (C ⊎ A)
\end{code}
}

But let us instead take this opportunity to do a rational reconstruction of
the usual interface to a prism.  Suppose that we have prism $∃C. S ≃ C ⊎ A$
in hand, then:
\begin{itemize}
\item Given just an $S$, what can we get? Running the isomorphism
forward, we can obtain a $C ⊎ A$ -- but that is unsatisfactory as $C$ is supposed
to be hidden. We can however \emph{squash} $C$ to obtain a $\AgdaRecord{Maybe} A$.
\item Given just an $A$? We can run the isomorphism backwards to get an $S$.
\item Given both an $A$ and an $S$ does not provide any new opportunities.
\end{itemize}

It is common to describe prisms in terms of \emph{pattern matching}. This is
adequate when the isomorphism embedded in a prism is a ``refocusing'' of
a member of a sum type -- but less so with a non-trivial isomorphism. The
formulation as $∃C. S ≃ C ⊎ A$ instead suggests that a prism is a
\emph{partition} view of $S$; we will thus choose to use \AgdaField{belongs}
and \AgdaField{inject} as field names, rather than (respectively)
\AgdaField{preview} and \AgdaField{review} as is common in Haskell implementations.
As with the fields of the interface, we can reconstruct the laws by attempting
various (legal) compositions. Putting all of this together, we get:
\begin{code}
record BI-Prism {ℓs ℓa : Level} (S : Set ℓs) (A : Set ℓa) : Set (ℓs ⊔ ℓa) where
  field
    belongs    : S → Maybe A
    inject     : A → S
    belongsinject : (a : A) → belongs (inject a) ≡ just a
    belongs≡just→inject : (s : S) → (a : A) → (belongs s ≡ just a → inject a ≡ s)
\end{code}

From this, we can again prove soundness:
\begin{code}
module _ {ℓ : Level} (S A : Set ℓ) where
  prism-sound₁ : Prism₁ S A → BI-Prism S A
  prism-sound₁ (prism₁ (f , qinv g α β) ) = record
    { belongs = λ s → [ const nothing , just ]′ (f s)
    ; inject = g ∘ inj₂
    ; belongsinject = λ _ → cong ([ _ , _ ]′) (α _)
    ; belongs≡just→inject = refine
    }
    where
      refine : (t : S) → (a : A) → [ const nothing , just ]′ (f t) ≡ just a → g (inj₂ a) ≡ t
      refine s b pf with f s | inspect f s
      refine s b () | inj₁ x | _
      refine s _ refl | inj₂ y | [ eq ] = trans (cong g (sym eq)) (β s)
\end{code}
\noindent where injectivity of constructors is used in a crucial way.
The combinator \AgdaFunction{[\_,\_]′} for $⊎$ is akin to Haskell's \texttt{either}.
The details of the $\AgdaFunction{refine}$ implementation rely on
\emph{injectivity of constructors} to reject impossible cases.

But, as with lens, this is not quite complete. We thus upgrade the
definition in the same way:
\begin{code}
record ∃-Prism {ℓ : Level} (S : Set ℓ) (A : Set ℓ) : Set (suc ℓ) where
  constructor ∃-prism
  field
    {C} : Setoid ℓ ℓ
    iso : Inverse (P.setoid S) (C ⊎S (P.setoid A))

prism : {ℓ : Level} {S A C : Set ℓ} → S ≃ (C ⊎ A) → ∃-Prism S A
prism {S = S} {A} {C} (f , qinv g α β) = ∃-prism {C = P.setoid C} (record
  { to = record { _⟨$⟩_ = f ; cong = cong-f }
  ; from = record { _⟨$⟩_ = g ; cong = cong-g }
  ; inverse-of = record
    { left-inverse-of = β
    ; right-inverse-of = λ { (inj₁ x) → Setoid.reflexive Z (α (inj₁ x))
                           ; (inj₂ y) → Setoid.reflexive Z (α (inj₂ y))}
    }
  })
  where
    Z = P.setoid C ⊎S P.setoid A
    cong-f : {i j : S} → i ≡ j → (P.setoid C ≈S P.setoid A) (f i) (f j)
    cong-f {i} {.i} refl with f i
    cong-f {i} {.i} refl | inj₁ x = refl
    cong-f {i} {.i} refl | inj₂ y = refl
    cong-g : {i j : C ⊎ A} → (P.setoid C ≈S P.setoid A) i j → g i ≡ g j
    cong-g {inj₁ x} {inj₁ .x} refl = refl
    cong-g {inj₁ x} {inj₂ y} (lift ())
    cong-g {inj₂ y} {inj₁ x} (lift ())
    cong-g {inj₂ y} {inj₂ .y} refl = refl
\end{code}
The principal reason for including all of this code is to show that
there are rather substantial differences in the details. Where
$\eta$ for products was crucial before, here injectivity of
$\AIC{inj₁}$ and $\AIC{inj₂}$ play a similar role.

From this, we can then prove a new soundness result as well as a completeness
result.  The full details are omitted as they are quite lengthy. The main
component is the computation of the ``other'' component, corresponding
roughly to $S - A$, which is the \AgdaRecord{Setoid} with
\AgdaField{Carrier}~$\Sigma S (λ s → \AIC{belongs} bi s ≡ \AIC{nothing})$
and equivalence on the first field. This is roughly equivalent to what
Grenrus showed~\cite{oleg-blog}, but without the need for proof irrelevance
in the meta-theory, as we build it in to our \AgdaRecord{Setoid} instead.

\AgdaHide{
\begin{code}
prism-sound′ : {ℓ : Level} {S A : Set ℓ} → ∃-Prism S A → BI-Prism S A
prism-sound′ {S = S} {A} (∃-prism p) =
  let f = to p ⟨$⟩_
      g = from p ⟨$⟩_ in record
    { belongs = λ s → [ const nothing , just ]′ (f s)
    ; inject = g ∘ inj₂
    ; belongsinject = bi
    ; belongs≡just→inject = refine
    }
    where
      bi : (a : A) → [ const nothing , just ]′ (to p ⟨$⟩ (from p ⟨$⟩ inj₂ a)) ≡ just a
      bi a with to p ⟨$⟩ (from p ⟨$⟩ inj₂ a) | right-inverse-of p (inj₂ a)
      bi a | inj₁ x | lift ()
      bi a | inj₂ y | pf = cong just pf
      refine : (s : S) (a : A) → [ const nothing , just ]′ (to p ⟨$⟩ s) ≡ just a →
                         from p ⟨$⟩ inj₂ a ≡ s
      refine s a pf with to p ⟨$⟩ s | inspect (to p ⟨$⟩_) s
      refine s a () | inj₁ x | _
      refine s .y refl | inj₂ y | [ eq ] = trans (cong (from p ⟨$⟩_) (sym eq)) (left-inverse-of p s)

prism-complete : {ℓ : Level} {S A : Set ℓ} → BI-Prism S A → ∃-Prism S A
prism-complete {ℓ} {S} {A} bi = ∃-prism {C = D} (record
  { to = record { _⟨$⟩_ = fwd ; cong = λ { refl → Setoid.reflexive Z (cong fwd refl) } }
  ; from = record { _⟨$⟩_ = bwd ; cong = λ {i} {j} → cong-bwd {i} {j} }
  ; inverse-of = record
    { left-inverse-of = left
    ; right-inverse-of = right
    } })
  where
    open BI-Prism
    D : Setoid ℓ ℓ
    D = record
      { Carrier = Σ S (λ s → belongs bi s ≡ nothing)
      ; _≈_ = λ x y → proj₁ x ≡ proj₁ y
      ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
      }
    Z = D ⊎S P.setoid A
    fwd : (x : S) → Σ S (λ s → belongs bi s ≡ nothing) ⊎ A
    fwd x with belongs bi x | inspect (belongs bi) x
    fwd x | just x₁ | _ = inj₂ x₁
    fwd x | nothing | [ eq ] = inj₁ (x , eq)
    bwd : (x : Σ S (λ s → belongs bi s ≡ nothing) ⊎ A) → S
    bwd (inj₁ (s , pf))  = s
    bwd (inj₂ a)         = inject bi a
    cong-bwd : {i j : Σ S (λ s → belongs bi s ≡ nothing) ⊎ A} → Setoid._≈_ Z i j → bwd i ≡ bwd j
    cong-bwd {inj₁ x} {inj₁ x₁} ≈ = ≈
    cong-bwd {inj₁ x} {inj₂ y} (lift ())
    cong-bwd {inj₂ y} {inj₁ x} (lift ())
    cong-bwd {inj₂ y} {inj₂ y₁} ≈ = cong (inject bi) ≈
    left : (x : S) → bwd (fwd x) ≡ x
    left x with belongs bi x | inspect (belongs bi) x
    left x | just x₁ | [ eq ] = belongs≡just→inject bi x x₁ eq
    left x | nothing | [ eq ] = refl
    contra : {Y : Set ℓ} {y : Y} → (Maybe {ℓ} Y ∋ nothing)  ≡ (Maybe Y ∋ just y) → ⊥
    contra ()
    right : (x : Σ S (λ s → belongs bi s ≡ nothing) ⊎ A) → Setoid._≈_ Z (fwd (bwd x))  x
    right (inj₁ x) with belongs bi (proj₁ x) | inspect (belongs bi) (proj₁ x)
    right (inj₁ (s , snd)) | just x₁ | [ eq ] = lift (contra (trans (sym snd) eq))
    right (inj₁ x) | nothing | yyy = refl
    right (inj₂ y) with belongs bi (inject bi y) | inspect (belongs bi) (inject bi y)
    right (inj₂ y) | just x | [ eq ] = just-injective (trans (sym eq) (belongsinject bi y))
    right (inj₂ y) | nothing | [ eq ] = lift (contra (trans (sym eq) (belongsinject bi y)))
\end{code}
}
Note that there is one more way, again equivalent, of defining a prism:
rather than using $\AgdaRecord{Maybe} A$, use $S ⊎ A$ and replace
$\AgdaField{belongs}$ with
$λ s → \AgdaFunction{Data.Sum.map} (\AgdaFunction{const} s) \AgdaFunction{id} (f s)$.

\subsection{Other Optics}

A number of additional optics have been put forth. Their salient
properties can be contrasted in the following table which lists the relation between the source and the view in each case:

\medskip
\begin{figure}[h]
\begin{center}\begin{tabular}{ll}\hline
Equality & $S = A$ \\ \hline
Iso & $S ≃ A$ \\ \hline
Lens & $∃C. S ≃ C × A$ \\
Prism & $∃C . S ≃ C + A$ \\
Achroma & $∃C. S ≃ ⊤ ⊎ (C × A)$ \\
Affine & $∃C, D. S ≃ D ⊎ (C × A)$ \\ \hline
Grate & $∃I. S ≃ I → A$ \\ \hline
Setter & $∃ F : \mathit{Set} → \mathit{Set}. S ≃ F A$ \\ \hline
\end{tabular}\end{center}
\caption{A variety of optics}
\label{fig:optics}
\end{figure}

The names used are as found in various bits of the
literature~\cite{oleg-blog,achromatic,affine,grate}. A line is drawn
when the language is extended.  Equality is sometimes called Adapter:
it merely witnesses equi-inhabitation of $S$ and $A$ without any
requirements that the witnessing functions are in any way
related. Iso, short for Isomorphism, is exactly type equivalence.
Then we have Lens and Prism, as well as two new ones:
Achroma~\cite{achromatic} and Affine~\cite{affine}. This latter
construction is the most general. Using it, we obtain:
\begin{itemize}
\item Lens when $D = ⊥$,
\item Prism when $C = ⊤$,
\item Achroma when $D = ⊤$,
\item Iso when $D = ⊥$ and $C = ⊤$.
\end{itemize}
Specializing $C$ to $⊤$ in Affine does not give anything useful, as it
ignores $A$ and just says that $S$ is isomorphic to \emph{something},
which is a tautology (as $D$ can be taken to be $S$ itself).

Grate~\cite{grate} moves us to a rather different world, one that
involves function types. And Setter is more general still, where all
we know is that $S$ is isomorphic to some \emph{container} of $A$s.

%% \jc{What are the other optics?}

\section{Discussion}

\subsection{Categorical approaches}

So why all the complications with \texttt{Profunctor}? Basically, that is mostly
Haskell-isms: by relying on \emph{Free Theorems}, one can get the type system to
reject a lot of ill-formed lenses, though, of course, not all. Optics, in Agda and
using equivalences turn out to be \emph{simpler}, not harder!

Another thread is via the Yoneda lemma. Of course, one can see this here too:
the existentials correspond to a co-end, and the isomorphisms are exactly what is
in the Hom-set. But we get more mileage from looking ``under the hood'' to see
the fundamental \textbf{programming language} underlying Optics, rather than jumping
to abstractions too early.

\subsection{Laws}

Why do lenses have 3 laws but equivalences have two?  Because the functions that
make up lenses have 3 laws --- the products have η. And the proof of setset uses it.
Why do prisms have 2 laws then? They should have 3 as well: the 2nd law really ought to
be a logical equivalence; injectivity of constructors is the 3rd law involve in prism.

Why do some bidirectional programming eschew the setset law? Basically because they want
to hide one more component in their lens: a $C → C$ function that is applied on
\AgdaField{set}. For example, this allows a ``logging'' implementation to be lawful.

\subsection{Geometry of types}

Lens is a cartesian factoring.  Prism is a partition.

Note that we should really view $S$ as a sort of curve 2-dimensional type, while
$C × A$ is our cartesian, 2-dimensional version. $C$ doesn't depend on $A$, which is
why the name \emph{constant complement} is quite apt.  A Lens is a change of coordinates
that allows one to see $A$ as a cartesian projection. Similarly, a Prism is a
change of coordinates that shuffles all of $A$ ``to the right''.

\section{Conclusion}

\bibliographystyle{alpha}
\bibliography{cites,cites2}
%inline the .bbl file directly for mailing to authors.

\end{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Stuff cut out from above.

\subsection{A Language of Type Equivalences}

\begin{figure}[t]
\[
\begin{array}{rrcll}
\idc :& t & \iso & t &: \idc \\
\\
\identlp :&  0 \sumtype t & \iso & t &: \identrp \\
\swapp :&  t_1 \sumtype t_2 & \iso & t_2 \sumtype t_1 &: \swapp \\
\assoclp :&  t_1 \sumtype (t_2 \sumtype t_3) & \iso & (t_1 \sumtype t_2) \sumtype t_3 &: \assocrp \\
\\
\identlt :&  1 {\prodtype} t & \iso & t &: \identrt \\
\swapt :&  t_1 {\prodtype} t_2 & \iso & t_2 {\prodtype} t_1 &: \swapt \\
\assoclt :&  t_1 {\prodtype} (t_2 {\prodtype} t_3) & \iso & (t_1 {\prodtype} t_2) {\prodtype} t_3 &: \assocrt \\
\\
\absorbr :&~ 0 {\prodtype} t & \iso & 0 ~ &: \factorzl \\
\dist :&~ (t_1 \sumtype t_2) {\prodtype} t_3 & \iso & (t_1 {\prodtype} t_3) \sumtype (t_2 {\prodtype} t_3)~ &: \factor
\end{array}
\]
\caption{$\Pi$-terms.}
\label{pi-terms}
\end{figure}

This gives us the denotational semantics for types and for
equivalences. From this, we want to
a programming language, which we call $\Pi$,
where we have ground terms whose denotation are
all $16$ type isomorphisms of Fig.~\ref{type-isos}.
We can simply do this literally. To make the
analogy with commutative semirings stand out even more, we will use
$0, 1, \sumtype$, and ${\prodtype}$ at the type level, and will denote
``equivalence'' by $\iso$.  Thus Fig.~\ref{pi-terms} shows the
``constants'' of the language.  As these all come in symmetric pairs
(some of which are self-symmetric), we give names for both directions.
Note how we have continued with the spirit of Curry-Howard: the terms
of $\Pi$ are \emph{proof terms}, but rather than being witnesses of
inhabitation, they are witnesses of equivalences. Thus we get an
unexpected programming language design:

\begin{center}
\fbox{ The proof terms denoting commutative semiring equivalences
  induce the terms of $\Pi$.}
\end{center}
\vspace*{3mm}

\begin{figure}[t]
\[
\Rule{}
{\jdg{}{}{c_1 : t_1 \iso t_2} \quad \vdash c_2 : t_2 \iso t_3}
{\jdg{}{}{c_1 \odot c_2 : t_1 \iso t_3}}
{}
\qquad
\Rule{}
{\jdg{}{}{c_1 : t_1 \iso t_2} \quad \vdash c_2 : t_3 \iso t_4}
{\jdg{}{}{c_1 \oplus c_2 : t_1 \sumtype t_3 \iso t_2 \sumtype t_4}}
{}
\]
\[
\Rule{}
{\jdg{}{}{c_1 : t_1 \iso t_2} \quad \vdash c_2 : t_3 \iso t_4}
{\jdg{}{}{c_1 \otimes c_2 : t_1 {\prodtype} t_3 \iso t_2 {\prodtype} t_4}}
{}
\]
\caption{$\Pi$-combinators.}
\label{pi-combinators}
\end{figure}

\noindent
Of course, one does not get a programming language with just typed
constants! We need to put together multiple equivalences to form
other equivalences. There are
in fact three ways to do this: sequential composition $\odot$, choice
composition $\oplus$ (sometimes called juxtaposition), and parallel
composition $\otimes$. See Fig.~\ref{pi-combinators} for the
signatures. The construction $c_1 \odot c_2$ corresponds to performing
$c_1$ first, then $c_2$, and is the usual notion of composition.
The construction $c_1 \oplus c_2$ chooses to
perform $c_1$ or $c_2$ depending on whether the input is labelled
$\textsf{left}$ or $\textsf{right}$ respectively. Finally the
construction $c_1 \otimes c_2$ operates on a product structure, and
applies $c_1$ to the first component and $c_2$ to the second.

\begin{figure}[t]
\[
\Rule{}
{\jdg{}{}{c_1 : t_1 \iso t_2}}
{\jdg{}{}{\ !\ c_1 : t_2 \iso t_1}}
{}
\]
\caption{Derived $\Pi$-combinator.}
\label{derived-pi-combinator}
\end{figure}

Embedded in our definition of $\Pi$ is a conscious design decision: to make the
terms of $\Pi$ \emph{syntactically} reversible. In other words, to
every $\Pi$ constant, there is another $\Pi$ constant which is its
inverse. As this is used frequently, we give it the short name $!$,
and its type is given in Fig.~\ref{derived-pi-combinator}. This
combinator is \emph{defined}, by pattern matching on the syntax of
its argument and structural recursion.
This is not the only choice.  Another would be to add a
$\mathit{flip}$ combinator to the language; we could then remove
quite a few combinators as redundant. The drawback is that many
programs in $\Pi$ become longer. Furthermore, some of the symmetry
at ``higher levels'' (see next section) is also lost. Since the
extra burden of language definition and of proofs is quite low, we
prefer the structural symmetry over a minimalistic language definition.

\begin{figure}[t]
\[
\begin{array}{rrcll}
\identlsp :&  t \sumtype 0 & \iso & t &: \identrsp \\
\identlst :&  t {\prodtype} 1 & \iso & t &: \identrst \\
\\
\absorbl :&~ t {\prodtype} 0 & \iso & 0 ~ &: \factorzr \\
\distl :&~ t_1 {\prodtype} (t_2 \sumtype t_3) & \iso & (t_1 {\prodtype} t_2) \sumtype (t_1 {\prodtype} t_3)~ &: \factorl
\end{array}
\]
\caption{Additional $\Pi$-terms.}
\label{more-pi}
\end{figure}

We also make a second design decision, which is to make the $\Pi$
language itself symmetric in another sense: we want both left
and right introduction/elimination rules for units, $0$ absorption
and distributivity. Specifically, we add the $\Pi$-terms of
Fig.~\ref{more-pi} to our language. These are redundant because
of $\swapp$ and $\swapt$, but will later enable shorter programs
and more elegant presentation of program transformations.

%%%%%%%%%
\subsection{Operational Semantics}
\label{sec:opsem}

It is then quite straightforward to give an operational semantics to
$\Pi$: we write a ``forward evaluator'' which, given a
program program \ensuremath{c : b_1 \leftrightarrow b_2} in \ensuremath{\Pi },
and a value \ensuremath{ v_1 : b_1}, returns a value of type $b_2$. Of course,
what makes $\Pi$ interesting is that we can also write a ``backward
evaluator'' from values of type $b_2$ to values of type $b_1$. Furthermore
we can prove that these are exact inverses. Given our denotational semantics,
this should not be surprising. As the details are straightforward but
verbose, we elide them. As we mentioned before, $!$ is a defined combinator.
Only a few cases need commenting on.

Since there are no values that have the type \ensuremath{0}, the
reductions for the combinators \identlp, \identrp, \identlsp, and
\identrsp\ omit the impossible cases. \factorzr\ and \factorzl\
likewise do not appear as they have no possible cases at all. However,
\absorbr\ and \absorbl\ are treated slightly differently: rather than
\emph{eagerly} assuming they are impossible, the purported inhabitant
of $0$ given on one side is passed on to the other side. The reason
for this choice will have to wait for Sec.~\ref{langeqeq} when we
explain some higher-level symmetries (see Fig.~\ref{figc}).

%%%%%%%%%
\subsection{Further features}

The language $\Pi$ also captures ideas around the size of types, aka
cardinality, and their relation to type equivalences.

Combinators of \ensuremath{\Pi } can be written in terms of the
operators described previously or via a graphical language similar in
spirit to those developed for Geometry of Interaction
\cite{DBLP:conf/popl/Mackie95} and string diagrams for category
theory~\cite{BLUTE1996229,selinger-graphical}.
\ensuremath{\Pi } combinators expressed in this graphical language
look like ``wiring diagrams.'' Values take the form of ``particles''
that flow along the wires. Computation is expressed by the flow of
particles.

The interested reader can
find more details for both features in~\cite{CaretteJamesSabryArxiv}.

Lastly, in previous work~\cite{Carette2016}, we had shown that
the denotational and operational semantics correspond, and given
a constructive proof of this. In other words, to each $\Pi$
combinator we can associate an equivalence between the denotation
of each type, which has all the obvious desirable properties we
would want from such an association.

%%%%%%%%%
\subsection{A Language of Equivalences between Type Equivalences}
\label{langeqeq}

As motivated in the previous section, the equivalences between type
equivalences are perfectly modeled by the coherence conditions of weak
Rig Groupoids. Syntactically, we take the easiest way there: simply
make every coherence isomorphism into a programming construct. These
constructs are collected in several figures (Fig.~\ref{figj} to
Fig.~\ref{figa}). We present these without much comment as this
would take us too far afield. \jc{cite}

Conveniently, the various coherence conditions can be naturally
grouped into ``related'' laws.  Each group basically captures the
interactions between compositions of level-1 $\Pi$ combinators.

\begin{figure}[t]
Let $c_1 : t_1 \leftrightarrow t_2$, $c_2 : t_3 \leftrightarrow t_4$, $c_3 : t_1 \leftrightarrow t_2$, and $c_4 : t_3 \leftrightarrow t_4$. \\
Let $a_1 : t_5 \leftrightarrow t_1$,  $a_2 : t_6 \leftrightarrow t_2$, $a_3 : t_1 \leftrightarrow t_3$, and $a_4 : t_2 \leftrightarrow t_4$.
\[\def\arraystretch{1.3}
\begin{array}{c}
\Rule{}
  {c_1 \Leftrightarrow c_3 \quad c_2 \Leftrightarrow c_4}
  {c_1 \oplus c_2 \Leftrightarrow c_3 \oplus c_4}
  {}
\qquad
\Rule{}
  {c_1 \Leftrightarrow c_3 \quad c_2 \Leftrightarrow c_4}
  {c_1 \otimes c_2 \Leftrightarrow c_3 \otimes c_4}
  {}
\\
  {(a_1 \odot a_3) \oplus (a_2 \odot a_4) \Leftrightarrow (a_1 \oplus a_2) \odot (a_3 \oplus a_4)}
\\
  {(a_1 \odot a_3) \otimes (a_2 \odot a_4) \Leftrightarrow (a_1 \otimes a_2) \odot (a_3 \otimes a_4)}
\end{array}\]
\caption{\label{fige}Signatures of level-2 $\Pi$-combinators: functors}
\end{figure}

\begin{figure}[t]
Let $c_1 : t_1 \leftrightarrow t_2$,  $c_2 : t_2 \leftrightarrow t_3$, and $c_3 : t_3 \leftrightarrow t_4$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {c_1 \odot (c_2 \odot c_3) \Leftrightarrow (c_1 \odot c_2) \odot c_3}
\\
  {(c_1 \oplus (c_2 \oplus c_3)) \odot \assoclp \Leftrightarrow \assoclp \odot ((c_1 \oplus c_2) \oplus c_3)}
\\
  {(c_1 \otimes (c_2 \otimes c_3)) \odot \assoclt \Leftrightarrow \assoclt \odot ((c_1 \otimes c_2) \otimes c_3)}
\\
  {((c_1 \oplus c_2) \oplus c_3) \odot \assocrp \Leftrightarrow \assocrp \odot (c_1 \oplus (c_2 \oplus c_3))}
\\
  {((c_1 \otimes c_2) \otimes c_3) \odot \assocrt \Leftrightarrow \assocrt \odot (c_1 \otimes (c_2 \otimes c_3))}
\\
  {\assocrp \odot \assocrp \Leftrightarrow ((\assocrp \oplus \idc) \odot \assocrp) \odot (\idc \oplus \assocrp)}
\\
  {\assocrt \odot \assocrt \Leftrightarrow ((\assocrt \otimes \idc) \odot \assocrt) \odot (\idc \otimes \assocrt)}
\end{array}\]
\caption{\label{figj}Signatures of level-2 $\Pi$-combinators: associativity}
\end{figure}

The bottom line in Fig.~\ref{figj} is actually a linear
restatement of the famous ``pentagon diagram'' stating a
particular coherence condition for monoidal categories~\cite{KELLY197197}.
To make the relation between $\Pi$ as a language and the
language of category theory, the figure below displays
the same morphism but in categorical terms.

\begin{center}
\begin{tikzcd}[column sep=normal]
   & (A \times (B \times C)) \times D \arrow [dr, "\assocrt"] & \\
((A \times B) \times C) \times D \arrow [ur, "\assocrt \otimes \mathit{id}\leftrightarrow"]
   \arrow [d, "\assocrt"] &
       & A \times ((B \times C) \times D) \arrow [d, "\mathit{id}\leftrightarrow \otimes \assocrt" ]\\
(A \times B) \times (C \times D) \arrow [rr, "\assocrt"] & & A \times (B \times (C \times D))
\end{tikzcd}
\end{center}

\begin{figure}[t]
Let $c_1 : t_1 \leftrightarrow t_2$, $c_2 : t_3 \leftrightarrow t_4$, and $c_3 : t_5 \leftrightarrow t_6$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {((c_1 \oplus c_2) \otimes c_3) \odot \dist \Leftrightarrow \dist \odot ((c_1 \otimes c_3) \oplus (c_2 \otimes c_3))}
\\
  {(c_1 \otimes (c_2 \oplus c_3)) \odot \distl \Leftrightarrow \distl \odot ((c_1 \otimes c_2) \oplus (c_1 \otimes c_3))}
\\
  {((c_1 \otimes c_3) \oplus (c_2 \otimes c_3)) \odot \factor \Leftrightarrow \factor \odot ((c_1 \oplus c_2) \otimes c_3)}
\\
  {((c_1 \otimes c_2) \oplus (c_1 \otimes c_3)) \odot \factorl \Leftrightarrow \factorl \odot (c_1 \otimes (c_2 \oplus c_3))}
\end{array}\]
\caption{\label{figi}Signatures of level-2 $\Pi$-combinators: distributivity and factoring}
\end{figure}

\begin{figure}[t]
Let $c_0, c_1, c_2, c_3 : t_1 \leftrightarrow t_2$ and $c_4, c_5 : t_3 \leftrightarrow t_4$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {\idc \odot \, c_0 \Leftrightarrow c_0}
\quad
  {c_0 \, \odot \idc \, \Leftrightarrow c_0}
\quad
  {c_0\,\, \odot\,!\, c_0 \Leftrightarrow \idc}
\quad
  {!\, c_0 \odot c_0 \Leftrightarrow \idc}
\\
  {\idc \oplus \, \idc \, \Leftrightarrow \idc}
\qquad
  {\idc \otimes \, \idc \, \Leftrightarrow \idc}
\\
  {c_0 \Leftrightarrow c_0}
\quad
\Rule{}
  {c_1 \Leftrightarrow c_2 \quad c_2 \Leftrightarrow c_3}
  {c_1 \Leftrightarrow c_3}
  {}
\quad
\Rule{}
  {c_1 \Leftrightarrow c_4 \quad c_2 \Leftrightarrow c_5}
  {c_1 \odot c_2 \Leftrightarrow c_4 \odot c_5}
  {}
\end{array}\]
\caption{\label{figh}Signatures of level-2 $\Pi$-combinators: identity and composition}
\end{figure}

\begin{figure}[t]
Let $c_0 : 0 \leftrightarrow 0$, $c_1 : 1 \leftrightarrow 1$, and $c_3 : t_1 \leftrightarrow t_2$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {\identlp \odot c_3 \Leftrightarrow (c_0 \oplus c_3) \odot \identlp}
\qquad
  {\identrp \odot (c_0 \oplus c_3) \Leftrightarrow c_3 \odot \identrp}
\\
  {\identlsp \odot c_3 \Leftrightarrow (c_3 \oplus c_0) \odot \identlsp}
\qquad
  {\identrsp \odot (c_3 \oplus c_0) \Leftrightarrow c_3 \odot \identrsp}
\\
  {\identlt \odot c_3 \Leftrightarrow (c_1 \otimes c_3) \odot \identlt}
\qquad
  {\identrt \odot (c_1 \otimes c_3) \Leftrightarrow c_3 \odot \identrp}
\\
  {\identlst \odot c_3 \Leftrightarrow (c_3 \otimes c_1) \odot \identlst}
\qquad
  {\identrst \odot (c_3 \otimes c_1) \Leftrightarrow c_3 \odot \identrst}
\\
  {\identlt \Leftrightarrow \distl \odot (\identlt \oplus \identlt)}
\\
\identlp \Leftrightarrow \swapp \odot \identlsp
\qquad
\identlt \Leftrightarrow \swapt \odot \identlst
\end{array}\]
\caption{\label{figg}Signatures of level-2 $\Pi$-combinators: unit}
\end{figure}

The constructs in Fig.~\ref{figg} may at first blush look similarly straightforward,
but deserve some pause. One obvious question: What is the point of
$c_0 : 0 \leftrightarrow 0$, isn't it just the identity combinator $\idc$
for $A = 0$ (as defined in Fig.~\ref{type-isos})? Operationally, $c_0$
is indeed indistinguishable from $\idc$. However, there are multiple syntactic
ways of writing down combinators of type $0 \leftrightarrow 0$, and the
first combinator in Fig.~\ref{figg} applies to all of them uniformly.
This is another subtle aspect of coherence: all reasoning must be valid for
all possible models, not just the one we have in mind. So even though
operational reasoning may suggest that some relations \emph{may} be
true between combinators, it can also mislead. The same reasoning
applies to $c_1 : 1 \leftrightarrow 1$.  The first $8$ combinators can
then be read as basic coherence for unit introduction and elimination,
in both additive and multiplicative cases.

\begin{figure}[t]
Let $c_1 : t_1 \leftrightarrow t_2$ and $c_2 : t_3 \leftrightarrow t_4$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {\swapp \odot (c_1 \oplus c_2) \Leftrightarrow (c_2 \oplus c_1) \odot \swapp}
\quad
  {\swapt \odot (c_1 \otimes c_2) \Leftrightarrow (c_2 \otimes c_1) \odot \swapt}
\\
  {(\assocrp \odot \swapp) \odot \assocrp \Leftrightarrow ((\swapp \oplus \idc) \odot \assocrp) \odot (\idc \oplus \swapp)}
\\
  {(\assoclp \odot \swapp) \odot \assoclp \Leftrightarrow ((\idc \oplus \swapp) \odot \assoclp) \odot (\swapp \oplus \idc)}
\\
  {(\assocrt \odot \swapt) \odot \assocrt \Leftrightarrow ((\swapt \otimes \idc) \odot \assocrt) \odot (\idc \otimes \swapt)}
\\
  {(\assoclt \odot \swapt) \odot \assoclt \Leftrightarrow ((\idc \otimes \swapt) \odot \assoclt) \odot (\swapt \otimes \idc)}
\end{array}\]
\caption{\label{figf}Signatures of level-2 $\Pi$-combinators: commutativity and associativity}
\end{figure}

\begin{figure}[t]
\[\def\arraystretch{1.3}
\begin{array}{c}
  {\identlsp \oplus \idc ~\Leftrightarrow~ \assocrp \odot (\idc \oplus \, \identlp)}
\\
  {\identlst \otimes \idc ~\Leftrightarrow~ \assocrt \odot (\idc \otimes \, \identlt)}
\end{array}\]
\caption{\label{figd}Signatures of level-2 $\Pi$-combinators: unit and associativity}
\end{figure}

\begin{figure}[t]
Let $c : t_1 \leftrightarrow t_2$:
\[\def\arraystretch{1.3}
\begin{array}{c}
  {(c \otimes \idc) \odot \absorbl \Leftrightarrow \absorbl \odot \idc}
\quad
  {(\idc \, \otimes c) \odot \absorbr \Leftrightarrow \absorbr \odot \idc}
\\
  {\idc \odot \, \factorzl \Leftrightarrow \factorzl \odot (\idc \otimes c)}
\quad
  {\idc \odot \, \factorzr \Leftrightarrow \factorzr \odot (c \otimes \idc)}
\\
  {\absorbr \Leftrightarrow \absorbl}
\\
  {\absorbr \Leftrightarrow (\distl \odot (\absorbr \oplus \absorbr)) \odot \identlp}
\\
  {\identlst \Leftrightarrow \absorbr}
\qquad
  {\absorbl \Leftrightarrow \swapt \odot \absorbr}
\\
  {\absorbr \Leftrightarrow (\assoclt \odot (\absorbr \otimes \idc)) \odot \absorbr}
\\
  {(\idc \otimes \absorbr) \odot \absorbl \Leftrightarrow (\assoclt \odot (\absorbl \otimes \idc)) \odot \absorbr}
\\
  {\idc \otimes \, \identlp \Leftrightarrow (\distl \odot (\absorbl \oplus \idc)) \odot \identlp}
\end{array}\]
\caption{\label{figc}Signatures of level-2 $\Pi$-combinators: zero}
\end{figure}

The constructs in Fig.~\ref{figc} are significantly more subtle, as they
deal with combinators involving $0$, aka an impossibility.  For example,
\[  {(c \otimes \idc_{0}) \odot \absorbl \Leftrightarrow \absorbl \odot \idc_{0}}
\]
(where we have explicitly annotated the types of $\idc$ for increased clarity)
tells us that of the two ways of transforming from $t_1  *\  0$ to $0$,
namely first doing some arbitrary transformation $c$ from $t_1$ to $t_2$ and
(in parallel) leaving $0$ alone then eliminating $0$, or first eliminating $0$
then doing the identity (at $0$), are equivalent. This is the ``naturality'' of
$\absorbl$. One item to note is the fact that this combinator is not
irreducible, as the $\idc$ on the right can be eliminated. But that is actually
a property visible at an even higher level (which we will not touch in this
paper).  The next $3$ are similarly expressing the naturality of $\absorbr$,
$\factorzl$ and $\factorzr$.

The next combinator, $\absorbr \Leftrightarrow \absorbl$, is
particularly fascinating: while it says something simple --- that the
two obvious ways of transforming $0 * 0$ into $0$, namely absorbing
either the left or right $0$ --- it implies something subtle.  A
straightforward proof of $\absorbl$ which proceeds by saying that
$0 * t$ cannot be inhabited because the first member of the pair
cannot, is not in fact equivalent to $\absorbr$ on $0 * 0$.  However,
if we instead define $\absorbl$ to ``transport'' the putative
impossible first member of the pair to its (equally impossible)
output, then these do form equivalent pairs.

There are further subtle issues when the types
involved are asymmetric: they do not have the same occurrences
on the left and right. Such cases are particularly troublesome for
finding normal forms. Laplaza~\cite{laplaza72} certainly comments on this,
but in mostly terse and technical terms. Blute et al.~\cite{BLUTE1996229}
offer much more intuitive explanations.

\begin{figure}[t]
\[\def\arraystretch{1.3}
\begin{array}{c}
  {((\assoclp \otimes \idc) \odot \dist) \odot (\dist \oplus \idc) \Leftrightarrow (\dist \odot (\idc \oplus \dist)) \odot \assoclp}
\\
  {\assoclt \odot \distl \Leftrightarrow ((\idc \otimes \distl) \odot \distl) \odot (\assoclt \oplus \assoclt)}
\end{array}\]
\vspace{ -0.5em}
\[\def\arraystretch{1.3}
\begin{array}{rcl}
  (\distl \odot (\dist \oplus \dist)) \odot \assoclp &\Leftrightarrow&
   \dist \odot (\distl \oplus \distl) \odot \assoclp ~\odot \\
&& (\assocrp \oplus \idc) ~\odot \\
&& ((\idc \oplus \swapp) \oplus \idc) ~\odot \\
&&      (\assoclp \oplus \idc)
\end{array}\]
\caption{\label{figb}Signatures of level-2 $\Pi$-combinators: associativity and distributivity}
\end{figure}

\begin{figure}[t]
\[\def\arraystretch{1.3}
\begin{array}{rcl}
  (\idc \otimes \swapp) \odot \distl &\Leftrightarrow& \distl \odot \swapp
\\
  \dist \odot (\swapt \oplus \swapt) &\Leftrightarrow & \swapt \odot \distl
\end{array}\]
\caption{\label{figa}Signatures of level-2 $\Pi$-combinators: commutativity and distributivity}
\end{figure}

Unfortunately, giving a detailed example would take us too far afield. \jc{cite}

\renewcommand{\AgdaIndentSpace}{\AgdaSpace{}$\;\;$}

We will however mention one last interpretation.
Recalling that the $\lambda$-calculus arises as the internal language
of Cartesian Closed Categories (Elliott~\cite{Elliott-2017} gives a particularly
readable account of this), we can think of $\Pi$ in similar terms, but
for symmetric Rig Groupoids instead.  Programs at level-2 of $\Pi$
are a ``linear'' representation of a 2-categorial commutative
diagram! In fact, it is a painfully verbose version thereof, as it
includes many \emph{refocusing} steps because our language does not
build associativity into its syntax. Categorical diagrams usually do.
