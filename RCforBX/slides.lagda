\documentclass[11pt]{beamer}

\usepackage{amssymb,amsthm,amsmath}
\usepackage{latex/agda}
\usepackage{catchfilebetweentags}
\usepackage{graphicx}
\usepackage{lmodern}
\usepackage[utf8x]{inputenc}
\usepackage{textgreek}
\usepackage[LGR,TS1,T1]{fontenc}
\usepackage{newunicodechar}
%\usepackage{comment}
%\usepackage{tikz}
%\usepackage{tikz-cd}
%\usepackage[nocenter]{qtree}
%\usepackage{fullpage}
\usepackage{hyperref}
%\usepackage{multicol}
\usepackage{stmaryrd}
%\usepackage{proof}
\usepackage{ucs}
\usepackage{listings}

%%

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
% \newcommand{\alt}{~|~}
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

\DeclareUnicodeCharacter{9679}{\ensuremath{\bullet}}

%\newunicodechar{●}{\ensuremath{\bullet}}
%\newunicodechar{→}{\ensuremath{\mathnormal\to}}
%\newunicodechar{ℓ}{\ensuremath{\ell}}
%\newunicodechar{⊔}{\ensuremath{\lub}}
%\newunicodechar{≡}{\ensuremath{\equiv}}

\DeclareMathAlphabet{\mymathbb}{U}{bbold}{m}{n}

% TIKZ declarations
%\tikzstyle{func}=[rectangle,draw,fill=black!20,minimum size=1.9em,
% text width=2.4em, text centered]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% set up beamer
\usetheme{Boadilla}
\usecolortheme{crane}
\setbeamertemplate{navigation symbols}{}
\setbeamertemplate{page number in head/foot}{}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% set up listings
\lstset{language=Haskell,basicstyle=\footnotesize} % maybe even \scriptsize ?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% For Agda typesetting

% no extra indenting of Agda code
\newdimen\mathindent\mathindent0pt

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

\newcommand{\jc}[1]{\authornote{purple}{JC}{#1}}
\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.9\textwidth}\color{red}{Amr says: {#1}}\end{minipage}}}
\newcommand{\ch}[1]{\authornote{green}{CHC}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\title{Optics and Type Equivalences}
\author[Carette, Sabry]{Jacques Carette, Amr Sabry}
\institute{}
\date{}

\begin{document}
\maketitle

% needs to go inside document, to suppress too much extra space between blocks
\AgdaNoSpaceAroundCode{}

\begin{code}[hide]
{-# OPTIONS --without-K #-}
module slides where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
  renaming (map to map×)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Data.Maybe.Properties
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
    ; sym = λ { {inj₁ x} {inj₁ x₁} e → Setoid.sym S e ; {inj₁ x} {inj₂ y} (lift ())
              ; {inj₂ y} {inj₁ x} (lift ()) ; {inj₂ y} {inj₂ y₁} e → Setoid.sym T e}
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

%% Optics is the name of the zoo of lens-inspired constructs in haskell,
%%   including prisms, achroma, affine, etc.
\begin{frame}[fragile]{Optics}
\begin{center}
\only<1>{\includegraphics[scale=0.20]{Hierarchy.png}}
%% As well known, lens are related to reversible programming -- somehow
%% Zoom on iso in "Field Guide" above
\only<2>{
Based on a `reversible' core:
\includegraphics[scale=0.65]{Iso.png}}
\end{center}
\end{frame}


%% *************************************************************************
\begin{frame}[fragile]{Lens in Haskell}
\begin{lstlisting}
data Lens s a = Lens { view :: s -> a, set :: s -> a -> s }
\end{lstlisting}
\pause
Example:
%%   (JC: why? what's the point being made by the example?)
\begin{lstlisting}
_1 :: Lens (a , b) a
_1 = Lens { view = fst , set = \s a -> (a, snd b) }
\end{lstlisting}
\pause
Laws? Optimizations?
\begin{lstlisting}
view (set s a) == a
set s (view s) == s
set (set s a) a' == set s a'
\end{lstlisting}
\end{frame}

%% *************************************************************************
%% Lens in Agda
\begin{frame}{Lens in Agda}
\begin{code}
record GS-Lens {ℓs ℓa : Level} (S : Set ℓs) (A : Set ℓa) : Set (ℓs ⊔ ℓa) where
  field
    get     : S → A
    set     : S → A → S
    getput  : {s : S} {a : A}    → get (set s a) ≡ a
    putget  : (s : S)            → set s (get s) ≡ s
    putput  : (s : S) (a a' : A) → set (set s a) a' ≡ set s a'
open GS-Lens
\end{code}
%% Write example above in Agda ??

Works... but the proofs can be tedious in larger examples (later)
\begin{code}[hide]
module fst₁ where
\end{code}
\begin{code}
  fst : {A B : Set} → GS-Lens (A × B) A
  fst = record { get = proj₁
               ; set = λ s a → (a , proj₂ s)
               ; getput = refl
               ; putget = λ _ → refl
               ; putput = λ _ _ _ → refl }
\end{code}
\end{frame}

%% Better (and **equivalent**) formulation in Agda
%% Lens1 (no need to mess with setoids)
\begin{frame}{Lens in Agda 2}
\only<1-2,4-6>{
Or, the return of constant-complement lenses:
\begin{code}
record Lens₁ {ℓ : Level} (S : Set ℓ) (A : Set ℓ) : Set (suc ℓ) where
  constructor ∃-lens
  field
    {C} : Set ℓ
    iso : S ≃ (C × A)
\end{code}
}
\visible<2>{
\vspace*{0.5mm}
\begin{code}[hide]
module fst₂ where
\end{code}
\begin{code}
  fst : {A B : Set} → Lens₁ (A × B) A
  fst = ∃-lens swap⋆equiv
\end{code}
}
\only<3>{
where
\ExecuteMetaData[latex/Equiv.tex]{isqinv}
\vspace*{1.5mm}
\ExecuteMetaData[latex/Equiv.tex]{equiv}
}
\onslide<5-6>{
\begin{code}
sound : {ℓ : Level} {S A : Set ℓ} → Lens₁ S A → GS-Lens S A
\end{code}
\begin{code}[hide]
sound (∃-lens (f , qinv g α β)) = record
  { get = λ s → proj₂ (f s)
  ; set = λ s a → g (proj₁ (f s) , a)
  ; getput = cong proj₂ (α _)
  ; putget = β
  ; putput = λ s a a' → cong g (cong₂ _,_ (cong proj₁ (α _)) P.refl) }
\end{code}
}
\onslide<6>{

\vspace*{1.5mm}
\noindent \AgdaFunction{complete} requires moving to \AgdaRecord{Setoid} --
see online code.
\vspace*{1.5mm}
\begin{code}
_≈_under_ : ∀ {ℓ} {S A : Set ℓ} → (s t : S) (l : GS-Lens S A) → Set ℓ
_≈_under_ s t l = ∀ a → set l s a ≡ set l t a
\end{code}
}
\end{frame}

%%
%% Show same example; can now exploit work on type equivalences
\begin{frame}{Exploiting type equivalences}
\begin{minipage}{0.49\textwidth}
\begin{code}
module _ {A B D : Set} where
 l₁ : Lens₁ A A
 l₁ = ∃-lens uniti⋆equiv
 l₂ : Lens₁ (B × A) A
 l₂ = ∃-lens id≃
 l₃ : Lens₁ (B × A) B
 l₃ = ∃-lens swap⋆equiv
 l₄ : Lens₁ (D × (B × A)) A
 l₄ = ∃-lens assocl⋆equiv
 l₅ : Lens₁ ⊥ A
 l₅ = ∃-lens factorzequiv
 l₆ : Lens₁ ((D × A) ⊎ (B × A)) A
 l₆ = ∃-lens factorequiv
\end{code}
\end{minipage}
\begin{minipage}{0.49\textwidth}
$\AgdaFunction{uniti⋆equiv}~:~A ≃ (⊤ × A)$\\
$\AgdaFunction{id≃}~:~A ≃ A$\\
$\AgdaFunction{swap⋆equiv}~:~A × B ≃ B × A$\\
$\AgdaFunction{assocl⋆equiv}~:~(A × B) × C ≃ A × (B × C)$\\
$\AgdaFunction{factorzequiv}~:~⊥ ≃ (⊥ × A)$\\
$\AgdaFunction{factorequiv}~:~((A × D) ⊎ (B × D)) ≃ ((A ⊎ B) × D)$
\end{minipage}
\end{frame}

%% *************************************************************************
%% Even better we have proof-relevant type equivalences

\begin{frame}[fragile]{Proof relevance}
Different proofs that $A × A ≃ A × A$ give different lenses:
\begin{code}
 l₇ : Lens₁ (A × A) A
 l₇ = ∃-lens id≃
 l₈ : Lens₁ (A × A) A
 l₈ = ∃-lens swap⋆equiv
\end{code}

\vspace*{2.5mm}
Plain Curry-Howard: $A ∧ A ≡ A$ implies $A × A ⟷ A$ (equi-inhabitation).
\end{frame}

\begin{frame}{Type Equivalences}
\begin{minipage}{0.43\textwidth}
\begin{center}
Semiring
\end{center}
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
\pause
\begin{minipage}{0.55\textwidth}
\begin{center}
Types
\end{center}
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
\end{frame}

%% Categorify!
\begin{frame}[fragile]{Categorify: weak symmetric Rig Groupoids!}
\only<1>{
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
}
\only<2>{
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
}
\only<3>{
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
}
\only<4>{
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
}
\only<5>{
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
}
\only<6>{
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

\[\def\arraystretch{1.3}
\begin{array}{c}
  {\identlsp \oplus \idc ~\Leftrightarrow~ \assocrp \odot (\idc \oplus \, \identlp)}
\\
  {\identlst \otimes \idc ~\Leftrightarrow~ \assocrt \odot (\idc \otimes \, \identlt)}
\end{array}\]
}
\only<7>{
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
}
\only<8>{
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

\[\def\arraystretch{1.3}
\begin{array}{rcl}
  (\idc \otimes \swapp) \odot \distl &\Leftrightarrow& \distl \odot \swapp
\\
  \dist \odot (\swapt \oplus \swapt) &\Leftrightarrow & \swapt \odot \distl
\end{array}\]
}
\end{frame}

\begin{frame}{So what?}
Up shot: coherence theorem (like the one for monoidal categories).\\
\vspace*{1.5mm}
Sound and complete set of rewrites / optimization rules for type equivalences.\\
\end{frame}

%%
%% *************************************************************************
%%
%% Exploring the space of "lens programs"
%% -- Colour
%% -- Toffoli
\begin{frame}{More lens programs}
\begin{code}
data Colour : Set where red green blue : Colour

∃-Colour-in-A+A+A : (A : Set) → Lens₁ (A ⊎ A ⊎ A) Colour
\end{code}

\pause
\begin{code}[hide]
∃-Colour-in-A+A+A A = ∃-lens eq
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
\begin{code}
GS-Colour-in-A+A+A : (A : Set) → GS-Lens (A ⊎ A ⊎ A) Colour
\end{code}

\vspace*{1.5mm}
For $n ∈ ℕ$ and $n A$, \AgdaRecord{Lens₁} proof terms $O(n)$,
\AgdaRecord{GS-Lens} are \textcolor{red}{$O(n^3)$}.\\
\begin{code}[hide]
GS-Colour-in-A+A+A A = record
  { get = λ { (inj₁ x) → red ; (inj₂ (inj₁ x)) → green ; (inj₂ (inj₂ y)) → blue}
  ; set = λ { (inj₁ x) red → inj₁ x ; (inj₁ x) green → inj₂ (inj₁ x) ; (inj₁ x) blue → inj₂ (inj₂ x)
            ; (inj₂ (inj₁ x)) red → inj₁ x ; (inj₂ (inj₁ x)) green → inj₂ (inj₁ x) ; (inj₂ (inj₁ x)) blue → inj₂ (inj₂ x)
            ; (inj₂ (inj₂ y)) red → inj₁ y ; (inj₂ (inj₂ y)) green → inj₂ (inj₁ y) ; (inj₂ (inj₂ y)) blue → inj₂ (inj₂ y)}
  ; getput = λ { {inj₁ x} {red} → refl ; {inj₁ x} {green} → refl ; {inj₁ x} {blue} → refl
               ; {inj₂ (inj₁ x)} {red} → refl ; {inj₂ (inj₁ x)} {green} → refl ; {inj₂ (inj₁ x)} {blue} → refl
               ; {inj₂ (inj₂ y)} {red} → refl ; {inj₂ (inj₂ y)} {green} → refl ; {inj₂ (inj₂ y)} {blue} → refl}
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
\pause
\vspace*{2.5mm}
Inspired by Quantum Computing:
\begin{code}
gcnot-equiv : {A B C : Set} →
  ((A ⊎ B) × (C ⊎ C)) ≃ ((A ⊎ B) × (C ⊎ C))
gcnot-equiv = factorequiv ● id≃ ⊎≃ (id≃ ×≃ swap₊equiv) ● distequiv

gcnot-lens : {A B C : Set} → Lens₁ ((A ⊎ B) × (C ⊎ C))  (C ⊎ C)
gcnot-lens {A} {B} = ∃-lens gcnot-equiv
\end{code}

\end{frame}
%%
%% *************************************************************************
%% Many extensions to lenses
%%
%% http://oleg.fi/gists/posts/2018-12-12-find-correct-laws.html
%% with more kinds of lenses and questions about which laws they should satisfy
%%
\begin{frame}{Optics}
\begin{center}\begin{tabular}{ll}\hline
Equality & $S = A$ \\ \hline
Iso & $S ≃ A$ \\ \hline
Lens & $∃C. S ≃ C × A$ \\
Prism & $∃C . S ≃ C + A$ \\
Achroma & $∃C. S ≃ (⊤ ⊎ C) × A)$ \\
Affine & $∃C, D. S ≃ D ⊎ (C × A)$ \\ \hline
Grate & $∃I. S ≃ I → A$ \\ \hline
Setter & $∃ F : \mathit{Set} → \mathit{Set}. S ≃ F A$ \\ \hline
\end{tabular}\end{center}
\end{frame}
%% *************************************************************************
%% Geometric interpretation of optics
\begin{frame}{Geometric interpretation}
\begin{center}
\begin{tabular}{lll} \hline
Iso & $S ≃ A$ & $S$ is $A$ up to change of coordinates (CoC) \\
Lens & $∃C. S ≃ C × A$ & $S$ is a \emph{cartesian product} over $A$, up to CoC \\
Prism & $∃C . S ≃ C + A$ & $S$ has a \emph{partition} into $A$ and $C$, up to CoC \\ \hline
\end{tabular}
\end{center}
\end{frame}
%%

\end{document}

%% * we want to understand lenses in the setting of proof-relevant type isomorphisms

%% The inspiration for this paper comes from a number of sources:
%% \begin{enumerate}
%%   \item Oleg Grenrus' \textit{Finding correct (lens) laws}~\cite{oleg-blog},
%%   \item The paper \textit{Synthesizing Bijective Lenses}~\cite{Miltner2018},
%%   \item Twan van Laarhoven's blog \textit{Isomorphism Lenses},
%% \end{enumerate}
%%

\noindent It is important to notice that the conversion above only uses the
\AgdaField{iso} part of the \AgdaRecord{Lens₁}.

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
  ; getput = λ {s} {a} → proj₂ (α (proj₁ (f s) , a))
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
    ; _≈_ = _≈_under l
    ; isEquivalence = record { refl = λ _ → P.refl ; sym = λ i≈j a → P.sym (i≈j a)
                             ; trans = λ i≈j j≈k a → P.trans (i≈j a) (j≈k a) } }}
   (record
     { to = record { _⟨$⟩_ = λ s → s , get l s ; cong = λ { refl → (λ _ → P.refl) , P.refl } }
     ; from = record { _⟨$⟩_ = λ {(s , a) → set l s a} ; cong = λ { {_ , a₁} (≈ , P.refl) → ≈ a₁ } }
     ; inverse-of = record
         { left-inverse-of = putget l
         ; right-inverse-of = λ { (s , a) → (λ a' → putput l s a a') , getput l}
         }
     })
\end{code}

\subsection{Unusual lenses}

Let us consider a type \verb|Colour| with exactly $3$ inhabitants,
The equivalence is not too painful to establish. But let's do
the same for the \verb|GS-Lens|:

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
result.  The full details are omitted as they are quite lengthy%
\footnote{Though available, in full, in the source already cited.}. The main
component is the computation of the ``other'' component, corresponding
roughly to $S - A$, which is the \AgdaRecord{Setoid} with
\AgdaField{Carrier}~$\Sigma S (\lambda s → \AIC{belongs} bi s ≡ \AIC{nothing})$
and equivalence on the first field. This is roughly equivalent to what
Grenrus showed~\cite{oleg-blog}, but without the need for proof irrelevance
in the meta-theory, as we build it in to our \AgdaRecord{Setoid} instead.

\subsection{Other Optics}

A number of additional optics have been put forth. Their salient
properties can be contrasted in the following table which lists
the relation between the source and the view in each case:

\medskip
\begin{figure}[h]
\begin{center}\begin{tabular}{ll}\hline
Equality & $S = A$ \\ \hline
Iso & $S ≃ A$ \\ \hline
Lens & $∃C. S ≃ C × A$ \\
Prism & $∃C . S ≃ C + A$ \\
Achroma & $∃C. S ≃ (⊤ ⊎ C) × A)$ \\
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
\item Achroma when $D = ⊥$ and $C = ⊤ ⊎ C′$,
\item Iso when $D = ⊥$ and $C = ⊤$.
\end{itemize}
Specializing $C$ to $⊤$ in Affine does not give anything useful, as it
ignores $A$ and just says that $S$ is isomorphic to \emph{something},
which is a tautology (as $D$ can be taken to be $S$ itself). Strangely
the table is obviously missing one case, which is when
$D = ⊤$.

Grate~\cite{grate} moves us to a rather different world, one that
involves function types. And Setter is more general still, where all
we know is that $S$ is isomorphic to some \emph{container} of $A$s.

\begin{comment}
\subsection{Laws}

Why do lenses have 3 laws but equivalences have two?  Because the functions that
make up lenses have 3 laws --- the products have $\eta$. And the proof of putput uses it.
Why do prisms have 2 laws then? This remains unclear.

Why do some bidirectional programming eschew the putput law? In part, this seems due
to
\end{comment}

\subsection{Geometry of types}

The type equivalence view brings to the fore a certain ``geometric''
picture of types: A Lens is exactly a \emph{cartesian factoring},
where a type can be seen, via an isomorphism, as a cartesian product.
That the complement does not depend on $A$ is an integral part of
it being ``cartesian''.

By the same reasoning, a Prism is the identification of a type as
being \emph{partitionable} into two pieces.

A reasonable picture is to view $A$ as a sort of \emph{curved}
2-dimensional type, while
$C × A$ is the cartesian, straightened ``rectangular'' version. $C$ doesn't depend on $A$, which is
why the name \emph{constant complement} is quite apt.  In other words, a Lens is a
\emph{change of coordinates}
that allows one to see $A$ as a cartesian projection. Similarly, a Prism is a
\emph{change of coordinates} that shuffles all of $A$ ``to the right''.

\subsection{Optimizing Optics programs}

Unlike general programs, which are fiendish to optimize, equivalences, written
in the language in this paper, are rather different: there is a sound and
complete set of equations that hold for those which are
``sufficiently polymorphic'' (the technical details can be found in
\cite{laplaza72,Fiore-2008}).  Most of those equations can be oriented
(by size) to produce an optimizer.  Of course, more general approaches are
needed if wants a \emph{global} optimizer --- there is much room for future
research in this area.  The complete system is rather daunting: over $200$
equations!
