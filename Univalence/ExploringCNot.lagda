\begin{code}
{-# OPTIONS --without-K #-}
module ExploringCNot where
open import PiU
open import PiLevel0

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

Various experiments around ``controlled not'', a reversible variant of (boolean) not.

The traditional cnot combinator, i.e. the one from the reversible circuits literature
is from a pair of booleans to another pair of booleans. But in the $Π$ setting, this
is an odd signature, basically because the completeness theorem doesn't apply: it
only guarantess that two \emph{maximially polymorphic} circuits with the same signature
will be provably equivalent. And the various circuit expressions for cnot are indeed
more polymorphic that just taking pairs of booleans.  If we take a look at one of the
more common expressions, we can hand-infer its type. Let us walk our way through it.
To do so, we need some combinators that lets us annotate each step
\begin{code}
infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : U) {t₂ : U} {t₃ : U} →
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U) → {t : U} → (t ⟷ t)
_□ t = id⟷
\end{code}

So a combinator program is easiest read ``down'' the right hand side, but the
types annotate each step.
\AgdaHide{
\begin{code}
gcnot : {A B C : U} →
        (TIMES (PLUS A B) (PLUS C C)) ⟷ (TIMES (PLUS A B) (PLUS C C))
\end{code}
}
\begin{code}
gcnot {A} {B} {C} =
  let D = PLUS C C in
  TIMES (PLUS A B) D           ⟷⟨ dist ⟩
  PLUS (TIMES A D) (TIMES B D) ⟷⟨ id⟷ ⊕ (id⟷ ⊗ swap₊) ⟩
  PLUS (TIMES A D) (TIMES B D) ⟷⟨ factor ⟩
  TIMES (PLUS A B) D □
\end{code}

(The following should be typeset properly, later)

The use of dist does not introduce new constraints, its type is most polymorphic,
assuming that D were in fact anything. The next line would then force D to in fact
be something like PLUS E F.  The result would then have type
PLUS (TIMES A (PLUS E F) (TIMES B (PLUS F E))).
factor cannot be applied to this, as it requires that PLUS E F and PLUS F E be
unifiable -- which forces E = F; if we call the joined variable C, we get the
type above.

But this is almost as bad as using Bool! The problem, of course, is that we
have a non-linear use of C in gcnot's type. Let's start exploring what we can
do.

First, let's take a very ``classical'' route, where we're going to use
propositional equality to force things to be equal. We won't use the
line-by-line definition, as it doesn't show anything new.

\begin{code}
gcnot-≡ : {A B C D : U} → (C ≡ D) →
        (TIMES (PLUS A B) (PLUS C D)) ⟷ (TIMES (PLUS A B) (PLUS C D))
gcnot-≡ refl = dist ◎ ( id⟷ ⊕ ( id⟷ ⊗ swap₊ )) ◎ factor
\end{code}

So while we have indeed obtained what looks like a mild generalization, we
don't \emph{really} have four type parameters. And this isn't really in the
spirit of $Π$. So instead, let's merely assume that $C ⟷ D$.

\begin{code}
gcnot-⟷ : {A B C D : U} → (C ⟷ D) →
        (TIMES (PLUS A B) (PLUS C D)) ⟷ (TIMES (PLUS A B) (PLUS C D))
gcnot-⟷ p = dist ◎ ( id⟷ ⊕ ( id⟷ ⊗ swap₊ )) ◎ (id⟷ ⊕ (id⟷ ⊗ (! p ⊕ p))) ◎ factor
\end{code}

Naturally, if C and D are the same, p can be taken as id⟷, and this is provably
the same as gcnot. But if C and D are merely related, then p doesn't have to be
the identity. Of course, this was already true of gcnot-≡ : if C and D were Bool,
we could have chosen the proof to be the univalent transport of swap₊ rather than
refl. Of course, this would not have given us anything ``new''.
