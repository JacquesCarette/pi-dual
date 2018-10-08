\begin{code}
{-# OPTIONS --without-K #-}
module ExploringCNot where
open import PiU
open import PiLevel0
open import PiEquiv using (eval; ⟦_⟧)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_; Σ; proj₁)
open import Data.Sum using (inj₁; inj₂; _⊎_; [_,_])
open import Data.Unit using (tt)
open import Level
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
refl. Of course, this would not have given us anything ``new''. And, of course,
in classical reversible circuits, all of A, B, C and D are unit.

Before we move on, we should indeed check, extensionally, that all these
circuits really do correspond to cnot. So we need a bit of checking code:

\begin{code}
BOOL : U
BOOL  = PLUS ONE ONE

BOOL² : U
BOOL² = TIMES BOOL BOOL

check : (BOOL² ⟷ BOOL²) → Set₀
check p =
  (eval p (inj₁ tt , inj₁ tt) ≡ (inj₁ tt , inj₁ tt)) ×
  (eval p (inj₂ tt , inj₁ tt) ≡ (inj₂ tt , inj₂ tt)) ×
  (eval p (inj₁ tt , inj₂ tt) ≡ (inj₁ tt , inj₂ tt)) ×
  (eval p (inj₂ tt , inj₂ tt) ≡ (inj₂ tt , inj₁ tt))
\end{code}

Which then enables us to verify that, indeed, this is the case. Below, we give
the implicit parameters explicitly, as an extra level of checking.
\begin{code}
test-gcnot : check (gcnot {ONE} {ONE} {ONE})
test-gcnot = refl , refl , refl , refl

test-gcnot-≡ : (p : ONE ≡ ONE) → check (gcnot-≡ {ONE} {ONE} {ONE} {ONE} p)
test-gcnot-≡ refl = refl , refl , refl , refl
\end{code}

Without quite a bit of work, we can't actually prove the following:
test-gcnot-⟷ : (c : ONE ⟷ ONE) → check (gcnot-⟷ {ONE} {ONE} {ONE} {ONE} c)
test-gcnot-⟷ c = refl , {!!} , refl , {!!}
The issue is that even though it should be clear that
eval c tt ≡ tt
for any c : ONE ⟷ ONE, this is actually non-trivial, as eval is defined
by induction on the syntax of combinators. We can, of course, prove the
degenerate version easily:
\begin{code}
test-gcnot-⟷ : check (gcnot-⟷ {ONE} {ONE} {ONE} {ONE} id⟷)
test-gcnot-⟷ = refl , refl , refl , refl
\end{code}

Interestingly, there is a rather different way of writing gcnot which is
related to the one above. It is not quite a cnot, but can be turned into
one when A is ONE.
\begin{code}
gcnot-left′ : {A C D : U} →
   (TIMES (PLUS A A) (PLUS C D)) ⟷ (TIMES A (PLUS (PLUS C D) (PLUS D C)))
gcnot-left′ {A} {C} {D} =
  TIMES (PLUS A A) (PLUS C D)                    ⟷⟨ dist ⟩
  PLUS (TIMES A (PLUS C D)) (TIMES A (PLUS C D)) ⟷⟨ id⟷ ⊕ (id⟷ ⊗ swap₊) ⟩
  PLUS (TIMES A (PLUS C D)) (TIMES A (PLUS D C)) ⟷⟨ factorl ⟩
  TIMES A ((PLUS (PLUS C D) (PLUS D C))) □
\end{code}

And upon specialization, we can certainly see that this is an
isomorphism between 2*(C+D) and (C+D)+(D+C).
\begin{code}
gcnot-left : {C D : U} →
  (TIMES BOOL (PLUS C D)) ⟷ (PLUS (PLUS C D) (PLUS D C))
gcnot-left = gcnot-left′ ◎ unite⋆l
\end{code}
And from here, there are a variety of ways of showing that 2*2 = 2+2.
The problem is that, while that equation is true, it is in some sense
a coincidence in that it does not generalize.

Nevertheless gcnot-left′ is interesting, as it shows a different
behaviour in its types: it consumes a ``marked'' value of type A
(i.e. a value of type (PLUS A A)) to choose whether to flip from
(PLUS C D) to (PLUS D C) or not. This can be generalized quite
a bit into a function which chooses between applying two different
combinators:
\begin{code}
choose : {A C E F : U} (p : C ⟷ E) (q : C ⟷ F) →
  (TIMES (PLUS A A) C) ⟷ (TIMES A (PLUS E F))
choose p q = dist ◎ ((id⟷ ⊗ p) ⊕ (id⟷ ⊗ q)) ◎ factorl
\end{code}
And, of course, gcnot-left′ is an instance with p = id⟷ and q = swap₊.
(Simple ⇔ proof omitted). It is also possible to generalize the above
along the same lines of what was done with the original gcnot, to
transform PLUS A A into PLUS A B where A and B are known to be related.

But it remains that all of these indeed build in a relation between its
parameters, i.e. not of these are ``fully polymorphic''.

What are we really doing?  This is probably most visible in the contrast
between gcnot-⟷ and choose:
while in gcnot-⟷ it looks like we use the first value as a control bit for
whether we swap or not, but then there is a price to pay, which is the use
of p to ``fix up'' the types so they line up. choose shows a different
compromise: we actually consume a bit (for control) to choose.

In other words, this is what the coincidence of types (i.e. D = PLUS C C)
allows us to do: completely hide that a bit has been consumed! In general,
when C isn't ONE, gcnot-⟷ shows how this becomes a proof-relevant operation,
i.e. the choice of (p : C ⟷ C) matters. More precisely, we will only be
able to prove that
gcnot-⟷ p ⇔ gcnot-⟷ q
when we have a proof that p ⇔ q. And vice-versa.

Another way to say this is that, when seen at type BOOL², gcnot collapses
some higher-dimensional phenomenon, which only becomes properly visible when
looked at via the lens of polymorphic types. But we can understand polymorphic
types in another way: what if, instead of a bit signal, we had a qbit? While
qbits do obey some rules that fully polymorphic types do not, certainly we
should be wary of coincidences, as demonstrated above.

There is one more way of demonstrating that something odd is happening,
and that is to generalize further, from simple types to dependent types.
We first need to be able to choose a type depending on a value:
\begin{code}
choose-U : {a b : Level} {A : Set a} {B : Set b} →
  (choice : A ⊎ B) → U → U → U
choose-U (inj₁ _) C D = C
choose-U (inj₂ _) C D = D
\end{code}

Which then allows us to really express gcnot as an \emph{action} rather
than merely as a combinator. In other words, the type of the result will
depend on the actual value that will be used:
\begin{code}
full-gcnot : {A B C D : U} →
  let t = TIMES (PLUS A B) (PLUS C D) in
  (x : ⟦ t ⟧) → (t ⟷ (TIMES (PLUS A B) (choose-U (proj₁ x) (PLUS C D) (PLUS D C))))
full-gcnot (inj₁ _ , C⊎D) = id⟷
full-gcnot (inj₂ _ , C⊎D) = id⟷ ⊗ swap₊
\end{code}
But, of course, if we try to write this using combinators, we will fail. The problem
is, again, factor. It is not that factor's type is wrong, it is rather that factor
requires a coincidence.

Inspired by the above and choose, we can generalize further. We know that in circuits
cnot (and after that toffoli, etc) is the basis for if-then-else, we can do so here
as well:
\begin{code}
full-choice : {A B C D E : U} → (C ⟷ D) → (C ⟷ E) →
  let t = TIMES (PLUS A B) C in
  (x : ⟦ t ⟧) → (t ⟷ (TIMES (PLUS A B) (choose-U (proj₁ x) D E)))
full-choice p _ (inj₁ _ , c) = id⟷ ⊗ p
full-choice _ q (inj₂ _ , c) = id⟷ ⊗ q
\end{code}
The above really has its ``proper'' type: one can plainly see that a bit of x is
actually consumed to make the choice. So even though it looks like the value is
untouched, this is not so.
