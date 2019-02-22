\documentclass{article}

\begin{document}
\begin{code}
module WeaklyDepLens where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
  renaming (map to map×)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; cong; cong₂; sym; trans; refl; inspect; [_])

open import Equiv
open import TypeEquiv
\end{code}

The basic idea here is that we have three types that are isomorphic,
with one being in Lens shape (i.e. constant complement), one being
``messy'' and one being dependently-typed.

What conclusion can be drawn from that?  I'm not entirely sure!  But
it is worth pondering. The idea came from thinking about gcnot and
Toffoli.

The "point" is that the code below shows that both
Lens T1 A
and
Lens T3 A
are inhabited.  T1 is really the non-dependent expansion
of T3, where the index has been internalized into the
choice of ``side'' of $⊎$. This is actually very much
related to the \AgdaRecord{Colour} example!

\begin{code}
module _ {A : Set} where

  Bool : Set
  Bool = ⊤ ⊎ ⊤

  T1 : Set
  T1 = (A ⊎ A) ⊎ (Bool × A)

  T2 : Set
  T2 = (Bool × Bool) × A

  Fam : (b : Bool) → Set
  Fam (inj₁ tt) = A  ⊎ A
  Fam (inj₂ tt) = Bool × A

  T3 : Set
  T3 = Σ Bool Fam

  -- through equivalences
  1≃2 : T1 ≃ T2
  1≃2 = ((factorequiv ● (uniti⋆equiv {⊤ ⊎ ⊤} ⊎≃ uniti⋆equiv {⊤ ⊎ ⊤})) ×≃ id≃ ● factorequiv) ●
       ((factorequiv ● (uniti⋆equiv ⊎≃ uniti⋆equiv)) ⊎≃ id≃)

  -- by hand; the first bit of T2 goes to the index of Fam
  2≃3 : T2 ≃ T3
  2≃3 = f , (qinv g α β)
    where
      f : T2 → T3
      f ((inj₁ x , inj₁ x₁) , a) = inj₁ tt , inj₁ a
      f ((inj₁ x , inj₂ y) , a) = inj₁ tt , inj₂ a
      f ((inj₂ y , inj₁ x) , a) = inj₂ tt , inj₁ tt , a
      f ((inj₂ y , inj₂ y₁) , a) = inj₂ tt , inj₂ tt , a
      g : T3 → T2
      g (inj₁ x , inj₁ x₁) = (inj₁ tt , inj₁ tt) , x₁
      g (inj₁ x , inj₂ y) = (inj₁ tt , inj₂ tt) , y
      g (inj₂ y , inj₁ x , a) = (inj₂ tt , inj₁ tt) , a
      g (inj₂ y , inj₂ y₁ , a) = (inj₂ tt , inj₂ tt) , a
      α : (x : T3) → f (g x) ≡ x
      α (inj₁ x , inj₁ x₁) = refl
      α (inj₁ x , inj₂ y) = refl
      α (inj₂ y , inj₁ x , snd) = refl
      α (inj₂ y , inj₂ y₁ , snd) = refl
      β : (x : T2) → g (f x) ≡ x
      β ((inj₁ x , inj₁ x₁) , snd) = refl
      β ((inj₁ x , inj₂ y) , snd) = refl
      β ((inj₂ y , inj₁ x) , snd) = refl
      β ((inj₂ y , inj₂ y₁) , snd) = refl

\end{code}
\end{document}
