{-# OPTIONS --without-K #-}

-- Define all the permutations that occur in Pi
-- These are defined by transport, using univalence

module Permutation where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  
open import Data.Nat            using    (_+_;_*_)
open import Data.Fin            using    (Fin)
open import Relation.Binary     using    (Setoid)
open import Function.Equality   using    (_⟨$⟩_)

open import Equiv using (_≃_; id≃; sym≃; trans≃; _●_)
open import ConcretePermutation
open import ConcretePermutationProperties
open import SEquivSCPermEquiv
open import FinEquiv using (module Plus; module Times)
open import EquivEquiv

open import Proofs using (
  -- FiniteFunctions
  finext
  )

------------------------------------------------------------------------------

-- useful short-hands; these should all be moved elsewhere.
e⇒p : ∀ {m n} → (Fin m ≃ Fin n) → CPerm m n
e⇒p e = _≃S_.g univalence ⟨$⟩ e

p⇒e : ∀ {m n} → CPerm m n → (Fin m ≃ Fin n)
p⇒e p = _≃S_.f univalence ⟨$⟩ p

αu : ∀ {m n} → {e : Fin m ≃ Fin n} → e ≋ e → p⇒e (e⇒p e) ≋ e
αu e≋e = _≃S_.α univalence e≋e

βu : ∀ {m n} → {p : CPerm m n} → p ≡ p → e⇒p (p⇒e p) ≡ p
βu p≡p = _≃S_.β univalence p≡p

-- inside an e⇒p, we can freely replace equivalences
-- this expresses the fundamental property that equivalent equivalences
-- map to THE SAME permutation.
≋⇒≡ : ∀ {m n} → {e₁ e₂ : Fin m ≃ Fin n} → e₁ ≋ e₂ → e⇒p e₁ ≡ e⇒p e₂
≋⇒≡ {e₁} {e₂} (eq fwd bwd) = p≡ (finext bwd)

-- combination of above, where we use αu on left/right of ●
right-α-over-● : ∀ {m n o} → (e₁ : Fin n ≃ Fin o) → (e₂ : Fin m ≃ Fin n) →
    (e₁ ● (p⇒e (e⇒p e₂))) ≋ (e₁ ● e₂)
right-α-over-● e₁ e₂ = ●-resp-≋ (id≋ {x = e₁}) (αu {e = e₂} id≋)

left-α-over-● : ∀ {m n o} → (e₁ : Fin n ≃ Fin o) → (e₂ : Fin m ≃ Fin n) →
    ((p⇒e (e⇒p e₁)) ● e₂) ≋ (e₁ ● e₂)
left-α-over-● e₁ e₂ = ●-resp-≋ (αu {e = e₁} id≋) (id≋ {x = e₂})

------------------------------------------------------------------------------
-- zero permutation
0p : CPerm 0 0
0p = e⇒p (id≃ {A = Fin 0})

-- identity permutation
idp : ∀ {n} → CPerm n n
idp {n} = e⇒p (id≃ {A = Fin n})

-- disjoint union
_⊎p_ : ∀ {m₁ m₂ n₁ n₂} → CPerm m₁ m₂ → CPerm n₁ n₂ → CPerm (m₁ + n₁) (m₂ + n₂)
p₁ ⊎p p₂ = e⇒p (Plus.cong+-iso (p⇒e p₁) (p⇒e p₂))

-- cartesian product
_×p_ : ∀ {m₁ m₂ n₁ n₂} → CPerm m₁ m₂ → CPerm n₁ n₂ → CPerm (m₁ * n₁) (m₂ * n₂)
p₁ ×p p₂ = e⇒p (Times.cong*-iso (p⇒e p₁) (p⇒e p₂))

-- symmetry
symp : ∀ {m n} → CPerm m n → CPerm n m
symp p = e⇒p (sym≃ (p⇒e p))

-- transitivity; note the 'transposition' of the arguments!
transp : ∀ {m₁ m₂ m₃} → CPerm m₂ m₁ → CPerm m₃ m₂ → CPerm m₃ m₁
transp p₁ p₂ = e⇒p (trans≃ (p⇒e p₂) (p⇒e p₁))
