{-# OPTIONS --without-K --safe #-}

-- Pointed type and its 'inverse'

module Pointed where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)
-- open import Level
--   using (zero)
-- open import Axiom.Extensionality.Propositional
--   using (Extensionality)

------------------------------------------------------------------------------
-- Pointed type: A type with a distinguished point
--  The 'interesting' part is that the point is both a parameter
--  and a field.

record Pointed (A : Set) (v : A) : Set where
  constructor ⇑
  field
    ● : A
    v≡● : v ≡ ●

open Pointed public

-- Pointed types are contractible:
pointed-contr : {A : Set} {v : A} {p : Pointed A v} → ⇑ v refl ≡ p
pointed-contr {p = ⇑ v refl} = refl

-- and thus have all paths between them:
pointed-all-paths : {A : Set} {v : A} {p q : Pointed A v} → p ≡ q
pointed-all-paths {p = p} {q} = trans (sym pointed-contr) pointed-contr

------------------------------------------------------------------------------
-- The 'reciprocal' of a Pointed type is a function that accepts exactly
-- that point, and returns no information. It acts as a 'witness' that
-- the right point has been fed to it.
Recip : (A : Set) → (v : A) → Set
Recip A v = (w : A) → (v ≡ w) → ⊤
-- Recip A v = Pointed A v → ⊤

-- Recip is also contractible, if we're thinking of homotopy types.
-- We need funext to prove it which is unsafe.

-- posulate
--   funext : Extensionality zero zero

-- recip-contr : {A : Set} {v : A} {p : Recip A v} → (λ w p → tt) ≡ p
-- recip-contr = funext (λ w → funext (λ p → refl))


------------------------------------------------------------------------------
