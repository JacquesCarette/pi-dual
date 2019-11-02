{-# OPTIONS --without-K --safe #-}

-- Pointed type and its 'inverse'

module Pointed where

open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

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


------------------------------------------------------------------------------
