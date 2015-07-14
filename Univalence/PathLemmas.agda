{-# OPTIONS --without-K #-}

module PathLemmas where

open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; refl)
  
------------------------------------------------------------------------------
-- These also follow from irrelevance, but this is nicer

sym-sym : {A : Set} {x y : A} {p : x ≡ y} → sym (sym p) ≡ p
sym-sym {_} {x} {.x} {refl} = refl

------------------------------------------------------------------------------
