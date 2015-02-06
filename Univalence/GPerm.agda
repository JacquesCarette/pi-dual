{-# OPTIONS --without-K #-}

module GPerm where

-- Definition of a general permutation, and some combinators.
-- This is the 'abstract' view, in terms of functions.  Contrast with the 
-- concrete view in term of vectors (and restricted to Enumerable sets)

-- In some sense, even better would be to consider 'weak' permutations
-- as exactly _≃_.  Having both side be syntactically equal is weird, as we
-- are exactly trying to liberate ourselves from that!

-- In other words, we won't actually use GPerm anywhere.

open import Level using (_⊔_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)

open import Equiv
open import TypeEquivalences

GPerm : Set → Set
GPerm A = A ≃ A

-- composition.  Stick to Set₀.
_⊙_ : {A : Set} → GPerm A → GPerm A → GPerm A
_⊙_ = trans≃

-- parallel composition.
_⊕_ : {A C : Set} → GPerm A → GPerm C → GPerm (A ⊎ C)
_⊕_ = path⊎

-- tensor product
_⊗_ :  {A B : Set} → GPerm A → GPerm B → GPerm (A × B)
_⊗_ = path×
