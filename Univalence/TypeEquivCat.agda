{-# OPTIONS --without-K #-}

module TypeEquivCat where

open import Level using (zero)
import Relation.Binary.PropositionalEquality as P

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism

open import Equiv
open import TypeEquiv

TypeEquivCat : Category zero zero zero
TypeEquivCat = ?

TypeEquivGroupoid : Groupoid TypeEquivCat
TypeEquivGroupoid = ?

⊎-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
⊎-bifunctor = ?

×-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
×-bifunctor = ?

-- the 0 below is the id from CPermMonoidal
module ⊎h = MonoidalHelperFunctors TypeEquivCat ⊎-bifunctor 0

0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊎x≡x = ?

CPM⊎ : Monoidal TypeEquivCat
CPM⊎ = record
  { ⊗ = ⊎-bifunctor
   ; id = ?
   ; identityˡ = ?
   ; identityʳ = {!!}
   ; assoc = {!!}
   ; triangle = {!!}
   ; pentagon = {!!}
   }

CPM× : Monoidal TypeEquivCat
CPM× = record
  { ⊗ = ×-bifunctor
  ; id = ?
  ; identityˡ = ?
  ; identityʳ = {!!}
  ; assoc = {!!}
  ; triangle = {!!}
  ; pentagon = {!!}
  }
