{-# OPTIONS --without-K #-}

-- Note that this is properly named, but it does depend on our version of
-- Equiv and TypeEquiv for a number of things.

module Data.SumProd.Properties where

open import Level using (zero; suc)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (Rel)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (map to map×)
open import Data.Empty
import Function as F

open import Equiv
open import TypeEquiv

-- Note that all these lemmas are "simple" in the sense that they
-- are all about map⊎ rather than [_,_]

distl-commute : {A B C D E F : Set} → {f : A → D} {g : B → E} {h : C → F} →
  (x : A × (B ⊎ C)) → distl (map× f (map⊎ g h) x) P.≡ (map⊎ (map× f g) (map× f h) (distl x))
distl-commute (a , inj₁ x) = P.refl
distl-commute (a , inj₂ y) = P.refl

factorl-commute : {A B C D E F : Set} → {f : A → D} {g : B → E} {h : C → F} →
  (x : (A × B) ⊎ (A × C)) → factorl (map⊎ (map× f g) (map× f h) x) P.≡
                            (map× f (map⊎ g h) (factorl x))
factorl-commute (inj₁ (a , b)) = P.refl
factorl-commute (inj₂ (a , c)) = P.refl
