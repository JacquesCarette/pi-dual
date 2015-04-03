{-# OPTIONS --without-K #-}

module FinEquivCat where

open import Level using () renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (Rel)
open import Data.Nat
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_,_; proj₁; proj₂;_×_; Σ) renaming (map to map×)
open import Data.Unit
open import Data.Empty
import Function as F

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided

open import FinEquiv using (_fin≃_; _●_)
open import Equiv using (id≃)
open import TypeEquivCat using (_≋_)


------------------------------------------------------------------------------

FinEquivCat : Category lzero lzero lzero
FinEquivCat = record
  { Obj = ℕ
  ; _⇒_ = _fin≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = λ bc ab → ab ● bc 
  ; assoc = {!!} 
  ; identityˡ = {!!} 
  ; identityʳ = {!!} 
  ; equiv = {!!} 
  ; ∘-resp-≡ = {!!} 
  }

