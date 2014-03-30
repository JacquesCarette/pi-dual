{-# OPTIONS --without-K #-}
module UnivalenceFiniteTypes where

open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Function renaming (_∘_ to _○_)

open import FT
open import SimpleHoTT
open import Equivalences
open import TypeEquivalences
open import Path2Equiv
open import FT-Nat
open import Inspect
open import LeftCancellation
open import Equiv2Path

-- univalence
{-  This does not typecheck in reasonable time.
univalence₁ : {B₁ B₂ : FT} → 
  (e : ⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → path2equiv (equiv2path e) ≡ e
univalence₁ {B₁} {B₂} (f , feq) with equiv₂ feq
... | mkqinv g  α  β = {!!} 
-}

-- and this can't possibly be true!
-- note that even the "normal form" of equiv2path idequiv (ctrl-C ctrl-N)
-- is an absolutely enormous term.
univalence₂ : {B₁ B₂ : FT} → (p : B₁ ⇛ B₂) → equiv2path (path2equiv p) ≡ p
univalence₂ unite₊⇛ = {!!}
univalence₂ uniti₊⇛ = {!!}
univalence₂ swap₊⇛ = {!!}
univalence₂ assocl₊⇛ = {!!}
univalence₂ assocr₊⇛ = {!!}
univalence₂ unite⋆⇛ = {!!}
univalence₂ uniti⋆⇛ = {!!}
univalence₂ swap⋆⇛ = {!!}
univalence₂ assocl⋆⇛ = {!!}
univalence₂ assocr⋆⇛ = {!!}
univalence₂ distz⇛ = {!!}
univalence₂ factorz⇛ = {!!}
univalence₂ dist⇛ = {!!}
univalence₂ factor⇛ = {!!}
univalence₂ id⇛ = {!!}
univalence₂ (sym⇛ p) = {!!}
univalence₂ (p ◎ q) = {!!} 
univalence₂ (p ⊕ q) = {!!}
univalence₂ (p ⊗ q) = {!!} 

{-
univalence : {B₁ B₂ : FT} → (B₁ ⇛ B₂) ≃ (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) 
univalence = 
  (path2equiv , equiv₁ (mkqinv equiv2path univalence₁ univalence₂))
-}