{-# OPTIONS --without-K #-}
module Equiv2Path where

open import FT using (FT; ⟦_⟧; _⇛_; _◎_; sym⇛)
open import Equivalences using (_≃_)
open import FT-Nat using (normal; bridge)

equiv2path : {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → (B₁ ⇛ B₂)
equiv2path {B₁} {B₂} eq = ((normal B₁) ◎ bridge eq) ◎ (sym⇛ (normal B₂))

