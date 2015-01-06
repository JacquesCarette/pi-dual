{-# OPTIONS --without-K #-}
module Path2Equiv where

-- nothing for the standard library needed directly!

open import FT
open import Equivalences
open import TypeEquivalences

-- We now have enough to map each Pi combinator to the corresponding type equivalence

path2equiv : {B₁ B₂ : FT} → (B₁ ⇛ B₂) → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧)
path2equiv unite₊⇛  = unite₊equiv
path2equiv uniti₊⇛  = uniti₊equiv
path2equiv swap₊⇛   = swap₊equiv
path2equiv assocl₊⇛ = assocl₊equiv
path2equiv assocr₊⇛ = assocr₊equiv
path2equiv unite⋆⇛  = unite⋆equiv
path2equiv uniti⋆⇛  = uniti⋆equiv
path2equiv swap⋆⇛   = swap⋆equiv
path2equiv assocl⋆⇛ = assocl⋆equiv
path2equiv assocr⋆⇛ = assocr⋆equiv
path2equiv distz⇛   = distzequiv
path2equiv factorz⇛ = factorzequiv
path2equiv dist⇛    = distequiv
path2equiv factor⇛  = factorequiv
path2equiv id⇛      = idequiv
path2equiv (sym⇛ p) = sym≃ (path2equiv p)
path2equiv (p ◎ q)  = trans≃ (path2equiv p) (path2equiv q) 
path2equiv (p ⊕ q)  = path⊎ (path2equiv p) (path2equiv q)
path2equiv (p ⊗ q)  = path× (path2equiv p) (path2equiv q) 


