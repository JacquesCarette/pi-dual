{-# OPTIONS --without-K #-}

module PiEquiv where

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Equiv
open import TypeEquiv as TE
open import PiLevel0

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes an equivalence to types
-- note how we don't have to look at the types at all.

c2equiv : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → ⟦ t₁ ⟧ ≃ ⟦ t₂ ⟧
c2equiv unite₊ = TE.unite₊equiv
c2equiv uniti₊ = TE.uniti₊equiv
c2equiv swap₊ = TE.swap₊equiv
c2equiv assocl₊ = TE.assocl₊equiv
c2equiv assocr₊ = TE.assocr₊equiv
c2equiv unite⋆ = TE.unite⋆equiv
c2equiv uniti⋆ = TE.uniti⋆equiv
c2equiv swap⋆ = TE.swap⋆equiv
c2equiv assocl⋆ = TE.assocl⋆equiv
c2equiv assocr⋆ = TE.assocr⋆equiv
c2equiv absorbr = TE.distzequiv
c2equiv absorbl = TE.distzrequiv
c2equiv factorzr = TE.factorzrequiv
c2equiv factorzl = TE.factorzequiv
c2equiv dist = TE.distequiv
c2equiv factor = TE.factorequiv
c2equiv id⟷ = TE.idequiv
c2equiv (c ◎ c₁) = c2equiv c₁ ● c2equiv c
c2equiv (c ⊕ c₁) = path⊎ (c2equiv c) (c2equiv c₁)
c2equiv (c ⊗ c₁) = path× (c2equiv c) (c2equiv c₁)

-- and these are 'coherent'
lemma1 : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → (v : ⟦ t₂ ⟧) →
  evalB c v ≡ (sym≃ (c2equiv c)) ⋆ v
lemma1 PiLevel0.unite₊ v = refl
lemma1 PiLevel0.uniti₊ (inj₁ ())
lemma1 PiLevel0.uniti₊ (inj₂ y) = refl
lemma1 PiLevel0.swap₊ (inj₁ x) = refl
lemma1 PiLevel0.swap₊ (inj₂ y) = refl
lemma1 PiLevel0.assocl₊ (inj₁ (inj₁ x)) = refl
lemma1 PiLevel0.assocl₊ (inj₁ (inj₂ y)) = refl
lemma1 PiLevel0.assocl₊ (inj₂ y) = refl
lemma1 PiLevel0.assocr₊ (inj₁ x) = refl
lemma1 PiLevel0.assocr₊ (inj₂ (inj₁ x)) = refl
lemma1 PiLevel0.assocr₊ (inj₂ (inj₂ y)) = refl
lemma1 PiLevel0.unite⋆ v = refl
lemma1 PiLevel0.uniti⋆ (tt , x) = refl
lemma1 PiLevel0.swap⋆ (x , y) = refl
lemma1 PiLevel0.assocl⋆ ((x , y) , z) = refl
lemma1 PiLevel0.assocr⋆ (x , y , z) = refl
lemma1 absorbr ()
lemma1 absorbl ()
lemma1 PiLevel0.factorzr (_ , ())
lemma1 factorzl (() , v)
lemma1 PiLevel0.dist (inj₁ (proj₁ , proj₂)) = refl
lemma1 PiLevel0.dist (inj₂ (proj₁ , proj₂)) = refl
lemma1 PiLevel0.factor (inj₁ x , proj₂) = refl
lemma1 PiLevel0.factor (inj₂ y , proj₂) = refl
lemma1 id⟷ v = refl
lemma1 (c₀ ◎ c₁) v = 
  trans (cong (evalB c₀) (lemma1 c₁ v)) (
        lemma1 c₀ (qinv.g (proj₂ (c2equiv c₁)) v))
lemma1 (c₀ ⊕ c₁) (inj₁ x) = cong inj₁ (lemma1 c₀ x)
lemma1 (c₀ ⊕ c₁) (inj₂ y) = cong inj₂ (lemma1 c₁ y)
lemma1 (c₀ ⊗ c₁) (x , y) = cong₂ _,_ (lemma1 c₀ x) (lemma1 c₁ y)
