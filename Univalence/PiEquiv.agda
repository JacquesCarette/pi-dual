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
open import TypeEquivCat -- for ≋
open import PiLevel0
open import PiLevel1

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes an equivalence to types
-- note how we don't have to look at the types at all.

c2equiv : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → ⟦ t₁ ⟧ ≃ ⟦ t₂ ⟧
c2equiv unite₊l = TE.unite₊equiv
c2equiv uniti₊l = TE.uniti₊equiv
c2equiv unite₊r = TE.unite₊′equiv
c2equiv uniti₊r = TE.uniti₊′equiv
c2equiv swap₊ = TE.swap₊equiv
c2equiv assocl₊ = TE.assocl₊equiv
c2equiv assocr₊ = TE.assocr₊equiv
c2equiv unite⋆l = TE.unite⋆equiv
c2equiv uniti⋆l = TE.uniti⋆equiv
c2equiv unite⋆r = TE.unite⋆′equiv
c2equiv uniti⋆r = TE.uniti⋆′equiv
c2equiv swap⋆ = TE.swap⋆equiv
c2equiv assocl⋆ = TE.assocl⋆equiv
c2equiv assocr⋆ = TE.assocr⋆equiv
c2equiv absorbr = TE.distzequiv
c2equiv absorbl = TE.distzrequiv
c2equiv factorzr = TE.factorzrequiv
c2equiv factorzl = TE.factorzequiv
c2equiv dist = TE.distequiv
c2equiv factor = TE.factorequiv
c2equiv distl = TE.distlequiv
c2equiv factorl = TE.factorlequiv
c2equiv id⟷ = TE.idequiv
c2equiv (c ◎ c₁) = c2equiv c₁ ● c2equiv c
c2equiv (c ⊕ c₁) = path⊎ (c2equiv c) (c2equiv c₁)
c2equiv (c ⊗ c₁) = path× (c2equiv c) (c2equiv c₁)

-- and these are 'coherent'
lemma1 : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → (v : ⟦ t₂ ⟧) →
  evalB c v ≡ (sym≃ (c2equiv c)) ⋆ v
lemma1 PiLevel0.unite₊l v = refl
lemma1 PiLevel0.uniti₊l (inj₁ ())
lemma1 PiLevel0.uniti₊l (inj₂ y) = refl
lemma1 PiLevel0.unite₊r v = refl
lemma1 uniti₊r (inj₁ x) = refl
lemma1 uniti₊r (inj₂ ())
lemma1 PiLevel0.swap₊ (inj₁ x) = refl
lemma1 PiLevel0.swap₊ (inj₂ y) = refl
lemma1 PiLevel0.assocl₊ (inj₁ (inj₁ x)) = refl
lemma1 PiLevel0.assocl₊ (inj₁ (inj₂ y)) = refl
lemma1 PiLevel0.assocl₊ (inj₂ y) = refl
lemma1 PiLevel0.assocr₊ (inj₁ x) = refl
lemma1 PiLevel0.assocr₊ (inj₂ (inj₁ x)) = refl
lemma1 PiLevel0.assocr₊ (inj₂ (inj₂ y)) = refl
lemma1 PiLevel0.unite⋆l v = refl
lemma1 PiLevel0.uniti⋆l (tt , x) = refl
lemma1 PiLevel0.unite⋆r v = refl
lemma1 uniti⋆r (x , tt) = refl
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
lemma1 PiLevel0.distl (inj₁ (proj₁ , proj₂)) = refl
lemma1 PiLevel0.distl (inj₂ (proj₁ , proj₂)) = refl
lemma1 PiLevel0.factorl (v , inj₁ x) = refl
lemma1 PiLevel0.factorl (v , inj₂ y) = refl
lemma1 id⟷ v = refl
lemma1 (c₀ ◎ c₁) v = 
  trans (cong (evalB c₀) (lemma1 c₁ v)) (
        lemma1 c₀ (qinv.g (proj₂ (c2equiv c₁)) v))
lemma1 (c₀ ⊕ c₁) (inj₁ x) = cong inj₁ (lemma1 c₀ x)
lemma1 (c₀ ⊕ c₁) (inj₂ y) = cong inj₂ (lemma1 c₁ y)
lemma1 (c₀ ⊗ c₁) (x , y) = cong₂ _,_ (lemma1 c₀ x) (lemma1 c₁ y)

----------------------------------------------------------

-- c2equiv : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → ⟦ t₁ ⟧ ≃ ⟦ t₂ ⟧
cc2equiv : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} (ce : c₁ ⇔ c₂) →
  c2equiv c₁ ≋ c2equiv c₂
cc2equiv assoc◎l = ?
cc2equiv assoc◎r = ?
cc2equiv assocl⊕l = {!!}
cc2equiv assocl⊕r = {!!}
cc2equiv assocl⊗l = {!!}
cc2equiv assocl⊗r = {!!}
cc2equiv assocr⊕r = {!!}
cc2equiv assocr⊗l = {!!}
cc2equiv assocr⊗r = {!!}
cc2equiv assocr⊕l = {!!}
cc2equiv dist⇔l = {!!}
cc2equiv dist⇔r = {!!}
cc2equiv distl⇔l = {!!}
cc2equiv distl⇔r = {!!}
cc2equiv factor⇔l = {!!}
cc2equiv factor⇔r = {!!}
cc2equiv factorl⇔l = {!!}
cc2equiv factorl⇔r = {!!}
cc2equiv idl◎l = {!!}
cc2equiv idl◎r = {!!}
cc2equiv idr◎l = {!!}
cc2equiv idr◎r = {!!}
cc2equiv linv◎l = {!!}
cc2equiv linv◎r = {!!}
cc2equiv rinv◎l = {!!}
cc2equiv rinv◎r = {!!}
cc2equiv unite₊l⇔l = {!!}
cc2equiv unite₊l⇔r = {!!}
cc2equiv uniti₊l⇔l = {!!}
cc2equiv uniti₊l⇔r = {!!}
cc2equiv unite₊r⇔l = {!!}
cc2equiv unite₊r⇔r = {!!}
cc2equiv uniti₊r⇔l = {!!}
cc2equiv uniti₊r⇔r = {!!}
cc2equiv swapl₊⇔ = {!!}
cc2equiv swapr₊⇔ = {!!}
cc2equiv unitel⋆⇔l = {!!}
cc2equiv uniter⋆⇔l = {!!}
cc2equiv unitil⋆⇔l = {!!}
cc2equiv unitir⋆⇔l = {!!}
cc2equiv unitel⋆⇔r = {!!}
cc2equiv uniter⋆⇔r = {!!}
cc2equiv unitil⋆⇔r = {!!}
cc2equiv unitir⋆⇔r = {!!}
cc2equiv swapl⋆⇔ = {!!}
cc2equiv swapr⋆⇔ = {!!}
cc2equiv swapfl⋆⇔ = {!!}
cc2equiv swapfr⋆⇔ = {!!}
cc2equiv id⇔ = {!!}
cc2equiv (trans⇔ ce ce₁) = {!!}
cc2equiv (ce ⊡ ce₁) = {!!}
cc2equiv (resp⊕⇔ ce ce₁) = {!!}
cc2equiv (resp⊗⇔ ce ce₁) = {!!}
cc2equiv id⟷⊕id⟷⇔ = {!!}
cc2equiv split⊕-id⟷ = {!!}
cc2equiv hom⊕◎⇔ = {!!}
cc2equiv hom◎⊕⇔ = {!!}
cc2equiv id⟷⊗id⟷⇔ = {!!}
cc2equiv split⊗-id⟷ = {!!}
cc2equiv hom⊗◎⇔ = {!!}
cc2equiv hom◎⊗⇔ = {!!}
cc2equiv triangle⊕l = {!!}
cc2equiv triangle⊕r = {!!}
cc2equiv triangle⊗l = {!!}
cc2equiv triangle⊗r = {!!}
cc2equiv pentagon⊕l = {!!}
cc2equiv pentagon⊕r = {!!}
cc2equiv pentagon⊗l = {!!}
cc2equiv pentagon⊗r = {!!}
cc2equiv hexagonr⊕l = {!!}
cc2equiv hexagonr⊕r = {!!}
cc2equiv hexagonl⊕l = {!!}
cc2equiv hexagonl⊕r = {!!}
cc2equiv hexagonr⊗l = {!!}
cc2equiv hexagonr⊗r = {!!}
cc2equiv hexagonl⊗l = {!!}
cc2equiv hexagonl⊗r = {!!}
cc2equiv absorbl⇔l = {!!}
cc2equiv absorbl⇔r = {!!}
cc2equiv absorbr⇔l = {!!}
cc2equiv absorbr⇔r = {!!}
cc2equiv factorzl⇔l = {!!}
cc2equiv factorzl⇔r = {!!}
cc2equiv factorzr⇔l = {!!}
cc2equiv factorzr⇔r = {!!}
cc2equiv swap₊distl⇔l = {!!}
cc2equiv swap₊distl⇔r = {!!}
cc2equiv dist-swap⋆⇔l = {!!}
cc2equiv dist-swap⋆⇔r = {!!}
cc2equiv assocl₊-dist-dist⇔l = {!!}
cc2equiv assocl₊-dist-dist⇔r = {!!}
cc2equiv assocl⋆-distl⇔l = {!!}
cc2equiv assocl⋆-distl⇔r = {!!}
cc2equiv absorbr0-absorbl0⇔ = {!!}
cc2equiv absorbl0-absorbr0⇔ = {!!}
cc2equiv absorbr⇔distl-absorb-unite = {!!}
cc2equiv distl-absorb-unite⇔absorbr = {!!}
cc2equiv unite⋆r0-absorbr1⇔ = {!!}
cc2equiv absorbr1-unite⋆r-⇔ = {!!}
cc2equiv absorbl≡swap⋆◎absorbr = {!!}
cc2equiv swap⋆◎absorbr≡absorbl = {!!}
cc2equiv absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr = {!!}
cc2equiv [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr = {!!}
cc2equiv [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr = {!!}
cc2equiv assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl = {!!}
cc2equiv elim⊥-A[0⊕B]⇔l = {!!}
cc2equiv elim⊥-A[0⊕B]⇔r = {!!}
cc2equiv elim⊥-1[A⊕B]⇔l = {!!}
cc2equiv elim⊥-1[A⊕B]⇔r = {!!}
cc2equiv fully-distribute⇔l = {!!}
cc2equiv fully-distribute⇔r = {!!}
