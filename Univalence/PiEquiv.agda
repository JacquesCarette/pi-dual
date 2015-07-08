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

open import Data.Sum.Properties

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
cc2equiv assoc◎l = eq (λ x → refl) (λ x → refl)
cc2equiv assoc◎r = eq (λ x → refl) (λ x → refl)
cc2equiv assocl⊕l = eq (sym∼ [[,],]∘assocl₊) (sym∼ assocr₊∘[[,],])
cc2equiv assocl⊕r = eq [[,],]∘assocl₊ assocr₊∘[[,],]
cc2equiv assocl⊗l = eq (λ x → refl) (λ x → refl)
cc2equiv assocl⊗r = eq (λ x → refl) (λ x → refl)
cc2equiv assocr⊕r = eq assocr₊∘[[,],] [[,],]∘assocl₊
cc2equiv assocr⊗l = eq (λ x → refl) (λ x → refl)
cc2equiv assocr⊗r = eq (λ x → refl) (λ x → refl)
cc2equiv assocr⊕l = eq (sym∼ assocr₊∘[[,],]) (sym∼ [[,],]∘assocl₊)
cc2equiv dist⇔l = eq {!!} {!!}
cc2equiv dist⇔r = eq {!!} {!!}
cc2equiv distl⇔l = eq {!!} {!!}
cc2equiv distl⇔r = eq {!!} {!!}
cc2equiv factor⇔l = eq {!!} {!!}
cc2equiv factor⇔r = eq {!!} {!!}
cc2equiv factorl⇔l = eq {!!} {!!}
cc2equiv factorl⇔r = eq {!!} {!!}
cc2equiv idl◎l = eq {!!} {!!}
cc2equiv idl◎r = eq {!!} {!!}
cc2equiv idr◎l = eq {!!} {!!}
cc2equiv idr◎r = eq {!!} {!!}
cc2equiv linv◎l = eq {!!} {!!}
cc2equiv linv◎r = eq {!!} {!!}
cc2equiv rinv◎l = eq {!!} {!!}
cc2equiv rinv◎r = eq ? ?
cc2equiv unite₊l⇔l = eq ? ?
cc2equiv unite₊l⇔r = eq ? ?
cc2equiv uniti₊l⇔l = eq ? ?
cc2equiv uniti₊l⇔r = eq ? ?
cc2equiv unite₊r⇔l = eq ? ?
cc2equiv unite₊r⇔r = eq ? ?
cc2equiv uniti₊r⇔l = eq ? ?
cc2equiv uniti₊r⇔r = eq ? ?
cc2equiv swapl₊⇔ = eq ? ?
cc2equiv swapr₊⇔ = eq ? ?
cc2equiv unitel⋆⇔l = eq ? ?
cc2equiv uniter⋆⇔l = eq ? ?
cc2equiv unitil⋆⇔l = eq ? ?
cc2equiv unitir⋆⇔l = eq ? ?
cc2equiv unitel⋆⇔r = eq ? ?
cc2equiv uniter⋆⇔r = eq ? ?
cc2equiv unitil⋆⇔r = eq ? ?
cc2equiv unitir⋆⇔r = eq ? ?
cc2equiv swapl⋆⇔ = eq ? ?
cc2equiv swapr⋆⇔ = eq ? ?
cc2equiv swapfl⋆⇔ = eq ? ?
cc2equiv swapfr⋆⇔ = eq ? ?
cc2equiv id⇔ = eq ? ?
cc2equiv (trans⇔ ce ce₁) = eq ? ?
cc2equiv (ce ⊡ ce₁) = eq ? ?
cc2equiv (resp⊕⇔ ce ce₁) = eq ? ?
cc2equiv (resp⊗⇔ ce ce₁) = eq ? ?
cc2equiv id⟷⊕id⟷⇔ = eq ? ?
cc2equiv split⊕-id⟷ = eq ? ?
cc2equiv hom⊕◎⇔ = eq ? ?
cc2equiv hom◎⊕⇔ = eq ? ?
cc2equiv id⟷⊗id⟷⇔ = eq ? ?
cc2equiv split⊗-id⟷ = eq ? ?
cc2equiv hom⊗◎⇔ = eq ? ?
cc2equiv hom◎⊗⇔ = eq ? ?
cc2equiv triangle⊕l = eq ? ?
cc2equiv triangle⊕r = eq ? ?
cc2equiv triangle⊗l = eq ? ?
cc2equiv triangle⊗r = eq ? ?
cc2equiv pentagon⊕l = eq ? ?
cc2equiv pentagon⊕r = eq ? ?
cc2equiv pentagon⊗l = eq ? ?
cc2equiv pentagon⊗r = eq ? ?
cc2equiv hexagonr⊕l = eq ? ?
cc2equiv hexagonr⊕r = eq ? ?
cc2equiv hexagonl⊕l = eq {!!} {!!}
cc2equiv hexagonl⊕r = eq {!!} {!!}
cc2equiv hexagonr⊗l = eq {!!} {!!}
cc2equiv hexagonr⊗r = eq {!!} {!!}
cc2equiv hexagonl⊗l = eq {!!} {!!}
cc2equiv hexagonl⊗r = eq {!!} {!!}
cc2equiv absorbl⇔l = eq {!!} {!!}
cc2equiv absorbl⇔r = eq {!!} {!!}
cc2equiv absorbr⇔l = eq {!!} {!!}
cc2equiv absorbr⇔r = eq {!!} {!!}
cc2equiv factorzl⇔l = eq {!!} {!!}
cc2equiv factorzl⇔r = eq {!!} {!!}
cc2equiv factorzr⇔l = eq {!!} {!!}
cc2equiv factorzr⇔r = eq {!!} {!!}
cc2equiv swap₊distl⇔l = eq {!!} {!!}
cc2equiv swap₊distl⇔r = eq {!!} {!!}
cc2equiv dist-swap⋆⇔l = eq {!!} {!!}
cc2equiv dist-swap⋆⇔r = eq {!!} {!!}
cc2equiv assocl₊-dist-dist⇔l = eq {!!} {!!}
cc2equiv assocl₊-dist-dist⇔r = eq {!!} {!!}
cc2equiv assocl⋆-distl⇔l = eq {!!} {!!}
cc2equiv assocl⋆-distl⇔r = eq {!!} {!!}
cc2equiv absorbr0-absorbl0⇔ = eq {!!} {!!}
cc2equiv absorbl0-absorbr0⇔ = eq {!!} {!!}
cc2equiv absorbr⇔distl-absorb-unite = eq {!!} {!!}
cc2equiv distl-absorb-unite⇔absorbr = eq {!!} {!!}
cc2equiv unite⋆r0-absorbr1⇔ = eq {!!} {!!}
cc2equiv absorbr1-unite⋆r-⇔ = eq {!!} {!!}
cc2equiv absorbl≡swap⋆◎absorbr = eq {!!} {!!}
cc2equiv swap⋆◎absorbr≡absorbl = eq {!!} {!!}
cc2equiv absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr = eq {!!} {!!}
cc2equiv [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr = eq {!!} {!!}
cc2equiv [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr = eq {!!} {!!}
cc2equiv assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl = eq {!!} {!!}
cc2equiv elim⊥-A[0⊕B]⇔l = eq {!!} {!!}
cc2equiv elim⊥-A[0⊕B]⇔r = eq {!!} {!!}
cc2equiv elim⊥-1[A⊕B]⇔l = eq {!!} {!!}
cc2equiv elim⊥-1[A⊕B]⇔r = eq {!!} {!!}
cc2equiv fully-distribute⇔l = eq {!!} {!!}
cc2equiv fully-distribute⇔r = eq {!!} {!!}
