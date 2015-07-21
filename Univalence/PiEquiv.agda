{-# OPTIONS --without-K #-}

module PiEquiv where

open import Data.Empty
open import Data.Unit
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Function using (_∘_)

open import Equiv
open import EquivEquiv 
open _≋_
open import TypeEquiv as TE
open import TypeEquivCat
open import PiU
open import PiLevel0
open import PiLevel1

open import Data.Sum.Properties
open import Data.SumProd.Properties

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes an equivalence to types
-- note how we don't have to look at the types at all.

⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

eval : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
eval unite₊l (inj₁ ())
eval unite₊l (inj₂ v) = v
eval uniti₊l v = inj₂ v
eval unite₊r (inj₁ x) = x
eval unite₊r (inj₂ ())
eval uniti₊r v = inj₁ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆l (tt , v) = v
eval uniti⋆l v = (tt , v)
eval unite⋆r (v , tt) = v
eval uniti⋆r v = v , tt
eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbr (() , _)
eval absorbl (_ , ())
eval factorzl ()
eval factorzr ()
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval distl (v , inj₁ x) = inj₁ (v , x)
eval distl (v , inj₂ y) = inj₂ (v , y)
eval factorl (inj₁ (x , y)) = x , inj₁ y
eval factorl (inj₂ (x , y)) = x , inj₂ y
eval id⟷ v = v
eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

-- useful to have the backwards eval too

evalB : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
evalB unite₊l x = inj₂ x
evalB uniti₊l (inj₁ ())
evalB uniti₊l (inj₂ y) = y
evalB unite₊r v = inj₁ v
evalB uniti₊r (inj₁ x) = x
evalB uniti₊r (inj₂ ())
evalB swap₊ (inj₁ x) = inj₂ x
evalB swap₊ (inj₂ y) = inj₁ y
evalB assocl₊ (inj₁ (inj₁ x)) = inj₁ x
evalB assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB assocl₊ (inj₂ y) = inj₂ (inj₂ y)
evalB assocr₊ (inj₁ x) = inj₁ (inj₁ x)
evalB assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB assocr₊ (inj₂ (inj₂ y)) = inj₂ y
evalB unite⋆l x = tt , x
evalB uniti⋆l (tt , x) = x
evalB unite⋆r v = v , tt
evalB uniti⋆r (v , tt) = v
evalB swap⋆ (x , y) = y , x
evalB assocl⋆ ((x , y) , z) = x , y , z
evalB assocr⋆ (x , y , z) = (x , y) , z
evalB absorbr ()
evalB absorbl ()
evalB factorzr (_ , ())
evalB factorzl (() , _)
evalB dist (inj₁ (x , y)) = inj₁ x , y
evalB dist (inj₂ (x , y)) = inj₂ x , y
evalB factor (inj₁ x , z) = inj₁ (x , z)
evalB factor (inj₂ y , z) = inj₂ (y , z)
evalB distl (inj₁ (x , y)) = x , inj₁ y
evalB distl (inj₂ (x , y)) = x , inj₂ y
evalB factorl (v , inj₁ x) = inj₁ (v , x)
evalB factorl (v , inj₂ y) = inj₂ (v , y)
evalB id⟷ x = x
evalB (c₀ ◎ c₁) x = evalB c₀ (evalB c₁ x)
evalB (c₀ ⊕ c₁) (inj₁ x) = inj₁ (evalB c₀ x)
evalB (c₀ ⊕ c₁) (inj₂ y) = inj₂ (evalB c₁ y)
evalB (c₀ ⊗ c₁) (x , y) = evalB c₀ x , evalB c₁ y

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
c2equiv id⟷ = id≃
c2equiv (c ◎ c₁) = c2equiv c₁ ● c2equiv c
c2equiv (c ⊕ c₁) = path⊎ (c2equiv c) (c2equiv c₁)
c2equiv (c ⊗ c₁) = path× (c2equiv c) (c2equiv c₁)

-- and these are 'coherent'
-- first with evaluation:
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

-- and with reverse
!≡sym≃ : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) →
  c2equiv (! c) ≡ sym≃ (c2equiv c)
!≡sym≃ unite₊l = refl
!≡sym≃ uniti₊l = refl
!≡sym≃ unite₊r = refl
!≡sym≃ uniti₊r = refl
!≡sym≃ PiLevel0.swap₊ = refl
!≡sym≃ PiLevel0.assocl₊ = refl
!≡sym≃ PiLevel0.assocr₊ = refl
!≡sym≃ unite⋆l = refl
!≡sym≃ uniti⋆l = refl
!≡sym≃ unite⋆r = refl
!≡sym≃ uniti⋆r = refl
!≡sym≃ PiLevel0.swap⋆ = refl
!≡sym≃ PiLevel0.assocl⋆ = refl
!≡sym≃ PiLevel0.assocr⋆ = refl
!≡sym≃ absorbr = refl
!≡sym≃ absorbl = refl
!≡sym≃ PiLevel0.factorzr = refl
!≡sym≃ factorzl = refl
!≡sym≃ PiLevel0.dist = refl
!≡sym≃ PiLevel0.factor = refl
!≡sym≃ PiLevel0.distl = refl
!≡sym≃ PiLevel0.factorl = refl
!≡sym≃ id⟷ = refl
!≡sym≃ (c₀ ◎ c₁) = cong₂ _●_ (!≡sym≃ c₀) (!≡sym≃ c₁) 
!≡sym≃ (c₀ ⊕ c₁) = cong₂ path⊎ (!≡sym≃ c₀) (!≡sym≃ c₁)
!≡sym≃ (c₀ ⊗ c₁) = cong₂ path× (!≡sym≃ c₀) (!≡sym≃ c₁)

left-inv : {t₁ t₂ : U} (c : t₁ ⟷ t₂) →
  (c2equiv (! c) ● c2equiv c) ≋ id≃
left-inv c =
  let p = c2equiv c in
  eq (λ x → trans (cong (λ y → (y ● p) ⋆ x) (!≡sym≃ c)) (p∘!p≡id {p = p} x))
     (λ x → trans (cong (λ y → ((sym≃ p) ● (sym≃ y)) ⋆ x) (!≡sym≃ c)) (!p∘p≡id {p = sym≃ p} x))

right-inv : {t₁ t₂ : U} (c : t₁ ⟷ t₂) →
  (c2equiv c ● c2equiv (! c)) ≋ id≃
right-inv c =
  let p = c2equiv c in
  eq (λ x → trans (cong (λ y → (p ● y) ⋆ x) (!≡sym≃ c)) (!p∘p≡id {p = p} x))
     (λ x → trans (cong (λ y → ((sym≃ y) ● (sym≃ p)) ⋆ x) (!≡sym≃ c)) (p∘!p≡id {p = sym≃ p} x))

----------------------------------------------------------

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
cc2equiv dist⇔l = eq dist-commute (sym ∘ factor-commute)
cc2equiv dist⇔r = eq (sym ∘ dist-commute) factor-commute
cc2equiv distl⇔l = eq distl-commute (sym ∘ factorl-commute)
cc2equiv distl⇔r = eq (sym ∘ distl-commute) factorl-commute
cc2equiv factor⇔l = eq factor-commute (sym ∘ dist-commute)
cc2equiv factor⇔r = eq (sym ∘ factor-commute) dist-commute
cc2equiv factorl⇔l = eq factorl-commute (sym ∘ distl-commute)
cc2equiv factorl⇔r = eq (sym ∘ factorl-commute) distl-commute
cc2equiv idl◎l = eq (λ x → refl) (λ x → refl)
cc2equiv idl◎r = eq (λ x → refl) (λ x → refl)
cc2equiv idr◎l = eq (λ x → refl) (λ x → refl)
cc2equiv idr◎r = eq (λ x → refl) (λ x → refl)
cc2equiv (linv◎l {c = c}) = left-inv c
cc2equiv (linv◎r {c = c}) = sym≋ (left-inv c)
cc2equiv (rinv◎l {c = c}) = right-inv c
cc2equiv (rinv◎r {c = c}) = sym≋ (right-inv c)
cc2equiv unite₊l⇔l = eq (sym∼ unite₊∘[id,f]≡f∘unite₊) (λ x → refl)
cc2equiv unite₊l⇔r = eq unite₊∘[id,f]≡f∘unite₊ (λ x → refl)
cc2equiv uniti₊l⇔l = eq (λ x → refl) unite₊∘[id,f]≡f∘unite₊
cc2equiv uniti₊l⇔r = eq (λ x → refl) (sym∼ unite₊∘[id,f]≡f∘unite₊)
cc2equiv unite₊r⇔l = eq (sym∼ unite₊′∘[id,f]≡f∘unite₊′) (λ x → refl)
cc2equiv unite₊r⇔r = eq unite₊′∘[id,f]≡f∘unite₊′ (λ x → refl)
cc2equiv uniti₊r⇔l = eq (λ x → refl) unite₊′∘[id,f]≡f∘unite₊′
cc2equiv uniti₊r⇔r = eq (λ x → refl) (sym∼ unite₊′∘[id,f]≡f∘unite₊′)
cc2equiv swapl₊⇔ = eq (sym∼ swap₊∘[f,g]≡[g,f]∘swap₊) swap₊∘[f,g]≡[g,f]∘swap₊
cc2equiv swapr₊⇔ = eq swap₊∘[f,g]≡[g,f]∘swap₊ (sym∼ swap₊∘[f,g]≡[g,f]∘swap₊)
cc2equiv unitel⋆⇔l = eq (λ x → refl) (λ x → refl)
cc2equiv uniter⋆⇔l = eq (λ x → refl) (λ x → refl)
cc2equiv unitil⋆⇔l = eq (λ x → refl) (λ x → refl)
cc2equiv unitir⋆⇔l = eq (λ x → refl) (λ x → refl)
cc2equiv unitel⋆⇔r = eq (λ x → refl) (λ x → refl)
cc2equiv uniter⋆⇔r = eq (λ x → refl) (λ x → refl)
cc2equiv unitil⋆⇔r = eq (λ x → refl) (λ x → refl)
cc2equiv unitir⋆⇔r = eq (λ x → refl) (λ x → refl)
cc2equiv swapl⋆⇔ = eq (λ x → refl) (λ x → refl)
cc2equiv swapr⋆⇔ = eq (λ x → refl) (λ x → refl)
cc2equiv id⇔ = eq (λ x → refl) (λ x → refl)
cc2equiv (trans⇔ ce₀ ce₁) = trans≋ (cc2equiv ce₀) (cc2equiv ce₁)
cc2equiv (ce₀ ⊡ ce₁) = ●-resp-≋ (cc2equiv ce₁) (cc2equiv ce₀)  -- flip!
cc2equiv (resp⊕⇔ ce₀ ce₁) =
  eq (map⊎-resp-≡ {e₁ = f≡ e₀} {f≡ e₁})
     (map⊎-resp-≡ {e₁ =  g≡ e₀} {g≡ e₁})
  where
    e₀ = cc2equiv ce₀
    e₁ = cc2equiv ce₁
cc2equiv (resp⊗⇔ ce₀ ce₁) =
  eq (path×-resp-≡ {e₁ = f≡ e₀} {f≡ e₁})
     (path×-resp-≡ {e₁ = g≡ e₀} {g≡ e₁})
    where
    e₀ = cc2equiv ce₀
    e₁ = cc2equiv ce₁
cc2equiv id⟷⊕id⟷⇔ = eq map⊎idid≡id map⊎idid≡id
cc2equiv split⊕-id⟷ = eq (sym∼ map⊎idid≡id) (sym∼ map⊎idid≡id)
cc2equiv hom⊕◎⇔ = eq map⊎-∘ map⊎-∘
cc2equiv hom◎⊕⇔ = eq (sym∼ map⊎-∘) (sym∼ map⊎-∘)
cc2equiv id⟷⊗id⟷⇔ = eq (λ x → refl) (λ x → refl)
cc2equiv split⊗-id⟷ = eq (λ x → refl) (λ x → refl)
cc2equiv hom⊗◎⇔ = eq (λ x → refl) (λ x → refl)
cc2equiv hom◎⊗⇔ = eq (λ x → refl) (λ x → refl)
cc2equiv triangle⊕l = eq triangle⊎-right triangle⊎-left
cc2equiv triangle⊕r = eq (sym∼ triangle⊎-right) (sym∼ triangle⊎-left)
cc2equiv triangle⊗l = eq (λ x → refl) (λ x → refl)
cc2equiv triangle⊗r = eq (λ x → refl) (λ x → refl)
cc2equiv pentagon⊕l = eq pentagon⊎-right pentagon⊎-left
cc2equiv pentagon⊕r = eq (sym∼ pentagon⊎-right) (sym∼ pentagon⊎-left)
cc2equiv pentagon⊗l = eq (λ x → refl) (λ x → refl)
cc2equiv pentagon⊗r = eq (λ x → refl) (λ x → refl)
cc2equiv hexagonr⊕l = eq hexagon⊎-right hexagon⊎-left
cc2equiv hexagonr⊕r = eq (sym∼ hexagon⊎-right) (sym∼ hexagon⊎-left)
cc2equiv hexagonl⊕l = eq hexagon⊎-left hexagon⊎-right
cc2equiv hexagonl⊕r = eq (sym∼ hexagon⊎-left) (sym∼ hexagon⊎-right)
cc2equiv hexagonr⊗l = eq (λ x → refl) (λ x → refl)
cc2equiv hexagonr⊗r = eq (λ x → refl) (λ x → refl)
cc2equiv hexagonl⊗l = eq (λ x → refl) (λ x → refl)
cc2equiv hexagonl⊗r = eq (λ x → refl) (λ x → refl)
cc2equiv absorbl⇔l = eq (λ x → refl) (λ {()})
cc2equiv absorbl⇔r = eq (λ x → refl) (λ {()})
cc2equiv absorbr⇔l = eq (λ x → refl) (λ {()})
cc2equiv absorbr⇔r = eq (λ x → refl) (λ {()})
cc2equiv factorzl⇔l = eq (λ {()}) (λ _ → refl)
cc2equiv factorzl⇔r = eq (λ {()}) (λ _ → refl)
cc2equiv factorzr⇔l = eq (λ {()}) (λ _ → refl)
cc2equiv factorzr⇔r = eq (λ {()}) (λ _ → refl)
cc2equiv swap₊distl⇔l = eq distl-swap₊-lemma factorl-swap₊-lemma
cc2equiv swap₊distl⇔r = eq (sym∼ distl-swap₊-lemma) (sym∼ factorl-swap₊-lemma)
cc2equiv dist-swap⋆⇔l = eq dist-swap⋆-lemma factor-swap⋆-lemma
cc2equiv dist-swap⋆⇔r = eq (sym∼ dist-swap⋆-lemma) (sym∼ factor-swap⋆-lemma)
cc2equiv assocl₊-dist-dist⇔l = eq dist-dist-assoc-lemma assoc-factor-factor-lemma
cc2equiv assocl₊-dist-dist⇔r = eq (sym∼ dist-dist-assoc-lemma) (sym∼ assoc-factor-factor-lemma)
cc2equiv assocl⋆-distl⇔l = eq distl-assoc-lemma assoc-factorl-lemma
cc2equiv assocl⋆-distl⇔r = eq (sym∼ distl-assoc-lemma) (sym∼ assoc-factorl-lemma)
cc2equiv absorbr0-absorbl0⇔ = eq distz0≡distrz0 factorz0≡factorzr0
cc2equiv absorbl0-absorbr0⇔ = eq (sym∼ distz0≡distrz0) (sym∼ factorz0≡factorzr0)
cc2equiv absorbr⇔distl-absorb-unite =
  eq distz0≡unite₊∘[distz,distz]∘distl factorz0≡factorl∘[factorz,factorz]∘uniti₊
cc2equiv distl-absorb-unite⇔absorbr =
  eq (sym∼ distz0≡unite₊∘[distz,distz]∘distl)
     (sym∼ factorz0≡factorl∘[factorz,factorz]∘uniti₊)
cc2equiv unite⋆r0-absorbr1⇔ = eq unite⋆r0≡absorb1 uniti⋆r0≡factorz
cc2equiv absorbr1-unite⋆r-⇔ = eq (sym∼ unite⋆r0≡absorb1) (sym∼ uniti⋆r0≡factorz)
cc2equiv absorbl≡swap⋆◎absorbr = eq absorbl≡absorbr∘swap⋆ factorzr≡swap⋆∘factorz
cc2equiv swap⋆◎absorbr≡absorbl = eq (sym∼ absorbl≡absorbr∘swap⋆) (sym∼ factorzr≡swap⋆∘factorz)
cc2equiv absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr =
  eq absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr factorz⇔factorz◎[factorz⊗id]◎assocr⋆
cc2equiv [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr =
  eq (sym∼ absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr)
     (sym∼ factorz⇔factorz◎[factorz⊗id]◎assocr⋆)
cc2equiv [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr =
  eq elim-middle-⊥ insert-middle-⊥
cc2equiv assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl =
  eq (sym∼ elim-middle-⊥) (sym∼ insert-middle-⊥)
cc2equiv elim⊥-A[0⊕B]⇔l = eq elim⊥-A[0⊕B] insert⊕⊥-AB
cc2equiv elim⊥-A[0⊕B]⇔r = eq (sym∼ elim⊥-A[0⊕B]) (sym∼ insert⊕⊥-AB)
cc2equiv elim⊥-1[A⊕B]⇔l = eq elim⊤-1[A⊕B] insert⊤l⊗-A⊕B
cc2equiv elim⊥-1[A⊕B]⇔r = eq (sym∼ elim⊤-1[A⊕B]) (sym∼ insert⊤l⊗-A⊕B)
cc2equiv fully-distribute⇔l = eq fully-distribute fully-factor
cc2equiv fully-distribute⇔r = eq (sym∼ fully-distribute) (sym∼ fully-factor)
