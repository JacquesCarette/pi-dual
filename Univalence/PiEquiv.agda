{-# OPTIONS --without-K #-}

module PiEquiv where

open import Data.Empty
open import Data.Unit
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Function using (_∘_; id)

open import Equiv
open import EquivEquiv
open _≋_
open import TypeEquiv as TE
open import TypeEquivEquiv
-- open import TypeEquivCat
open import PiU
open import PiLevel0
open import PiLevel1

open import Data.Sum.Properties2
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
eval absorbr (x , _) = x
eval absorbl (_ , y) = y
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
evalB factorzr (_ , x) = x
evalB factorzl (x , _) = x
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

-- should probably prove that these are inverses!
-- to a certain extent, no need, because here's
-- the right way to do it:

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
c2equiv (c ⊕ c₁) = (c2equiv c) ⊎≃ (c2equiv c₁)
c2equiv (c ⊗ c₁) = (c2equiv c) ×≃ (c2equiv c₁)

-- and these are 'coherent'
-- first with evaluation:

lemma0 : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → (v : ⟦ t₁ ⟧) →
  eval c v ≡ proj₁ (c2equiv c) v
lemma0 unite₊l (inj₁ ())
lemma0 unite₊l (inj₂ y) = refl
lemma0 uniti₊l v = refl
lemma0 unite₊r (inj₁ x) = refl
lemma0 unite₊r (inj₂ ())
lemma0 uniti₊r v = refl
lemma0 PiLevel0.swap₊ (inj₁ x) = refl
lemma0 PiLevel0.swap₊ (inj₂ y) = refl
lemma0 PiLevel0.assocl₊ (inj₁ x) = refl
lemma0 PiLevel0.assocl₊ (inj₂ (inj₁ x)) = refl
lemma0 PiLevel0.assocl₊ (inj₂ (inj₂ y)) = refl
lemma0 PiLevel0.assocr₊ (inj₁ (inj₁ x)) = refl
lemma0 PiLevel0.assocr₊ (inj₁ (inj₂ y)) = refl
lemma0 PiLevel0.assocr₊ (inj₂ y) = refl
lemma0 unite⋆l v = refl -- yay for η !
lemma0 uniti⋆l v = refl
lemma0 unite⋆r v = refl
lemma0 uniti⋆r v = refl
lemma0 PiLevel0.swap⋆ v = refl
lemma0 PiLevel0.assocl⋆ v = refl
lemma0 PiLevel0.assocr⋆ v = refl
lemma0 absorbr v = refl
lemma0 absorbl v = refl
lemma0 factorzr ()
lemma0 factorzl ()
lemma0 PiLevel0.dist (inj₁ x , proj₂) = refl
lemma0 PiLevel0.dist (inj₂ y , proj₂) = refl
lemma0 PiLevel0.factor (inj₁ x) = refl
lemma0 PiLevel0.factor (inj₂ y) = refl
lemma0 PiLevel0.distl (proj₁ , inj₁ x) = refl
lemma0 PiLevel0.distl (proj₁ , inj₂ y) = refl
lemma0 PiLevel0.factorl (inj₁ x) = refl
lemma0 PiLevel0.factorl (inj₂ y) = refl
lemma0 id⟷ v = refl
lemma0 (c ◎ c₁) v =
  trans (cong (eval c₁) (lemma0 c v)) (
  trans (lemma0 c₁ (proj₁ (c2equiv c) v))
        (sym (β₁ v)))
lemma0 (c ⊕ c₁) (inj₁ x) =
  trans (cong inj₁ (lemma0 c x)) (sym (β⊎₁ (inj₁ x)))
lemma0 (c ⊕ c₁) (inj₂ y) =
 trans (cong inj₂ (lemma0 c₁ y)) (sym (β⊎₁ (inj₂ y)))
lemma0 (c ⊗ c₁) (x , y) =
  trans (cong₂ _,_ (lemma0 c x) (lemma0 c₁ y)) (sym (β×₁ (x , y)))

lemma1 : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → (v : ⟦ t₂ ⟧) →
  evalB c v ≡ proj₁ (sym≃ (c2equiv c)) v
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
lemma1 (c₀ ◎ c₁) v = trans (
  trans (cong (evalB c₀) (lemma1 c₁ v)) (lemma1 c₀ (gg (c2equiv c₁) v)) )
  (sym (β₂ v))
lemma1 (c₀ ⊕ c₁) (inj₁ x) = trans (cong inj₁ (lemma1 c₀ x)) (sym (β⊎₂ (inj₁ x))) -- cong inj₁ (lemma1 c₀ x)
lemma1 (c₀ ⊕ c₁) (inj₂ y) = trans (cong inj₂ (lemma1 c₁ y)) (sym (β⊎₂ (inj₂ y)))
lemma1 (c₀ ⊗ c₁) (x , y) = trans (cong₂ _,_ (lemma1 c₀ x) (lemma1 c₁ y)) (sym (β×₂ (x , y)))

-- and with reverse
!≡sym≃ : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) →
  c2equiv (! c) ≋ sym≃ (c2equiv c)
!≡sym≃ unite₊l = id≋
!≡sym≃ uniti₊l = id≋
!≡sym≃ unite₊r = id≋
!≡sym≃ uniti₊r = id≋
!≡sym≃ PiLevel0.swap₊ = id≋
!≡sym≃ PiLevel0.assocl₊ = id≋
!≡sym≃ PiLevel0.assocr₊ = id≋
!≡sym≃ unite⋆l = id≋
!≡sym≃ uniti⋆l = id≋
!≡sym≃ unite⋆r = id≋
!≡sym≃ uniti⋆r = id≋
!≡sym≃ PiLevel0.swap⋆ = id≋
!≡sym≃ PiLevel0.assocl⋆ = id≋
!≡sym≃ PiLevel0.assocr⋆ = id≋
!≡sym≃ absorbr = id≋
!≡sym≃ absorbl = id≋
!≡sym≃ PiLevel0.factorzr = id≋
!≡sym≃ factorzl = id≋
!≡sym≃ PiLevel0.dist = id≋
!≡sym≃ PiLevel0.factor = id≋
!≡sym≃ PiLevel0.distl = id≋
!≡sym≃ PiLevel0.factorl = id≋
!≡sym≃ id⟷ = id≋
!≡sym≃ (c ◎ c₁) = trans≋ (EquivEquiv._◎_ (!≡sym≃ c) (!≡sym≃ c₁)) (sym≋ sym≃●)
!≡sym≃ (c ⊕ c₁) = trans≋ ((!≡sym≃ c) ⊎≋ (!≡sym≃ c₁)) (sym≋ sym≃-distrib⊎)
!≡sym≃ (c ⊗ c₁) = trans≋ ((!≡sym≃ c) ×≋ (!≡sym≃ c₁)) (sym≋ sym≃-distrib×)

left-inv : {t₁ t₂ : U} (c : t₁ ⟷ t₂) →
  (c2equiv (! c) ● c2equiv c) ≋ id≃
left-inv c =
  let p = c2equiv c in
  trans≋ (!≡sym≃ c EquivEquiv.◎ id≋) (linv≋ p)

right-inv : {t₁ t₂ : U} (c : t₁ ⟷ t₂) →
  (c2equiv c ● c2equiv (! c)) ≋ id≃
right-inv c =
  let p = c2equiv c in
  trans≋ (id≋ EquivEquiv.◎ (!≡sym≃ c)) (rinv≋ p)

----------------------------------------------------------

cc2equiv : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} (ce : c₁ ⇔ c₂) →
  c2equiv c₁ ≋ c2equiv c₂
cc2equiv assoc◎l = ●-assoc
cc2equiv assoc◎r = ●-assocl
cc2equiv assocl⊕l = assocl₊-nat
cc2equiv assocl⊕r = sym≋ assocl₊-nat
cc2equiv assocl⊗l = assocl⋆-nat
cc2equiv assocl⊗r = sym≋ assocl⋆-nat
cc2equiv assocr⊕r = assocr₊-nat
cc2equiv assocr⊗l = sym≋ assocr⋆-nat
cc2equiv assocr⊗r = assocr⋆-nat
cc2equiv assocr⊕l = sym≋ assocr₊-nat
cc2equiv dist⇔l = dist-nat
cc2equiv dist⇔r = sym≋ dist-nat
cc2equiv distl⇔l = distl-nat
cc2equiv distl⇔r = sym≋ distl-nat
cc2equiv factor⇔l = factor-nat
cc2equiv factor⇔r = sym≋ factor-nat
cc2equiv factorl⇔l = factorl-nat
cc2equiv factorl⇔r = sym≋ factorl-nat
cc2equiv idl◎l = rid≋
cc2equiv idl◎r = sym≋ rid≋
cc2equiv idr◎l = lid≋
cc2equiv idr◎r = sym≋ lid≋
cc2equiv (linv◎l {c = c}) = left-inv c
cc2equiv (linv◎r {c = c}) = sym≋ (left-inv c)
cc2equiv (rinv◎l {c = c}) = right-inv c
cc2equiv (rinv◎r {c = c}) = sym≋ (right-inv c)
cc2equiv (unite₊l⇔l {c₁ = c₁} {c₂}) = sym≋ (unite₊-nat {f = c2equiv c₂})
cc2equiv unite₊l⇔r = unite₊-nat
cc2equiv uniti₊l⇔l = sym≋ uniti₊-nat
cc2equiv uniti₊l⇔r = uniti₊-nat
cc2equiv unite₊r⇔l = sym≋ unite₊′-nat
cc2equiv unite₊r⇔r = unite₊′-nat
cc2equiv uniti₊r⇔l = sym≋ uniti₊′-nat
cc2equiv uniti₊r⇔r = uniti₊′-nat
cc2equiv swapl₊⇔ = sym≋ swap₊-nat
cc2equiv swapr₊⇔ = swap₊-nat
cc2equiv unitel⋆⇔l = sym≋ unite⋆-nat
cc2equiv uniter⋆⇔l = unite⋆-nat
cc2equiv unitil⋆⇔l = sym≋ uniti⋆-nat
cc2equiv unitir⋆⇔l = uniti⋆-nat
cc2equiv unitel⋆⇔r = sym≋ unite⋆′-nat
cc2equiv uniter⋆⇔r = unite⋆′-nat
cc2equiv unitil⋆⇔r = sym≋ uniti⋆′-nat
cc2equiv unitir⋆⇔r = uniti⋆′-nat
cc2equiv swapl⋆⇔ = sym≋ swap⋆-nat
cc2equiv swapr⋆⇔ = swap⋆-nat
cc2equiv id⇔ = id≋
cc2equiv (trans⇔ ce ce₁) = trans≋ (cc2equiv ce) (cc2equiv ce₁)
cc2equiv (ce ⊡ ce₁) = (cc2equiv ce₁) EquivEquiv.◎ (cc2equiv ce)
cc2equiv (resp⊕⇔ ce ce₁) = cc2equiv ce ⊎≋ cc2equiv ce₁
cc2equiv (resp⊗⇔ ce ce₁) = cc2equiv ce ×≋ cc2equiv ce₁
cc2equiv id⟷⊕id⟷⇔ = [id,id]≋id
cc2equiv split⊕-id⟷ = sym≋ [id,id]≋id
cc2equiv hom⊕◎⇔ = ⊎●≋●⊎
cc2equiv hom◎⊕⇔ = sym≋ ⊎●≋●⊎
cc2equiv id⟷⊗id⟷⇔ = id×id≋id
cc2equiv split⊗-id⟷ = sym≋ id×id≋id
cc2equiv hom⊗◎⇔ = ×●≋●×
cc2equiv hom◎⊗⇔ = sym≋ ×●≋●×
cc2equiv triangle⊕l = unite-assocr₊-coh
cc2equiv triangle⊕r = sym≋ unite-assocr₊-coh
cc2equiv triangle⊗l = unite-assocr⋆-coh
cc2equiv triangle⊗r = sym≋ unite-assocr⋆-coh
cc2equiv unite₊l-coh-l = unite₊l-coh
cc2equiv unite₊l-coh-r = sym≋ unite₊l-coh
cc2equiv unite⋆l-coh-l = unite⋆l-coh
cc2equiv unite⋆l-coh-r = sym≋ unite⋆l-coh
cc2equiv pentagon⊕l = assocr₊-coh
cc2equiv pentagon⊕r = sym≋ assocr₊-coh
cc2equiv pentagon⊗l = assocr⋆-coh
cc2equiv pentagon⊗r = sym≋ assocr⋆-coh
cc2equiv hexagonr⊕l = assocr₊-swap₊-coh
cc2equiv hexagonr⊕r = sym≋ assocr₊-swap₊-coh
cc2equiv hexagonl⊕l = assocl₊-swap₊-coh
cc2equiv hexagonl⊕r = sym≋ assocl₊-swap₊-coh
cc2equiv hexagonr⊗l = assocr⋆-swap⋆-coh
cc2equiv hexagonr⊗r = sym≋ assocr⋆-swap⋆-coh
cc2equiv hexagonl⊗l = assocl⋆-swap⋆-coh
cc2equiv hexagonl⊗r = sym≋ assocl⋆-swap⋆-coh
cc2equiv absorbl⇔l = distzr-nat
cc2equiv absorbl⇔r = sym≋ distzr-nat
cc2equiv absorbr⇔l = distz-nat
cc2equiv absorbr⇔r = sym≋ distz-nat
cc2equiv factorzl⇔l = factorz-nat
cc2equiv factorzl⇔r = sym≋ factorz-nat
cc2equiv factorzr⇔l = factorzr-nat
cc2equiv factorzr⇔r = sym≋ factorzr-nat
cc2equiv swap₊distl⇔l = A×[B⊎C]≃[A×C]⊎[A×B]
cc2equiv swap₊distl⇔r = sym≋ A×[B⊎C]≃[A×C]⊎[A×B]
cc2equiv dist-swap⋆⇔l = [A⊎B]×C≃[C×A]⊎[C×B]
cc2equiv dist-swap⋆⇔r = sym≋ [A⊎B]×C≃[C×A]⊎[C×B]
cc2equiv assocl₊-dist-dist⇔l = [A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D
cc2equiv assocl₊-dist-dist⇔r = sym≋ [A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D
cc2equiv assocl⋆-distl⇔l = A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D
cc2equiv assocl⋆-distl⇔r = sym≋ A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D
cc2equiv absorbr0-absorbl0⇔ = 0×0≃0
cc2equiv absorbl0-absorbr0⇔ = sym≋ 0×0≃0
cc2equiv absorbr⇔distl-absorb-unite = 0×[A⊎B]≃0
cc2equiv distl-absorb-unite⇔absorbr = sym≋ 0×[A⊎B]≃0
cc2equiv unite⋆r0-absorbr1⇔ = 0×1≃0
cc2equiv absorbr1-unite⋆r-⇔ = sym≋ 0×1≃0
cc2equiv absorbl≡swap⋆◎absorbr = A×0≃0
cc2equiv swap⋆◎absorbr≡absorbl = sym≋ A×0≃0
cc2equiv absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr = 0×A×B≃0
cc2equiv [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr = sym≋ 0×A×B≃0
cc2equiv [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr = A×0×B≃0
cc2equiv assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl = sym≋ A×0×B≃0
cc2equiv elim⊥-A[0⊕B]⇔l = A×[0+B]≃A×B
cc2equiv elim⊥-A[0⊕B]⇔r = sym≋ A×[0+B]≃A×B
cc2equiv elim⊥-1[A⊕B]⇔l = 1×[A⊎B]≃A⊎B
cc2equiv elim⊥-1[A⊕B]⇔r = sym≋ 1×[A⊎B]≃A⊎B
cc2equiv fully-distribute⇔l = [A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D
cc2equiv fully-distribute⇔r = sym≋ [A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D

--
-- These programs really are equivalent.  Here's two ways to see that:

-- 1. they give the same results as programs:

≋⇒≡ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} (ce : c₁ ⇔ c₂) →
  eval c₁ ∼ eval c₂
≋⇒≡ {c₁ = c₁} {c₂} ce =
  trans∼ (lemma0 c₁) (
  trans∼ (_≋_.f≡ (cc2equiv ce))
         (sym∼ (lemma0 c₂)))

-- 2. in fact, you can run one forward, then the other
--    backward, and that's the identity

ping-pong : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} (ce : c₁ ⇔ c₂) →
  evalB c₂ ∘ eval c₁ ∼ id
ping-pong {c₁ = c₁} {c₂} ce =
  trans∼ (cong₂∘ (lemma1 c₂) (lemma0 c₁)) (
  trans∼ (cong∘r (proj₁ (c2equiv c₁)) (_≋_.f≡ (flip≋ (cc2equiv (2! ce))) )) (
  trans∼(sym∼ β₁)
         (_≋_.f≡ (linv≋ (c2equiv c₁)))))
