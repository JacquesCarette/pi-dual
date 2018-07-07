{-# OPTIONS --without-K #-}

module PiLevel1 where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.Core using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; [_])

open import PiU using (U; ZERO; ONE; PLUS; TIMES)
open import PiLevel0
  -- hiding triv≡ certainly; we are replacing it with _⇔_
  using (_⟷_; !;
         unite₊l; uniti₊l; unite₊r; uniti₊r; swap₊; assocl₊; assocr₊;
         unite⋆l; uniti⋆l; unite⋆r; uniti⋆r; swap⋆; assocl⋆; assocr⋆;
         absorbr; absorbl; factorzr; factorzl;
         dist; factor; distl; factorl;
         id⟷; _◎_; _⊕_; _⊗_)

------------------------------------------------------------------------------
-- Level 1: instead of using triv≡ to reason about equivalence of
-- combinators, we use the following 2-combinators

infix  30 _⇔_

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  assocl⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⇔ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⇔ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocl⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆) ⇔ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃))
  assocl⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)) ⇔ ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆)
  assocr⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⇔ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
           (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃))) ⇔ (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assocr⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
          (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⇔ (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃)))
  assocr⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  dist⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      ((a ⊕ b) ⊗ c) ◎ dist ⇔ dist ◎ ((a ⊗ c) ⊕ (b ⊗ c))
  dist⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      dist ◎ ((a ⊗ c) ⊕ (b ⊗ c)) ⇔ ((a ⊕ b) ⊗ c) ◎ dist
  distl⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      (a ⊗ (b ⊕ c)) ◎ distl ⇔ distl ◎ ((a ⊗ b) ⊕ (a ⊗ c))
  distl⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      distl ◎ ((a ⊗ b) ⊕ (a ⊗ c)) ⇔ (a ⊗ (b ⊕ c)) ◎ distl
  factor⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor ⇔ factor ◎ ((a ⊕ b) ⊗ c)
  factor⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       factor ◎ ((a ⊕ b) ⊗ c) ⇔ ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor
  factorl⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl ⇔ factorl ◎ (a ⊗ (b ⊕ c))
  factorl⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U}
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       factorl ◎ (a ⊗ (b ⊕ c)) ⇔ ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ id⟷ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ id⟷)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c)
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c)
  unite₊l⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (unite₊l ◎ c₂) ⇔ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          ((c₁ ⊕ c₂) ◎ unite₊l) ⇔ (unite₊l ◎ c₂)
  uniti₊l⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⇔ (c₂ ◎ uniti₊l)
  uniti₊l⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti₊l) ⇔ (uniti₊l ◎ (c₁ ⊕ c₂))
  unite₊r⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (unite₊r ◎ c₂) ⇔ ((c₂ ⊕ c₁) ◎ unite₊r)
  unite₊r⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          ((c₂ ⊕ c₁) ◎ unite₊r) ⇔ (unite₊r ◎ c₂)
  uniti₊r⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (uniti₊r ◎ (c₂ ⊕ c₁)) ⇔ (c₂ ◎ uniti₊r)
  uniti₊r⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti₊r) ⇔ (uniti₊r ◎ (c₂ ⊕ c₁))
  swapl₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          (swap₊ ◎ (c₁ ⊕ c₂)) ⇔ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          ((c₂ ⊕ c₁) ◎ swap₊) ⇔ (swap₊ ◎ (c₁ ⊕ c₂))
  unitel⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
          (unite⋆l ◎ c₂) ⇔ ((c₁ ⊗ c₂) ◎ unite⋆l)
  uniter⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
          ((c₁ ⊗ c₂) ◎ unite⋆l) ⇔ (unite⋆l ◎ c₂)
  unitil⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
          (uniti⋆l ◎ (c₁ ⊗ c₂)) ⇔ (c₂ ◎ uniti⋆l)
  unitir⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti⋆l) ⇔ (uniti⋆l ◎ (c₁ ⊗ c₂))
  unitel⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
          (unite⋆r ◎ c₂) ⇔ ((c₂ ⊗ c₁) ◎ unite⋆r)
  uniter⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
          ((c₂ ⊗ c₁) ◎ unite⋆r) ⇔ (unite⋆r ◎ c₂)
  unitil⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
          (uniti⋆r ◎ (c₂ ⊗ c₁)) ⇔ (c₂ ◎ uniti⋆r)
  unitir⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} →
          (c₂ ◎ uniti⋆r) ⇔ (uniti⋆r ◎ (c₂ ⊗ c₁))
  swapl⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          (swap⋆ ◎ (c₁ ⊗ c₂)) ⇔ ((c₂ ⊗ c₁) ◎ swap⋆)
  swapr⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} →
          ((c₂ ⊗ c₁) ◎ swap⋆) ⇔ (swap⋆ ◎ (c₁ ⊗ c₂))
  id⇔     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ c
  trans⇔  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} →
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : {t₁ t₂ t₃ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  -- below are the combinators added for the RigCategory structure
  id⟷⊕id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⇔ id⟷
  split⊕-id⟷ : {t₁ t₂ : U} → (id⟷ {PLUS t₁ t₂}) ⇔ (id⟷ ⊕ id⟷)
  hom⊕◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  id⟷⊗id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊗ id⟷ {t₂}) ⇔ id⟷
  split⊗-id⟷ : {t₁ t₂ : U} → (id⟷ {TIMES t₁ t₂}) ⇔ (id⟷ ⊗ id⟷)
  hom⊗◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)) ⇔ ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄))
  hom◎⊗⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)) ⇔ ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄))
  -- associativity triangle
  triangle⊕l : {t₁ t₂ : U} →
    (unite₊r {t₁} ⊕ id⟷ {t₂}) ⇔ assocr₊ ◎ (id⟷ ⊕ unite₊l)
  triangle⊕r : {t₁ t₂ : U} →
    assocr₊ ◎ (id⟷ {t₁} ⊕ unite₊l {t₂}) ⇔ (unite₊r ⊕ id⟷)
  triangle⊗l : {t₁ t₂ : U} →
    ((unite⋆r {t₁}) ⊗ id⟷ {t₂}) ⇔ assocr⋆ ◎ (id⟷ ⊗ unite⋆l)
  triangle⊗r : {t₁ t₂ : U} →
    (assocr⋆ ◎ (id⟷ {t₁} ⊗ unite⋆l {t₂})) ⇔ (unite⋆r ⊗ id⟷)
  pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
    assocr₊ ◎ (assocr₊ {t₁} {t₂} {PLUS t₃ t₄}) ⇔
    ((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊)
  pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr₊ {t₁} {t₂} {t₃} ⊕ id⟷ {t₄}) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊) ⇔
    assocr₊ ◎ assocr₊
  pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
    assocr⋆ ◎ (assocr⋆ {t₁} {t₂} {TIMES t₃ t₄}) ⇔
    ((assocr⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆)
  pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr⋆ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆) ⇔
    assocr⋆ ◎ assocr⋆
  -- from the braiding
  -- unit coherence
  unite₊l-coh-l : {t₁ : U} → unite₊l {t₁} ⇔ swap₊ ◎ unite₊r
  unite₊l-coh-r : {t₁ : U} → swap₊ ◎ unite₊r ⇔ unite₊l {t₁}
  unite⋆l-coh-l : {t₁ : U} → unite⋆l {t₁} ⇔ swap⋆ ◎ unite⋆r
  unite⋆l-coh-r : {t₁ : U} → swap⋆ ◎ unite⋆r ⇔ unite⋆l {t₁}
  hexagonr⊕l : {t₁ t₂ t₃ : U} →
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃} ⇔
    ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)
  hexagonr⊕r : {t₁ t₂ t₃ : U} →
    ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊) ⇔
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃}
  hexagonl⊕l : {t₁ t₂ t₃ : U} →
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃} ⇔
    ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷)
  hexagonl⊕r : {t₁ t₂ t₃ : U} →
    ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷) ⇔
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃}
  hexagonr⊗l : {t₁ t₂ t₃ : U} →
    (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃} ⇔
    ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆)
  hexagonr⊗r : {t₁ t₂ t₃ : U} →
    ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆) ⇔
    (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃}
  hexagonl⊗l : {t₁ t₂ t₃ : U} →
    (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃} ⇔
    ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷)
  hexagonl⊗r : {t₁ t₂ t₃ : U} →
    ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷) ⇔
    (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃}
  absorbl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl ⇔ absorbl ◎ id⟷ {ZERO}
  absorbl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    absorbl ◎ id⟷ {ZERO} ⇔ (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl
  absorbr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (id⟷ {ZERO} ⊗ c₁) ◎ absorbr ⇔ absorbr ◎ id⟷ {ZERO}
  absorbr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    absorbr ◎ id⟷ {ZERO} ⇔ (id⟷ {ZERO} ⊗ c₁) ◎ absorbr
  factorzl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    id⟷ ◎ factorzl ⇔ factorzl ◎ (id⟷ ⊗ c₁)
  factorzl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    factorzl ◎ (id⟷ {ZERO} ⊗ c₁) ⇔ id⟷ {ZERO} ◎ factorzl
  factorzr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    id⟷ ◎ factorzr ⇔ factorzr ◎ (c₁ ⊗ id⟷)
  factorzr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    factorzr ◎ (c₁ ⊗ id⟷) ⇔ id⟷ ◎ factorzr
  -- from the coherence conditions of RigCategory
  swap₊distl⇔l : {t₁ t₂ t₃ : U} →
    (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl ⇔ distl ◎ swap₊
  swap₊distl⇔r : {t₁ t₂ t₃ : U} →
    distl ◎ swap₊ ⇔ (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl
  dist-swap⋆⇔l : {t₁ t₂ t₃ : U} →
    dist {t₁} {t₂} {t₃} ◎ (swap⋆ ⊕ swap⋆) ⇔ swap⋆ ◎ distl
  dist-swap⋆⇔r : {t₁ t₂ t₃ : U} →
    swap⋆ ◎ distl {t₁} {t₂} {t₃} ⇔ dist ◎ (swap⋆ ⊕ swap⋆)
  assocl₊-dist-dist⇔l : {t₁ t₂ t₃ t₄ : U} →
    ((assocl₊ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ dist) ◎ (dist ⊕ id⟷) ⇔
    (dist ◎ (id⟷ ⊕ dist)) ◎ assocl₊
  assocl₊-dist-dist⇔r : {t₁ t₂ t₃ t₄ : U} →
    (dist {t₁} ◎ (id⟷ ⊕ dist {t₂} {t₃} {t₄})) ◎ assocl₊ ⇔
    ((assocl₊ ⊗ id⟷) ◎ dist) ◎ (dist ⊕ id⟷)
  assocl⋆-distl⇔l : {t₁ t₂ t₃ t₄ : U} →
    assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄} ⇔
    ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆)
  assocl⋆-distl⇔r : {t₁ t₂ t₃ t₄ : U} →
    ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆) ⇔
    assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄}
  absorbr0-absorbl0⇔ : absorbr {ZERO} ⇔ absorbl {ZERO}
  absorbl0-absorbr0⇔ : absorbl {ZERO} ⇔ absorbr {ZERO}
  absorbr⇔distl-absorb-unite : {t₁ t₂ : U} →
    absorbr ⇔ (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l
  distl-absorb-unite⇔absorbr : {t₁ t₂ : U} →
    (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l ⇔ absorbr
  unite⋆r0-absorbr1⇔ : unite⋆r ⇔ absorbr
  absorbr1-unite⋆r-⇔ : absorbr ⇔ unite⋆r
  absorbl≡swap⋆◎absorbr : {t₁ : U} → absorbl {t₁} ⇔ swap⋆ ◎ absorbr
  swap⋆◎absorbr≡absorbl : {t₁ : U} → swap⋆ ◎ absorbr ⇔ absorbl {t₁}
  absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr : {t₁ t₂ : U} →
    absorbr ⇔ (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr
  [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr : {t₁ t₂ : U} →
    (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr ⇔ absorbr
  [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr : {t₁ t₂ : U} →
    (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁} ⇔
    (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr
  assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl : {t₁ t₂ : U} →
    (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr ⇔
    (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁}
  elim⊥-A[0⊕B]⇔l : {t₁ t₂ : U} →
     (id⟷ {t₁} ⊗ unite₊l {t₂}) ⇔
     (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l
  elim⊥-A[0⊕B]⇔r : {t₁ t₂ : U} →
     (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l ⇔ (id⟷ {t₁} ⊗ unite₊l {t₂})
  elim⊥-1[A⊕B]⇔l : {t₁ t₂ : U} →
    unite⋆l ⇔
    distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂})
  elim⊥-1[A⊕B]⇔r : {t₁ t₂ : U} →
    distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂}) ⇔ unite⋆l
  fully-distribute⇔l : {t₁ t₂ t₃ t₄ : U} →
    (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊ ⇔
      ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
         ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷)
  fully-distribute⇔r : {t₁ t₂ t₃ t₄ : U} →
    ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
       ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷) ⇔
    (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊

-- At the next level we have a trivial equivalence that equates all
-- 2-morphisms of the same type.

triv≡ : {t₁ t₂ : U} {f g : t₁ ⟷ t₂} → (α β : f ⇔ g) → Set
triv≡ _ _ = ⊤

triv≡Equiv : {t₁ t₂ : U} {f₁ f₂ : t₁ ⟷ t₂} →
             IsEquivalence (triv≡ {t₁} {t₂} {f₁} {f₂})
triv≡Equiv = record
  { refl = tt
  ; sym = λ _ → tt
  ; trans = λ _ _ → tt
  }

------------------------------------------------------------------------------
-- Inverses for 2paths

2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l = assoc◎r
2! assoc◎r = assoc◎l
2! assocl⊕l = assocl⊕r
2! assocl⊕r = assocl⊕l
2! assocl⊗l = assocl⊗r
2! assocl⊗r = assocl⊗l
2! assocr⊕r = assocr⊕l
2! assocr⊕l = assocr⊕r
2! assocr⊗r = assocr⊗l
2! assocr⊗l = assocr⊗r
2! dist⇔l = dist⇔r
2! dist⇔r = dist⇔l
2! distl⇔l = distl⇔r
2! distl⇔r = distl⇔l
2! factor⇔l = factor⇔r
2! factor⇔r = factor⇔l
2! factorl⇔l = factorl⇔r
2! factorl⇔r = factorl⇔l
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! idr◎l = idr◎r
2! idr◎r = idr◎l
2! linv◎l = linv◎r
2! linv◎r = linv◎l
2! rinv◎l = rinv◎r
2! rinv◎r = rinv◎l
2! unite₊l⇔l = unite₊l⇔r
2! unite₊l⇔r = unite₊l⇔l
2! uniti₊l⇔l = uniti₊l⇔r
2! uniti₊l⇔r = uniti₊l⇔l
2! unite₊r⇔l = unite₊r⇔r
2! unite₊r⇔r = unite₊r⇔l
2! uniti₊r⇔l = uniti₊r⇔r
2! uniti₊r⇔r = uniti₊r⇔l
2! swapl₊⇔ = swapr₊⇔
2! swapr₊⇔ = swapl₊⇔
2! unitel⋆⇔l = uniter⋆⇔l
2! uniter⋆⇔l = unitel⋆⇔l
2! unitil⋆⇔l = unitir⋆⇔l
2! unitir⋆⇔l = unitil⋆⇔l
2! unitel⋆⇔r = uniter⋆⇔r
2! uniter⋆⇔r = unitel⋆⇔r
2! unitil⋆⇔r = unitir⋆⇔r
2! unitir⋆⇔r = unitil⋆⇔r
2! swapl⋆⇔ = swapr⋆⇔
2! swapr⋆⇔ = swapl⋆⇔
2! id⇔ = id⇔
2! (α ⊡ β) = (2! α) ⊡ (2! β)
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β)
2! id⟷⊕id⟷⇔ = split⊕-id⟷
2! split⊕-id⟷ = id⟷⊕id⟷⇔
2! hom⊕◎⇔ = hom◎⊕⇔
2! hom◎⊕⇔ = hom⊕◎⇔
2! id⟷⊗id⟷⇔ = split⊗-id⟷
2! split⊗-id⟷ = id⟷⊗id⟷⇔
2! hom⊗◎⇔ = hom◎⊗⇔
2! hom◎⊗⇔ = hom⊗◎⇔
2! triangle⊕l = triangle⊕r
2! triangle⊕r = triangle⊕l
2! triangle⊗l = triangle⊗r
2! triangle⊗r = triangle⊗l
2! pentagon⊕l = pentagon⊕r
2! pentagon⊕r = pentagon⊕l
2! pentagon⊗l = pentagon⊗r
2! pentagon⊗r = pentagon⊗l
2! unite₊l-coh-l = unite₊l-coh-r
2! unite₊l-coh-r = unite₊l-coh-l
2! unite⋆l-coh-l = unite⋆l-coh-r
2! unite⋆l-coh-r = unite⋆l-coh-l
2! hexagonr⊕l = hexagonr⊕r
2! hexagonr⊕r = hexagonr⊕l
2! hexagonl⊕l = hexagonl⊕r
2! hexagonl⊕r = hexagonl⊕l
2! hexagonr⊗l = hexagonr⊗r
2! hexagonr⊗r = hexagonr⊗l
2! hexagonl⊗l = hexagonl⊗r
2! hexagonl⊗r = hexagonl⊗l
2! absorbl⇔l = absorbl⇔r
2! absorbl⇔r = absorbl⇔l
2! absorbr⇔l = absorbr⇔r
2! absorbr⇔r = absorbr⇔l
2! factorzl⇔l = factorzl⇔r
2! factorzl⇔r = factorzl⇔l
2! factorzr⇔l = factorzr⇔r
2! factorzr⇔r = factorzr⇔l
2! swap₊distl⇔l = swap₊distl⇔r
2! swap₊distl⇔r = swap₊distl⇔l
2! dist-swap⋆⇔l = dist-swap⋆⇔r
2! dist-swap⋆⇔r = dist-swap⋆⇔l
2! assocl₊-dist-dist⇔l = assocl₊-dist-dist⇔r
2! assocl₊-dist-dist⇔r = assocl₊-dist-dist⇔l
2! assocl⋆-distl⇔l = assocl⋆-distl⇔r
2! assocl⋆-distl⇔r = assocl⋆-distl⇔l
2! absorbr0-absorbl0⇔ = absorbl0-absorbr0⇔
2! absorbl0-absorbr0⇔ = absorbr0-absorbl0⇔
2! absorbr⇔distl-absorb-unite = distl-absorb-unite⇔absorbr
2! distl-absorb-unite⇔absorbr = absorbr⇔distl-absorb-unite
2! unite⋆r0-absorbr1⇔ = absorbr1-unite⋆r-⇔
2! absorbr1-unite⋆r-⇔ = unite⋆r0-absorbr1⇔
2! absorbl≡swap⋆◎absorbr = swap⋆◎absorbr≡absorbl
2! swap⋆◎absorbr≡absorbl = absorbl≡swap⋆◎absorbr
2! absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr =
    [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr
2!  [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr =
    absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr
2! [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr =
    assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl
2! assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl =
    [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr
2! elim⊥-A[0⊕B]⇔l = elim⊥-A[0⊕B]⇔r
2! elim⊥-A[0⊕B]⇔r = elim⊥-A[0⊕B]⇔l
2! elim⊥-1[A⊕B]⇔l = elim⊥-1[A⊕B]⇔r
2! elim⊥-1[A⊕B]⇔r = elim⊥-1[A⊕B]⇔l
2! fully-distribute⇔l = fully-distribute⇔r
2! fully-distribute⇔r = fully-distribute⇔l

2!! : {t₁ t₂ : U} {f g : t₁ ⟷ t₂} {α : f ⇔ g} → triv≡ (2! (2! α)) α
2!! = tt

-- This makes _⇔_ an equivalence relation...

⇔Equiv : {t₁ t₂ : U} → IsEquivalence (_⇔_ {t₁} {t₂})
⇔Equiv = record
  { refl = id⇔
  ; sym = 2!
  ; trans = trans⇔
  }

------------------------------------------------------------------------------

-- Unit coherence has two versions, but one is derivable
-- from the other.  As it turns out, one of our examples
-- needs the 'flipped' version.

unite₊r-coh-r : {t₁ : U} → swap₊ ◎ unite₊l ⇔ unite₊r {t₁}
unite₊r-coh-r =
  trans⇔ (id⇔ ⊡ unite₊l-coh-l) (
  trans⇔ assoc◎l ((
  trans⇔ (linv◎l ⊡ id⇔) idl◎l ) ) )

------------------------------------------------------------------------------

-- It is often useful to have that reversing c twice is ⇔ c rather than ≡
-- Unfortunately, it needs a 'proof', which is quite dull, though
-- it does have 3 non-trivial cases.
!!⇔id : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! (! c)) ⇔ c
!!⇔id {c = unite₊l} = id⇔
!!⇔id {c = uniti₊l} = id⇔
!!⇔id {c = unite₊r} = id⇔
!!⇔id {c = uniti₊r} = id⇔
!!⇔id {c = swap₊} = id⇔
!!⇔id {c = assocl₊} = id⇔
!!⇔id {c = assocr₊} = id⇔
!!⇔id {c = unite⋆l} = id⇔
!!⇔id {c = uniti⋆l} = id⇔
!!⇔id {c = unite⋆r} = id⇔
!!⇔id {c = uniti⋆r} = id⇔
!!⇔id {c = swap⋆} = id⇔
!!⇔id {c = assocl⋆} = id⇔
!!⇔id {c = assocr⋆} = id⇔
!!⇔id {c = absorbr} = id⇔
!!⇔id {c = absorbl} = id⇔
!!⇔id {c = factorzr} = id⇔
!!⇔id {c = factorzl} = id⇔
!!⇔id {c = dist} = id⇔
!!⇔id {c = factor} = id⇔
!!⇔id {c = distl} = id⇔
!!⇔id {c = factorl} = id⇔
!!⇔id {c = id⟷} = id⇔
!!⇔id {c = c ◎ c₁} = !!⇔id ⊡ !!⇔id
!!⇔id {c = c ⊕ c₁} = resp⊕⇔ !!⇔id !!⇔id
!!⇔id {c = c ⊗ c₁} = resp⊗⇔ !!⇔id !!⇔id

-------------
mutual
  eval₁ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} (ce : c₁ ⇔ c₂) → (t₁ ⟷ t₂)
  eval₁ (assoc◎l {c₁ = c₁} {c₂} {c₃}) = (c₁ ◎ c₂) ◎ c₃
  eval₁ (assoc◎r {c₁ = c₁} {c₂} {c₃}) = c₁ ◎ (c₂ ◎ c₃)
  eval₁ (assocl⊕l {c₁ = c₁} {c₂} {c₃}) = assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)
  eval₁ (assocl⊕r {c₁ = c₁} {c₂} {c₃}) = (c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊
  eval₁ (assocl⊗l {c₁ = c₁} {c₂} {c₃}) = assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)
  eval₁ (assocl⊗r {c₁ = c₁} {c₂} {c₃}) = (c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆
  eval₁ (assocr⊕r {c₁ = c₁} {c₂} {c₃}) = assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))
  eval₁ (assocr⊗l {c₁ = c₁} {c₂} {c₃}) = ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆
  eval₁ (assocr⊗r {c₁ = c₁} {c₂} {c₃}) = assocr⋆ ◎(c₁ ⊗ (c₂ ⊗ c₃))
  eval₁ (assocr⊕l {c₁ = c₁} {c₂} {c₃}) = ((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊
  eval₁ (dist⇔l {a = c₁} {c₂} {c₃}) = dist ◎ ((c₁ ⊗ c₃) ⊕ (c₂ ⊗ c₃))
  eval₁ (dist⇔r {a = c₁} {c₂} {c₃}) = ((c₁ ⊕ c₂) ⊗ c₃) ◎ dist
  eval₁ (distl⇔l {a = c₁} {c₂} {c₃}) = distl ◎ ((c₁ ⊗ c₂) ⊕ (c₁ ⊗ c₃))
  eval₁ (distl⇔r {a = c₁} {c₂} {c₃}) = (c₁ ⊗ (c₂ ⊕ c₃)) ◎ distl
  eval₁ (factor⇔l {a = c₁} {c₂} {c₃}) = factor ◎ ((c₁ ⊕ c₂) ⊗ c₃)
  eval₁ (factor⇔r {a = c₁} {c₂} {c₃}) = ((c₁ ⊗ c₃) ⊕ (c₂ ⊗ c₃)) ◎ factor
  eval₁ (factorl⇔l {a = c₁} {c₂} {c₃}) = factorl ◎ (c₁ ⊗ (c₂ ⊕ c₃))
  eval₁ (factorl⇔r {a = c₁} {c₂} {c₃}) = ((c₁ ⊗ c₂) ⊕ (c₁ ⊗ c₃)) ◎ factorl
  eval₁ (idl◎l {c = c}) = c
  eval₁ (idl◎r {c = c}) = id⟷ ◎ c
  eval₁ (idr◎l {c = c}) = c
  eval₁ (idr◎r {c = c}) = c ◎ id⟷
  eval₁ (linv◎l {c = c}) = id⟷
  eval₁ (linv◎r {c = c}) = c ◎ ! c
  eval₁ (rinv◎l {c = c}) = id⟷
  eval₁ (rinv◎r {c = c}) = ! c ◎ c
  eval₁ (unite₊l⇔l {c₁ = c₁} {c₂}) = (c₁ ⊕ c₂) ◎ unite₊l
  eval₁ (unite₊l⇔r {c₁ = c₁} {c₂}) = unite₊l ◎ c₂
  eval₁ (uniti₊l⇔l {c₁ = c₁} {c₂}) = c₂ ◎ uniti₊l
  eval₁ (uniti₊l⇔r {c₁ = c₁} {c₂}) = uniti₊l ◎ (c₁ ⊕ c₂)
  eval₁ (unite₊r⇔l {c₁ = c₁} {c₂}) = (c₂ ⊕ c₁) ◎ unite₊r
  eval₁ (unite₊r⇔r {c₁ = c₁} {c₂}) = unite₊r ◎ c₂
  eval₁ (uniti₊r⇔l {c₁ = c₁} {c₂}) = c₂ ◎ uniti₊r
  eval₁ (uniti₊r⇔r {c₁ = c₁} {c₂}) = uniti₊r ◎ (c₂ ⊕ c₁)
  eval₁ (swapl₊⇔  {c₁ = c₁} {c₂}) = (c₂ ⊕ c₁) ◎ swap₊
  eval₁ (swapr₊⇔  {c₁ = c₁} {c₂}) = swap₊ ◎ (c₁ ⊕ c₂)
  eval₁ (unitel⋆⇔l {c₁ = c₁} {c₂}) = (c₁ ⊗ c₂) ◎ unite⋆l
  eval₁ (uniter⋆⇔l {c₁ = c₁} {c₂}) = unite⋆l ◎ c₂
  eval₁ (unitil⋆⇔l {c₁ = c₁} {c₂}) = c₂ ◎ uniti⋆l
  eval₁ (unitir⋆⇔l {c₁ = c₁} {c₂}) = uniti⋆l ◎ (c₁ ⊗ c₂)
  eval₁ (unitel⋆⇔r {c₁ = c₁} {c₂}) = (c₂ ⊗ c₁) ◎ unite⋆r
  eval₁ (uniter⋆⇔r {c₁ = c₁} {c₂}) = unite⋆r ◎ c₂
  eval₁ (unitil⋆⇔r {c₁ = c₁} {c₂}) = c₂ ◎ uniti⋆r
  eval₁ (unitir⋆⇔r {c₁ = c₁} {c₂}) = uniti⋆r ◎ (c₂ ⊗ c₁)
  eval₁ (swapl⋆⇔ {c₁ = c₁} {c₂}) = (c₂ ⊗ c₁) ◎ swap⋆
  eval₁ (swapr⋆⇔ {c₁ = c₁} {c₂}) = swap⋆ ◎ (c₁ ⊗ c₂)
  eval₁ (id⇔ {c = c}) = c
  eval₁ (trans⇔ {t₁} {t₂} {c₁} {c₂} {c₃} ce ce₁) with eval₁ ce | exact ce
  ... | cc | refl =  eval₁ {c₁ = cc} {c₃} ce₁
  eval₁ (_⊡_ {c₁ = c₁} {c₂} {c₃} {c₄} ce₀ ce₁) =
    let r₀ = eval₁ ce₀ in
    let r₁ = eval₁ ce₁ in
    r₀ ◎ r₁
  eval₁ (resp⊕⇔ ce₀ ce₁) =
    let r₀ = eval₁ ce₀ in
    let r₁ = eval₁ ce₁ in
    r₀ ⊕ r₁
  eval₁ (resp⊗⇔ ce₀ ce₁) =
    let r₀ = eval₁ ce₀ in
    let r₁ = eval₁ ce₁ in
    r₀ ⊗ r₁
  eval₁ id⟷⊕id⟷⇔ = id⟷
  eval₁ split⊕-id⟷ = id⟷ ⊕ id⟷
  eval₁ (hom⊕◎⇔ {c₁ = c₁} {c₂} {c₃} {c₄}) = (c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)
  eval₁ (hom◎⊕⇔ {c₁ = c₁} {c₂} {c₃} {c₄}) = (c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)
  eval₁ id⟷⊗id⟷⇔ = id⟷
  eval₁ split⊗-id⟷ = id⟷ ⊗ id⟷
  eval₁ (hom⊗◎⇔ {c₁ = c₁} {c₂} {c₃} {c₄}) = (c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)
  eval₁ (hom◎⊗⇔ {c₁ = c₁} {c₂} {c₃} {c₄}) = (c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)
  eval₁ triangle⊕l = assocr₊ ◎ (id⟷ ⊕ unite₊l)
  eval₁ triangle⊕r = unite₊r ⊕ id⟷
  eval₁ triangle⊗l = assocr⋆ ◎ (id⟷ ⊗ unite⋆l)
  eval₁ triangle⊗r = unite⋆r ⊗ id⟷
  eval₁ pentagon⊕l = ((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊)
  eval₁ pentagon⊕r = assocr₊ ◎ assocr₊
  eval₁ pentagon⊗l = ((assocr⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆)
  eval₁ pentagon⊗r = assocr⋆ ◎ assocr⋆
  eval₁ unite₊l-coh-l = swap₊ ◎ unite₊r
  eval₁ unite₊l-coh-r = unite₊l
  eval₁ unite⋆l-coh-l = swap⋆ ◎ unite⋆r
  eval₁ unite⋆l-coh-r = unite⋆l
  eval₁ hexagonr⊕l = ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)
  eval₁ hexagonr⊕r = (assocr₊ ◎ swap₊) ◎ assocr₊
  eval₁ hexagonl⊕l = ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷)
  eval₁ hexagonl⊕r = (assocl₊ ◎ swap₊) ◎ assocl₊
  eval₁ hexagonr⊗l = ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆)
  eval₁ hexagonr⊗r = (assocr⋆ ◎ swap⋆) ◎ assocr⋆
  eval₁ hexagonl⊗l = ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷)
  eval₁ hexagonl⊗r = (assocl⋆ ◎ swap⋆) ◎ assocl⋆
  eval₁ absorbl⇔l = absorbl ◎ id⟷
  eval₁ (absorbl⇔r {c₁ = c₁}) = (c₁ ⊗ id⟷) ◎ absorbl
  eval₁ absorbr⇔l = absorbr ◎ id⟷
  eval₁ (absorbr⇔r {c₁ = c₁}) = (id⟷ ⊗ c₁) ◎ absorbr
  eval₁ (factorzl⇔l {c₁ = c₁}) = factorzl ◎ (id⟷ ⊗ c₁)
  eval₁ (factorzl⇔r {c₁ = c₁}) = id⟷ ◎ factorzl
  eval₁ (factorzr⇔l {c₁ = c₁}) = factorzr ◎ (c₁ ⊗ id⟷)
  eval₁ (factorzr⇔r {c₁ = c₁}) = id⟷ ◎ factorzr
  eval₁ swap₊distl⇔l = distl ◎ swap₊
  eval₁ swap₊distl⇔r = (id⟷ ⊗ swap₊) ◎ distl
  eval₁ dist-swap⋆⇔l = swap⋆ ◎ distl
  eval₁ dist-swap⋆⇔r = dist ◎ (swap⋆ ⊕ swap⋆)
  eval₁ assocl₊-dist-dist⇔l = (dist ◎ (id⟷ ⊕ dist)) ◎ assocl₊
  eval₁ assocl₊-dist-dist⇔r = ((assocl₊ ⊗ id⟷) ◎ dist) ◎ (dist ⊕ id⟷)
  eval₁ assocl⋆-distl⇔l = ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆)
  eval₁ assocl⋆-distl⇔r = assocl⋆ ◎ distl
  eval₁ absorbr0-absorbl0⇔ = absorbl
  eval₁ absorbl0-absorbr0⇔ = absorbr
  eval₁ absorbr⇔distl-absorb-unite = (distl ◎ (absorbr ⊕ absorbr)) ◎ unite₊l
  eval₁ distl-absorb-unite⇔absorbr = absorbr
  eval₁ unite⋆r0-absorbr1⇔ = absorbr
  eval₁ absorbr1-unite⋆r-⇔ = unite⋆r
  eval₁ absorbl≡swap⋆◎absorbr = swap⋆ ◎ absorbr
  eval₁ swap⋆◎absorbr≡absorbl = absorbl
  eval₁ absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr = (assocl⋆ ◎ (absorbr ⊗ id⟷)) ◎ absorbr
  eval₁ [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr = absorbr
  eval₁ [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr = (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr
  eval₁ assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl = (id⟷ ⊗ absorbr) ◎ absorbl
  eval₁ elim⊥-A[0⊕B]⇔l = (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l
  eval₁ elim⊥-A[0⊕B]⇔r = id⟷ ⊗ unite₊l
  eval₁ elim⊥-1[A⊕B]⇔l = distl ◎ (unite⋆l ⊕ unite⋆l)
  eval₁ elim⊥-1[A⊕B]⇔r = unite⋆l
  eval₁ fully-distribute⇔l = ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
                                ((id⟷ ⊕ swap₊) ⊕ id⟷))
                               ◎ (assocl₊ ⊕ id⟷)
  eval₁ fully-distribute⇔r = (distl ◎ (dist ⊕ dist)) ◎ assocl₊

  exact : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} (ce : c₁ ⇔ c₂) → eval₁ ce ≡ c₂
  exact assoc◎l = refl
  exact assoc◎r = refl
  exact assocl⊕l = refl
  exact assocl⊕r = refl
  exact assocl⊗l = refl
  exact assocl⊗r = refl
  exact assocr⊕r = refl
  exact assocr⊗l = refl
  exact assocr⊗r = refl
  exact assocr⊕l = refl
  exact dist⇔l = refl
  exact dist⇔r = refl
  exact distl⇔l = refl
  exact distl⇔r = refl
  exact factor⇔l = refl
  exact factor⇔r = refl
  exact factorl⇔l = refl
  exact factorl⇔r = refl
  exact idl◎l = refl
  exact idl◎r = refl
  exact idr◎l = refl
  exact idr◎r = refl
  exact linv◎l = refl
  exact linv◎r = refl
  exact rinv◎l = refl
  exact rinv◎r = refl
  exact unite₊l⇔l = refl
  exact unite₊l⇔r = refl
  exact uniti₊l⇔l = refl
  exact uniti₊l⇔r = refl
  exact unite₊r⇔l = refl
  exact unite₊r⇔r = refl
  exact uniti₊r⇔l = refl
  exact uniti₊r⇔r = refl
  exact swapl₊⇔ = refl
  exact swapr₊⇔ = refl
  exact unitel⋆⇔l = refl
  exact uniter⋆⇔l = refl
  exact unitil⋆⇔l = refl
  exact unitir⋆⇔l = refl
  exact unitel⋆⇔r = refl
  exact uniter⋆⇔r = refl
  exact unitil⋆⇔r = refl
  exact unitir⋆⇔r = refl
  exact swapl⋆⇔ = refl
  exact swapr⋆⇔ = refl
  exact id⇔ = refl
  exact (trans⇔ ce ce₁) rewrite exact ce | exact ce₁ = refl
  exact (ce ⊡ ce₁) rewrite exact ce | exact ce₁ = refl
  exact (resp⊕⇔ ce ce₁) rewrite exact ce | exact ce₁ = refl
  exact (resp⊗⇔ ce ce₁) rewrite exact ce | exact ce₁ = refl
  exact id⟷⊕id⟷⇔ = refl
  exact split⊕-id⟷ = refl
  exact hom⊕◎⇔ = refl
  exact hom◎⊕⇔ = refl
  exact id⟷⊗id⟷⇔ = refl
  exact split⊗-id⟷ = refl
  exact hom⊗◎⇔ = refl
  exact hom◎⊗⇔ = refl
  exact triangle⊕l = refl
  exact triangle⊕r = refl
  exact triangle⊗l = refl
  exact triangle⊗r = refl
  exact pentagon⊕l = refl
  exact pentagon⊕r = refl
  exact pentagon⊗l = refl
  exact pentagon⊗r = refl
  exact unite₊l-coh-l = refl
  exact unite₊l-coh-r = refl
  exact unite⋆l-coh-l = refl
  exact unite⋆l-coh-r = refl
  exact hexagonr⊕l = refl
  exact hexagonr⊕r = refl
  exact hexagonl⊕l = refl
  exact hexagonl⊕r = refl
  exact hexagonr⊗l = refl
  exact hexagonr⊗r = refl
  exact hexagonl⊗l = refl
  exact hexagonl⊗r = refl
  exact absorbl⇔l = refl
  exact absorbl⇔r = refl
  exact absorbr⇔l = refl
  exact absorbr⇔r = refl
  exact factorzl⇔l = refl
  exact factorzl⇔r = refl
  exact factorzr⇔l = refl
  exact factorzr⇔r = refl
  exact swap₊distl⇔l = refl
  exact swap₊distl⇔r = refl
  exact dist-swap⋆⇔l = refl
  exact dist-swap⋆⇔r = refl
  exact assocl₊-dist-dist⇔l = refl
  exact assocl₊-dist-dist⇔r = refl
  exact assocl⋆-distl⇔l = refl
  exact assocl⋆-distl⇔r = refl
  exact absorbr0-absorbl0⇔ = refl
  exact absorbl0-absorbr0⇔ = refl
  exact absorbr⇔distl-absorb-unite = refl
  exact distl-absorb-unite⇔absorbr = refl
  exact unite⋆r0-absorbr1⇔ = refl
  exact absorbr1-unite⋆r-⇔ = refl
  exact absorbl≡swap⋆◎absorbr = refl
  exact swap⋆◎absorbr≡absorbl = refl
  exact absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr = refl
  exact [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr = refl
  exact [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr = refl
  exact assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl = refl
  exact elim⊥-A[0⊕B]⇔l = refl
  exact elim⊥-A[0⊕B]⇔r = refl
  exact elim⊥-1[A⊕B]⇔l = refl
  exact elim⊥-1[A⊕B]⇔r = refl
  exact fully-distribute⇔l = refl
  exact fully-distribute⇔r = refl
