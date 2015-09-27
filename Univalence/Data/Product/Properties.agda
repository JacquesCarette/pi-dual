{-# OPTIONS --without-K #-}

-- Note that this is properly named, but it does depend on our version of
-- Equiv and TypeEquiv for a number of things.

module Data.Product.Properties where

open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
  renaming (map to _×→_)

import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong; cong₂)
open import Function using (id; _∘_)

open import Equiv using (_∼_)
open import TypeEquiv
  using (unite⋆; uniti⋆; unite⋆′; uniti⋆′;
    swap⋆; assocl⋆; assocr⋆)

------------------------------------------------------------------------------

id×id∼id : {A B : Set} → (id ×→ id) ∼ id {A = A × B}
id×id∼id x = P.refl

×∘∼∘× : {A B C D E F : Set} →
  {f : A → C} {g : B → D} {h : C → E} {i : D → F} →
  (h ∘ f) ×→ (i ∘ g) ∼ (h ×→ i) ∘ (f ×→ g)
×∘∼∘× x = P.refl

×→-resp-∼ : {A B C D : Set} → {f₀ g₀ : A → B} {f₁ g₁ : C → D} →
  (e₁ : f₀ ∼ g₀) → (e₂ : f₁ ∼ g₁) →
  f₀ ×→ f₁ ∼ g₀ ×→ g₁
×→-resp-∼ e₁ e₂ x = P.cong₂ _,_ (e₁ (proj₁ x)) (e₂ (proj₂ x))

unite⋆-coh : {A B : Set} {f : A → B} →
  unite⋆ ∘ (id ×→ f) ∼ f ∘ unite⋆
unite⋆-coh x = P.refl

-- and the 'converse', of sorts; g is used here because
-- this is usually applied with g = f⁻¹
uniti⋆-coh : {A B : Set} {g : A → B} →
  (id ×→ g) ∘ uniti⋆ ∼ (uniti⋆ ∘ g)
uniti⋆-coh x = P.refl

unite⋆′-coh : {A B : Set} {f : A → B} →
  unite⋆′ ∘ (f ×→ id) ∼ f ∘ unite⋆′
unite⋆′-coh _ = P.refl

uniti⋆′-coh : {A B : Set} {g : A → B} →
  (g ×→ id) ∘ uniti⋆′ ∼ uniti⋆′ ∘ g
uniti⋆′-coh x = P.refl

-- wf = well-formed.  Need a better name than 'coh' everywhere
assocr⋆-wf : {A B C D E F : Set} →
  {f₀ : A → D} {f₁ : B → E} {f₂ : C → F} →
  assocr⋆ ∘ ((f₀ ×→ f₁) ×→ f₂) ∼ (f₀ ×→ (f₁ ×→ f₂)) ∘ assocr⋆
assocr⋆-wf _ = P.refl

assocl⋆-wf : {A B C D E F : Set} →
  {f₀ : A → D} {f₁ : B → E} {f₂ : C → F} →
  ((f₀ ×→ f₁) ×→ f₂) ∘ assocl⋆ ∼ assocl⋆ ∘ (f₀ ×→ (f₁ ×→ f₂))
assocl⋆-wf _ = P.refl

triangle⋆-right : {A B : Set} →
  unite⋆′ ×→ id {A = B} ∼ (id {A = A} ×→ unite⋆) ∘ assocr⋆
triangle⋆-right _ = P.refl

triangle⋆-left : {A B : Set} →
  uniti⋆′ ×→ id {A = B} ∼ assocl⋆ {A} ∘ (id ×→ uniti⋆)
triangle⋆-left _ = P.refl

pentagon⋆-right : {A B C D : Set} →
  assocr⋆ ∘ assocr⋆ {A × B} {C} {D} ∼ id ×→ assocr⋆ ∘ assocr⋆ ∘ assocr⋆ ×→ id
pentagon⋆-right _ = P.refl

pentagon⋆-left : {A B C D : Set} →
  assocl⋆ ∘ assocl⋆ {A} {B} {C × D} ∼ assocl⋆ ×→ id ∘ assocl⋆ ∘ id ×→ assocl⋆
pentagon⋆-left _ = P.refl

{-
swap₊∘[f,g]≡[g,f]∘swap₊ : {A B C D : Set} {f : A → C} {g : B → D} →
  (x : A ⊎ B) → swap₊ (map⊎ f g x) P.≡ map⊎ g f (swap₊ x)
swap₊∘[f,g]≡[g,f]∘swap₊ (inj₁ x) = P.refl
swap₊∘[f,g]≡[g,f]∘swap₊ (inj₂ y) = P.refl

hexagon⊎-right : {A B C : Set} → (x : (A ⊎ B) ⊎ C) →
  assocr₊ (swap₊ (assocr₊ x)) P.≡ map⊎ F.id swap₊ (assocr₊ (map⊎ swap₊ F.id x))
hexagon⊎-right (inj₁ (inj₁ x)) = P.refl
hexagon⊎-right (inj₁ (inj₂ y)) = P.refl
hexagon⊎-right (inj₂ y) = P.refl

hexagon⊎-left : {A B C : Set} → (x : A ⊎ B ⊎ C) →
  assocl₊ (swap₊ (assocl₊ x)) P.≡ map⊎ swap₊ F.id (assocl₊ (map⊎ F.id swap₊ x))
hexagon⊎-left (inj₁ x) = P.refl
hexagon⊎-left (inj₂ (inj₁ x)) = P.refl
hexagon⊎-left (inj₂ (inj₂ y)) = P.refl
-}
------------------------------------------------------------------------------
