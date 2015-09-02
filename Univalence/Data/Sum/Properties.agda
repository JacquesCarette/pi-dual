{-# OPTIONS --without-K #-}

-- Note that this is properly named, but it does depend on our version of
-- Equiv and TypeEquiv for a number of things.

module Data.Sum.Properties where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)

import Relation.Binary.PropositionalEquality as P using (_≡_; refl; cong)
import Function as F using (id; _∘_)

open import Equiv using (_∼_)
open import TypeEquiv using (unite₊; unite₊′; swap₊; assocl₊; assocr₊)

------------------------------------------------------------------------------
-- Note that all these lemmas are "simple" in the sense that they
-- are all about map⊎ rather than [_,_]

map⊎idid≡id : {A B : Set} → (x : A ⊎ B) → map⊎ F.id F.id x P.≡ x
map⊎idid≡id (inj₁ x) = P.refl
map⊎idid≡id (inj₂ y) = P.refl

map⊎-∘ : {A B C D E F : Set} →
  {f : A → C} {g : B → D} {h : C → E} {i : D → F} →
  ∀ x → map⊎ (h F.∘ f) (i F.∘ g) x P.≡ map⊎ h i (map⊎ f g x)
map⊎-∘ (inj₁ x) = P.refl
map⊎-∘ (inj₂ y) = P.refl

map⊎-resp-≡ : {A B C D : Set} → {f₀ g₀ : A → B} {f₁ g₁ : C → D} →
  (e₁ : f₀ ∼ g₀) → (e₂ : f₁ ∼ g₁) →  
  (x : A ⊎ C) → map⊎ f₀ f₁ x P.≡ map⊎ g₀ g₁ x
map⊎-resp-≡ f₀~g₀ _ (inj₁ x) = P.cong inj₁ (f₀~g₀ x)
map⊎-resp-≡ _ f₁~g₁ (inj₂ y) = P.cong inj₂ (f₁~g₁ y)

unite₊∘[id,f]≡f∘unite₊ : {A B : Set} {f : A → B} {g : ⊥ → ⊥} →
  (x : ⊥ ⊎ A) → unite₊ (map⊎ g f x) P.≡ f (unite₊ x)
unite₊∘[id,f]≡f∘unite₊ (inj₁ ())
unite₊∘[id,f]≡f∘unite₊ (inj₂ y) = P.refl

unite₊′∘[id,f]≡f∘unite₊′ : {A B : Set} {f : A → B} {g : ⊥ → ⊥} →
  (x : A ⊎ ⊥) → unite₊′ (map⊎ f g x) P.≡ f (unite₊′ x)
unite₊′∘[id,f]≡f∘unite₊′ (inj₁ x) = P.refl
unite₊′∘[id,f]≡f∘unite₊′ (inj₂ ())

inj₂∘unite₊~id : {A : Set} → (x : ⊥ ⊎ A) → inj₂ (unite₊ x) P.≡ x
inj₂∘unite₊~id (inj₁ ())
inj₂∘unite₊~id (inj₂ y) = P.refl

f∘unite₊′≡unite₊′∘[f,id] : {A B : Set} {f : A → B} →
  (x : A ⊎ ⊥) → f (unite₊′ x) P.≡ unite₊′ (map⊎ f F.id x)
f∘unite₊′≡unite₊′∘[f,id] (inj₁ x) = P.refl
f∘unite₊′≡unite₊′∘[f,id] (inj₂ ())

inj₁∘unite₊′~id : {A : Set} → (x : A ⊎ ⊥) → inj₁ (unite₊′ x) P.≡ x
inj₁∘unite₊′~id (inj₁ x) = P.refl
inj₁∘unite₊′~id (inj₂ ())

assocr₊∘[[,],] : {A B C D E F : Set} →
  {f₀ : A → D} {f₁ : B → E} {f₂ : C → F} → (x : (A ⊎ B) ⊎ C) →
  assocr₊ (map⊎ (map⊎ f₀ f₁) f₂ x) P.≡ map⊎ f₀ (map⊎ f₁ f₂) (assocr₊ x)
assocr₊∘[[,],] (inj₁ (inj₁ x)) = P.refl
assocr₊∘[[,],] (inj₁ (inj₂ y)) = P.refl
assocr₊∘[[,],] (inj₂ y) = P.refl

[[,],]∘assocl₊ : {A B C D E F : Set} →
  {f₀ : A → D} {f₁ : B → E} {f₂ : C → F} → (x : A ⊎ (B ⊎ C)) →
  map⊎ (map⊎ f₀ f₁) f₂ (assocl₊ x) P.≡ assocl₊ (map⊎ f₀ (map⊎ f₁ f₂) x)
[[,],]∘assocl₊ (inj₁ x) = P.refl
[[,],]∘assocl₊ (inj₂ (inj₁ x)) = P.refl
[[,],]∘assocl₊ (inj₂ (inj₂ y)) = P.refl

triangle⊎-right : {A B : Set} → (x : (A ⊎ ⊥) ⊎ B) →
  map⊎ unite₊′ F.id x P.≡ map⊎ F.id unite₊ (assocr₊ x)
triangle⊎-right (inj₁ (inj₁ x)) = P.refl
triangle⊎-right (inj₁ (inj₂ ()))
triangle⊎-right (inj₂ y) = P.refl

-- note how C is completely arbitrary here (and not ⊥ like in the above)
triangle⊎-left : {A B C : Set} → (x : A ⊎ B) →
  map⊎ (inj₁ {B = C}) F.id x P.≡ assocl₊ (map⊎ F.id inj₂ x)
triangle⊎-left (inj₁ x) = P.refl
triangle⊎-left (inj₂ y) = P.refl

pentagon⊎-right : {A B C D : Set} → (x : ((A ⊎ B) ⊎ C) ⊎ D) →
  assocr₊ (assocr₊ x) P.≡ map⊎ F.id assocr₊ (assocr₊ (map⊎ assocr₊ F.id x))
pentagon⊎-right (inj₁ (inj₁ (inj₁ x))) = P.refl
pentagon⊎-right (inj₁ (inj₁ (inj₂ y))) = P.refl
pentagon⊎-right (inj₁ (inj₂ y)) = P.refl
pentagon⊎-right (inj₂ y) = P.refl

pentagon⊎-left : {A B C D : Set} → (x : A ⊎ B ⊎ C ⊎ D) →
  assocl₊ (assocl₊ x) P.≡ map⊎ assocl₊ F.id (assocl₊ (map⊎ F.id assocl₊ x))
pentagon⊎-left (inj₁ x) = P.refl
pentagon⊎-left (inj₂ (inj₁ x)) = P.refl
pentagon⊎-left (inj₂ (inj₂ (inj₁ x))) = P.refl
pentagon⊎-left (inj₂ (inj₂ (inj₂ y))) = P.refl


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

------------------------------------------------------------------------------
