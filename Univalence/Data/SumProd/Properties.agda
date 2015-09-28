{-# OPTIONS --without-K #-}

-- Note that this is properly named, but it does depend on our version of
-- Equiv and TypeEquiv for a number of things.

module Data.SumProd.Properties where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_×_; _,_) renaming (map to map×)

import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Function using (id; _∘_)

open import Equiv using (_∼_; sym∼)
open import TypeEquiv
  using (unite₊; uniti₊; swap₊; assocl₊; assocr₊;
         unite⋆; uniti⋆; unite⋆′; uniti⋆′; swap⋆; assocl⋆; assocr⋆;
         distz; distzr; factorz; factorzr;
         dist; factor; distl; factorl)

infixr 1 _⊎→_
infixr 4 _×→_

_⊎→_ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
_⊎→_ = map⊎

_×→_ : ∀ {a b p q}
        {A : Set a} {B : Set b} {P : Set p} {Q : Set q} →
      (A → B) → (P → Q) → (A × P) → (B × Q)
f ×→ g = λ { (x , y) → (f x , g y) }

------------------------------------------------------------------------------
-- Note that all these lemmas are "simple" in the sense that they
-- are all about map⊎ rather than [_,_]

distl-coh : {A B C D E F : Set} →
  {f : A → D} {g : B → E} {h : C → F} →
  distl ∘ (f ×→ (g ⊎→ h)) ∼ ((f ×→ g) ⊎→ (f ×→ h)) ∘ distl
distl-coh (a , inj₁ x) = P.refl
distl-coh (a , inj₂ y) = P.refl

factorl-coh : {A B C D E F : Set} →
  {f : A → D} {g : B → E} {h : C → F} →
  (f ×→ (g ⊎→ h)) ∘ factorl ∼ factorl ∘ ((f ×→ g) ⊎→ (f ×→ h))
factorl-coh (inj₁ (a , b)) = P.refl
factorl-coh (inj₂ (a , c)) = P.refl

dist-coh : {A B C D E F : Set} →
  {f : A → D} {g : B → E} {h : C → F} →
  dist ∘ ((f ⊎→ g) ×→ h) ∼ ((f ×→ h) ⊎→ (g ×→ h)) ∘ dist
dist-coh (inj₁ x , c) = P.refl
dist-coh (inj₂ y , c) = P.refl

factor-coh : {A B C D E F : Set} →
  {f : A → D} {g : B → E} {h : C → F} →
  ((f ⊎→ g) ×→ h) ∘ factor ∼ factor ∘ ((f ×→ h) ⊎→ (g ×→ h))
factor-coh (inj₁ x) = P.refl
factor-coh (inj₂ y) = P.refl

distl-swap₊-lemma : {A B C : Set} →
  distl ∘ (id {A = A} ×→ swap₊ {B} {C}) ∼ swap₊ ∘ distl
distl-swap₊-lemma (x , inj₁ y) = P.refl
distl-swap₊-lemma (x , inj₂ y) = P.refl

factorl-swap₊-lemma : {A B C : Set} →
  (id ×→ swap₊) ∘ factorl ∼ factorl ∘ swap₊ {A × C} {A × B}
factorl-swap₊-lemma (inj₁ x) = P.refl
factorl-swap₊-lemma (inj₂ y) = P.refl

dist-swap⋆-lemma : {A B C : Set} →
  (swap⋆ ⊎→ swap⋆) ∘ dist ∼ distl ∘ swap⋆ {A ⊎ B} {C}
dist-swap⋆-lemma (inj₁ x , z) = P.refl
dist-swap⋆-lemma (inj₂ y , z) = P.refl

factor-swap⋆-lemma : {A B C : Set} →
  factor ∘ (swap⋆ {C} {A} ⊎→ swap⋆ {C} {B}) ∼ swap⋆ ∘ factorl
factor-swap⋆-lemma (inj₁ x) = P.refl
factor-swap⋆-lemma (inj₂ y) = P.refl

dist-dist-assoc-lemma : {A B C D : Set} →
  (dist ⊎→ id) ∘ dist ∘ (assocl₊ {A} {B} {C} ×→ id {A = D}) ∼
  assocl₊ ∘ (id ⊎→ dist) ∘ dist
dist-dist-assoc-lemma (inj₁ x , d) = P.refl
dist-dist-assoc-lemma (inj₂ (inj₁ x) , d) = P.refl
dist-dist-assoc-lemma (inj₂ (inj₂ y) , d) = P.refl

assoc-factor-factor-lemma : {A B C D : Set} →
  (assocr₊ ×→ id) ∘ factor ∘ (factor {A} {B} {D} ⊎→ id {A = C × D}) ∼
  factor ∘ (id ⊎→ factor) ∘ assocr₊
assoc-factor-factor-lemma (inj₁ (inj₁ x)) = P.refl
assoc-factor-factor-lemma (inj₁ (inj₂ y)) = P.refl
assoc-factor-factor-lemma (inj₂ y) = P.refl

distl-assoc-lemma : {A B C D : Set} →
  distl ∘ assocl⋆ {A} {B} {C ⊎ D} ∼ (assocl⋆ ⊎→ assocl⋆) ∘ distl ∘ (id ×→ distl)
distl-assoc-lemma (a , b , inj₁ x) = P.refl
distl-assoc-lemma (a , b , inj₂ y) = P.refl

assoc-factorl-lemma : {A B C D : Set} →
  assocr⋆ ∘ factorl {A × B} {C} {D} ∼ (id ×→ factorl) ∘ factorl ∘ (assocr⋆ ⊎→ assocr⋆)
assoc-factorl-lemma (inj₁ x) = P.refl
assoc-factorl-lemma (inj₂ y) = P.refl

-- in theory, this actually says that all ⊥ are equal!

distz0≡distrz0 : distz ∼ distzr
distz0≡distrz0 (() , _)

factorz0≡factorzr0 : factorz ∼ factorzr
factorz0≡factorzr0 ()

distz0≡unite₊∘[distz,distz]∘distl : {A B : Set} →
  distz ∼ unite₊ ∘ (distz ⊎→ distz) ∘ distl {⊥} {A} {B}
distz0≡unite₊∘[distz,distz]∘distl (() , inj₁ _)
distz0≡unite₊∘[distz,distz]∘distl (x , inj₂ y) = P.refl

factorz0≡factorl∘[factorz,factorz]∘uniti₊ : {A B : Set} →
  factorz ∼ factorl {B = A} {B} ∘ (factorz ⊎→ factorz) ∘ uniti₊
factorz0≡factorl∘[factorz,factorz]∘uniti₊ ()

unite⋆r0≡absorb1 : unite⋆′ ∼ distz
unite⋆r0≡absorb1 _ = P.refl

uniti⋆r0≡factorz : uniti⋆′ ∼ factorz
uniti⋆r0≡factorz ()

absorbl≡absorbr∘swap⋆ : {A : Set} → distzr {A} ∼ distz ∘ swap⋆
absorbl≡absorbr∘swap⋆ _ = P.refl

factorzr≡swap⋆∘factorz : {A : Set} → factorzr {A} ∼ swap⋆ ∘ factorz
factorzr≡swap⋆∘factorz ()

absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr : {A B : Set} →
  distz ∼ distz ∘ (distz ×→ id) ∘ assocl⋆ {⊥} {A} {B}
absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr x = P.refl

factorz⇔factorz◎[factorz⊗id]◎assocr⋆ : {A B : Set} →
  factorz ∼ assocr⋆ {B = A} {B} ∘ (factorz ×→ id) ∘ factorz
factorz⇔factorz◎[factorz⊗id]◎assocr⋆ ()

elim-middle-⊥ : {A B : Set} →
  distzr ∘ (id ×→ distz) ∼ distz ∘ (distzr ×→ id) ∘ assocl⋆ {A} {⊥} {B}
elim-middle-⊥ x = P.refl

insert-middle-⊥ : {A B : Set} →
  (id ×→ factorz {B}) ∘ factorzr {A} ∼ assocr⋆ ∘ (factorzr ×→ id) ∘ factorz
insert-middle-⊥ ()

elim⊥-A[0⊕B] : {A B : Set} →
  (id {A = A} ×→ unite₊ {B}) ∼ unite₊ ∘ (distzr ⊎→ id) ∘ distl
elim⊥-A[0⊕B] (a , inj₁ ())
elim⊥-A[0⊕B] (a , inj₂ y) = P.refl

insert⊕⊥-AB : {A B : Set} →
  (id ×→ uniti₊) ∼ factorl ∘ (factorzr ⊎→ id) ∘ uniti₊ {A × B}
insert⊕⊥-AB (a , b) = P.refl

elim⊤-1[A⊕B] : {A B : Set} →
  unite⋆ ∼ (unite⋆ ⊎→ unite⋆) ∘ distl {⊤} {A} {B}
elim⊤-1[A⊕B] (tt , inj₁ x) = P.refl
elim⊤-1[A⊕B] (tt , inj₂ y) = P.refl

insert⊤l⊗-A⊕B : {A B : Set} →
  uniti⋆ ∼ factorl ∘ (uniti⋆ {A} ⊎→ uniti⋆ {B})
insert⊤l⊗-A⊕B (inj₁ x) = P.refl
insert⊤l⊗-A⊕B (inj₂ y) = P.refl

fully-distribute : {A B C D : Set} →
  assocl₊ ∘ (dist ⊎→ dist) ∘ distl ∼
  (assocl₊ ⊎→ id) ∘ ((id ⊎→ swap₊) ⊎→ id) ∘
     (assocr₊ ⊎→ id) ∘ assocl₊ ∘ (distl ⊎→ distl) ∘ dist {A} {B} {C ⊎ D}
fully-distribute (inj₁ x , inj₁ x₁) = P.refl
fully-distribute (inj₁ x , inj₂ y) = P.refl
fully-distribute (inj₂ y , inj₁ x) = P.refl
fully-distribute (inj₂ y , inj₂ y₁) = P.refl

fully-factor : {A B C D : Set} →
  -- (x : (((A × C) ⊎ (B × C)) ⊎ (A × D)) ⊎ (B × D)) →
  factorl ∘ (factor ⊎→ factor) ∘ assocr₊ ∼
  factor ∘ (factorl ⊎→ factorl) ∘ assocr₊ ∘(assocl₊ ⊎→ id) ∘
      ((id ⊎→ swap₊) ⊎→ id) ∘ (assocr₊ {A × C} ⊎→ id {A = B × D})
fully-factor (inj₁ (inj₁ (inj₁ (a , c)))) = P.refl
fully-factor (inj₁ (inj₁ (inj₂ (b , c)))) = P.refl
fully-factor (inj₁ (inj₂ (a , d))) = P.refl
fully-factor (inj₂ (b , d)) = P.refl

------------------------------------------------------------------------------
