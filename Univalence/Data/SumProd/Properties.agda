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

-- note how this is true without relying on ⊥ as input
distzr-coh : {A B : Set} → {f : A → B} → {g : ⊥ → ⊥} →
  distzr ∘ (f ×→ g) ∼ g ∘ distzr
distzr-coh _ = P.refl

-- but this is only true because of ⊥
factorzr-coh : {A B : Set} → {f : B → A} → {g : ⊥ → ⊥} →
  (f ×→ g) ∘ factorzr ∼ factorzr ∘ g
factorzr-coh ()

-- note how this is true without relying on ⊥ as input
distz-coh : {A B : Set} → {f : A → B} → {g : ⊥ → ⊥} →
  distz ∘ (g ×→ f) ∼ g ∘ distz
distz-coh _ = P.refl

-- but this is only true because of ⊥
factorz-coh : {A B : Set} → {f : B → A} → {g : ⊥ → ⊥} →
  (g ×→ f) ∘ factorz ∼ factorz ∘ g
factorz-coh ()

---------------------------------------------------------------
-- various coherence lemmas

-- These will be named for the action they perform on the
-- underlying type, rather than for the program they
-- represent.  
A×[B⊎C]→[A×C]⊎[A×B] : {A B C : Set} →
  distl ∘ (id {A = A} ×→ swap₊ {B} {C}) ∼ swap₊ ∘ distl
A×[B⊎C]→[A×C]⊎[A×B] (x , inj₁ y) = P.refl
A×[B⊎C]→[A×C]⊎[A×B] (x , inj₂ y) = P.refl

[A×C]⊎[A×B]→A×[B⊎C] : {A B C : Set} →
  (id ×→ swap₊) ∘ factorl ∼ factorl ∘ swap₊ {A × C} {A × B}
[A×C]⊎[A×B]→A×[B⊎C] (inj₁ x) = P.refl
[A×C]⊎[A×B]→A×[B⊎C] (inj₂ y) = P.refl

[A⊎B]×C→[C×A]⊎[C×B] : {A B C : Set} →
  (swap⋆ ⊎→ swap⋆) ∘ dist ∼ distl ∘ swap⋆ {A ⊎ B} {C}
[A⊎B]×C→[C×A]⊎[C×B] (inj₁ x , z) = P.refl
[A⊎B]×C→[C×A]⊎[C×B] (inj₂ y , z) = P.refl

[C×A]⊎[C×B]→[A⊎B]×C : {A B C : Set} →
  factor ∘ (swap⋆ {C} {A} ⊎→ swap⋆ {C} {B}) ∼ swap⋆ ∘ factorl
[C×A]⊎[C×B]→[A⊎B]×C (inj₁ x) = P.refl
[C×A]⊎[C×B]→[A⊎B]×C (inj₂ y) = P.refl

-- × binds tighter than ⊎ (in the name)
[A⊎B⊎C]×D→[A×D⊎B×D]⊎C×D : {A B C D : Set} →
  (dist ⊎→ id) ∘ dist ∘ (assocl₊ {A} {B} {C} ×→ id {A = D}) ∼
  assocl₊ ∘ (id ⊎→ dist) ∘ dist
[A⊎B⊎C]×D→[A×D⊎B×D]⊎C×D (inj₁ x , d) = P.refl
[A⊎B⊎C]×D→[A×D⊎B×D]⊎C×D (inj₂ (inj₁ x) , d) = P.refl
[A⊎B⊎C]×D→[A×D⊎B×D]⊎C×D (inj₂ (inj₂ y) , d) = P.refl

[A×D⊎B×D]⊎C×D→[A⊎B⊎C]×D : {A B C D : Set} →
  (assocr₊ ×→ id) ∘ factor ∘ (factor {A} {B} {D} ⊎→ id {A = C × D}) ∼
  factor ∘ (id ⊎→ factor) ∘ assocr₊
[A×D⊎B×D]⊎C×D→[A⊎B⊎C]×D (inj₁ (inj₁ x)) = P.refl
[A×D⊎B×D]⊎C×D→[A⊎B⊎C]×D (inj₁ (inj₂ y)) = P.refl
[A×D⊎B×D]⊎C×D→[A⊎B⊎C]×D (inj₂ y) = P.refl


A×B×[C⊎D]→[A×B]×C⊎[A×B]×D : {A B C D : Set} →
  distl ∘ assocl⋆ {A} {B} {C ⊎ D} ∼ (assocl⋆ ⊎→ assocl⋆) ∘ distl ∘ (id ×→ distl)
A×B×[C⊎D]→[A×B]×C⊎[A×B]×D (a , b , inj₁ x) = P.refl
A×B×[C⊎D]→[A×B]×C⊎[A×B]×D (a , b , inj₂ y) = P.refl

[A×B]×C⊎[A×B]×D→A×B×[C⊎D] : {A B C D : Set} →
  assocr⋆ ∘ factorl {A × B} {C} {D} ∼ (id ×→ factorl) ∘ factorl ∘ (assocr⋆ ⊎→ assocr⋆)
[A×B]×C⊎[A×B]×D→A×B×[C⊎D] (inj₁ x) = P.refl
[A×B]×C⊎[A×B]×D→A×B×[C⊎D] (inj₂ y) = P.refl

-- in theory, this actually says that all ⊥ are equal!
-- the annotations can be inferred, but this makes it
-- clearer still
0×0→0 : distz {⊥} ∼ distzr {⊥}
0×0→0 (() , ())

0→0×0 : factorz {⊥} ∼ factorzr {⊥}
0→0×0 ()

0×[A⊎B]→0 : {A B : Set} →
  distz ∼ unite₊ ∘ (distz ⊎→ distz) ∘ distl {⊥} {A} {B}
0×[A⊎B]→0 (() , inj₁ _)
0×[A⊎B]→0 (_  , inj₂ _) = P.refl

0→0×[A⊎B] : {A B : Set} →
  factorz ∼ factorl {B = A} {B} ∘ (factorz ⊎→ factorz) ∘ uniti₊
0→0×[A⊎B] ()

0×1→0 : unite⋆′ {⊥} ∼ distz {⊤}
0×1→0 _ = P.refl

0→0×1 : uniti⋆′ {⊥} ∼ factorz {⊤}
0→0×1 ()

A×0→0 : {A : Set} → distzr {A} ∼ distz ∘ swap⋆
A×0→0 _ = P.refl

0→A×0 : {A : Set} → factorzr {A} ∼ swap⋆ ∘ factorz
0→A×0 ()

0×A×B→0 : {A B : Set} →
  distz ∼ distz ∘ (distz ×→ id) ∘ assocl⋆ {⊥} {A} {B}
0×A×B→0 _ = P.refl

0→0×A×B : {A B : Set} →
  factorz ∼ assocr⋆ {B = A} {B} ∘ (factorz ×→ id) ∘ factorz
0→0×A×B ()

A×0×B→0 : {A B : Set} →
  distzr ∘ (id ×→ distz) ∼ distz ∘ (distzr ×→ id) ∘ assocl⋆ {A} {⊥} {B}
A×0×B→0 _ = P.refl

0→A×0×B : {A B : Set} →
  (id ×→ factorz {B}) ∘ factorzr {A} ∼ assocr⋆ ∘ (factorzr ×→ id) ∘ factorz
0→A×0×B ()

A×[0+B]→A×B : {A B : Set} →
  (id {A = A} ×→ unite₊ {B}) ∼ unite₊ ∘ (distzr ⊎→ id) ∘ distl
A×[0+B]→A×B (_ , inj₁ ())
A×[0+B]→A×B (_ , inj₂ _) = P.refl

A×B→A×[0+B] : {A B : Set} →
  (id ×→ uniti₊) ∼ factorl ∘ (factorzr ⊎→ id) ∘ uniti₊ {A × B}
A×B→A×[0+B] (_ , _) = P.refl

1×[A⊎B]→A⊎B : {A B : Set} →
  unite⋆ ∼ (unite⋆ ⊎→ unite⋆) ∘ distl {⊤} {A} {B}
1×[A⊎B]→A⊎B (tt , inj₁ x) = P.refl
1×[A⊎B]→A⊎B (tt , inj₂ y) = P.refl

A⊎B→1×[A⊎B] : {A B : Set} →
  uniti⋆ ∼ factorl ∘ (uniti⋆ {A} ⊎→ uniti⋆ {B})
A⊎B→1×[A⊎B] (inj₁ x) = P.refl
A⊎B→1×[A⊎B] (inj₂ y) = P.refl

-- [A⊎B]×[C⊎D]→[[A×C⊎B×C]⊎A×D]⊎B×D
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
