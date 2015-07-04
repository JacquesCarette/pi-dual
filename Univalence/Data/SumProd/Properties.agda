{-# OPTIONS --without-K #-}

-- Note that this is properly named, but it does depend on our version of
-- Equiv and TypeEquiv for a number of things.

module Data.SumProd.Properties where

open import Level using (zero; suc)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (Rel)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (map to map×)
open import Data.Empty
open import Data.Unit
import Function as F

open import Equiv
open import TypeEquiv

-- Note that all these lemmas are "simple" in the sense that they
-- are all about map⊎ rather than [_,_]

distl-commute : {A B C D E F : Set} → {f : A → D} {g : B → E} {h : C → F} →
  (x : A × (B ⊎ C)) → distl (map× f (map⊎ g h) x) P.≡ (map⊎ (map× f g) (map× f h) (distl x))
distl-commute (a , inj₁ x) = P.refl
distl-commute (a , inj₂ y) = P.refl

factorl-commute : {A B C D E F : Set} → {f : A → D} {g : B → E} {h : C → F} →
  (x : (A × B) ⊎ (A × C)) → factorl (map⊎ (map× f g) (map× f h) x) P.≡
                            (map× f (map⊎ g h) (factorl x))
factorl-commute (inj₁ (a , b)) = P.refl
factorl-commute (inj₂ (a , c)) = P.refl

dist-commute : {A B C D E F : Set} → {f : A → D} {g : B → E} {h : C → F} →
  (x : (A ⊎ B) × C) → dist (map× (map⊎ f g) h x) P.≡ (map⊎ (map× f h) (map× g h) (dist x))
dist-commute (inj₁ x , c) = P.refl
dist-commute (inj₂ y , c) = P.refl

factor-commute : {A B C D E F : Set} → {f : A → D} {g : B → E} {h : C → F} →
  (x : (A × C) ⊎ (B × C)) → factor (map⊎ (map× f h) (map× g h) x) P.≡
                           (map× (map⊎ f g) h (factor x))
factor-commute (inj₁ x) = P.refl
factor-commute (inj₂ y) = P.refl

distl-swap₊-lemma : {A B C : Set} → (x : (A × (B ⊎ C))) →
  distl (map× F.id swap₊ x) P.≡ (swap₊ (distl x))
distl-swap₊-lemma (x , inj₁ y) = P.refl
distl-swap₊-lemma (x , inj₂ y) = P.refl

factorl-swap₊-lemma : {A B C : Set} → (x : (A × C) ⊎ (A × B)) →
  map× F.id swap₊ (factorl x) P.≡ factorl (swap₊ x)
factorl-swap₊-lemma (inj₁ x) = P.refl
factorl-swap₊-lemma (inj₂ y) = P.refl

dist-swap⋆-lemma : {A B C : Set} → (x : (A ⊎ B) × C) →
  map⊎ swap⋆ swap⋆ (dist x) P.≡ distl (swap⋆ x)
dist-swap⋆-lemma (inj₁ x , z) = P.refl
dist-swap⋆-lemma (inj₂ y , z) = P.refl

factor-swap⋆-lemma : {A B C : Set} → (x : (C × A) ⊎ (C × B)) →
  factor (map⊎ swap⋆ swap⋆ x) P.≡ swap⋆ (factorl x)
factor-swap⋆-lemma (inj₁ x) = P.refl
factor-swap⋆-lemma (inj₂ y) = P.refl

dist-dist-assoc-lemma : {A B C D : Set} → (x : (A ⊎ B ⊎ C) × D) →
  map⊎ dist F.id (dist (map× assocl₊ F.id x)) P.≡
  assocl₊ (map⊎ F.id dist (dist x))
dist-dist-assoc-lemma (inj₁ x , d) = P.refl
dist-dist-assoc-lemma (inj₂ (inj₁ x) , d) = P.refl
dist-dist-assoc-lemma (inj₂ (inj₂ y) , d) = P.refl

assoc-factor-factor-lemma : {A B C D : Set} → (x : ((A × D) ⊎ (B × D)) ⊎ (C × D)) →
  map× assocr₊ F.id (factor (map⊎ factor F.id x))  P.≡
  factor (map⊎ F.id factor (assocr₊ x))
assoc-factor-factor-lemma (inj₁ (inj₁ x)) = P.refl
assoc-factor-factor-lemma (inj₁ (inj₂ y)) = P.refl
assoc-factor-factor-lemma (inj₂ y) = P.refl

distl-assoc-lemma : {A B C D : Set} → (x : A × (B × (C ⊎ D))) →
  distl (assocl⋆ x) P.≡ map⊎ assocl⋆ assocl⋆ (distl (map× F.id distl x))
distl-assoc-lemma (a , b , inj₁ x) = P.refl
distl-assoc-lemma (a , b , inj₂ y) = P.refl

assoc-factorl-lemma : {A B C D : Set} → (x : ((A × B) × C) ⊎ ((A × B) × D)) →
  assocr⋆ (factorl x) P.≡ map× F.id factorl (factorl (map⊎ assocr⋆ assocr⋆ x))
assoc-factorl-lemma (inj₁ x) = P.refl
assoc-factorl-lemma (inj₂ y) = P.refl

-- in theory, this actually says that all ⊥ are equal!
distz0≡distrz0 : (x : ⊥ × ⊥) → distz x P.≡ distzr x
distz0≡distrz0 (() , _)

factorz0≡factorzr0 : (x : ⊥) → factorz x P.≡ factorzr x
factorz0≡factorzr0 ()

distz0≡unite₊∘[distz,distz]∘distl : {A B : Set} (x : ⊥ × (A ⊎ B)) →
  distz x P.≡ unite₊ (map⊎ distz distz (distl x))
distz0≡unite₊∘[distz,distz]∘distl (() , inj₁ _)
distz0≡unite₊∘[distz,distz]∘distl (x , inj₂ y) = P.refl

factorz0≡factorl∘[factorz,factorz]∘uniti₊ : {A B : Set} (x : ⊥) →
  factorz x P.≡ factorl {B = A} {B} (map⊎ factorz factorz (uniti₊ x))
factorz0≡factorl∘[factorz,factorz]∘uniti₊ ()

unite⋆r0≡absorb1 : (x : ⊥ × ⊤) → unite⋆′ x P.≡ distz x
unite⋆r0≡absorb1 _ = P.refl

uniti⋆r0≡factorz : (x : ⊥) → uniti⋆′ x P.≡ factorz x
uniti⋆r0≡factorz ()

absorbl≡absorbr∘swap⋆ : {A : Set} (x : A × ⊥) →
  distzr x P.≡ distz (swap⋆ x)
absorbl≡absorbr∘swap⋆ x = P.refl

factorzr≡swap⋆∘factorz : {A : Set} (x : ⊥) →
  factorzr {A} x P.≡ swap⋆ (factorz x)
factorzr≡swap⋆∘factorz ()

absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr : {A B : Set} → (x : ⊥ × (A × B)) →
  distz x P.≡ distz (map× distz F.id (assocl⋆ x))
absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr x = P.refl

factorz⇔factorz◎[factorz⊗id]◎assocr⋆ : {A B : Set} → (x : ⊥) →
  factorz x P.≡ assocr⋆ {B = A} {B} (map× factorz F.id (factorz x))
factorz⇔factorz◎[factorz⊗id]◎assocr⋆ ()

elim-middle-⊥ : {A B : Set} (x : A × (⊥ × B)) →
  distzr (map× F.id distz x) P.≡ distz (map× distzr F.id (assocl⋆ x))
elim-middle-⊥ x = P.refl

insert-middle-⊥ : {A B : Set} (x : ⊥) →
  map× F.id (factorz {B}) (factorzr {A} x) P.≡ assocr⋆ (map× factorzr F.id (factorz x))
insert-middle-⊥ ()

elim⊥-A[0⊕B] : {A B : Set} (x : A × (⊥ ⊎ B)) →
  map× F.id unite₊ x P.≡ unite₊ (map⊎ distzr F.id (distl x))
elim⊥-A[0⊕B] (a , inj₁ ())
elim⊥-A[0⊕B] (a , inj₂ y) = P.refl

insert⊕⊥-AB : {A B : Set} (x : A × B) →
  map× F.id uniti₊ x P.≡ factorl (map⊎ factorzr F.id (uniti₊ x))
insert⊕⊥-AB (a , b) = P.refl

elim⊤-1[A⊕B] : {A B : Set} (x : ⊤ × (A ⊎ B)) →
  unite⋆ x P.≡ map⊎ unite⋆ unite⋆ (distl x)
elim⊤-1[A⊕B] (tt , inj₁ x) = P.refl
elim⊤-1[A⊕B] (tt , inj₂ y) = P.refl

insert⊤l⊗-A⊕B : {A B : Set} (x : A ⊎ B) →
  uniti⋆ x P.≡ factorl (map⊎ uniti⋆ uniti⋆ x)
insert⊤l⊗-A⊕B (inj₁ x) = P.refl
insert⊤l⊗-A⊕B (inj₂ y) = P.refl

fully-distribute : {A B C D : Set} (x : (A ⊎ B) × (C ⊎ D)) →
  assocl₊ (map⊎ dist dist (distl x)) P.≡
  map⊎ assocl₊ F.id (map⊎ (map⊎ F.id swap₊) F.id (map⊎ assocr₊ F.id (assocl₊
    (map⊎ distl distl (dist x)))))
fully-distribute (inj₁ x , inj₁ x₁) = P.refl
fully-distribute (inj₁ x , inj₂ y) = P.refl
fully-distribute (inj₂ y , inj₁ x) = P.refl
fully-distribute (inj₂ y , inj₂ y₁) = P.refl

fully-factor : {A B C D : Set} (x : (((A × C) ⊎ (B × C)) ⊎ (A × D)) ⊎ (B × D)) →
  factorl (map⊎ factor factor (assocr₊ x)) P.≡
  factor (map⊎ factorl factorl (assocr₊ (map⊎ assocl₊ F.id (map⊎ (map⊎ F.id swap₊) F.id
    (map⊎ assocr₊ F.id x)))))
fully-factor (inj₁ (inj₁ (inj₁ (a , c)))) = P.refl
fully-factor (inj₁ (inj₁ (inj₂ (b , c)))) = P.refl
fully-factor (inj₁ (inj₂ (a , d))) = P.refl
fully-factor (inj₂ (b , d)) = P.refl
