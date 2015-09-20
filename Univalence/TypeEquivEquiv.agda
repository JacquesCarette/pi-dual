{-# OPTIONS --without-K #-}

module TypeEquivEquiv where

open import Equiv using (sym∼; sym≃; _⊎≃_; id≃; _≃_; _●_)
open import TypeEquiv
  using (unite₊equiv; uniti₊equiv; unite₊′equiv; uniti₊′equiv;
    assocr₊equiv; assocl₊equiv)
open import EquivEquiv

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)

open import Data.Sum.Properties
  using (map⊎idid≡id; map⊎-∘; map⊎-resp-≡;
    unite₊∘[id,f]≡f∘unite₊; [id,g]∘uniti₊≡uniti₊∘g;
    unite₊′∘[f,id]≡f∘unite₊′; [g,id]∘uniti₊′≡uniti₊′∘g;
    assocr₊∘[[,],]; [[,],]∘assocl₊;
    triangle⊎-left; triangle⊎-right;
    pentagon⊎-right; pentagon⊎-left)

-- we define all the equivalences-between-equivalences that hold
-- between type equivalences.

[id,id]≋id : ∀ {A B : Set} → id≃ {A = A} ⊎≃ id≃ {A = B} ≋ id≃
[id,id]≋id = eq map⊎idid≡id map⊎idid≡id

-- ● and ⊎≃ commute.  Better name?
[h●f,i●g]≋[h,i]●[f,g] : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  (h ● f) ⊎≃ (i ● g) ≋ (h ⊎≃ i) ● (f ⊎≃ g)
[h●f,i●g]≋[h,i]●[f,g] = eq map⊎-∘ map⊎-∘

-- ⊎≃ respects ≋
⊎≃-respects-≋ : ∀ {A B C D} {f g : A ≃ B} {h i : C ≃ D} →
  (e₁ : f ≋ g) → (e₂ : h ≋ i) → f ⊎≃ h ≋ g ⊎≃ i
⊎≃-respects-≋ (eq f~g f⁻¹~g⁻¹) (eq h~i h⁻¹~i⁻¹) =
  eq (map⊎-resp-≡ f~g h~i) (map⊎-resp-≡ f⁻¹~g⁻¹ h⁻¹~i⁻¹)

-- Use '-nat' to signify that operation induces a
-- natural transformation, and that the induced operation
-- satisfies the naturality condition thus encoded
unite₊-nat : ∀ {A B} {f : A ≃ B} →
  unite₊equiv ● (id≃ {A = ⊥} ⊎≃ f) ≋ f ● unite₊equiv
unite₊-nat =
  eq unite₊∘[id,f]≡f∘unite₊ [id,g]∘uniti₊≡uniti₊∘g

uniti₊-nat : ∀ {A B} {f : A ≃ B} →
  uniti₊equiv ● f ≋ (id≃ {A = ⊥} ⊎≃ f) ● uniti₊equiv
uniti₊-nat =  flip-sym≋ unite₊-nat

unite₊′-nat : ∀ {A B} {f : A ≃ B} →
  unite₊′equiv ● (f ⊎≃ id≃ {A = ⊥}) ≋ f ● unite₊′equiv
unite₊′-nat =
  eq unite₊′∘[f,id]≡f∘unite₊′ [g,id]∘uniti₊′≡uniti₊′∘g

uniti₊′-nat : ∀ {A B} {f : A ≃ B} →
  uniti₊′equiv ● f ≋ (f ⊎≃ id≃ {A = ⊥}) ● uniti₊′equiv
uniti₊′-nat = flip-sym≋ unite₊′-nat

assocr₊-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocr₊equiv ● ((f₀ ⊎≃ f₁) ⊎≃ f₂) ≋ (f₀ ⊎≃ (f₁ ⊎≃ f₂)) ● assocr₊equiv
assocr₊-nat = eq assocr₊∘[[,],] [[,],]∘assocl₊

assocl₊-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocl₊equiv ● (f₀ ⊎≃ (f₁ ⊎≃ f₂)) ≋ ((f₀ ⊎≃ f₁) ⊎≃ f₂) ● assocl₊equiv
assocl₊-nat = flip-sym≋ assocr₊-nat

⊎≃-triangle : ∀ {A B : Set} →
  unite₊′equiv ⊎≃ id≃ ≋ (id≃ ⊎≃ unite₊equiv) ● assocr₊equiv {A} {⊥} {B}
⊎≃-triangle = eq triangle⊎-right triangle⊎-left

⊎≃-pentagon : ∀ {A B C D : Set} →
  assocr₊equiv {A} {B} {C ⊎ D} ● assocr₊equiv ≋
  (id≃ ⊎≃ assocr₊equiv) ● assocr₊equiv ● (assocr₊equiv ⊎≃ id≃)
⊎≃-pentagon = eq pentagon⊎-right pentagon⊎-left
