{-# OPTIONS --without-K #-}

module TypeEquivEquiv where

open import Equiv using (sym∼; sym≃; _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv)
open import TypeEquiv
  using (unite₊equiv; uniti₊equiv; unite₊′equiv; uniti₊′equiv;
    assocr₊equiv; assocl₊equiv; swap₊equiv;
    unite⋆equiv; uniti⋆equiv; unite⋆′equiv; uniti⋆′equiv;
    assocr⋆equiv; assocl⋆equiv)
open import EquivEquiv

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; _×_)

open import Data.Sum.Properties
  using (id⊎id∼id; ⊎∘∼∘⊎; ⊎→-resp-∼;
    unite₊∘[id,f]≡f∘unite₊; [id,g]∘uniti₊≡uniti₊∘g;
    unite₊′∘[f,id]≡f∘unite₊′; [g,id]∘uniti₊′≡uniti₊′∘g;
    assocr₊∘[[,],]; [[,],]∘assocl₊;
    triangle⊎-left; triangle⊎-right;
    pentagon⊎-right; pentagon⊎-left;
    swap₊-coh; hexagon⊎-right; hexagon⊎-left)

open import Data.Product.Properties
  using (id×id∼id; ×∘∼∘×; ×→-resp-∼;
    unite⋆-coh; uniti⋆-coh; unite⋆′-coh; uniti⋆′-coh;
    assocr⋆-wf; assocl⋆-wf;
    triangle⋆-left; triangle⋆-right;
    pentagon⋆-right; pentagon⋆-left)
  
-- we define all the equivalences-between-equivalences that hold
-- between type equivalences.

----
-- equivalences for the ⊎ structure

[id,id]≋id : ∀ {A B : Set} → id≃ {A = A} ⊎≃ id≃ {A = B} ≋ id≃
[id,id]≋id = eq id⊎id∼id id⊎id∼id

-- ● and ⊎≃ commute.
⊎●≋●⊎ : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  (h ● f) ⊎≃ (i ● g) ≋ (h ⊎≃ i) ● (f ⊎≃ g)
⊎●≋●⊎ = eq ⊎∘∼∘⊎ ⊎∘∼∘⊎

-- ⊎≃ respects ≋
⊎≃-respects-≋ : ∀ {A B C D} {f g : A ≃ B} {h i : C ≃ D} →
  (e₁ : f ≋ g) → (e₂ : h ≋ i) → f ⊎≃ h ≋ g ⊎≃ i
⊎≃-respects-≋ (eq f~g f⁻¹~g⁻¹) (eq h~i h⁻¹~i⁻¹) =
  eq (⊎→-resp-∼ f~g h~i) (⊎→-resp-∼ f⁻¹~g⁻¹ h⁻¹~i⁻¹)

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

-- often called 'triangle'
unite-assocr₊-coh : ∀ {A B : Set} →
  unite₊′equiv ⊎≃ id≃ ≋ (id≃ ⊎≃ unite₊equiv) ● assocr₊equiv {A} {⊥} {B}
unite-assocr₊-coh = eq triangle⊎-right triangle⊎-left

-- often called 'pentagon'
assocr₊-coh : ∀ {A B C D : Set} →
  assocr₊equiv {A} {B} {C ⊎ D} ● assocr₊equiv ≋
  (id≃ ⊎≃ assocr₊equiv) ● assocr₊equiv ● (assocr₊equiv ⊎≃ id≃)
assocr₊-coh = eq pentagon⊎-right pentagon⊎-left

swap₊-nat : {A B C D : Set} {f : A ≃ C} {g : B ≃ D} →
  swap₊equiv ● (f ⊎≃ g) ≋ (g ⊎≃ f) ● swap₊equiv
swap₊-nat = eq swap₊-coh (sym∼ swap₊-coh)

-- often called 'hexagon'
assocr₊-swap₊-coh : ∀ {A B C : Set} →
  assocr₊equiv {B} {C} {A} ● swap₊equiv ● assocr₊equiv {A} {B} {C} ≋
  id≃ ⊎≃ swap₊equiv ● assocr₊equiv ● swap₊equiv ⊎≃ id≃
assocr₊-swap₊-coh = eq hexagon⊎-right hexagon⊎-left

-- and in the opposite direction
assocl₊-swap₊-coh : ∀ {A B C : Set} →
  assocl₊equiv {A} {B} {C} ● swap₊equiv ● assocl₊equiv {B} {C} {A} ≋
  swap₊equiv ⊎≃ id≃ ● assocl₊equiv ● id≃ ⊎≃ swap₊equiv
assocl₊-swap₊-coh = eq hexagon⊎-left hexagon⊎-right

----
-- equivalences for the × structure
id×id≋id : ∀ {A B : Set} → id≃ {A = A} ×≃ id≃ {A = B} ≋ id≃
id×id≋id = eq id×id∼id id×id∼id

×●≋●× : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  (h ● f) ×≃ (i ● g) ≋ (h ×≃ i) ● (f ×≃ g)
×●≋●× {f = f , qinv f′ _ _} {g , qinv g′ _ _} {h , qinv h′ _ _} {i , qinv i′ _ _} =
  eq (×∘∼∘× {f = f} {g} {h} {i}) (×∘∼∘× {f = h′} {i′} {f′} {g′})

×≃-resp-≋ :  ∀ {A B C D : Set} {f g : A ≃ B} {h i : C ≃ D} →
  (e₁ : f ≋ g) → (e₂ : h ≋ i) → f ×≃ h ≋ g ×≃ i
×≃-resp-≋ e₁ e₂ = eq (×→-resp-∼ (f≡ e₁) (f≡ e₂))
                     (×→-resp-∼ (g≡ e₁) (g≡ e₂))
  where open _≋_

unite⋆-nat : ∀ {A B} {f : A ≃ B} →
  unite⋆equiv ● (id≃ {A = ⊤} ×≃ f) ≋ f ● unite⋆equiv
unite⋆-nat = eq unite⋆-coh uniti⋆-coh

uniti⋆-nat : ∀ {A B} {f : A ≃ B} →
  uniti⋆equiv ● f ≋ (id≃ {A = ⊤} ×≃ f) ● uniti⋆equiv
uniti⋆-nat =  flip-sym≋ unite⋆-nat

unite⋆′-nat : ∀ {A B} {f : A ≃ B} →
  unite⋆′equiv ● (f ×≃ id≃ {A = ⊤}) ≋ f ● unite⋆′equiv
unite⋆′-nat = eq unite⋆′-coh uniti⋆′-coh

uniti⋆′-nat : ∀ {A B} {f : A ≃ B} →
  uniti⋆′equiv ● f ≋ (f ×≃ id≃ {A = ⊤}) ● uniti⋆′equiv
uniti⋆′-nat = flip-sym≋ unite⋆′-nat

assocr⋆-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocr⋆equiv ● ((f₀ ×≃ f₁) ×≃ f₂) ≋ (f₀ ×≃ (f₁ ×≃ f₂)) ● assocr⋆equiv
assocr⋆-nat = eq assocr⋆-wf assocl⋆-wf

assocl⋆-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocl⋆equiv ● (f₀ ×≃ (f₁ ×≃ f₂)) ≋ ((f₀ ×≃ f₁) ×≃ f₂) ● assocl⋆equiv
assocl⋆-nat = flip-sym≋ assocr⋆-nat

-- often called 'triangle'
unite-assocr⋆-coh : ∀ {A B : Set} →
  unite⋆′equiv ×≃ id≃ ≋ (id≃ ×≃ unite⋆equiv) ● assocr⋆equiv {A} {⊤} {B}
unite-assocr⋆-coh = eq triangle⋆-right triangle⋆-left

-- often called 'pentagon'
assocr⋆-coh : ∀ {A B C D : Set} →
  assocr⋆equiv {A} {B} {C × D} ● assocr⋆equiv ≋
  (id≃ ×≃ assocr⋆equiv) ● assocr⋆equiv ● (assocr⋆equiv ×≃ id≃)
assocr⋆-coh = eq pentagon⋆-right pentagon⋆-left
