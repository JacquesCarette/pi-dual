{-# OPTIONS --without-K #-}

module TypeEquivEquiv where

open import Equiv using (path⊎; id≃; _≃_; _●_)
open import EquivEquiv

open import Data.Sum.Properties
  using (map⊎idid≡id; map⊎-∘; map⊎-resp-≡)

-- we define all the equivalences-between-equivalences that hold
-- between type equivalences.

[id,id]≋id : ∀ {A B : Set} → path⊎ {A} {B} id≃ id≃ ≋ id≃
[id,id]≋id = eq map⊎idid≡id map⊎idid≡id

-- ● and path⊎ commute.  Better name?
[h●f,i●g]≋[h,i]●[f,g] : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  path⊎ (h ● f) (i ● g) ≋ ((path⊎ h i) ● (path⊎ f g))
[h●f,i●g]≋[h,i]●[f,g] = eq map⊎-∘ map⊎-∘

-- path⊎ respects ≋
path⊎-respects-≋ : ∀ {A B C D} {f g : A ≃ B} {h i : C ≃ D} →
  (e₁ : f ≋ g) → (e₂ : h ≋ i) → path⊎ f h ≋ path⊎ g i
path⊎-respects-≋ (eq f~g f⁻¹~g⁻¹) (eq h~i h⁻¹~i⁻¹) =
  eq (map⊎-resp-≡ f~g h~i) (map⊎-resp-≡ f⁻¹~g⁻¹ h⁻¹~i⁻¹)

