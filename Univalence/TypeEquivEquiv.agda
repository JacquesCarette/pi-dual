{-# OPTIONS --without-K #-}

module TypeEquivEquiv where

open import Equiv using (path⊎; id≃; _≃_; _●_)
open import EquivEquiv

open import Data.Sum.Properties
  using (map⊎idid≡id; map⊎-∘)

-- we define all the equivalences-between-equivalences that hold
-- between type equivalences.

[id,id]≋id : ∀ {A B : Set} → path⊎ {A} {B} id≃ id≃ ≋ id≃
[id,id]≋id = eq map⊎idid≡id map⊎idid≡id

-- map⊎-∘ : {A B C D E F : Set} →
--  {f : A → C} {g : B → D} {h : C → E} {i : D → F} →
--  ∀ x → map⊎ (h F.∘ f) (i F.∘ g) x P.≡ map⊎ h i (map⊎ f g x)

[h●f,i●g]≋[h,i]●[f,g] : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  path⊎ (h ● f) (i ● g) ≋ ((path⊎ h i) ● (path⊎ f g))
[h●f,i●g]≋[h,i]●[f,g] = eq map⊎-∘ map⊎-∘
