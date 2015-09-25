{-# OPTIONS --without-K #-}

module FinEquivEquiv where

open import Equiv using (sym∼; sym≃; _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv)
open import FinEquivTypeEquiv
open import EquivEquiv

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_)

open import Data.Sum.Properties
  using (id⊎id∼id; ⊎∘∼∘⊎; ⊎→-resp-∼;
    unite₊∘[id,f]≡f∘unite₊; [id,g]∘uniti₊≡uniti₊∘g;
    unite₊′∘[f,id]≡f∘unite₊′; [g,id]∘uniti₊′≡uniti₊′∘g;
    assocr₊∘[[,],]; [[,],]∘assocl₊;
    triangle⊎-left; triangle⊎-right;
    pentagon⊎-right; pentagon⊎-left)

open import Data.Product.Properties
  using (id×id∼id; ×∘∼∘×; ×→-resp-∼;
    unite⋆-coh; uniti⋆-coh)

------------------------------------------------------------------------------
-- equivalences for the ⊎ structure

[id,id]≋id : ∀ {m n : ℕ} →
  id≃ {A = Fin m} ⊎≃ id≃ {A = Fin n} ≋ id≃ {A = Fin m ⊎ Fin n}
[id,id]≋id = eq id⊎id∼id id⊎id∼id 


------------------------------------------------------------------------------


