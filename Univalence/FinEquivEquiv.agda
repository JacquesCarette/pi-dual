{-# OPTIONS --without-K #-}

module FinEquivEquiv where

open import Data.Product using (_×_; proj₁; proj₂)

open import Equiv using (sym∼; sym≃; _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv)
open import FinEquivPlusTimes using (module Plus)
open Plus using (⊎≃+; +≃⊎)
open import FinEquivTypeEquiv
  using (module PlusE; module TimesE; module PlusTimesE)
open PlusE using (_+F_)
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

open import TypeEquivEquiv using ([id,id]≋id)

------------------------------------------------------------------------------
-- equivalences for the ⊎ structure

[id+id]≋id : ∀ {p : ℕ × ℕ} →
    let m = proj₁ p in let n = proj₂ p in
    id≃ {A = Fin m} +F id≃ {A = Fin n} ≋ id≃
[id+id]≋id {(m , n)} =
  let em = id≃ {A = Fin m} in 
  let en = id≃ {A = Fin n} in 
  let em⊎en = id≃ {A = Fin m ⊎ Fin n} in 
  let em+n = id≃ {A = Fin (m + n)} in
  let f≋ = id≋ {x = ⊎≃+ {m} {n}} in
  let g≋ = id≋ {x = +≃⊎ {m} {n}} in
  begin (
  em +F en
    ≋⟨ id≋ ⟩
  ⊎≃+ ● (em ⊎≃ en) ● +≃⊎
    ≋⟨ ●-resp-≋ f≋ (●-resp-≋ [id,id]≋id g≋) ⟩
  ⊎≃+ ● id≃ {A = Fin m ⊎ Fin n} ● +≃⊎
    ≋⟨ ●-resp-≋ f≋ (lid≋ {f = +≃⊎}) ⟩
  ⊎≃+ {m} ● +≃⊎ 
    ≋⟨ rinv≋ (⊎≃+ {m}) ⟩
  em+n ∎)
  where open ≋-Reasoning

------------------------------------------------------------------------------


