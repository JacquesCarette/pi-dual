{-# OPTIONS --without-K #-}

module FinEquivEquiv where

open import Data.Product using (_×_; proj₁; proj₂)

open import Equiv using (sym∼; sym≃; _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv)

open import FinEquivPlusTimes using (module Plus)
open Plus using (⊎≃+; +≃⊎)

open import FinEquivTypeEquiv
  using (_fin≃_; module PlusE; module TimesE; module PlusTimesE)
open PlusE using (_+F_)
open import EquivEquiv

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_)

open import TypeEquivEquiv 
  using ([id,id]≋id; ⊎●≋●⊎)

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
    ≋⟨ f≋ ◎ ([id,id]≋id ◎ g≋) ⟩
  ⊎≃+ ● id≃ {A = Fin m ⊎ Fin n} ● +≃⊎
    ≋⟨ f≋ ◎ lid≋ {f = +≃⊎} ⟩
  ⊎≃+ {m} ● +≃⊎ 
    ≋⟨ rinv≋ (⊎≃+ {m}) ⟩
  em+n ∎)
  where open ≋-Reasoning

intro-inv-r : {m n o p : ℕ} (f : (Fin m ⊎ Fin n) ≃ (Fin o ⊎ Fin p)) → f ≋ (f ● +≃⊎) ● ⊎≃+
intro-inv-r f = 
  begin (
    f
      ≋⟨ sym≋ rid≋ ⟩
    f ● id≃
      ≋⟨ id≋ {x = f} ◎ sym≋ (linv≋ ⊎≃+) ⟩
    f ● (+≃⊎ ● ⊎≃+)
      ≋⟨ ●-assocl {f = ⊎≃+} {+≃⊎} {f} ⟩
    (f ● +≃⊎) ● ⊎≃+ ∎)
  where open ≋-Reasoning

+●≋●+ : {A B C D E F : ℕ} →
  {f : A fin≃ C} {g : B fin≃ D} {h : C fin≃ E} {i : D fin≃ F} →
  (h ● f) +F (i ● g) ≋ (h +F i) ● (f +F g)
+●≋●+ {f = f} {g} {h} {i} =
  let f≋ = id≋ {x = ⊎≃+} in
  let g≋ = id≋ {x = +≃⊎} in
  let id≋fg = id≋ {x = f ⊎≃ g} in
  begin (
    (h ● f) +F (i ● g)
      ≋⟨ id≋ ⟩
    ⊎≃+ ● ((h ● f) ⊎≃ (i ● g)) ● +≃⊎
      ≋⟨ f≋ ◎ (⊎●≋●⊎ ◎ g≋) ⟩ -- the real work, rest is shuffling
    ⊎≃+ ● ((h ⊎≃ i) ● (f ⊎≃ g)) ● +≃⊎
      ≋⟨ ●-assocl {f = +≃⊎} { (h ⊎≃ i) ● (f ⊎≃ g) } {⊎≃+} ⟩
    (⊎≃+ ● ((h ⊎≃ i) ● (f ⊎≃ g))) ● +≃⊎
      ≋⟨ ●-assocl {f = f ⊎≃ g} {h ⊎≃ i} {⊎≃+} ◎ g≋ ⟩
    ((⊎≃+ ● h ⊎≃ i) ● f ⊎≃ g) ● +≃⊎
      ≋⟨ ((f≋ ◎ intro-inv-r (h ⊎≃ i)) ◎ id≋fg) ◎ g≋ ⟩
    ((⊎≃+ ● (h ⊎≃ i ● +≃⊎) ● ⊎≃+) ● f ⊎≃ g) ● +≃⊎
      ≋⟨ (●-assocl {f = ⊎≃+} {h ⊎≃ i ● +≃⊎} {⊎≃+} ◎ id≋fg) ◎ g≋ ⟩
    (((⊎≃+ ● (h ⊎≃ i ● +≃⊎)) ● ⊎≃+) ● f ⊎≃ g) ● +≃⊎
      ≋⟨ id≋ ⟩ -- the left part is done, show it
    ((h +F i ● ⊎≃+) ● f ⊎≃ g) ● +≃⊎
      ≋⟨ ●-assoc {f = f ⊎≃ g} {⊎≃+} {h +F i} ◎ g≋ ⟩
    (h +F i ● (⊎≃+ ● f ⊎≃ g)) ● +≃⊎
      ≋⟨ ●-assoc {f = +≃⊎} {⊎≃+ ● f ⊎≃ g} {h +F i}⟩
    (h +F i) ● ((⊎≃+ ● f ⊎≃ g) ● +≃⊎)
      ≋⟨ id≋ {x = h +F i} ◎ ●-assoc {f = +≃⊎} {f ⊎≃ g} {⊎≃+}⟩
    (h +F i) ● (f +F g) ∎)
  where open ≋-Reasoning
------------------------------------------------------------------------------


