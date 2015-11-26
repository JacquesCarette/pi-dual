{-# OPTIONS --without-K #-}

module FinEquivEquivTimes where

open import Data.Product using (_×_; proj₁; proj₂)

open import Equiv using (refl∼; sym∼; sym≃; _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv)

open import FinEquivPlusTimes using (F0≃⊥; module Plus; module Times)
open Plus using (⊎≃+; +≃⊎)
open Times using (×≃*; *≃×)

open import FinEquivTypeEquiv
  using (_fin≃_; module PlusE; module TimesE; module PlusTimesE)
open PlusE using (_+F_; unite+; uniti+; unite+r; uniti+r; assocr+; assocl+;
                 swap+; sswap+)
open TimesE using (_*F_; unite*; uniti*; unite*r; uniti*r; assocr*; assocl*;
                  swap*; sswap*)
open PlusTimesE using (distz; factorz; distzr; factorzr;
                       dist; factor; distl; factorl)
open import EquivEquiv
open import TypeEquiv
  using (unite₊equiv; unite₊′equiv; assocl₊equiv)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as P using (refl)

import TypeEquivEquiv as T
  using ([id,id]≋id; ⊎●≋●⊎; _⊎≋_; sym≃-distrib⊎;
    unite₊-nat; assocl₊-nat;
    [g+1]●[1+f]≋[1+f]●[g+1]; unite₊′-nat;
    id×id≋id; ×●≋●×;
    -- much lower down
    0×0≃0)

------------------------------------------------------------------------------
-- Equivalences for the multiplicative structure

id1≃ : Fin 1 ≃ Fin 1
id1≃ = id≃ {A = Fin 1}

id*id≋id : ∀ {m n : ℕ} →
    id≃ {A = Fin m} *F id≃ {A = Fin n} ≋ id≃
id*id≋id {m} {n} =
  let em = id≃ {A = Fin m} in 
  let en = id≃ {A = Fin n} in 
  let em×en = id≃ {A = Fin m × Fin n} in 
  let em*n = id≃ {A = Fin (m * n)} in
  let f≋ = id≋ {x = ×≃* {m} {n}} in
  let g≋ = id≋ {x = *≃× {m} {n}} in
  begin (
  em *F en
    ≋⟨ id≋ ⟩
  ×≃* ● (em ×≃ en) ● *≃×
    ≋⟨ f≋ ◎ (T.id×id≋id ◎ g≋) ⟩
  ×≃* ● id≃ {A = Fin m × Fin n} ● *≃×
    ≋⟨ f≋ ◎ lid≋ {f = *≃×} ⟩
  ×≃* {m} ● *≃× 
    ≋⟨ rinv≋ (×≃* {m}) ⟩
  em*n ∎)
  where open ≋-Reasoning

intro-inv-r* : {m n : ℕ} {B : Set} (f : (Fin m × Fin n) ≃ B) → f ≋ (f ● *≃×) ● ×≃*
intro-inv-r* f = 
  begin (
    f
      ≋⟨ sym≋ rid≋ ⟩
    f ● id≃
      ≋⟨ id≋ {x = f} ◎ sym≋ (linv≋ ×≃*) ⟩
    f ● (*≃× ● ×≃*)
      ≋⟨ ●-assocl  ⟩
    (f ● *≃×) ● ×≃* ∎)
  where open ≋-Reasoning

*●≋●* : {A B C D E F : ℕ} →
  {f : A fin≃ C} {g : B fin≃ D} {h : C fin≃ E} {i : D fin≃ F} →
  (h ● f) *F (i ● g) ≋ (h *F i) ● (f *F g)
*●≋●* {f = f} {g} {h} {i} =
  begin (
    (h ● f) *F (i ● g)
      ≋⟨ id≋ ⟩
    ×≃* ● ((h ● f) ×≃ (i ● g)) ● *≃×
      ≋⟨ id≋ ◎ (T.×●≋●× {f = f} {g} {h} {i} ◎ id≋) ⟩
    ×≃* ● ((h ×≃ i) ● (f ×≃ g)) ● *≃×
      ≋⟨ ●-assocl ⟩
    (×≃* ● (h ×≃ i) ● (f ×≃ g)) ● *≃×
      ≋⟨ (id≋ ◎ (intro-inv-r* (h ×≃ i) ◎ id≋)) ◎ id≋ ⟩
    {!!}
      ≋⟨ {!!} ⟩
    (h *F i) ● (f *F g) ∎)
  where open ≋-Reasoning

_*≋_ : {A B C D : ℕ} {f₁ g₁ : A fin≃ B} {f₂ g₂ : C fin≃ D} →
    (f₁ ≋ g₁) → (f₂ ≋ g₂) → (f₁ *F f₂ ≋ g₁ *F g₂)
_*≋_ = {!!} 

unite*-nat : {m n : ℕ} {f : m fin≃ n} →
    unite* ● (id1≃ *F f) ≋ f ● unite*
unite*-nat = {!!} 

uniti*-nat : ∀ {A B} {f : A fin≃ B} →
    uniti* ● f ≋ (id1≃ *F f) ● uniti*
uniti*-nat = {!!} 

unite*r-nat : {m n : ℕ} {f : m fin≃ n} →
   unite*r ● (f *F id1≃) ≋ f ● unite*r
unite*r-nat = {!!} 

uniti*r-nat : {m n : ℕ} {f : m fin≃ n} →
      uniti*r ● f ≋ (f *F id1≃) ● uniti*r
uniti*r-nat = {!!} 

assocr*-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocr* {m'} {n'} {o'} ● ((f *F g) *F h) ≋
    (f *F (g *F h)) ● assocr* {m} {n} {o}
assocr*-nat = {!!} 

assocl*-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocl* {m'} {n'} {o'} ● (f *F (g *F h)) ≋
    ((f *F g) *F h) ● assocl* {m} {n} {o}
assocl*-nat = {!!} 

unite-assocr*-coh : {m n : ℕ} → 
    unite*r {m = m} *F id≃ {A = Fin n} ≋
    (id≃ {A = Fin m} *F unite* {m = n}) ● assocr* {m} {1} {n}
unite-assocr*-coh = {!!} 

assocr*-coh : {m n o p : ℕ} → 
    assocr* {m} {n} {o * p} ● assocr* {m * n} {o} {p} ≋
    (id≃ {A = Fin m} *F assocr* {n} {o} {p}) ●
      assocr* {m} {n * o} {p} ● (assocr* {m} {n} {o} *F id≃ {A = Fin p})
assocr*-coh = {!!} 

swap*-nat : {m n o p : ℕ} {f : m fin≃ o} {g : n fin≃ p} →
    swap* {o} {p} ● (f *F g) ≋ (g *F f) ● swap* {m} {n}
swap*-nat = {!!} 

sswap*-nat : {m n o p : ℕ} {f : m fin≃ o} {g : n fin≃ p} →
    sswap* {o} {p} ● (g *F f) ≋ (f *F g) ● sswap* {m} {n}
sswap*-nat = {!!} 

assocr*-swap*-coh : {m n o : ℕ} →
    assocr* {n} {o} {m} ● swap* {m} {n * o} ● assocr* {m} {n} {o} ≋
    (id≃ {A = Fin n} *F swap* {m} {o}) ●
      assocr* {n} {m} {o} ● (swap* {m} {n} *F id≃ {A = Fin o})
assocr*-swap*-coh = {!!} 

assocl*-swap*-coh : {m n o : ℕ} →
    assocl* {o} {m} {n} ● swap* {m * n} {o} ● assocl* {m} {n} {o} ≋
    (swap* {m} {o} *F id≃ {A = Fin n}) ● 
      assocl* {m} {o} {n} ● (id≃ {A = Fin m} *F swap* {n} {o})
assocl*-swap*-coh = {!!} 

------------------------------------------------------------------------------
