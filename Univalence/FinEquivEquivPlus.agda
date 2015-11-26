{-# OPTIONS --without-K #-}

module FinEquivEquivPlus where

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
-- equivalences for the ⊎ structure

id0≃ : Fin 0 ≃ Fin 0
id0≃ = id≃ {A = Fin 0}

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
    ≋⟨ f≋ ◎ (T.[id,id]≋id ◎ g≋) ⟩
  ⊎≃+ ● id≃ {A = Fin m ⊎ Fin n} ● +≃⊎
    ≋⟨ f≋ ◎ lid≋ {f = +≃⊎} ⟩
  ⊎≃+ {m} ● +≃⊎ 
    ≋⟨ rinv≋ (⊎≃+ {m}) ⟩
  em+n ∎)
  where open ≋-Reasoning

intro-inv-r+ : {m n : ℕ} {B : Set} (f : (Fin m ⊎ Fin n) ≃ B) → f ≋ (f ● +≃⊎) ● ⊎≃+
intro-inv-r+ f = 
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
      ≋⟨ f≋ ◎ (T.⊎●≋●⊎ ◎ g≋) ⟩ -- the real work, rest is shuffling
    ⊎≃+ ● ((h ⊎≃ i) ● (f ⊎≃ g)) ● +≃⊎
      ≋⟨ ●-assocl ⟩
    (⊎≃+ ● ((h ⊎≃ i) ● (f ⊎≃ g))) ● +≃⊎
      ≋⟨ ●-assocl ◎ g≋ ⟩
    ((⊎≃+ ● h ⊎≃ i) ● f ⊎≃ g) ● +≃⊎
      ≋⟨ ((f≋ ◎ intro-inv-r+ (h ⊎≃ i)) ◎ id≋fg) ◎ g≋ ⟩
    ((⊎≃+ ● (h ⊎≃ i ● +≃⊎) ● ⊎≃+) ● f ⊎≃ g) ● +≃⊎
      ≋⟨ (●-assocl ◎ id≋fg) ◎ g≋ ⟩
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

_+≋_ : {A B C D : ℕ} {f₁ g₁ : A fin≃ B} {f₂ g₂ : C fin≃ D} →
  (f₁ ≋ g₁) → (f₂ ≋ g₂) → (f₁ +F f₂ ≋ g₁ +F g₂)
_+≋_ {A} {B} {C} {D} {f₁} {g₁} {f₂} {g₂} f₁≋g₁ f₂≋g₂ =
  let f≋ = id≋ {x = ⊎≃+} in
  let g≋ = id≋ {x = +≃⊎} in
  begin (
    f₁ +F f₂
      ≋⟨ id≋ ⟩ 
    ⊎≃+ ● (f₁ ⊎≃ f₂) ● +≃⊎
      ≋⟨ f≋ ◎ (T._⊎≋_ f₁≋g₁ f₂≋g₂ ◎ g≋) ⟩
    ⊎≃+ ● (g₁ ⊎≃ g₂) ● +≃⊎
      ≋⟨ id≋ ⟩ 
    g₁ +F g₂ ∎)
  where open ≋-Reasoning

unite₊-nat : {m n : ℕ} {f : m fin≃ n} →
  unite+ ● (id0≃ +F f) ≋ f ● unite+
unite₊-nat {m} {n} {f} =
  begin (
    unite+ ● (id0≃ +F f) 
      ≋⟨ id≋ ⟩ 
    (unite₊equiv ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎) ● ⊎≃+ ● ((id≃ ⊎≃ f) ● +≃⊎)
      ≋⟨ ●-assocl {f = (id≃ ⊎≃ f) ● +≃⊎} {⊎≃+} {unite₊equiv ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎} ⟩
    ((unite₊equiv ● ((F0≃⊥ ⊎≃ id≃) ● +≃⊎)) ● ⊎≃+) ● ((id≃ ⊎≃ f) ● +≃⊎)
      ≋⟨ (●-assocl ◎ id≋) ◎ id≋ ⟩
    (((unite₊equiv ● (F0≃⊥ ⊎≃ id≃)) ● +≃⊎) ● ⊎≃+) ● (id≃ ⊎≃ f) ● +≃⊎ 
      ≋⟨ sym≋ (intro-inv-r+ (unite₊equiv ● (F0≃⊥ ⊎≃ id≃))) ◎ id≋ ⟩
    (unite₊equiv ● (F0≃⊥ ⊎≃ id≃)) ● (id≃ ⊎≃ f) ● +≃⊎
      ≋⟨ ●-assocl ⟩
    ((unite₊equiv ● (F0≃⊥ ⊎≃ id≃)) ● (id≃ ⊎≃ f)) ● +≃⊎
      ≋⟨ ●-assoc ◎ id≋ ⟩
    (unite₊equiv ● (F0≃⊥ ⊎≃ id≃) ● (id≃ ⊎≃ f)) ● +≃⊎
      ≋⟨ (id≋ ◎ (T.[g+1]●[1+f]≋[1+f]●[g+1] {f = f} {F0≃⊥})) ◎ id≋ ⟩
    (unite₊equiv ● ((id≃ ⊎≃ f) ● (F0≃⊥ ⊎≃ id≃))) ● +≃⊎
      ≋⟨ ●-assocl ◎ id≋ ⟩
    ((unite₊equiv ● (id≃ ⊎≃ f)) ● (F0≃⊥ ⊎≃ id≃)) ● +≃⊎
      ≋⟨ ●-assoc ⟩
    (unite₊equiv ● (id≃ ⊎≃ f)) ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎
      ≋⟨ T.unite₊-nat ◎ id≋ ⟩
    (f ● unite₊equiv) ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎
      ≋⟨ ●-assoc ⟩
    f ● unite₊equiv ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎
      ≋⟨ id≋ ⟩
    f ● unite+ ∎)
  where open ≋-Reasoning

-- sym≃ distributes over +F
sym+F : ∀ {A B C D} {f : A fin≃ B} {g : C fin≃ D} →
  sym≃ (f +F g) ≋ sym≃ f +F sym≃ g
sym+F {f = f} {g = g} = 
  begin (
    sym≃ (f +F g) 
      ≋⟨ id≋ ⟩
    sym≃ (⊎≃+ ● (f ⊎≃ g ● +≃⊎))
      ≋⟨ sym≃● ⟩
    sym≃ (f ⊎≃ g ● +≃⊎) ● sym≃ ⊎≃+
      ≋⟨ sym≃● ◎ id≋ ⟩
    (sym≃ +≃⊎ ● sym≃ (f ⊎≃ g)) ● sym≃ ⊎≃+
      ≋⟨ (id≋ ◎ T.sym≃-distrib⊎) ◎ id≋ ⟩ 
    (sym≃ +≃⊎ ● (sym≃ f ⊎≃ sym≃ g)) ● sym≃ ⊎≃+
      ≋⟨ ●-assoc ⟩
    sym≃ +≃⊎ ● ((sym≃ f ⊎≃ sym≃ g) ● sym≃ ⊎≃+)
      ≋⟨ id≋ ⟩
    sym≃ f +F sym≃ g ∎)
  where open ≋-Reasoning

uniti₊-nat : ∀ {A B} {f : A fin≃ B} →
  uniti+ ● f ≋ (id0≃ +F f) ● uniti+
uniti₊-nat {f = f} = 
  begin (
    uniti+ ● f 
      ≋⟨ id≋ ⟩ 
    sym≃ unite+ ● sym≃ (sym≃ f)
      ≋⟨ sym≋ sym≃● ⟩ 
    sym≃ (sym≃ f ● unite+)
      ≋⟨ flip-sym≋ unite₊-nat ⟩ 
    sym≃ (unite+ ● (id0≃ +F sym≃ f))
      ≋⟨ sym≃● ⟩ 
    sym≃ (id0≃ +F sym≃ f) ● uniti+
      ≋⟨  sym+F ◎ id≋ {x = uniti+} ⟩ 
    (id0≃ +F sym≃ (sym≃ f)) ● uniti+
      ≋⟨ id≋ ⟩ 
    (id0≃ +F f) ● uniti+ ∎)
  where open ≋-Reasoning

unite₊r-nat : {m n : ℕ} {f : m fin≃ n} →
  unite+r ● (f +F id0≃) ≋ f ● unite+r
unite₊r-nat {m} {n} {f} =
  let 1+⊥ = id≃ ⊎≃ F0≃⊥ in
  let f+1 = f ⊎≃ id≃ in
  let g≋ = id≋ {x = +≃⊎} in
  let rhs≋ = id≋ {x = f+1 ● +≃⊎} in
  begin (
    unite+r ● (f +F id0≃) 
      ≋⟨ id≋ ⟩ 
    (unite₊′equiv ● 1+⊥ ● +≃⊎) ● ⊎≃+ ● (f+1 ● +≃⊎)
      ≋⟨ ●-assocl ⟩
    ((unite₊′equiv ● 1+⊥ ● +≃⊎) ● ⊎≃+) ● (f+1 ● +≃⊎)
      ≋⟨ (●-assocl ◎ id≋) ◎ id≋ ⟩
    (((unite₊′equiv ● 1+⊥) ● +≃⊎) ● ⊎≃+) ● (f+1 ● +≃⊎)
      ≋⟨ sym≋ (intro-inv-r+ (unite₊′equiv ● 1+⊥)) ◎ rhs≋ ⟩
    (unite₊′equiv ● 1+⊥) ● (f+1 ● +≃⊎)
      ≋⟨ trans≋ ●-assocl (●-assoc ◎ id≋) ⟩
    (unite₊′equiv ● (1+⊥ ● f+1)) ● +≃⊎
      ≋⟨ (id≋ {x = unite₊′equiv} ◎ sym≋ (T.[g+1]●[1+f]≋[1+f]●[g+1] {f = F0≃⊥} {f})) ◎ g≋ ⟩
    (unite₊′equiv ● (f ⊎≃ id≃) ● (id≃ ⊎≃ F0≃⊥)) ● +≃⊎ -- the id≃ are at different types!
      ≋⟨ ●-assocl ◎ id≋ ⟩
    ((unite₊′equiv ● (f ⊎≃ id≃)) ● (id≃ ⊎≃ F0≃⊥)) ● +≃⊎
      ≋⟨ ●-assoc ⟩
    (unite₊′equiv ● (f ⊎≃ id≃)) ● (id≃ ⊎≃ F0≃⊥) ● +≃⊎
      ≋⟨ T.unite₊′-nat ◎ id≋ {x = (id≃ ⊎≃ F0≃⊥) ● +≃⊎} ⟩
    (f ● unite₊′equiv) ● (id≃ ⊎≃ F0≃⊥) ● +≃⊎
      ≋⟨ ●-assoc ⟩ -- assoc + defn
    f ● unite+r ∎)
  where open ≋-Reasoning

uniti₊r-nat : {m n : ℕ} {f : m fin≃ n} →
    uniti+r ● f ≋ (f +F id0≃) ● uniti+r
uniti₊r-nat {f = f} =
  begin (
    uniti+r ● f 
      ≋⟨ id≋ ⟩
     sym≃ unite+r ● sym≃ (sym≃ f)
      ≋⟨ sym≋ sym≃● ⟩
     sym≃ (sym≃ f ● unite+r)
      ≋⟨ flip-sym≋ unite₊r-nat ⟩
     sym≃ (unite+r ● (sym≃ f +F id0≃))
      ≋⟨ sym≃● ⟩
     sym≃ (sym≃ f +F id0≃) ● uniti+r
      ≋⟨ sym+F ◎ id≋ {x = uniti+r} ⟩
     (sym≃ (sym≃ f) +F id0≃) ● uniti+r
      ≋⟨ id≋ ⟩
    (f +F id0≃) ● uniti+r ∎)
  where open ≋-Reasoning

-- assocl+ is the one which is defined directly (?)
assocl₊-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocl+ {m'} {n'} {o'} ● (f +F (g +F h)) ≋
    ((f +F g) +F h) ● assocl+ {m} {n} {o}
-- expand the definitions right away, the pattern is clear
assocl₊-nat {m} {n} {o} {m'} {n'} {o'} {f} {g} {h} =
  let αmno' = assocl₊equiv {Fin m'} {Fin n'} {Fin o'} in
  let αmno = assocl₊equiv {Fin m} {Fin n} {Fin o} in
  begin ( 
  (⊎≃+ ● ⊎≃+ ⊎≃ id≃ ● αmno' ● id≃ ⊎≃ +≃⊎ ● +≃⊎) ● 
            ⊎≃+ ● ((f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎)) ● +≃⊎)
    ≋⟨ ●-assocl ⟩
  ((⊎≃+ ● ⊎≃+ ⊎≃ id≃ ● assocl₊equiv ● id≃ ⊎≃ +≃⊎ ● +≃⊎) ● ⊎≃+) ● 
            (f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎) ● +≃⊎)
    ≋⟨ ((id≋ ◎ (id≋ ◎ ●-assocl)) ◎ id≋) ◎ id≋ ⟩
  ((⊎≃+ ● ⊎≃+ ⊎≃ id≃ ● (assocl₊equiv ● id≃ ⊎≃ +≃⊎) ● +≃⊎) ● ⊎≃+) ● 
            (f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎) ● +≃⊎)
    ≋⟨ ((id≋ ◎ ●-assocl) ◎ id≋) ◎ id≋ ⟩
  ((⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● (assocl₊equiv ● id≃ ⊎≃ +≃⊎)) ● +≃⊎) ● ⊎≃+) ● 
            (f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎) ● +≃⊎)
    ≋⟨ (●-assocl ◎ id≋) ◎ id≋ ⟩
  (((⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● (assocl₊equiv ● id≃ ⊎≃ +≃⊎))) ● +≃⊎) ● ⊎≃+) ● 
            (f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎) ● +≃⊎)
    ≋⟨ sym≋ (intro-inv-r+ (⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● (assocl₊equiv ● id≃ ⊎≃ +≃⊎)))) ◎ id≋ ⟩
   (⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● (assocl₊equiv ● id≃ ⊎≃ +≃⊎))) ●
          (f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎) ● +≃⊎)
    ≋⟨ ●-assoc ⟩
  ⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● (assocl₊equiv ● id≃ ⊎≃ +≃⊎)) ●  
          (f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎) ● +≃⊎)
    ≋⟨ id≋ ◎ (●-assocl ◎ id≋) ⟩
  ⊎≃+ ● ((⊎≃+ ⊎≃ id≃ ● assocl₊equiv) ● id≃ ⊎≃ +≃⊎) ●  
          (f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎) ● +≃⊎)
    ≋⟨ id≋ ◎ ●-assoc ⟩
  ⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● assocl₊equiv) ● (id≃ ⊎≃ +≃⊎ ●  
          (f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎) ● +≃⊎))
    ≋⟨ id≋ ◎ (id≋ ◎ ●-assocl) ⟩
  ⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● assocl₊equiv) ● ((id≃ ⊎≃ +≃⊎ ●  
          f ⊎≃ (⊎≃+ ● g ⊎≃ h ● +≃⊎)) ● +≃⊎)
    ≋⟨ id≋ ◎ (id≋ ◎ (sym≋ T.⊎●≋●⊎ ◎ id≋)) ⟩
  ⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● assocl₊equiv) ● ((id≃ ● f) ⊎≃ (+≃⊎ ● (⊎≃+ ● g ⊎≃ h ● +≃⊎))) ● +≃⊎
    ≋⟨ id≋ ◎ (id≋ ◎ (T._⊎≋_ (trans≋ lid≋ (sym≋ rid≋)) (trans≋ ●-assocl  (trans≋ (linv≋ ⊎≃+ ◎ id≋) lid≋)) ◎ id≋)) ⟩
  ⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● assocl₊equiv) ● ((f ● id≃) ⊎≃ (g ⊎≃ h ● +≃⊎)) ● +≃⊎
    ≋⟨ id≋ ◎ (id≋ ◎ (T.⊎●≋●⊎ ◎ id≋)) ⟩
  ⊎≃+ ● (⊎≃+ ⊎≃ id≃ ● assocl₊equiv) ● (f ⊎≃ (g ⊎≃ h) ● id≃ ⊎≃ +≃⊎) ● +≃⊎
    ≋⟨ id≋ ◎ ●-assocl ⟩
  ⊎≃+ ● ((⊎≃+ ⊎≃ id≃ ● assocl₊equiv) ● (f ⊎≃ (g ⊎≃ h) ● id≃ ⊎≃ +≃⊎)) ● +≃⊎
    ≋⟨ id≋ ◎ (●-assocl ◎ id≋) ⟩
  ⊎≃+ ● (((⊎≃+ ⊎≃ id≃ ● assocl₊equiv) ● f ⊎≃ (g ⊎≃ h)) ● id≃ ⊎≃ +≃⊎) ● +≃⊎
    ≋⟨ id≋ ◎ ((●-assoc ◎ id≋) ◎ id≋) ⟩
  ⊎≃+ ● ((⊎≃+ ⊎≃ id≃ ● (assocl₊equiv ● f ⊎≃ (g ⊎≃ h))) ● id≃ ⊎≃ +≃⊎) ● +≃⊎
    ≋⟨ id≋ ◎ ( ((id≋ ◎ T.assocl₊-nat) ◎ id≋) ◎ id≋) ⟩
  ⊎≃+ ● ((⊎≃+ ⊎≃ id≃ ● ((f ⊎≃ g) ⊎≃ h) ● assocl₊equiv) ● id≃ ⊎≃ +≃⊎) ● +≃⊎
    ≋⟨ id≋ ◎ ((●-assocl ◎ id≋)  ◎ id≋) ⟩
  ⊎≃+ ● (((⊎≃+ ⊎≃ id≃ ● (f ⊎≃ g) ⊎≃ h) ● assocl₊equiv) ● id≃ ⊎≃ +≃⊎) ● +≃⊎
    ≋⟨ id≋ ◎ (((T+1-nat ◎ id≋) ◎ id≋) ◎ id≋) ⟩
  ⊎≃+ ● ((((⊎≃+ ● f ⊎≃ g ● +≃⊎) ● ⊎≃+) ⊎≃ (h ● id≃) ● assocl₊equiv) ● id≃ ⊎≃ +≃⊎) ● +≃⊎
    ≋⟨ id≋ ◎ ●-assoc ⟩
  ⊎≃+ ● (((⊎≃+ ● f ⊎≃ g ● +≃⊎) ● ⊎≃+) ⊎≃ (h ● id≃) ● assocl₊equiv) ● (id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ id≋ ◎ ●-assoc ⟩
  ⊎≃+ ● ((⊎≃+ ● f ⊎≃ g ● +≃⊎) ● ⊎≃+) ⊎≃ (h ● id≃) ● (assocl₊equiv ● id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ ●-assocl ⟩
  (⊎≃+ ● ((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ● ⊎≃+) ⊎≃ (h ● id≃)) ● (αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ (id≋ ◎ T.⊎●≋●⊎ ) ◎ id≋ ⟩
  (⊎≃+ ●  (((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ⊎≃ h) ● (⊎≃+ ⊎≃ id≃))) ●
           (αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ ●-assocl ◎ id≋ ⟩
  ((⊎≃+ ●  ((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ⊎≃ h)) ● (⊎≃+ ⊎≃ id≃)) ●
           (αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ ●-assoc ⟩
  (⊎≃+ ●  ((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ⊎≃ h)) ● 
            (⊎≃+ ⊎≃ id≃ ● αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ id≋ ◎ sym≋ lid≋ ⟩
  (⊎≃+ ●  ((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ⊎≃ h)) ● 
            id≃ ● (⊎≃+ ⊎≃ id≃ ● αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ id≋ ◎ (sym≋ (rinv≋ +≃⊎) ◎ id≋) ⟩
  (⊎≃+ ●  ((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ⊎≃ h)) ● 
            (+≃⊎ ● ⊎≃+) ● (⊎≃+ ⊎≃ id≃ ● αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ id≋ ◎ ●-assoc ⟩
  ((⊎≃+ ●  ((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ⊎≃ h))) ● 
            (+≃⊎ ● ⊎≃+ ● ⊎≃+ ⊎≃ id≃ ● αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎)
    ≋⟨ ●-assocl ⟩
  ((⊎≃+ ●  ((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ⊎≃ h)) ● +≃⊎) ● 
            (⊎≃+ ● ⊎≃+ ⊎≃ id≃ ● αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎) 
    ≋⟨ ●-assoc ◎ id≋ ⟩
  (⊎≃+ ● ((⊎≃+ ● (f ⊎≃ g) ● +≃⊎) ⊎≃ h) ● +≃⊎) ● 
            (⊎≃+ ● ⊎≃+ ⊎≃ id≃ ● αmno ● id≃ ⊎≃ +≃⊎ ● +≃⊎) ∎) 
  where 
    open ≋-Reasoning
    T+1-nat : ⊎≃+ ⊎≃ id≃ ● (f ⊎≃ g) ⊎≃ h ≋  ((⊎≃+ ● f ⊎≃ g ● +≃⊎) ● ⊎≃+) ⊎≃ (h ● id≃)
    T+1-nat = begin (
      ⊎≃+ ⊎≃ id≃ ● (f ⊎≃ g) ⊎≃ h
        ≋⟨ sym≋ (T.⊎●≋●⊎) ⟩
      (⊎≃+ ● f ⊎≃ g) ⊎≃ (id≃ ● h)
        ≋⟨ id≋ T.⊎≋ (trans≋ lid≋ (sym≋ rid≋))⟩
      (⊎≃+ ● f ⊎≃ g) ⊎≃ (h ● id≃)
        ≋⟨ trans≋ (intro-inv-r+ ((⊎≃+ ● f ⊎≃ g))) ●-assoc T.⊎≋ id≋ ⟩
        ((⊎≃+ ● f ⊎≃ g) ● +≃⊎ ● ⊎≃+) ⊎≃ (h ● id≃)
         ≋⟨ trans≋ ●-assocl (●-assoc ◎ id≋) T.⊎≋ id≋ ⟩
       ((⊎≃+ ● f ⊎≃ g ● +≃⊎) ● ⊎≃+) ⊎≃ (h ● id≃) ∎)

assocr₊-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocr+ {m'} {n'} {o'} ● ((f +F g) +F h) ≋
    (f +F (g +F h)) ● assocr+ {m} {n} {o}
assocr₊-nat {m} {n} {o} {m'} {n'} {o'} {f} {g} {h} = begin (
  assocr+ {m'} {n'} {o'} ● ((f +F g) +F h)
    ≋⟨ id≋ ⟩
  sym≃ assocl+ ● sym≃ (sym≃ ((f +F g) +F h))
    ≋⟨ sym≋ (sym≃● {f = assocl+}) ⟩
  sym≃ (sym≃ ((f +F g) +F h) ● assocl+ {m'} {n'} {o'})
    ≋⟨ flip≋ ((trans≋ sym+F (sym+F +≋ id≋ )) ◎ id≋) ⟩
  sym≃ (((sym≃ f +F sym≃ g) +F sym≃ h) ● assocl+ {m'})
    ≋⟨ flip-sym≋ assocl₊-nat ⟩
  sym≃ (assocl+ {m} {n} {o} ● (sym≃ f +F (sym≃ g +F sym≃ h)))
    ≋⟨ flip≋ (id≋ ◎ (trans≋ (id≋ +≋ (sym≋ sym+F)) (sym≋ sym+F))) ⟩
  sym≃ ( assocl+ ● sym≃ (f +F (g +F h)))
    ≋⟨ sym≃● ⟩
  sym≃ (sym≃ (f +F (g +F h))) ● sym≃ (assocl+ {m} {n} {o})
    ≋⟨ id≋ ⟩
  (f +F (g +F h)) ● (assocr+ {m} {n} {o}) ∎)
  where open ≋-Reasoning


unite-assocr₊-coh : {m n : ℕ} → 
    unite+r {m = m} +F id≃ {A = Fin n} ≋
    (id≃ {A = Fin m} +F unite+ {m = n}) ● assocr+ {m} {0} {n}
unite-assocr₊-coh {m} {n} =  begin (
  ⊎≃+ ● (unite₊′equiv {Fin m} ● id≃ ⊎≃ F0≃⊥ ● +≃⊎) ⊎≃ id≃ {A = Fin n} ● +≃⊎
    ≋⟨ {!!} ⟩
  (⊎≃+ ● (id≃ ⊎≃ (unite₊equiv ● F0≃⊥ ⊎≃ id≃ ● +≃⊎)) ● +≃⊎) ● sym≃ (assocl+ {m} {0} {n}) ∎) 
  where open ≋-Reasoning

assocr₊-coh : {m n o p : ℕ} → 
    assocr+ {m} {n} {o + p} ● assocr+ {m + n} {o} {p} ≋
    (id≃ {A = Fin m} +F assocr+ {n} {o} {p}) ●
      assocr+ {m} {n + o} {p} ● (assocr+ {m} {n} {o} +F id≃ {A = Fin p})
assocr₊-coh = {!!} 
  where open ≋-Reasoning

swap₊-nat : {m n o p : ℕ} {f : m fin≃ o} {g : n fin≃ p} →
    swap+ {o} {p} ● (f +F g) ≋ (g +F f) ● swap+ {m} {n}
swap₊-nat = {!!} 

sswap₊-nat : {m n o p : ℕ} {f : m fin≃ o} {g : n fin≃ p} →
    sswap+ {o} {p} ● (g +F f) ≋ (f +F g) ● sswap+ {m} {n}
sswap₊-nat = {!!} 

assocr₊-swap₊-coh : {m n o : ℕ} →
    assocr+ {n} {o} {m} ● swap+ {m} {n + o} ● assocr+ {m} {n} {o} ≋
    (id≃ {A = Fin n} +F swap+ {m} {o}) ●
      assocr+ {n} {m} {o} ● (swap+ {m} {n} +F id≃ {A = Fin o})
assocr₊-swap₊-coh = {!!} 
  where open ≋-Reasoning

assocl₊-swap₊-coh : {m n o : ℕ} →
    assocl+ {o} {m} {n} ● swap+ {m + n} {o} ● assocl+ {m} {n} {o} ≋
    (swap+ {m} {o} +F id≃ {A = Fin n}) ● 
      assocl+ {m} {o} {n} ● (id≃ {A = Fin m} +F swap+ {n} {o})
assocl₊-swap₊-coh = {!!}
  where open ≋-Reasoning

------------------------------------------------------------------------------
