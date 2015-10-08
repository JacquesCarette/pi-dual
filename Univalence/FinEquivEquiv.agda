{-# OPTIONS --without-K #-}

module FinEquivEquiv where

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
  using (unite₊equiv; unite₊′equiv)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as P using (refl)

import TypeEquivEquiv as T
  using ([id,id]≋id; ⊎●≋●⊎; _⊎≋_; sym≃-distrib;
    unite₊-nat;
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
      ≋⟨ (id≋ ◎ T.sym≃-distrib) ◎ id≋ ⟩ 
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

assocr₊-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocr+ {m'} {n'} {o'} ● ((f +F g) +F h) ≋
    (f +F (g +F h)) ● assocr+ {m} {n} {o}
assocr₊-nat = {!!} 

assocl₊-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocl+ {m'} {n'} {o'} ● (f +F (g +F h)) ≋
    ((f +F g) +F h) ● assocl+ {m} {n} {o}
assocl₊-nat = {!!} 

unite-assocr₊-coh : {m n : ℕ} → 
    unite+r {m = m} +F id≃ {A = Fin n} ≋
    (id≃ {A = Fin m} +F unite+ {m = n}) ● assocr+ {m} {0} {n}
unite-assocr₊-coh = {!!} 

assocr₊-coh : {m n o p : ℕ} → 
    assocr+ {m} {n} {o + p} ● assocr+ {m + n} {o} {p} ≋
    (id≃ {A = Fin m} +F assocr+ {n} {o} {p}) ●
      assocr+ {m} {n + o} {p} ● (assocr+ {m} {n} {o} +F id≃ {A = Fin p})
assocr₊-coh = {!!} 

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

assocl₊-swap₊-coh : {m n o : ℕ} →
    assocl+ {o} {m} {n} ● swap+ {m + n} {o} ● assocl+ {m} {n} {o} ≋
    (swap+ {m} {o} +F id≃ {A = Fin n}) ● 
      assocl+ {m} {o} {n} ● (id≃ {A = Fin m} +F swap+ {n} {o})

------------------------------------------------------------------------------
-- and the multiplicative structure

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
assocl₊-swap₊-coh = {!!} 

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

------------------------------------------------------------------------------
-- equivalences for the distributivity
assocl*-swap*-coh = {!!} 

distl-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} →
    distl {m'} {n'} {o'} ● (f *F (g +F h)) ≋
      ((f *F g) +F (f *F h)) ● distl {m} {n} {o}
distl-nat = {!!} 

factorl-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} →
    factorl {m'} {n'} {o'} ● ((f *F g) +F (f *F h)) ≋
      (f *F (g +F h)) ● factorl {m} {n} {o}
factorl-nat = {!!} 

dist-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} →
    dist {m'} {n'} {o'} ● ((f +F g) *F h) ≋
      ((f *F h) +F (g *F h)) ● dist {m} {n} {o}
dist-nat = {!!} 

factor-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} →
    factor {m'} {n'} {o'} ● ((f *F h) +F (g *F h)) ≋
      ((f +F g) *F h) ● factor {m} {n} {o}
factor-nat = {!!} 

distzr-nat : {m n : ℕ} {f : m fin≃ n} {g : 0 fin≃ 0} →
    distzr {n} ● (f *F g) ≋ g ● distzr {m}
distzr-nat = {!!} 

factorzr-nat : {m n : ℕ} {f : m fin≃ n} {g : 0 fin≃ 0} →
    factorzr {n} ● g ≋ (f *F g) ● factorzr {m}
factorzr-nat = {!!} 

distz-nat : {m n : ℕ} → {f : m fin≃ n} → {g : 0 fin≃ 0} →
    distz {n} ● (g *F f) ≋ g ● distz {m}
distz-nat = {!!} 

factorz-nat : {m n : ℕ} → {f : m fin≃ n} → {g : 0 fin≃ 0} →
    factorz {n} ● g ≋ (g *F f) ● factorz {m}
factorz-nat = {!!} 

A×[B⊎C]≃[A×C]⊎[A×B] : {m n o : ℕ} → 
    distl {m} {o} {n} ● (id≃ {A = Fin m} *F swap+ {n} {o}) ≋
    swap+ {m * n} {m * o} ● distl {m} {n} {o}
A×[B⊎C]≃[A×C]⊎[A×B] = {!!} 

[A⊎B]×C≃[C×A]⊎[C×B] : {m n o : ℕ} → 
    (swap* {m} {o} +F swap* {n} {o}) ● dist {m} {n} {o} ≋
    distl {o} {m} {n} ● swap* {m + n} {o}
[A⊎B]×C≃[C×A]⊎[C×B] = {!!} 

[A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D : {m n o p : ℕ} →
    (dist {m} {n} {p} +F id≃ {A = Fin (o * p)}) ●
      dist {m + n} {o} {p} ● (assocl+ {m} {n} {o} *F id≃ {A = Fin p}) ≋
    assocl+ {m * p} {n * p} {o * p} ●
      (id≃ {A = Fin (m * p)} +F dist {n} {o} {p}) ● dist {m} {n + o} {p}
[A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D = {!!} 

A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D : {m n o p : ℕ} →
    distl {m * n} {o} {p} ● assocl* {m} {n} {o + p} ≋
    (assocl* {m} {n} {o} +F assocl* {m} {n} {p}) ●
      distl {m} {n * o} {n * p} ● (id≃ {A = Fin m} *F distl {n} {o} {p})
A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D = {!!} 

[A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D : {m n o p : ℕ} →
    assocl+ {(m * o) + (n * o)} {m * p} {n * p} ●
      (dist {m} {n} {o} +F dist {m} {n} {p}) ●
      distl {m + n} {o} {p} ≋
    (assocl+ {m * o} {n * o} {m * p} +F id≃ {A = Fin (n * p)}) ●
      ((id≃ {A = Fin (m * o)} +F swap+ {m * p} {n * o}) +F id≃ {A = Fin (n * p)}) ●
      (assocr+ {m * o} {m * p} {n * o} +F id≃ {A = Fin (n * p)}) ●
      assocl+ {(m * o) + (m * p)} {n * o} {n * p} ● 
      (distl {m} {o} {p} +F distl {n} {o} {p}) ● dist {m} {n} {o + p}
[A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D = {!!} 

-- can't be done via equational reasoning!?!?
-- cannot even dig into T.0×0≃0 as f≋ is abstract
0×0≃0 : distz {0} ≋ distzr {0}
0×0≃0 = eq (λ {()}) (λ {()}) -- wow, talk about low-level reasoning!
  
0×[A⊎B]≃0 : {m n : ℕ} →
    distz {m + n} ≋ unite+ ● (distz {m} +F distz {n}) ● distl {0} {m} {n}
0×[A⊎B]≃0 = {!!} 

0×1≃0 : unite*r ≋ distz {1}
0×1≃0 = {!!} 

A×0≃0 : {m : ℕ} → distzr {m} ≋ distz {m} ● swap* {m} {0}
A×0≃0 = {!!} 

0×A×B≃0 : {m n : ℕ} →
    distz {m * n} ≋
    distz {n} ● (distz {m} *F id≃ {A = Fin n}) ● assocl* {0} {m} {n}
0×A×B≃0 = {!!} 

A×0×B≃0 : {m n : ℕ} →
    distzr {m} ● (id≃ {A = Fin m} *F distz {n})  ≋ 
    distz {n} ● (distzr {m} *F id≃ {A = Fin n}) ● assocl* {m} {0} {n}
A×0×B≃0 = {!!} 

A×[0+B]≃A×B : {m n : ℕ} →
    (id≃ {A = Fin m} *F unite+ {n}) ≋
    unite+ ● (distzr {m} +F id≃) ● distl {m} {0} {n}
A×[0+B]≃A×B = {!!} 

1×[A⊎B]≃A⊎B : {m n : ℕ} →
    unite* ≋ (unite* {m} +F unite* {n}) ● distl {1} {m} {n}
1×[A⊎B]≃A⊎B = {!!} 

------------------------------------------------------------------------------
