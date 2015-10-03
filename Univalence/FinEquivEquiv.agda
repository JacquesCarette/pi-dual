{-# OPTIONS --without-K #-}

-- USING POSTULATES DURING DEVELOPMENT BECAUSE TYPE CHECKING WAS TAKING WAY TOO MUCH TIME
-- REPLACE ALL POSTULATES BY THE ACTUAL PROOFS

module FinEquivEquiv where

open import Data.Product using (_×_; proj₁; proj₂)

open import Equiv using (sym∼; sym≃; _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv)

open import FinEquivPlusTimes using (F0≃⊥; module Plus; module Times)
open Plus using (⊎≃+; +≃⊎)
open Times using (×≃*; *≃×)

open import FinEquivTypeEquiv
  using (_fin≃_; module PlusE; module TimesE; module PlusTimesE)
open PlusE using (_+F_; unite+; uniti+; unite+r; uniti+r; assocr+; assocl+)
open TimesE using (_*F_; unite*; uniti*; unite*r; uniti*r; assocr*; assocl*)
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
  using ([id,id]≋id; ⊎●≋●⊎; ⊎≃-respects-≋; unite₊-nat;
    [g+1]●[1+f]≋[1+f]●[g+1]; unite₊′-nat;
    id×id≋id)

------------------------------------------------------------------------------
-- equivalences for the ⊎ structure

id0≃ : Fin 0 ≃ Fin 0
id0≃ = id≃ {A = Fin 0}

postulate 
  [id+id]≋id : ∀ {p : ℕ × ℕ} →
      let m = proj₁ p in let n = proj₂ p in
      id≃ {A = Fin m} +F id≃ {A = Fin n} ≋ id≃

{--
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

intro-inv-r : {m n : ℕ} {B : Set} (f : (Fin m ⊎ Fin n) ≃ B) → f ≋ (f ● +≃⊎) ● ⊎≃+
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
--}

postulate
  +●≋●+ : {A B C D E F : ℕ} →
    {f : A fin≃ C} {g : B fin≃ D} {h : C fin≃ E} {i : D fin≃ F} →
    (h ● f) +F (i ● g) ≋ (h +F i) ● (f +F g)

{--
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
--}

postulate
  _+≋_ : {A B C D : ℕ} {f₁ g₁ : A fin≃ B} {f₂ g₂ : C fin≃ D} →
    (f₁ ≋ g₁) → (f₂ ≋ g₂) → (f₁ +F f₂ ≋ g₁ +F g₂)

{--
_+≋_ : {A B C D : ℕ} {f₁ g₁ : A fin≃ B} {f₂ g₂ : C fin≃ D} →
  (f₁ ≋ g₁) → (f₂ ≋ g₂) → (f₁ +F f₂ ≋ g₁ +F g₂)
_+≋_ {A} {B} {C} {D} {f₁} {g₁} {f₂} {g₂} f₁≋g₁ f₂≋g₂ =
  let f≋ = id≋ {x = ⊎≃+} in
  let g≋ = id≋ {x = +≃⊎} in
  begin (
    f₁ +F f₂
      ≋⟨ id≋ ⟩ 
    ⊎≃+ ● (f₁ ⊎≃ f₂) ● +≃⊎
      ≋⟨ f≋ ◎ (T.⊎≃-respects-≋ f₁≋g₁ f₂≋g₂ ◎ g≋) ⟩
    ⊎≃+ ● (g₁ ⊎≃ g₂) ● +≃⊎
      ≋⟨ id≋ ⟩ 
    g₁ +F g₂ ∎)
  where open ≋-Reasoning
--}

postulate 
  unite₊-nat : {m n : ℕ} {f : m fin≃ n} →
    unite+ ● (id0≃ +F f) ≋ f ● unite+

{--
unite₊-nat : {m n : ℕ} {f : m fin≃ n} →
  unite+ ● (id0≃ +F f) ≋ f ● unite+
unite₊-nat {m} {n} {f} =
  let rhs≋ = id≋ {x = (id≃ ⊎≃ f) ● +≃⊎} in
  let f≋ = id≋ {x = ⊎≃+ {m} {n}} in
  let g≋ = id≋ {x = +≃⊎} in
  begin (
    unite+ ● (id0≃ +F f) 
      ≋⟨ id≋ ⟩ 
    (unite₊equiv ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎) ● ⊎≃+ ● ((id≃ ⊎≃ f) ● +≃⊎)
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩
      -- ≋⟨ ●-assocl {f = (id≃ ⊎≃ f) ● +≃⊎} {⊎≃+} {unite₊equiv ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎} ⟩
    ((unite₊equiv ● ((F0≃⊥ ⊎≃ id≃) ● +≃⊎)) ● ⊎≃+) ● (id≃ ⊎≃ f) ● +≃⊎
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩
--       ≋⟨ (●-assocl {f = +≃⊎} {F0≃⊥ ⊎≃ id≃} {unite₊equiv} ◎ f≋ ) ◎ rhs≋ ⟩
    (((unite₊equiv ● (F0≃⊥ ⊎≃ id≃)) ● +≃⊎) ● ⊎≃+) ● (id≃ ⊎≃ f) ● +≃⊎
      ≋⟨ sym≋ (intro-inv-r (unite₊equiv ● (F0≃⊥ ⊎≃ id≃))) ◎ rhs≋ ⟩
    (unite₊equiv ● (F0≃⊥ ⊎≃ id≃)) ● (id≃ ⊎≃ f) ● +≃⊎
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩
--      ≋⟨ ●-assocl {f = +≃⊎} {id≃ ⊎≃ f} {unite₊equiv ● (F0≃⊥ ⊎≃ id≃)} ⟩
    ((unite₊equiv ● (F0≃⊥ ⊎≃ id≃)) ● (id≃ ⊎≃ f)) ● +≃⊎
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩
--      ≋⟨ ●-assoc {f = id≃ ⊎≃ f} {F0≃⊥ ⊎≃ id≃} {unite₊equiv} ◎ g≋ ⟩
    (unite₊equiv ● (F0≃⊥ ⊎≃ id≃) ● (id≃ ⊎≃ f)) ● +≃⊎
      ≋⟨ (id≋ {x = unite₊equiv} ◎ (T.[g+1]●[1+f]≋[1+f]●[g+1] {f = f} {F0≃⊥})) ◎ g≋ ⟩
    (unite₊equiv ● ((id≃ ⊎≃ f) ● (F0≃⊥ ⊎≃ id≃))) ● +≃⊎
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩
--      ≋⟨ ●-assocl {f = F0≃⊥ ⊎≃ id≃} {id≃ ⊎≃ f} {unite₊equiv} ◎ g≋ ⟩
    ((unite₊equiv ● (id≃ ⊎≃ f)) ● (F0≃⊥ ⊎≃ id≃)) ● +≃⊎
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩
--      ≋⟨ ●-assoc {f = +≃⊎} {F0≃⊥ ⊎≃ id≃} {unite₊equiv ● (id≃ ⊎≃ f)} ⟩
    (unite₊equiv ● (id≃ ⊎≃ f)) ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎ 
      ≋⟨ T.unite₊-nat ◎ id≋ {x = (F0≃⊥ ⊎≃ id≃) ● +≃⊎} ⟩
    (f ● unite₊equiv) ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩
--      ≋⟨ ●-assoc {f = (F0≃⊥ ⊎≃ id≃) ● +≃⊎} {unite₊equiv} {f} ⟩
    f ● unite₊equiv ● (F0≃⊥ ⊎≃ id≃) ● +≃⊎
      ≋⟨ id≋ ⟩
    f ● unite+ ∎)
  where open ≋-Reasoning
-- (h ● f) +F (i ● g) ≋ (h +F i) ● (f +F g)
-- Fin (0 + m) ≃ Fin m 
-- Fin (0 + m) ≃ Fin (0 + n)

-- Fin m ≃ Fin (0 + n)

sym+F : ∀ {A B C D} {f : A fin≃ B} {g : C fin≃ D} →
  sym≃ (f +F g) ≋ sym≃ f +F sym≃ g
sym+F {f = f} {g = g} =
  begin (
    sym≃ (f +F g) 
      ≋⟨ id≋ ⟩ 
    (sym≃ +≃⊎ ● (sym≃ f ⊎≃ sym≃ g)) ● sym≃ ⊎≃+
      ≋⟨ ●-assoc {f = sym≃ ⊎≃+} {g = (sym≃ f ⊎≃ sym≃ g)} {h = sym≃ +≃⊎} ⟩ 
    sym≃ +≃⊎ ● ((sym≃ f ⊎≃ sym≃ g) ● sym≃ ⊎≃+)
      ≋⟨ id≋ ⟩ 
    sym≃ f +F sym≃ g ∎)
  where open ≋-Reasoning
--}

postulate 
 uniti₊-nat : ∀ {A B} {f : A fin≃ B} →
    uniti+ ● f ≋ (id0≃ +F f) ● uniti+

{--
uniti₊-nat : ∀ {A B} {f : A fin≃ B} →
  uniti+ ● f ≋ (id0≃ +F f) ● uniti+
uniti₊-nat {f = f} = 
  begin (
    uniti+ ● f 
      ≋⟨ id≋ ⟩ 
    sym≃ unite+ ● sym≃ (sym≃ f)
      ≋⟨ id≋ ⟩ 
    sym≃ (sym≃ f ● unite+)
      ≋⟨ flip-sym≋ unite₊-nat ⟩ 
    sym≃ (unite+ ● (id0≃ +F sym≃ f))
      ≋⟨ id≋ ⟩ 
    sym≃ (id0≃ +F sym≃ f) ● uniti+
      ≋⟨  sym+F ◎ id≋ {x = uniti+} ⟩ 
    (id0≃ +F sym≃ (sym≃ f)) ● uniti+
      ≋⟨ id≋ ⟩ 
    (id0≃ +F f) ● uniti+ ∎)
  where open ≋-Reasoning
--}

postulate
  unite₊r-nat : {m n : ℕ} {f : m fin≃ n} →
   unite+r ● (f +F id0≃) ≋ f ● unite+r

{--
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
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩ -- lots of assoc
    (((unite₊′equiv ● 1+⊥) ● +≃⊎) ● ⊎≃+) ● (f+1 ● +≃⊎)
      ≋⟨ sym≋ (intro-inv-r (unite₊′equiv ● 1+⊥)) ◎ rhs≋ ⟩
    (unite₊′equiv ● 1+⊥) ● (f+1 ● +≃⊎)
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩ -- lots of assoc
    (unite₊′equiv ● (1+⊥ ● f+1)) ● +≃⊎
      ≋⟨ (id≋ {x = unite₊′equiv} ◎ sym≋ (T.[g+1]●[1+f]≋[1+f]●[g+1] {f = F0≃⊥} {f})) ◎ g≋ ⟩
    (unite₊′equiv ● (f ⊎≃ id≃) ● (id≃ ⊎≃ F0≃⊥)) ● +≃⊎ -- the id≃ are at different types!
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩ -- lots of assoc 
    (unite₊′equiv ● (f ⊎≃ id≃)) ● (id≃ ⊎≃ F0≃⊥) ● +≃⊎
      ≋⟨ T.unite₊′-nat ◎ id≋ {x = (id≃ ⊎≃ F0≃⊥) ● +≃⊎} ⟩
    (f ● unite₊′equiv) ● (id≃ ⊎≃ F0≃⊥) ● +≃⊎
      ≋⟨ eq (λ _ → P.refl) (λ _ → P.refl) ⟩ -- assoc + defn
    f ● unite+r ∎)
  where open ≋-Reasoning
--}

postulate 
  uniti₊r-nat : {m n : ℕ} {f : m fin≃ n} →
      uniti+r ● f ≋ (f +F id0≃) ● uniti+r

{--
uniti₊r-nat : {m n : ℕ} {f : m fin≃ n} →
    uniti+r ● f ≋ (f +F id0≃) ● uniti+r
uniti₊r-nat {f = f} =
  begin (
    uniti+r ● f 
      ≋⟨ id≋ ⟩
     sym≃ unite+r ● sym≃ (sym≃ f)
      ≋⟨ id≋ ⟩
     sym≃ (sym≃ f ● unite+r)
      ≋⟨ flip-sym≋ unite₊r-nat ⟩
     sym≃ (unite+r ● (sym≃ f +F id0≃))
      ≋⟨ id≋ ⟩
     sym≃ (sym≃ f +F id0≃) ● uniti+r
      ≋⟨ sym+F ◎ id≋ {x = uniti+r} ⟩
     (sym≃ (sym≃ f) +F id0≃) ● uniti+r
      ≋⟨ id≋ ⟩
    (f +F id0≃) ● uniti+r ∎)
  where open ≋-Reasoning
--}

postulate
  assocr₊-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocr+ {m'} {n'} {o'} ● ((f +F g) +F h) ≋
    (f +F (g +F h)) ● assocr+ {m} {n} {o}

postulate
  assocl₊-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocl+ {m'} {n'} {o'} ● (f +F (g +F h)) ≋
    ((f +F g) +F h) ● assocl+ {m} {n} {o}

postulate
  unite-assocr₊-coh : {m n : ℕ} → 
    unite+r {m = m} +F id≃ {A = Fin n} ≋
    (id≃ {A = Fin m} +F unite+ {m = n}) ● assocr+ {m} {0} {n}

postulate
  assocr₊-coh : {m n o p : ℕ} → 
    assocr+ {m} {n} {o + p} ● assocr+ {m + n} {o} {p} ≋
    (id≃ {A = Fin m} +F assocr+ {n} {o} {p}) ●
      assocr+ {m} {n + o} {p} ● (assocr+ {m} {n} {o} +F id≃ {A = Fin p})

------------------------------------------------------------------------------
-- and the multiplicative structure

id1≃ : Fin 1 ≃ Fin 1
id1≃ = id≃ {A = Fin 1}

postulate 
  id*id≋id : ∀ {m n : ℕ} →
      id≃ {A = Fin m} *F id≃ {A = Fin n} ≋ id≃

{--
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
--}

postulate
  *●≋●* : {A B C D E F : ℕ} →
    {f : A fin≃ C} {g : B fin≃ D} {h : C fin≃ E} {i : D fin≃ F} →
    (h ● f) *F (i ● g) ≋ (h *F i) ● (f *F g)

postulate
  _*≋_ : {A B C D : ℕ} {f₁ g₁ : A fin≃ B} {f₂ g₂ : C fin≃ D} →
    (f₁ ≋ g₁) → (f₂ ≋ g₂) → (f₁ *F f₂ ≋ g₁ *F g₂)

postulate 
  unite*-nat : {m n : ℕ} {f : m fin≃ n} →
    unite* ● (id1≃ *F f) ≋ f ● unite*

postulate 
 uniti*-nat : ∀ {A B} {f : A fin≃ B} →
    uniti* ● f ≋ (id1≃ *F f) ● uniti*

postulate
  unite*r-nat : {m n : ℕ} {f : m fin≃ n} →
   unite*r ● (f *F id1≃) ≋ f ● unite*r

postulate 
  uniti*r-nat : {m n : ℕ} {f : m fin≃ n} →
      uniti*r ● f ≋ (f *F id1≃) ● uniti*r

postulate
  assocr*-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocr* {m'} {n'} {o'} ● ((f *F g) *F h) ≋
    (f *F (g *F h)) ● assocr* {m} {n} {o}

postulate
  assocl*-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} → 
    assocl* {m'} {n'} {o'} ● (f *F (g *F h)) ≋
    ((f *F g) *F h) ● assocl* {m} {n} {o}

postulate
  unite-assocr*-coh : {m n : ℕ} → 
    unite*r {m = m} *F id≃ {A = Fin n} ≋
    (id≃ {A = Fin m} *F unite* {m = n}) ● assocr* {m} {1} {n}

postulate
  assocr*-coh : {m n o p : ℕ} → 
    assocr* {m} {n} {o * p} ● assocr* {m * n} {o} {p} ≋
    (id≃ {A = Fin m} *F assocr* {n} {o} {p}) ●
      assocr* {m} {n * o} {p} ● (assocr* {m} {n} {o} *F id≃ {A = Fin p})

------------------------------------------------------------------------------
