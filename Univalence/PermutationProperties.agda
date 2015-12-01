{-# OPTIONS --without-K #-}

module PermutationProperties where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning; proof-irrelevance; setoid)
open import Function.Equality   using    (_⟨$⟩_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; proj₁; proj₂)
--

import FinEquivPlusTimes using (module Plus) -- don't open, just import
import FinEquivTypeEquiv using (module PlusE) -- don't open, just import
open FinEquivPlusTimes.Plus using (⊎≃+; +≃⊎)
open FinEquivTypeEquiv.PlusE using (_+F_)
open import ConcretePermutation
open import Permutation
open import SEquivSCPermEquiv
open import Equiv using (_●_; id≃; sym≃; _⊎≃_)
open import EquivEquiv
  using (id≋; sym≋; ●-assoc; _◎_; lid≋; rid≋; linv≋; rinv≋;
     module ≋-Reasoning)
open import TypeEquivEquiv using (_⊎≋_)
open import FinEquivEquivPlus using ([id+id]≋id; +●≋●+)

open ≋-Reasoning

------------------------------------------------------------------------------
-- Composition

assocp : ∀ {m₁ m₂ m₃ n₁} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ m₁} →
  {p₃ : CPerm m₃ m₂} → 
  (p₁ ●p p₂) ●p p₃ ≡ p₁ ●p (p₂ ●p p₃)
assocp {p₁ = p₁} {p₂} {p₃} =
  let e₁ = p⇒e p₁ in let e₂ = p⇒e p₂ in let e₃ = p⇒e p₃ in
  ≋⇒≡ (begin (
  p⇒e (e⇒p (e₁ ● e₂)) ● e₃  
    ≋⟨ left-α-over-● (e₁ ● e₂) e₃ ⟩ 
  (e₁ ● e₂) ● e₃
    ≋⟨ ●-assoc {f = e₃} {e₂} {e₁} ⟩
  e₁ ● (e₂ ● e₃)
    ≋⟨ sym≋ (right-α-over-● e₁ (e₂ ● e₃)) ⟩
   e₁ ● (p⇒e (e⇒p (e₂ ● e₃))) ∎))

lidp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → idp ●p p ≡ p
lidp {p = p} = trans (≋⇒≡ (begin (
  (p⇒e (e⇒p id≃)) ● (p⇒e p)
    ≋⟨ left-α-over-● id≃ (p⇒e p) ⟩
  id≃ ● (p⇒e p)
    ≋⟨ lid≋ ⟩
  (p⇒e p) ∎))) (βu refl)

ridp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → p ●p idp ≡ p
ridp {p = p} = trans (≋⇒≡ (begin (
  (p⇒e p) ● (p⇒e (e⇒p id≃))
    ≋⟨ right-α-over-● (p⇒e p) id≃ ⟩
  (p⇒e p) ● id≃
    ≋⟨ rid≋ ⟩
  (p⇒e p) ∎))) (βu refl)
  
-- Inverses

rinv : ∀ {m₁ m₂} (p : CPerm m₂ m₁) → p ●p (symp p) ≡ idp
rinv p = let e = p⇒e p in ≋⇒≡ (begin (
  e ● (p⇒e (e⇒p (sym≃ e)))
    ≋⟨ right-α-over-● e (sym≃ e) ⟩
  e ● (sym≃ e)
    ≋⟨ rinv≋ e ⟩
  id≃ ∎))
  
linv : ∀ {m₁ m₂} (p : CPerm m₂ m₁) → (symp p) ●p p ≡ idp
linv p = let e = p⇒e p in ≋⇒≡ (begin (
  (p⇒e (e⇒p (sym≃ e))) ● e
    ≋⟨ left-α-over-● (sym≃ e) e ⟩
  (sym≃ e) ● e
    ≋⟨ linv≋ e ⟩
  id≃ ∎))

-- p₁ ⊎p p₂ = e⇒p ((p⇒e p₁) +F (p⇒e p₂))
--   Fm≃Fn +F Fo≃Fp = ⊎≃+ ● Fm≃Fn ⊎≃ Fo≃Fp ● +≃⊎
⊎p●p≡●p⊎p : {m₁ m₂ n₁ n₂ o₁ o₂ : ℕ} →
  {f : CPerm n₁ m₁} {g : CPerm n₂ m₂} {h : CPerm o₁ n₁} {i : CPerm o₂ n₂} →
  ((f ●p h) ⊎p (g ●p i)) ≡ ((f ⊎p g) ●p (h ⊎p i))
⊎p●p≡●p⊎p {f = f} {g} {h} {i} =
  let e₁ = p⇒e f in let e₂ = p⇒e g in let e₃ = p⇒e h in let e₄ = p⇒e i in
  let f≋ = id≋ {x = ⊎≃+} in
  let g≋ = id≋ {x = +≃⊎} in
  ≋⇒≡ (begin -- inline ⊎p 
  p⇒e (e⇒p (e₁ ● e₃)) +F p⇒e (e⇒p (e₂ ● e₄))
    ≋⟨ id≋ ⟩ -- inline +F
  ⊎≃+ ● (p⇒e (e⇒p (e₁ ● e₃)) ⊎≃ p⇒e (e⇒p (e₂ ● e₄))) ● +≃⊎
    ≋⟨ f≋ ◎ ((α₁ ⊎≋ α₁) ◎ g≋) ⟩
  ⊎≃+ ● ((e₁ ● e₃) ⊎≃ (e₂ ● e₄)) ● +≃⊎
    ≋⟨ +●≋●+ ⟩
  (e₁ +F e₂) ● (e₃ +F e₄)
    ≋⟨ sym≋ ((α₁ {e = e₁ +F e₂}) ◎ (α₁ {e = e₃ +F e₄})) ⟩
  (p⇒e (e⇒p (e₁ +F e₂)) ● p⇒e (e⇒p (e₃ +F e₄))) ∎)

-- Additives

1p⊎1p≡1p : ∀ {m n} → idp {m} ⊎p idp {n} ≡ idp {m + n}
1p⊎1p≡1p {m} {n} =
  let em = p⇒e (e⇒p (id≃ {A = Fin m})) in
  let en = p⇒e (e⇒p (id≃ {A = Fin n})) in
  let f≋ = id≋ {x = ⊎≃+ {m} {n}} in
  let g≋ = id≋ {x = +≃⊎ {m} {n}} in
  ≋⇒≡ (begin (
  em +F en
    ≋⟨ id≋ ⟩
  ⊎≃+ ● em ⊎≃ en ● +≃⊎
    ≋⟨ f≋ ◎ ((α₁ ⊎≋ α₁) ◎ g≋) ⟩
  ⊎≃+ ● (id≃ {A = Fin m}) ⊎≃ id≃ ● +≃⊎
    ≋⟨ [id+id]≋id ⟩
  id≃ {A = Fin (m + n)} ∎))

-- interaction with composition
{-  The underlying permutations are no longer defined!
unite+p∘[0⊎x]≡x∘unite+p : ∀ {m n} (p : CPerm m n) →
  transp unite+p (0p ⊎p p) ≡ transp p unite+p
unite+p∘[0⊎x]≡x∘unite+p p = p≡ unite+∘[0⊎x]≡x∘unite+

uniti+p∘x≡[0⊎x]∘uniti+p : ∀ {m n} (p : CPerm m n) →
  transp uniti+p p ≡ transp (0p ⊎p p) uniti+p
uniti+p∘x≡[0⊎x]∘uniti+p p = p≡ (uniti+∘x≡[0⊎x]∘uniti+ {x = CPerm.π p})

uniti+rp∘[x⊎0]≡x∘uniti+rp : ∀ {m n} (p : CPerm m n) →
  transp uniti+rp (p ⊎p 0p) ≡ transp p uniti+rp
uniti+rp∘[x⊎0]≡x∘uniti+rp p = p≡ uniti+r∘[x⊎0]≡x∘uniti+r
-}

{-
unite+rp∘[x⊎0]≡x∘unite+rp : ∀ {m n} (p : CPerm m n) →
  transp unite+rp p ≡ transp (p ⊎p 0p) unite+rp
unite+rp∘[x⊎0]≡x∘unite+rp p = p≡ unite+r∘[x⊎0]≡x∘unite+r
-}

-- Multiplicatives
{-
1p×1p≡1p : ∀ {m n} → idp {m} ×p idp {n} ≡ idp
1p×1p≡1p {m} = p≡ (1C×1C≡1C {m})

×p-distrib :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ n₂}
    → {p₃ : CPerm m₃ m₁} → {p₄ : CPerm m₄ m₂} →
      (transp p₁ p₃) ×p (transp p₂ p₄) ≡ transp (p₁ ×p p₂) (p₃ ×p p₄)
×p-distrib {p₁ = p₁} = p≡ (sym (×c-distrib {p₁ = CPerm.π p₁}))
-}
------------------------------------------------------------------------------
