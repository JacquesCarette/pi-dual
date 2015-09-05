{-# OPTIONS --without-K #-}

module PermutationProperties where

open import Data.Nat using (_+_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning; proof-irrelevance; setoid)
open import Function.Equality   using    (_⟨$⟩_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; proj₁; proj₂)
--

open import Data.Sum.Properties
  using (map⊎idid≡id)
  
open import FinEquiv using (module Plus)
open import ConcretePermutation
open import Permutation
open import SEquivSCPermEquiv
open import Equiv
open import EquivEquiv

------------------------------------------------------------------------------
-- Composition

assocp : ∀ {m₁ m₂ m₃ n₁} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ m₁} →
  {p₃ : CPerm m₃ m₂} → 
  transp p₁ (transp p₂ p₃) ≡ transp (transp p₁ p₂) p₃
assocp {p₁ = p₁} {p₂} {p₃} =
  let e₁ = p⇒e p₁ in let e₂ = p⇒e p₂ in let e₃ = p⇒e p₃ in
  ≋⇒≡ (begin (
  e₁ ● (p⇒e (e⇒p (e₂ ● e₃)))
    ≋⟨ right-α-over-● e₁ (e₂ ● e₃) ⟩ 
  e₁ ● (e₂ ● e₃)
    ≋⟨ sym≋ (●-assoc {f = e₃} {e₂} {e₁}) ⟩
  (e₁ ● e₂) ● e₃
    ≋⟨ sym≋ (left-α-over-● (e₁ ● e₂) e₃) ⟩
  p⇒e (e⇒p (e₁ ● e₂)) ● e₃ ∎))
  where open ≋-Reasoning

lidp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → transp idp p ≡ p
lidp {p = p} = trans (≋⇒≡ (begin (
  (p⇒e (e⇒p id≃)) ● (p⇒e p)
    ≋⟨ left-α-over-● id≃ (p⇒e p) ⟩
  id≃ ● (p⇒e p)
    ≋⟨ eq (λ _ → refl) (λ _ → refl) ⟩
  (p⇒e p) ∎))) (βu refl)
  where open ≋-Reasoning

ridp : ∀ {m₁ m₂} {p : CPerm m₂ m₁} → transp p idp ≡ p
ridp {p = p} = trans (≋⇒≡ (begin (
  (p⇒e p) ● (p⇒e (e⇒p id≃))
    ≋⟨ right-α-over-● (p⇒e p) id≃ ⟩
  (p⇒e p) ● id≃
    ≋⟨ eq (λ _ → refl) (λ _ → refl) ⟩
  (p⇒e p) ∎))) (βu refl)
  where open ≋-Reasoning
  
{-
transp-resp-≡ : ∀ {m₁ m₂ m₃} {f h : CPerm m₂ m₃} {g i : CPerm m₁ m₂} → 
  f ≡ h → g ≡ i → transp f g ≡ transp h i
transp-resp-≡ refl refl = refl
-}

-- Inverses

rinv : ∀ {m₁ m₂} (p : CPerm m₂ m₁) → transp p (symp p) ≡ idp
rinv p = let e = p⇒e p in ≋⇒≡ (begin (
  e ● (p⇒e (e⇒p (sym≃ e)))
    ≋⟨ right-α-over-● e (sym≃ e) ⟩
  e ● (sym≃ e)
    ≋⟨ rinv≋ e ⟩
  id≃ ∎))
  where open ≋-Reasoning
  

linv : ∀ {m₁ m₂} (p : CPerm m₂ m₁) → transp (symp p) p ≡ idp
linv p = let e = p⇒e p in ≋⇒≡ (begin (
  (p⇒e (e⇒p (sym≃ e))) ● e
    ≋⟨ left-α-over-● (sym≃ e) e ⟩
  (sym≃ e) ● e
    ≋⟨ linv≋ e ⟩
  id≃ ∎))
  where open ≋-Reasoning


-- Additives

1p⊎1p≡1p : ∀ {m n} → idp {m} ⊎p idp {n} ≡ idp {m + n}
1p⊎1p≡1p {m} {n} =
  let em = p⇒e (e⇒p (id≃ {A = Fin m})) in
  let en = p⇒e (e⇒p (id≃ {A = Fin n})) in
  let f≋ = id≋ {x = Plus.fwd-iso {m} {n}} in
  let g≋ = id≋ {x = sym≃ (Plus.fwd-iso {m} {n})} in
  ≋⇒≡ (begin (
  em +F en
    ≋⟨ id≋ ⟩
  Plus.fwd-iso ● em ⊎≃ en ● sym≃ Plus.fwd-iso
    ≋⟨ ●-resp-≋ f≋ (●-resp-≋ (⊎≃-resp-≋ α₁ α₁) g≋) ⟩
  Plus.fwd-iso ● ((id≃ {A = Fin m}) ⊎≃ id≃ ● (sym≃ Plus.fwd-iso))
    ≋⟨ ●-resp-≋ f≋ (●-resp-≋ {f = id≃ ⊎≃ id≃} {id≃} (eq map⊎idid≡id map⊎idid≡id) g≋) ⟩
  Plus.fwd-iso {m} {n} ● (id≃ {A = Fin m ⊎ Fin n} ● (sym≃ Plus.fwd-iso))
    ≋⟨ ●-resp-≋ {f = Plus.fwd-iso} {Plus.fwd-iso} {id≃ ● sym≃ Plus.fwd-iso} {sym≃ Plus.fwd-iso} f≋ (eq (λ _ → refl) (λ _ → refl)) ⟩
  Plus.fwd-iso {m} ● (sym≃ Plus.fwd-iso)  
    ≋⟨ rinv≋ (Plus.fwd-iso {m}) ⟩
  id≃ {A = Fin (m + n)} ∎))
  where open ≋-Reasoning
        open Plus
 
{-
0p⊎x≡x : ∀ {m n} {p : CPerm m n} → idp {0} ⊎p p ≡ p
0p⊎x≡x {p = p} = p≡ 1C₀⊎x≡x

⊎p-distrib :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : CPerm m₁ n₁} → {p₂ : CPerm m₂ n₂}
    → {p₃ : CPerm m₃ m₁} → {p₄ : CPerm m₄ m₂} →
      transp (p₁ ⊎p p₂) (p₃ ⊎p p₄) ≡ (transp p₁ p₃) ⊎p (transp p₂ p₄)
⊎p-distrib {p₁ = p₁} = p≡ (⊎c-distrib {p₁ = CPerm.π p₁})
-}

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
