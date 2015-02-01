{-# OPTIONS --without-K #-}

module ForAmr where

open import Level using (Level)

open import Data.Vec
  using (Vec; tabulate; []; _∷_; lookup; allFin)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import  Data.Vec.Properties
  using (lookup-++-≥; lookup∘tabulate; tabulate-∘; tabulate∘lookup; map-cong)
open import Function using (id;_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst; proof-irrelevance;
             _≗_; module ≡-Reasoning)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Fin using (Fin; zero; suc; inject+; raise; reduce≥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (proj₁)
open import Function using (flip)

open import SubstLemmas
open import VectorLemmas
open import Equiv
open import FinEquiv
open import Cauchy 

----------------------------------------------------

-- to make things look nicer
_!!_ : ∀ {m} {A : Set} → Vec A m → Fin m → A
v !! i = lookup i v

pcomp : ∀ {m n} {A B : Set} → Vec A m → Vec B n → Vec (A ⊎ B) (m + n)
pcomp {m} {n} α β = tabulate (inj₁ ∘ _!!_ α) ++V 
                                     tabulate (inj₂ ∘ _!!_ β)

-- the Cauchy version:
pcomp' : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m + n)
pcomp' α β = mapV fwd (pcomp α β)

swap⊎ : {A B : Set} → A ⊎ B → B ⊎ A
swap⊎ (inj₁ x) = inj₂ x
swap⊎ (inj₂ y) = inj₁ y

swap⊎-idemp : {A B : Set} → ∀ x → swap⊎ {B} {A} (swap⊎ x) ≡ id x
swap⊎-idemp (inj₁ x) = refl
swap⊎-idemp (inj₂ y) = refl

swap+ : {m n : ℕ} {A B : Set} → Vec (A ⊎ B) (m + n) → Vec (B ⊎ A) (m + n)
swap+ v = tabulate (swap⊎ ∘ _!!_ v)

-- the Cauchy version.  Both implementations work, not sure which is best.
swap+c : (m n : ℕ) → Cauchy (m + n)
-- swap+c m n = mapV (λ x → subst Fin (+-comm n m) (fwd x)) 
--   (swap+ {m = m} (tabulate {m + n} (bwd {m})))
swap+c m n = subst (λ x → Vec (Fin x) (m + n)) (+-comm n m)
  (mapV fwd (swap+ {m} (tabulate {m + n} (bwd {m} {n}))))

-- nested tabulate-lookup
denest-tab-!! : {A B C : Set} {k : ℕ} → (f : B → C) → (g : A → B) → (v : Vec A k) →
    tabulate (λ i → f (tabulate (λ j → g (v !! j)) !! i)) ≡ mapV (f ∘ g) v
denest-tab-!! f g v = 
  begin ( 
    tabulate (λ i → f (tabulate (λ j → g (v !! j)) !! i))
        ≡⟨ tabulate-∘ f (λ i → tabulate (λ j → g (v !! j)) !! i) ⟩
    mapV f (tabulate  (λ i → tabulate (λ j → g (v !! j)) !! i) )
        ≡⟨ cong (mapV f) (tabulate∘lookup (tabulate (λ j → g (v !! j)))) ⟩
    mapV f (tabulate (λ j → g (v !! j)))
        ≡⟨ cong (mapV f) (tabulate-∘ g (flip lookup v)) ⟩
    mapV f (mapV g (tabulate (flip lookup v)))
        ≡⟨ sym (map-∘ f g _) ⟩
    mapV (f ∘ g) (tabulate (flip lookup v))
        ≡⟨ cong (mapV (f ∘ g)) (tabulate∘lookup v) ⟩
    mapV (f ∘ g) v ∎)
  where open ≡-Reasoning

-- and now this is completely obvious:
swap+-idemp : {A B : Set} → {m n : ℕ} → (v : Vec (A ⊎ B) (m + n)) →
  swap+ {m} (swap+ {m} v) ≡ v
swap+-idemp v = 
  begin ( 
    tabulate (λ i → swap⊎ (tabulate (λ j → swap⊎ (v !! j)) !! i))
        ≡⟨ denest-tab-!! swap⊎ swap⊎ v ⟩
    mapV (swap⊎ ∘ swap⊎) v
        ≡⟨ map-cong swap⊎-idemp v ⟩
    mapV id v
        ≡⟨ map-id v ⟩
    v ∎) 
  where open ≡-Reasoning
