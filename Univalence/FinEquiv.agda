{-# OPTIONS --without-K #-}

module FinEquiv where

-- should restrict the imports (later)
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Fin renaming (_+_ to _+F_) hiding (_≤_;_<_)
open import Data.Fin.Properties
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple using (+-suc; +-comm; *-right-zero)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Data.Empty
open import Data.Nat
open import Data.Nat.DivMod
open import Function

open import Equiv
open import LeqLemmas
open import FinNatLemmas
open import TypeEquivalences using (swap₊; swap⋆)

-- Divide into 2 modules
module Plus where
  fwd : {m n : ℕ} → (Fin m ⊎ Fin n) → Fin (m + n)
  fwd {m} {n} (inj₁ x) = inject+ n x
  fwd {m} {n} (inj₂ y) = raise m y

  bwd : {m n : ℕ} → Fin (m + n) → (Fin m ⊎ Fin n)
  bwd {m} {n} i with toℕ i <? m
  ... | yes p = inj₁ (fromℕ≤ p)
  ... | no ¬p = inj₂ (reduce≥ i (≤-pred (≰⇒> ¬p)))

  fwd∘bwd~id : {m n : ℕ} → fwd {m} {n} ∘ bwd ∼ id
  fwd∘bwd~id {m} i with toℕ i <? m
  fwd∘bwd~id i | yes p = sym (inj₁-≡ i p)
  fwd∘bwd~id i | no ¬p = sym (inj₂-≡ i (≤-pred (≰⇒> ¬p)))

  bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
  bwd∘fwd~id {m} {n} (inj₁ x) with toℕ (inject+ n x) <? m 
  bwd∘fwd~id {n = n} (inj₁ x) | yes p = 
     cong inj₁ (inject+-injective (fromℕ≤ p) x (sym (inj₁-≡ (inject+ n x) p)))
  bwd∘fwd~id {m} {n} (inj₁ x) | no ¬p = ⊥-elim (1+n≰n pf)
   where
     open ≤-Reasoning
     pf : suc (toℕ x) ≤ toℕ x
     pf = let q =  (≤-pred (≰⇒> ¬p)) in 
            begin (
              suc (toℕ x)
                ≤⟨ bounded x ⟩
              m
                ≤⟨ q ⟩
              toℕ (inject+ n x)
                ≡⟨ sym (inject+-lemma n x) ⟩
              toℕ x ∎ )

  bwd∘fwd~id {m} {n} (inj₂ y) with toℕ (raise m y) <? m 
  bwd∘fwd~id {m} {n} (inj₂ y) | yes p = ⊥-elim (1+n≰n pf)
   where
     open ≤-Reasoning
     pf : suc m ≤ m
     pf = begin (
             suc m
                 ≤⟨ m≤m+n (suc m) (toℕ y) ⟩
             suc (m + toℕ y)
                 ≡⟨ cong suc (sym (toℕ-raise m y)) ⟩
             suc (toℕ (raise m y))
                 ≤⟨ p ⟩
             m ∎)
  bwd∘fwd~id {m} {n} (inj₂ y) | no ¬p = 
     cong inj₂ (raise-injective {m} (reduce≥ (raise m y) (≤-pred (≰⇒> ¬p))) 
                  y (sym (inj₂-≡ (raise m y) (≤-pred (≰⇒> ¬p)))))

  fwd-iso : {m n : ℕ} → (Fin m ⊎ Fin n) ≃ Fin (m + n)
  fwd-iso {m} {n} = fwd , mkqinv bwd (fwd∘bwd~id {m}) (bwd∘fwd~id {m})

  swapper : (m n : ℕ) → Fin (m + n) → Fin (n + m)
  swapper m n = fwd ∘ swap₊ ∘ bwd {m} {n} 

module Times where
  open import Perm hiding (absurd-quotient; Fin0-⊥) -- will fix later
  open import DivModUtils using (addMul-lemma)
  
  fwd : {m n : ℕ} → (Fin m × Fin n) → Fin (m * n)
  fwd {m} {n} (i , k) = inject≤ (fromℕ (toℕ i * n + toℕ k)) (i*n+k≤m*n i k)

  private
    absurd-quotient : (m n q : ℕ) (r : Fin (suc n)) (k : Fin (m * suc n)) 
         (k≡r+q*sn : toℕ k ≡ toℕ r + q * suc n) (p : m ≤ q) → ⊥
    absurd-quotient m n q r k k≡r+q*sn p = ¬i+1+j≤i (toℕ k) {toℕ r} k≥k+sr
      where k≥k+sr : toℕ k ≥ toℕ k + suc (toℕ r)
            k≥k+sr = begin (toℕ k + suc (toℕ r)
                       ≡⟨ +-suc (toℕ k) (toℕ r) ⟩
                     suc (toℕ k) + toℕ r
                       ≤⟨ cong+r≤ (bounded k) (toℕ r) ⟩ 
                     (m * suc n) + toℕ r
                       ≡⟨ +-comm (m * suc n) (toℕ r) ⟩ 
                     toℕ r + (m * suc n)
                       ≡⟨ refl ⟩ 
                     toℕ r + m * suc n
                       ≤⟨ cong+l≤ (cong*r≤ p (suc n)) (toℕ r) ⟩ 
                     toℕ r + q * suc n
                       ≡⟨ sym k≡r+q*sn ⟩
                     toℕ k ∎)
                      where open ≤-Reasoning

    Fin0-⊥ : Fin 0 → ⊥
    Fin0-⊥ ()

    elim-right-zero : ∀ {ℓ} {Whatever : Set ℓ} (m : ℕ) → Fin (m * 0) → Whatever
    elim-right-zero m i = ⊥-elim (Fin0-⊥ (subst Fin (*-right-zero m) i))
    
  -- this was fin-project in Perm.agda
  bwd : {m n : ℕ} → Fin (m * n) → (Fin m × Fin n)
  bwd {m} {0} k = elim-right-zero m k
  bwd {m} {suc n} k with (toℕ k) divMod (suc n)
  ... | result q r k≡r+q*sn = (fromℕ≤ {q} {m} (q≤m) , r)
    where q≤m : q < m
          q≤m with m ≤? q
          ... | yes p = ⊥-elim (absurd-quotient m n q r k k≡r+q*sn p)
          ... | no ¬p = ≰⇒> ¬p

  fwd∘bwd~id : {m n : ℕ} → fwd {m} {n} ∘ bwd ∼ id
  fwd∘bwd~id {m} {zero} i = elim-right-zero m i
  fwd∘bwd~id {m} {suc n} i with (toℕ i) divMod (suc n)
  ... | result q r k≡r+q*sn with m ≤? q
  ... | yes p = ⊥-elim (absurd-quotient m n q r i k≡r+q*sn p)
  ... | no ¬p = toℕ-injective toℕi
    where
      open ≡-Reasoning
      toℕi = let q<m = fromℕ≤ (≰⇒> ¬p) in
             begin (
               toℕ (inject≤ (fromℕ (toℕ q<m * suc n + toℕ r))
                 (i*n+k≤m*n q<m r))
                   ≡⟨ inject≤-lemma _ _ ⟩
               toℕ (fromℕ (toℕ q<m * suc n + toℕ r))
                   ≡⟨ to-from _ ⟩
               toℕ q<m * suc n + toℕ r
                   ≡⟨ cong (λ x → x * suc n + toℕ r)
                          (toℕ-fromℕ≤ (≰⇒> ¬p)) ⟩
               q * suc n + toℕ r
                   ≡⟨  trans (+-comm _ (toℕ r)) (sym k≡r+q*sn) ⟩
               toℕ i ∎ )
  bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
  bwd∘fwd~id {n = zero} (b , ())
  bwd∘fwd~id {m} {suc n} (b , d) with fwd (b , d) | inspect fwd (b , d)
  ... | k | [ eq ] with (toℕ k) divMod (suc n)
  ... | result q r pf with m ≤? q
  ... | yes p = ⊥-elim (absurd-quotient m n q r k pf p)
  ... | no ¬p = cong₂ _,_  pf₁ (proj₁ same-quot)
    where
      open ≡-Reasoning
      eq' : toℕ d + toℕ b * suc n ≡ toℕ r + q * suc n
      eq' = begin (
        toℕ d + toℕ b * suc n
          ≡⟨ +-comm (toℕ d) _ ⟩
        toℕ b * suc n + toℕ d
          ≡⟨ sym (to-from _) ⟩
        toℕ (fromℕ (toℕ b * suc n + toℕ d))
          ≡⟨ sym (inject≤-lemma _ _) ⟩
        toℕ (inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
          ≡⟨ cong toℕ eq ⟩
        toℕ k
          ≡⟨ pf ⟩
        toℕ r + q * suc n ∎ )
      same-quot : (r ≡ d) × (q ≡ toℕ b)
      same-quot = addMul-lemma q (toℕ b) n r d ( sym eq' )
      pf₁ = (toℕ-injective (trans (toℕ-fromℕ≤ (≰⇒> ¬p)) (proj₂ same-quot)))

  fwd-iso : {m n : ℕ} → (Fin m × Fin n) ≃ Fin (m * n)
  fwd-iso {m} {n} = fwd , mkqinv bwd (fwd∘bwd~id {m}) (bwd∘fwd~id {m})

  swapper : (m n : ℕ) → Fin (m * n) → Fin (n * m)
  swapper m n = fwd ∘ swap⋆ ∘ bwd {m} {n} 
