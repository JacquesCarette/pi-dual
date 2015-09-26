{-# OPTIONS --without-K #-}

module FinEquivPlusTimes where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; ≤-pred; _≥_; _≤?_;
         module ≤-Reasoning)
open import Data.Nat.DivMod using (_divMod_; result)
open import Data.Nat.Properties using (≰⇒>; 1+n≰n; m≤m+n; ¬i+1+j≤i)
open import Data.Nat.Properties.Simple
  using (+-assoc; +-suc; +-comm; *-right-zero) 

open import Data.Fin
  using (Fin; zero; suc; inject+; raise; toℕ; fromℕ≤; reduce≥)
open import Data.Fin.Properties
  using (bounded; inject+-lemma; toℕ-raise; toℕ-injective; toℕ-fromℕ≤)

open import Function using (_∘_; id; case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst;
         module ≡-Reasoning; inspect; [_])

--

open import Equiv using (_∼_; _≃_; qinv; id≃; sym≃; _●_; _⊎≃_)

open import Proofs using (
  -- LeqLemmas
  _<?_; cong+r≤; cong+l≤; cong*r≤; 
  -- FinNatLemmas 
  inj₁-≡; inj₂-≡; inject+-injective; raise-injective; addMul-lemma
  )

------------------------------------------------------------------------------
-- Additive unit and multiplicative unit are Fin 0 and Fin 1 which are
-- equivalent to ⊥ and ⊤

abstract

  Fin0-⊥ : Fin 0 → ⊥
  Fin0-⊥ ()

  F0≃⊥ : Fin 0 ≃ ⊥
  F0≃⊥ = f , qinv g α β
    where
      f : Fin 0 → ⊥
      f ()
      g : ⊥ → Fin 0
      g ()
      α : f ∘ g ∼ id
      α ()
      β : g ∘ f ∼ id
      β ()

  Fin1≃⊤ : Fin 1 ≃ ⊤
  Fin1≃⊤ = f , qinv g α β
    where
      f : Fin 1 → ⊤
      f zero = tt
      f (suc ())
      g : ⊤ → Fin 1
      g tt = zero
      α : f ∘ g ∼ id
      α tt = refl
      β : g ∘ f ∼ id
      β zero = refl
      β (suc ())

------------------------------------------------------------------------------
-- Additive monoid

module Plus where
  
  -- Main goal is to show (Fin m ⊎ Fin n) ≃ Fin (m + n) It is then
  -- fairly easy to show that ⊎ satisfies the commutative monoid
  -- axioms

  fwd : {m n : ℕ} → (Fin m ⊎ Fin n) → Fin (m + n)
  fwd {m} {n} (inj₁ x) = inject+ n x
  fwd {m} {n} (inj₂ y) = raise m y

  bwd : {m n : ℕ} → Fin (m + n) → (Fin m ⊎ Fin n)
  bwd {m} {n} = λ i → case (toℕ i <? m) of λ
    { (yes p) → inj₁ (fromℕ≤ p)
     ; (no ¬p) → inj₂ (reduce≥ i (≤-pred (≰⇒> ¬p)))
     }

  fwd∘bwd~id : {m n : ℕ} → fwd {m} {n} ∘ bwd ∼ id
  fwd∘bwd~id {m} i with toℕ i <? m
  fwd∘bwd~id i | yes p = sym (inj₁-≡ i p)
  fwd∘bwd~id i | no ¬p = sym (inj₂-≡ i (≤-pred (≰⇒> ¬p)))

  bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
  bwd∘fwd~id {m} {n} (inj₁ x) with toℕ (inject+ n x) <? m 
  bwd∘fwd~id {n = n} (inj₁ x) | yes p = 
     cong inj₁
       (inject+-injective (fromℕ≤ p) x (sym (inj₁-≡ (inject+ n x) p)))
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
     cong inj₂
       (raise-injective {m}
         (reduce≥ (raise m y) (≤-pred (≰⇒> ¬p)))
         y
         (sym (inj₂-≡ (raise m y) (≤-pred (≰⇒> ¬p)))))

  -- the main equivalence
  abstract
    fwd-iso : {m n : ℕ} → (Fin m ⊎ Fin n) ≃ Fin (m + n)
    fwd-iso {m} {n} = fwd , qinv bwd (fwd∘bwd~id {m}) (bwd∘fwd~id {m})

  -- aliases for the above which are more convenient
  ⊎≃+ : {m n : ℕ} → (Fin m ⊎ Fin n) ≃ Fin (m + n)
  ⊎≃+ = fwd-iso

  +≃⊎ : {m n : ℕ} → Fin (m + n) ≃ (Fin m ⊎ Fin n)
  +≃⊎ = sym≃ fwd-iso
  
-----------------------------------------------------------------------------
-- Multiplicative monoid

module Times where
  
  -- main goal is to show (Fin m × Fin n) ≃ Fin (m * n) It is then
  -- fairly easy to show that × satisfies the commutative monoid
  -- axioms

  fwd : {m n : ℕ} → (Fin m × Fin n) → Fin (m * n)
  fwd {suc m} {n} (zero , k) = inject+ (m * n) k
  fwd {n = n} (suc i , k) = raise n (fwd (i , k))

  private
    soundness : ∀ {m n} (i : Fin m) (j : Fin n) →
                toℕ (fwd (i , j)) ≡ toℕ i * n + toℕ j
    soundness {suc m} {n} zero     j = sym (inject+-lemma (m * n) j)
    soundness {n = n} (suc i) j
      rewrite toℕ-raise n (fwd (i , j)) | soundness i j
      = sym (+-assoc n (toℕ i * n) (toℕ j))

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

  elim-right-zero : ∀ {ℓ} {Whatever : Set ℓ}
                    (m : ℕ) → Fin (m * 0) → Whatever
  elim-right-zero m i = ⊥-elim (Fin0-⊥ (subst Fin (*-right-zero m) i))

  bwd : {m n : ℕ} → Fin (m * n) → (Fin m × Fin n)
  bwd {m} {0} k = elim-right-zero m k
  bwd {m} {suc n} k with (toℕ k) divMod (suc n)
  ... | result q r k≡r+q*sn = (fromℕ≤ {q} {m} (q<m) , r)
    where 
          q<m : q < m
          q<m with suc q ≤? m 
          ... | no ¬p = ⊥-elim
                          (absurd-quotient m n q r k k≡r+q*sn
                            (≤-pred (≰⇒> ¬p)))
          ... | yes p = p

  fwd∘bwd~id : {m n : ℕ} → fwd {m} {n} ∘ bwd ∼ id
  fwd∘bwd~id {m} {zero} i = elim-right-zero m i
  fwd∘bwd~id {m} {suc n} i with (toℕ i) divMod (suc n)
  ... | result q r k≡r+q*sn with suc q ≤? m
  ... | yes p = toℕ-injective (
      begin (
        toℕ (fwd (fromℕ≤ p , r))
          ≡⟨ soundness (fromℕ≤ p) r ⟩
        toℕ (fromℕ≤ p) * (suc n) + toℕ r
          ≡⟨ cong (λ x → x * (suc n) + toℕ r) (toℕ-fromℕ≤ p) ⟩
        q * (suc n) + toℕ r
          ≡⟨ +-comm _ (toℕ r) ⟩
        toℕ r  + q * (suc n)
          ≡⟨ sym (k≡r+q*sn) ⟩
        toℕ i ∎))
      where open ≡-Reasoning
  ... | no ¬p = ⊥-elim (absurd-quotient m n q r i k≡r+q*sn (≤-pred (≰⇒> ¬p)))

  bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
  bwd∘fwd~id {n = zero} (b , ())
  bwd∘fwd~id {m} {suc n} (b , d) with fwd (b , d) | inspect fwd (b , d)
  ... | k | [ eq ] with (toℕ k) divMod (suc n)
  ... | result q r pf with q <? m
  ... | no ¬p = ⊥-elim (absurd-quotient m n q r k pf (≤-pred (≰⇒> ¬p)))
  ... | yes p = cong₂ _,_  pf₁ (proj₁ same-quot)
    where
      open ≡-Reasoning
      eq' : toℕ d + toℕ b * suc n ≡ toℕ r + q * suc n
      eq' = begin (
        toℕ d + toℕ b * suc n
          ≡⟨ +-comm (toℕ d) _ ⟩
        toℕ b * suc n + toℕ d
          ≡⟨ trans (sym (soundness b d)) (cong toℕ eq) ⟩
        toℕ k
          ≡⟨ pf ⟩
        toℕ r + q * suc n ∎ )
      same-quot : (r ≡ d) × (q ≡ toℕ b)
      same-quot = addMul-lemma q (toℕ b) n r d ( sym eq' )
      pf₁ = (toℕ-injective (trans (toℕ-fromℕ≤ p) (proj₂ same-quot)))

  abstract
    fwd-iso : {m n : ℕ} → (Fin m × Fin n) ≃ Fin (m * n)
    fwd-iso {m} {n} = fwd , qinv bwd (fwd∘bwd~id {m}) (bwd∘fwd~id {m})

  -- convenient aliases
  ×≃* : {m n : ℕ} → (Fin m × Fin n) ≃ Fin (m * n)
  ×≃* = fwd-iso

  *≃× : {m n : ℕ} → Fin (m * n) ≃ (Fin m × Fin n)
  *≃× = sym≃ ×≃*
  
------------------------------------------------------------------------------
