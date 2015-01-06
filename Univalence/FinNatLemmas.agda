{-# OPTIONS --without-K #-}

module FinNatLemmas where

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; cong; module ≡-Reasoning)
open import Data.Nat.Properties
  using (cancel-+-left; n∸n≡0; +-∸-assoc; m+n∸n≡m; 1+n≰n; m≤m+n;
         n≤m+n; n≤1+n; cancel-*-right-≤; ≰⇒>; ¬i+1+j≤i; cancel-+-left-≤)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)
-- open import Relation.Binary using (Rel; Decidable; Setoid)
-- open import Relation.Binary.Core using (Transitive; _⇒_)

open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  z≤n; s≤s; _≟_; _≤?_; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤; _ℕ-_; _≺_; reduce≥; 
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties
  using (bounded; inject+-lemma; to-from; toℕ-injective; toℕ-raise; toℕ-fromℕ≤)

-- open import Function using (id; _∘_; _$_; _∋_)

------------------------------------------------------------------------------
-- Fin and Nat lemmas

toℕ-fin : (m n : ℕ) → (eq : m ≡ n) (fin : Fin m) →
  toℕ (subst Fin eq fin) ≡ toℕ fin
toℕ-fin m .m refl fin = refl

∸≡ : (m n : ℕ) (i j : Fin (m + n)) (i≥ : m ≤ toℕ i) (j≥ : m ≤ toℕ j) →
  toℕ i ∸ m ≡ toℕ j ∸ m → i ≡ j
∸≡ m n i j i≥ j≥ p = toℕ-injective pr
  where pr = begin (toℕ i
                    ≡⟨ sym (m+n∸n≡m (toℕ i) m) ⟩
                    (toℕ i + m) ∸ m
                    ≡⟨ cong (λ x → x ∸ m) (+-comm (toℕ i) m) ⟩ 
                    (m + toℕ i) ∸ m
                    ≡⟨ +-∸-assoc m i≥ ⟩
                    m + (toℕ i ∸ m)
                    ≡⟨ cong (λ x → m + x) p ⟩
                    m + (toℕ j ∸ m)
                    ≡⟨ sym (+-∸-assoc m j≥) ⟩
                    (m + toℕ j) ∸ m
                    ≡⟨ cong (λ x → x ∸ m) (+-comm m (toℕ j)) ⟩
                    (toℕ j + m) ∸ m
                    ≡⟨ m+n∸n≡m (toℕ j) m ⟩
                    toℕ j ∎)
             where open ≡-Reasoning

cancel-right∸ : (m n k : ℕ) (k≤m : k ≤ m) (k≤n : k ≤ n) →
  (m ∸ k ≡ n ∸ k) → m ≡ n
cancel-right∸ m n k k≤m k≤n mk≡nk =
  begin (m
         ≡⟨ sym (m+n∸n≡m m k) ⟩
         (m + k) ∸ k
         ≡⟨ cong (λ x → x ∸ k) (+-comm m k) ⟩
         (k + m) ∸ k
         ≡⟨ +-∸-assoc k k≤m ⟩
         k + (m ∸ k)
         ≡⟨ cong (λ x → k + x) mk≡nk ⟩
         k + (n ∸ k)
         ≡⟨ sym (+-∸-assoc k k≤n) ⟩
         (k + n) ∸ k
         ≡⟨ cong (λ x → x ∸ k) (+-comm k n) ⟩
         (n + k) ∸ k
         ≡⟨ m+n∸n≡m n k ⟩
         n ∎)
  where open ≡-Reasoning

raise< : (m n : ℕ) (i : Fin (m + n)) (i< : toℕ i < m) → 
         toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<))) ≡ n + toℕ i
raise< m n i i< =
  begin (toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<)))
         ≡⟨ toℕ-fin (n + m) (m + n) (+-comm n m) (raise n (fromℕ≤ i<)) ⟩
         toℕ (raise n (fromℕ≤ i<))
         ≡⟨ toℕ-raise n (fromℕ≤ i<) ⟩
         n + toℕ (fromℕ≤ i<)
         ≡⟨ cong (λ x → n + x) (toℕ-fromℕ≤ i<) ⟩ 
         n + toℕ i ∎)
  where open ≡-Reasoning

toℕ-reduce≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) →
               toℕ (reduce≥ i i≥) ≡ toℕ i ∸ m
toℕ-reduce≥ 0 n i _ = refl 
toℕ-reduce≥ (suc m) n zero ()
toℕ-reduce≥ (suc m) n (suc i) (s≤s i≥) = toℕ-reduce≥ m n i i≥

inject≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) →
        toℕ (subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥))) ≡ toℕ i ∸ m
inject≥ m n i i≥ =
  begin (toℕ (subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥)))
         ≡⟨ toℕ-fin (n + m) (m + n) (+-comm n m) (inject+ m (reduce≥ i i≥)) ⟩
         toℕ (inject+ m (reduce≥ i i≥))
         ≡⟨ sym (inject+-lemma m (reduce≥ i i≥)) ⟩
         toℕ (reduce≥ i i≥) 
         ≡⟨ toℕ-reduce≥ m n i i≥ ⟩ 
         toℕ i ∸ m ∎)
  where open ≡-Reasoning

fromℕ≤-inj : (m n : ℕ) (i j : Fin n) (i< : toℕ i < m) (j< : toℕ j < m) → 
  fromℕ≤ i< ≡ fromℕ≤ j< → i ≡ j
fromℕ≤-inj m n i j i< j< fi≡fj =
  toℕ-injective
    (trans (sym (toℕ-fromℕ≤ i<)) (trans (cong toℕ fi≡fj) (toℕ-fromℕ≤ j<)))

reduce≥-inj : (m n : ℕ) (i j : Fin (m + n)) (i≥ : m ≤ toℕ i) (j≥ : m ≤ toℕ j) →
  reduce≥ i i≥ ≡ reduce≥ j j≥ → i ≡ j
reduce≥-inj m n i j i≥ j≥ ri≡rj =
  toℕ-injective
    (cancel-right∸ (toℕ i) (toℕ j) m i≥ j≥
      (trans (sym (toℕ-reduce≥ m n i i≥))
      (trans (cong toℕ ri≡rj) (toℕ-reduce≥ m n j j≥))))

------------------------------------------------------------------------------
