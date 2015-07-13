{-# OPTIONS --without-K #-}

module LeqLemmas where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _≤?_; z≤n; s≤s;
    module ≤-Reasoning)
open import Data.Nat.Properties.Simple
  using (*-comm; +-right-identity; +-comm; +-assoc)
open import Data.Nat.Properties
  using (cancel-+-left-≤; n≤m+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)
open import Relation.Binary using (Decidable)
open import Relation.Binary.Core using (Transitive; _⇒_)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; raise; inject≤)
open import Data.Fin.Properties using (bounded; to-from)

------------------------------------------------------------------------------
-- Proofs and definitions about ≤ on natural numbers

_<?_ : Decidable _<_
i <? j = suc i ≤? j

-- buried in Data.Nat

refl′ : _≡_ ⇒ _≤_
refl′ {0} refl = z≤n
refl′ {suc m} refl = s≤s (refl′ refl)

trans< : Transitive _<_
trans< (s≤s z≤n) (s≤s _) = s≤s z≤n
trans< (s≤s (s≤s i≤j)) (s≤s sj<k) = s≤s (trans< (s≤s i≤j) sj<k) 

trans≤ : Transitive _≤_
trans≤ z≤n x = z≤n
trans≤ (s≤s m≤n) (s≤s n≤o) = s≤s (trans≤ m≤n n≤o)

i*1≡i : (i : ℕ) → i * 1 ≡ i
i*1≡i i = begin (i * 1
                   ≡⟨ *-comm i 1 ⟩ 
                 1 * i
                   ≡⟨ refl ⟩ 
                 i + 0
                   ≡⟨ +-right-identity i ⟩
                 i ∎)
  where open ≡-Reasoning

i≤i : (i : ℕ) → i ≤ i
i≤i 0 = z≤n
i≤i (suc i) = s≤s (i≤i i)

i≤si : (i : ℕ) → i ≤ suc i
i≤si 0       = z≤n
i≤si (suc i) = s≤s (i≤si i)

i≤j+i : ∀ {i j} → i ≤ j + i
i≤j+i {i} {0} = i≤i i
i≤j+i {i} {suc j} = 
  begin (i 
           ≤⟨ i≤j+i {i} {j} ⟩
         j + i 
           ≤⟨ i≤si (j + i) ⟩
         suc j + i ∎)
  where open ≤-Reasoning

cong+r≤ : ∀ {i j} → i ≤ j → (k : ℕ) → i + k ≤ j + k
cong+r≤ {0}     {j}     z≤n       k = n≤m+n j k
cong+r≤ {suc i} {0}     ()        k -- absurd
cong+r≤ {suc i} {suc j} (s≤s i≤j) k = s≤s (cong+r≤ {i} {j} i≤j k)

cong+l≤ : ∀ {i j} → i ≤ j → (k : ℕ) → k + i ≤ k + j
cong+l≤ {i} {j} i≤j k =
  begin (k + i
           ≡⟨ +-comm k i ⟩ 
         i + k
           ≤⟨ cong+r≤ i≤j k ⟩ 
         j + k
           ≡⟨ +-comm j k ⟩ 
         k + j ∎)
  where open ≤-Reasoning

cong*r≤ : ∀ {i j} → i ≤ j → (k : ℕ) → i * k ≤ j * k
cong*r≤ {0}     {j}     z≤n       k = z≤n
cong*r≤ {suc i} {0}     ()        k -- absurd
cong*r≤ {suc i} {suc j} (s≤s i≤j) k = cong+l≤ (cong*r≤ i≤j k) k 

sinj : ∀ {i j} → suc i ≡ suc j → i ≡ j
sinj = cong (λ { 0 → 0 ; (suc x) → x })

sinj≤ : ∀ {i j} → suc i ≤ suc j → i ≤ j
sinj≤ {0}     {j}     _        = z≤n
sinj≤ {suc i} {0}     (s≤s ()) -- absurd
sinj≤ {suc i} {suc j} (s≤s p)  = p

i*n+n≤sucm*n : ∀ {m n} → (i : Fin (suc m)) → toℕ i * n + n ≤ suc m * n
i*n+n≤sucm*n {0} {n} zero =
  begin (n
           ≡⟨ sym (+-right-identity n) ⟩
         n + 0
           ≤⟨ i≤i (n + 0) ⟩ 
         n + 0 ∎)
  where open ≤-Reasoning
i*n+n≤sucm*n {0} {n} (suc ())
i*n+n≤sucm*n {suc m} {n} i = 
  begin (toℕ i * n + n
           ≡⟨ +-comm (toℕ i * n) n ⟩
         n + toℕ i * n
           ≡⟨ refl ⟩
         suc (toℕ i) * n
           ≤⟨ cong*r≤ (bounded i) n ⟩ 
         suc (suc m) * n ∎)
  where open ≤-Reasoning

i*n+k≤m*n : ∀ {m n} → (i : Fin m) → (k : Fin n) → 
            (suc (toℕ i * n + toℕ k) ≤ m * n)
i*n+k≤m*n {0} {_} () _
i*n+k≤m*n {_} {0} _ ()
i*n+k≤m*n {suc m} {suc n} i k = 
  begin (suc (toℕ i * suc n + toℕ k) 
           ≡⟨  cong suc (+-comm (toℕ i * suc n) (toℕ k))  ⟩
         suc (toℕ k + toℕ i * suc n)
           ≡⟨ refl ⟩
         suc (toℕ k) + (toℕ i * suc n)
           ≤⟨ cong+r≤ (bounded k) (toℕ i * suc n) ⟩ 
         suc n + (toℕ i * suc n)
           ≤⟨ cong+l≤ (cong*r≤ (sinj≤ (bounded i)) (suc n)) (suc n) ⟩
         suc n + (m * suc n) 
           ≡⟨ refl ⟩
         suc m * suc n ∎)
  where open ≤-Reasoning

bounded' : (m : ℕ) → (j : Fin (suc m)) → (toℕ j ≤ m)
bounded' m j with bounded j
... | s≤s pr = pr

simplify-≤ : {m n m' n' : ℕ} → (m ≤ n) → (m ≡ m') → (n ≡ n') → (m' ≤ n') 
simplify-≤ leq refl refl = leq

cancel-Fin : ∀ (n y z : ℕ) → ((x : Fin (suc n)) → toℕ x + y ≤ n + z) → y ≤ z
cancel-Fin 0 y z pf = pf zero
cancel-Fin (suc n) y z pf =
  cancel-+-left-≤ n (trans≤ leq (sinj≤ (pf (fromℕ (suc n)))))
  where leq : n + y ≤ toℕ (fromℕ n) + y
        leq = begin (n + y
                       ≡⟨ cong (λ x → x + y) (sym (to-from n)) ⟩
                     toℕ (fromℕ n) + y ∎)
              where open ≤-Reasoning

≤-proof-irrelevance : {m n : ℕ} → (p q : m ≤ n) → p ≡ q
≤-proof-irrelevance z≤n z≤n = refl
≤-proof-irrelevance (s≤s p) (s≤s q) = cong s≤s (≤-proof-irrelevance p q)

raise-suc' : (n a b n+a : ℕ) (n+a≡ : n+a ≡ n + a) → 
  (leq : suc a ≤ b) → 
  (leq' : suc n+a ≤ n + b) → 
  raise n (inject≤ (fromℕ a) leq) ≡ inject≤ (fromℕ n+a) leq'
raise-suc' 0 a b .a refl leq leq' =
  cong (inject≤ (fromℕ a)) (≤-proof-irrelevance leq leq')
raise-suc' (suc n) a b .(suc (n + a)) refl leq (s≤s leq') =
  cong suc (raise-suc' n a b (n + a) refl leq leq') 

raise-suc : (m n : ℕ) (j : Fin (suc m)) (d : Fin (suc n))
  (leq : suc (toℕ j * suc n + toℕ d) ≤ suc m * suc n) → 
  (leq' : suc (toℕ (suc j) * suc n + toℕ d) ≤ suc (suc m) * suc n) →
  raise (suc n) (inject≤ (fromℕ (toℕ j * suc n + toℕ d)) leq) ≡
  inject≤ (fromℕ (toℕ (suc j) * suc n + toℕ d)) leq'
raise-suc m n j d leq leq' =
  raise-suc'
    (suc n)
    (toℕ j * suc n + toℕ d)
    (suc m * suc n)
    (toℕ (suc j) * suc n + toℕ d)
    (begin (toℕ (suc j) * suc n + toℕ d
              ≡⟨ refl ⟩
            (suc n + toℕ j * suc n) + toℕ d
              ≡⟨ +-assoc (suc n) (toℕ j * suc n) (toℕ d) ⟩
            suc n + (toℕ j * suc n + toℕ d) ∎))
    leq
    leq'
  where open ≡-Reasoning

{-
-- buried in Data.Nat
refl′ : _≡_ ⇒ _≤_
refl′ {0} refl = z≤n
refl′ {suc m} refl = s≤s (refl′ refl)

trans< : Transitive _<_
trans< (s≤s z≤n) (s≤s _) = s≤s z≤n
trans< (s≤s (s≤s i≤j)) (s≤s sj<k) = s≤s (trans< (s≤s i≤j) sj<k) 

trans≤ : Transitive _≤_
trans≤ z≤n x = z≤n
trans≤ (s≤s m≤n) (s≤s n≤o) = s≤s (trans≤ m≤n n≤o)

i*1≡i : (i : ℕ) → i * 1 ≡ i
i*1≡i i = begin (i * 1
                   ≡⟨ *-comm i 1 ⟩ 
                 1 * i
                   ≡⟨ refl ⟩ 
                 i + 0
                   ≡⟨ +-right-identity i ⟩
                 i ∎)
  where open ≡-Reasoning

i≤i : (i : ℕ) → i ≤ i
i≤i 0 = z≤n
i≤i (suc i) = s≤s (i≤i i)

i≤si : (i : ℕ) → i ≤ suc i
i≤si 0       = z≤n
i≤si (suc i) = s≤s (i≤si i)

i≤j+i : ∀ {i j} → i ≤ j + i
i≤j+i {i} {0} = i≤i i
i≤j+i {i} {suc j} = 
  begin (i 
           ≤⟨ i≤j+i {i} {j} ⟩
         j + i 
           ≤⟨ i≤si (j + i) ⟩
         suc j + i ∎)
  where open ≤-Reasoning

sinj : ∀ {i j} → suc i ≡ suc j → i ≡ j
sinj = cong (λ { 0 → 0 ; (suc x) → x })

i*n+n≤sucm*n : ∀ {m n} → (i : Fin (suc m)) → toℕ i * n + n ≤ suc m * n
i*n+n≤sucm*n {0} {n} zero =
  begin (n
           ≡⟨ sym (+-right-identity n) ⟩
         n + 0
           ≤⟨ i≤i (n + 0) ⟩ 
         n + 0 ∎)
  where open ≤-Reasoning
i*n+n≤sucm*n {0} {n} (suc ())
i*n+n≤sucm*n {suc m} {n} i = 
  begin (toℕ i * n + n
           ≡⟨ +-comm (toℕ i * n) n ⟩
         n + toℕ i * n
           ≡⟨ refl ⟩
         suc (toℕ i) * n
           ≤⟨ cong*r≤ (bounded i) n ⟩ 
         suc (suc m) * n ∎)
  where open ≤-Reasoning

i*n+k≤m*n : ∀ {m n} → (i : Fin m) → (k : Fin n) → 
            (suc (toℕ i * n + toℕ k) ≤ m * n)
i*n+k≤m*n {0} {_} () _
i*n+k≤m*n {_} {0} _ ()
i*n+k≤m*n {suc m} {suc n} i k = 
  begin (suc (toℕ i * suc n + toℕ k) 
           ≡⟨  cong suc (+-comm (toℕ i * suc n) (toℕ k))  ⟩
         suc (toℕ k + toℕ i * suc n)
           ≡⟨ refl ⟩
         suc (toℕ k) + (toℕ i * suc n)
           ≤⟨ cong+r≤ (bounded k) (toℕ i * suc n) ⟩ 
         suc n + (toℕ i * suc n)
           ≤⟨ cong+l≤ (cong*r≤ (sinj≤ (bounded i)) (suc n)) (suc n) ⟩
         suc n + (m * suc n) 
           ≡⟨ refl ⟩
         suc m * suc n ∎)
  where open ≤-Reasoning

bounded' : (m : ℕ) → (j : Fin (suc m)) → (toℕ j ≤ m)
bounded' m j with bounded j
... | s≤s pr = pr

simplify-≤ : {m n m' n' : ℕ} → (m ≤ n) → (m ≡ m') → (n ≡ n') → (m' ≤ n') 
simplify-≤ leq refl refl = leq

cancel-Fin : ∀ (n y z : ℕ) → ((x : Fin (suc n)) → toℕ x + y ≤ n + z) → y ≤ z
cancel-Fin 0 y z pf = pf zero
cancel-Fin (suc n) y z pf =
  cancel-+-left-≤ n (trans≤ leq (sinj≤ (pf (fromℕ (suc n)))))
  where leq : n + y ≤ toℕ (fromℕ n) + y
        leq = begin (n + y
                       ≡⟨ cong (λ x → x + y) (sym (to-from n)) ⟩
                     toℕ (fromℕ n) + y ∎)
              where open ≤-Reasoning

≤-proof-irrelevance : {m n : ℕ} → (p q : m ≤ n) → p ≡ q
≤-proof-irrelevance z≤n z≤n = refl
≤-proof-irrelevance (s≤s p) (s≤s q) = cong s≤s (≤-proof-irrelevance p q)


raise-suc' : (n a b n+a : ℕ) (n+a≡ : n+a ≡ n + a) → 
  (leq : suc a ≤ b) → 
  (leq' : suc n+a ≤ n + b) → 
  raise n (inject≤ (fromℕ a) leq) ≡ inject≤ (fromℕ n+a) leq'
raise-suc' 0 a b .a refl leq leq' =
  cong (inject≤ (fromℕ a)) (≤-proof-irrelevance leq leq')
raise-suc' (suc n) a b .(suc (n + a)) refl leq (s≤s leq') =
  cong suc (raise-suc' n a b (n + a) refl leq leq') 

raise-suc : (m n : ℕ) (j : Fin (suc m)) (d : Fin (suc n))
  (leq : suc (toℕ j * suc n + toℕ d) ≤ suc m * suc n) → 
  (leq' : suc (toℕ (suc j) * suc n + toℕ d) ≤ suc (suc m) * suc n) →
  raise (suc n) (inject≤ (fromℕ (toℕ j * suc n + toℕ d)) leq) ≡
  inject≤ (fromℕ (toℕ (suc j) * suc n + toℕ d)) leq'
raise-suc m n j d leq leq' =
  raise-suc'
    (suc n)
    (toℕ j * suc n + toℕ d)
    (suc m * suc n)
    (toℕ (suc j) * suc n + toℕ d)
    (begin (toℕ (suc j) * suc n + toℕ d
              ≡⟨ refl ⟩
            (suc n + toℕ j * suc n) + toℕ d
              ≡⟨ +-assoc (suc n) (toℕ j * suc n) (toℕ d) ⟩
            suc n + (toℕ j * suc n + toℕ d) ∎))
    leq
    leq'
  where open ≡-Reasoning
-}
