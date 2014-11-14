{-# OPTIONS --without-K #-}

module Cauchy where

-- Definitions for permutations in the Cauchy representation

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)
open import Data.Nat.DivMod using (_mod_)
open import Relation.Binary using (Rel; Decidable; Setoid)
open import Relation.Binary.Core using (Transitive)

open import Data.String using (String)
  renaming (_++_ to _++S_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  z≤n; s≤s; _≟_; _≤?_; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤; _ℕ-_; _≺_; reduce≥; 
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties using (bounded; inject+-lemma)
open import Data.Vec.Properties 
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin; tabulate-∘; 
         tabulate-allFin; allFin-map; lookup-++-inject+; lookup-++-≥)
open import Data.Product using (Σ)

open import Data.List 
  using (List; []; _∷_; _∷ʳ_; foldl; replicate; reverse; downFrom; 
         concatMap; gfilter; initLast; InitLast; _∷ʳ'_) 
  renaming (_++_ to _++L_; map to mapL; concat to concatL; zip to zipL)
open import Data.List.NonEmpty 
  using (List⁺; [_]; _∷⁺_; head; last; _⁺++_)
  renaming (toList to nonEmptyListtoList; _∷ʳ_ to _n∷ʳ_; tail to ntail)
open import Data.List.Any using (Any; here; there; any; module Membership)
open import Data.Maybe using (Maybe; nothing; just; maybe′)
open import Data.Vec 
  using (Vec; tabulate; []; _∷_; tail; lookup; zip; zipWith; splitAt;
         _[_]≔_; allFin; toList)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import Function using (id; _∘_; _$_)

open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------------
-- Proofs and definitions about natural numbers

_<?_ : Decidable _<_
i <? j = suc i ≤? j

trans< : Transitive _<_
trans< (s≤s z≤n) (s≤s _) = s≤s z≤n
trans< (s≤s (s≤s i≤j)) (s≤s sj<k) = s≤s (trans< (s≤s i≤j) sj<k) 

i*1≡i : (i : ℕ) → (i * 1 ≡ i)
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
cong+r≤ {0}     {j}     z≤n       k = i≤j+i {k} {j}
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

sinj≤ : ∀ {i j} → suc i ≤ suc j → i ≤ j
sinj≤ {0}     {j}     _        = z≤n
sinj≤ {suc i} {0}     (s≤s ()) -- absurd
sinj≤ {suc i} {suc j} (s≤s p)  = p

i*n+n≤sucm*n : ∀ {m n} → (i : Fin (suc m)) → (toℕ i * n + n ≤ suc m * n)
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

------------------------------------------------------------------------------
-- Semantic representations of permutations

-- One possibility of course is to represent them as functions but
-- this is a poor representation and eventually requires function
-- extensionality. 

-- Representation III
-- This is the 2 line Cauchy representation. The first line is in
-- canonical order and implicit in the indices of the vector

Cauchy : ℕ → Set
Cauchy n = Vec (Fin n) n

-- What JC thinks will actually work
-- we need injectivity.  surjectivity ought to be provable.

Permutation : ℕ → Set
Permutation n = Σ (Cauchy n) (λ v → ∀ {i j} → lookup i v ≡ lookup j v → i ≡ j)

showCauchy : ∀ {n} → Cauchy n → Vec String n
showCauchy {n} = 
  zipWith (λ i j → show (toℕ i) ++S " → " ++S show (toℕ j)) (allFin n)

-- Ex:

cauchyEx1 cauchyEx2 : Cauchy 6
-- cauchyEx1 (0 1 2 3 4 5)
--           (2 0 4 3 1 5)
cauchyEx1 = 
  (inject+ 3 (fromℕ 2)) ∷
  (inject+ 5 (fromℕ 0)) ∷
  (inject+ 1 (fromℕ 4)) ∷
  (inject+ 2 (fromℕ 3)) ∷
  (inject+ 4 (fromℕ 1)) ∷
  (inject+ 0 (fromℕ 5)) ∷ []
-- cauchyEx2 (0 1 2 3 4 5)
--           (3 2 1 0 5 4)
cauchyEx2 = 
  (inject+ 2 (fromℕ 3)) ∷
  (inject+ 3 (fromℕ 2)) ∷
  (inject+ 4 (fromℕ 1)) ∷
  (inject+ 5 (fromℕ 0)) ∷
  (inject+ 0 (fromℕ 5)) ∷
  (inject+ 1 (fromℕ 4)) ∷ []

------------------------------------------------------------------------------
-- Elementary permutations in the Cauchy representation 

idcauchy : (n : ℕ) → Cauchy n
idcauchy = allFin 

idperm : (n : ℕ) → Permutation n
idperm n = (idcauchy n , λ {i} {j} p → 
  (begin i 
           ≡⟨ sym (lookup∘tabulate id i) ⟩ 
         lookup i (idcauchy n)
           ≡⟨ p ⟩ 
         lookup j (idcauchy n)
           ≡⟨ lookup∘tabulate id j ⟩ 
         j ∎))
  where open ≡-Reasoning

-- proofs about sequenced permutations
-- Sequential composition

scompcauchy : ∀ {n} → Cauchy n → Cauchy n → Cauchy n
scompcauchy {n} perm₁ perm₂ = 
  tabulate (λ i → lookup (lookup i perm₁) perm₂)

-- this was not entirely straightforward!

scompperm : ∀ {n} → Permutation n → Permutation n → Permutation n
scompperm {n} (p₁ , i₁) (p₂ , i₂) =
  (scompcauchy p₁ p₂ , λ {i} {j} p → 
    let g = λ i → lookup (lookup i p₁) p₂ in
    let q = trans (sym (lookup∘tabulate g i)) (trans p (lookup∘tabulate g j)) in
    i₁ (i₂ q))

-- swap the first m elements with the last n elements
-- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
-- ==> 
-- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

swap+cauchy : (m n : ℕ) → Cauchy (m + n)
swap+cauchy m n = 
  subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
    (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))

-- Parallel additive composition 
-- append both permutations but adjust the indices in the second
-- permutation by the size of the first type so that it acts on the
-- second part of the vector

pcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m + n)
pcompcauchy {m} {n} α β = mapV (inject+ n) α ++V mapV (raise m) β

-- Tensor multiplicative composition
-- Transpositions in α correspond to swapping entire rows
-- Transpositions in β correspond to swapping entire columns

tcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m * n)
tcompcauchy {m} {n} α β = 
  concatV 
    (mapV 
      (λ b → 
         mapV (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)) β)
      α)

-- this is a non-dependently typed version of tensor product of vectors.

tensorvec : ∀ {m n} {A B C : Set} →
            (A → B → C) → Vec A m → Vec B n → Vec C (m * n)
tensorvec {0} _ [] _ = []
tensorvec {suc m} {n} {C = C} f (x ∷ α) β =
  subst
    (λ i → Vec C (n + m * n))
    (+-*-suc m n)
    (mapV (f x) β ++V tensorvec f α β)

-- this is a better template

tensorvec' : ∀ {A B C : ℕ → Set} → (∀ {m n} → A m → B n → C (m * n)) →
    (∀ {m} → (n : ℕ) → C m → C (n + m)) → 
    ∀ {m n j} →  Vec (A m) j → Vec (B n) n → Vec (C (m * n)) (j * n)
tensorvec' _ _ {j = 0} [] _ = []
tensorvec' {A} {B} {C} f shift {m} {n} {suc j} (x ∷ α) β =
  subst
    (λ i → Vec (C (m * n)) (n + j * n))
    (+-*-suc j n) 
    (mapV (f x) β ++V (tensorvec' {A} {B} {C} f shift α β))

-- raise d by b*n and inject in m*n

raise∘inject : ∀ {m n} → (b : Fin m) (d : Fin n) → Fin (m * n)
raise∘inject {0} {n} () d
raise∘inject {suc m} {n} b d =
  inject≤ (raise (toℕ b * n) d) (i*n+n≤sucm*n {m} {n} b)

tcompcauchy' : ∀ {i m n} → Vec (Fin m) i → Cauchy n → Vec (Fin (m * n)) (i * n)
tcompcauchy' {0} {m} {n} [] β = []
tcompcauchy' {suc i} {m} {n} (b ∷ α) β = 
  mapV (raise∘inject {m} {n} b) β ++V tcompcauchy' {i} {m} {n} α β
    
tcompcauchy2 : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m * n)
tcompcauchy2 = tcompcauchy'

-- swap⋆ 
-- 
-- This is essentially the classical problem of in-place matrix transpose:
-- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
-- Given m and n, the desired permutation in Cauchy representation is:
-- P(i) = m*n-1 if i=m*n-1
--      = m*i mod m*n-1 otherwise

transposeIndex : (m n : ℕ) → 
                 (b : Fin (suc (suc m))) → (d : Fin (suc (suc n))) → 
                 Fin (suc (suc m) * suc (suc n))
transposeIndex m n b d with toℕ b * suc (suc n) + toℕ d
transposeIndex m n b d | i with suc i ≟ suc (suc m) * suc (suc n)
transposeIndex m n b d | i | yes _ = 
  fromℕ (suc (n + suc (suc (n + m * suc (suc n))))) 
transposeIndex m n b d | i | no _ = 
  inject≤ 
    ((i * (suc (suc m))) mod (suc (n + suc (suc (n + m * suc (suc n))))))
    (i≤si (suc (n + suc (suc (n + m * suc (suc n))))))

swap⋆cauchy : (m n : ℕ) → Cauchy (m * n)
swap⋆cauchy 0 n = []
swap⋆cauchy 1 n = subst Cauchy (sym (+-right-identity n)) (idcauchy n)
swap⋆cauchy (suc (suc m)) 0 = 
  subst Cauchy (sym (*-right-zero (suc (suc m)))) []
swap⋆cauchy (suc (suc m)) 1 = 
  subst Cauchy (sym (i*1≡i (suc (suc m)))) (idcauchy (suc (suc m)))
swap⋆cauchy (suc (suc m)) (suc (suc n)) = 
  concatV 
    (mapV 
      (λ b → mapV (λ d → transposeIndex m n b d) (allFin (suc (suc n))))
      (allFin (suc (suc m))))

------------------------------------------------------------------------------
