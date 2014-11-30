{-# OPTIONS --without-K #-}

module CauchyProofsT where

-- Proofs about permutations defined in module Cauchy (multiplicative)

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Data.Nat.Properties
  using (m≤m+n; n≤m+n; n≤1+n; cancel-*-right-≤; ≰⇒>; ¬i+1+j≤i)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)
open import Data.Nat.DivMod using (DivMod; result; _divMod_; _div_; _mod_)
open import Relation.Binary using (Rel; Decidable; Setoid)
open import Relation.Binary.Core using (Transitive)

open import Data.String using (String)
  renaming (_++_ to _++S_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  _≥_; z≤n; s≤s; _≟_; _≤?_; ≤-pred; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤; _ℕ-_; _≺_; reduce≥; 
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties
  using (bounded; inject+-lemma; to-from; toℕ-injective; inject≤-lemma; toℕ-fromℕ≤)
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
open import Function using (id; _∘_; _$_; _∋_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Proofs
open import Cauchy
open import CauchyProofs

------------------------------------------------------------------------------
-- Proofs about multiplicative permutations

concat-nil : ∀ {m} → 
  concatV (tabulate {m} (λ b → [])) ≡ subst Cauchy (sym (*-right-zero m)) []
concat-nil {0} = refl
concat-nil {suc m} = concat-nil {m}

empty-vec : ∀ {m} → (eq : m ≡ 0) → allFin m ≡ subst Cauchy (sym eq) []
empty-vec {0} refl = refl 
empty-vec {suc m} ()

inj-lemma' : (m n : ℕ) (d : Fin n) (leq : suc (toℕ d) ≤ n + m) →
  inject+ m d ≡ inject≤ (fromℕ (toℕ d)) leq
inj-lemma' 0 0 () leq
inj-lemma' 0 (suc n) zero (s≤s leq) = refl
inj-lemma' 0 (suc n) (suc d) (s≤s leq) = cong suc (inj-lemma' 0 n d leq)
inj-lemma' (suc m) 0 () leq
inj-lemma' (suc m) (suc n) zero (s≤s leq) = refl
inj-lemma' (suc m) (suc n) (suc d) (s≤s leq) =
  cong suc (inj-lemma' (suc m) n d leq) 

inj-lemma : (m n : ℕ) (d : Fin n) (leq : suc (toℕ d) ≤ suc m * n) →
  inject+ (m * n) d ≡ inject≤ (fromℕ (toℕ d)) leq
inj-lemma 0 0 () leq
inj-lemma 0 (suc n) zero (s≤s leq) = refl
inj-lemma 0 (suc n) (suc d) (s≤s leq) = cong suc (inj-lemma 0 n d leq)
inj-lemma (suc m) 0 () leq
inj-lemma (suc m) (suc n) zero (s≤s leq) = refl
inj-lemma (suc m) (suc n) (suc d) (s≤s leq) =
  cong suc (inj-lemma' (suc m * suc n) n d leq) 

map-inj-lemma : (m n : ℕ) →
  (mapV (inject+ (m * suc n)) (allFin (suc n))) ≡ 
  (mapV
    (λ d → inject≤
             (fromℕ (toℕ d))
             (i*n+k≤m*n {suc m} {suc n} zero d))
    (allFin (suc n)))
map-inj-lemma m n = 
  begin (mapV (inject+ (m * suc n)) (tabulate {suc n} id)
           ≡⟨ sym (tabulate-∘ (inject+ (m * suc n)) id) ⟩
         tabulate {suc n} (λ d → inject+ (m * suc n) d)
           ≡⟨ finext
                 (λ d → inject+ (m * suc n) d)
                 (λ d → inject≤
                          (fromℕ (toℕ d))
                          (i*n+k≤m*n {suc m} {suc n} zero d))
                 (λ d → inj-lemma m (suc n) d
                          (i*n+k≤m*n {suc m} {suc n} zero d)) ⟩ 
         tabulate {suc n}
           (λ d → inject≤
                    (fromℕ (toℕ d))
                    (i*n+k≤m*n {suc m} {suc n} zero d))
           ≡⟨ tabulate-∘
                (λ d → inject≤
                         (fromℕ (toℕ d))
                         (i*n+k≤m*n {suc m} {suc n} zero d))
                id ⟩ 
         mapV
           (λ d → inject≤
                    (fromℕ (toℕ d))
                    (i*n+k≤m*n {suc m} {suc n} zero d))
           (allFin (suc n)) ∎)
  where open ≡-Reasoning

map-raise-suc : (m n : ℕ) (j : Fin (suc m)) → 
  mapV (λ d → raise 
                (suc n) 
                (inject≤
                  (fromℕ (toℕ j * suc n + toℕ d))
                   (i*n+k≤m*n j d)))
       (idcauchy (suc n)) ≡
  mapV (λ d → inject≤
                (fromℕ (toℕ (suc j) * suc n + toℕ d))
                (i*n+k≤m*n (suc j) d))
       (idcauchy (suc n))
map-raise-suc m n j =
  begin (mapV
          (λ d → raise 
                   (suc n) 
                   (inject≤
                     (fromℕ (toℕ j * suc n + toℕ d))
                     (i*n+k≤m*n j d)))
          (idcauchy (suc n)) 
          ≡⟨ (sym (tabulate-∘ _ id)) ⟩ 
         tabulate {suc n}
          (λ d → raise 
                   (suc n) 
                   (inject≤
                     (fromℕ (toℕ j * suc n + toℕ d))
                     (i*n+k≤m*n j d)))
          ≡⟨ finext _ _
             (λ d → raise-suc m n j d (i*n+k≤m*n j d) (i*n+k≤m*n (suc j) d)) ⟩
         tabulate {suc n} 
           (λ d → inject≤
                    (fromℕ (toℕ (suc j) * suc n + toℕ d))
                    (i*n+k≤m*n (suc j) d))
          ≡⟨ tabulate-∘ _ id ⟩ 
         mapV
           (λ d → inject≤
                    (fromℕ (toℕ (suc j) * suc n + toℕ d))
                    (i*n+k≤m*n (suc j) d))
           (idcauchy (suc n)) ∎)
  where open ≡-Reasoning

-- what should this be named?

lemma3 : (n m : ℕ) → (j : Fin m) →
  mapV (raise (suc n))
    (mapV (λ d → inject≤
                 (fromℕ (toℕ j * suc n + toℕ d))
                 (i*n+k≤m*n j d))
          (idcauchy (suc n)))
  ≡
  mapV (λ d → inject≤
              (fromℕ (toℕ (suc j) * suc n + toℕ d))
              (i*n+k≤m*n (suc j) d))
       (idcauchy (suc n))
lemma3 n 0 ()
lemma3 n (suc m) j = 
  begin (
  _
    ≡⟨ sym (map-∘ (raise (suc n)) (λ d → inject≤
                 (fromℕ (toℕ j * suc n + toℕ d))
                 (i*n+k≤m*n j d)) (idcauchy (suc n))) ⟩
  mapV (λ d → raise (suc n) (inject≤
                 (fromℕ (toℕ j * suc n + toℕ d))
                 (i*n+k≤m*n j d))) (idcauchy (suc n))
    ≡⟨ map-raise-suc m n j ⟩ 
  _ ∎)
  where open ≡-Reasoning
  
map-raise-lemma : (m n : ℕ) → 
  mapV
    (λ b → mapV
             (raise (suc n))
             (mapV
               (λ d → inject≤
                        (fromℕ (toℕ b * suc n + toℕ d))
                        (i*n+k≤m*n b d))
               (idcauchy (suc n))))
    (idcauchy m) ≡
  mapV 
    (λ b → mapV
             (λ d → inject≤
                      (fromℕ (toℕ b * suc n + toℕ d))
                      (i*n+k≤m*n b d))
             (idcauchy (suc n)))
    (tabulate {m} suc)
map-raise-lemma 0 n = refl
map-raise-lemma (suc m) n = 
  begin (
  mapV (λ b → mapV (raise (suc n))
             (mapV
               (λ d → inject≤
                        (fromℕ (toℕ b * suc n + toℕ d))
                        (i*n+k≤m*n b d))
               (idcauchy (suc n))))
    (idcauchy (suc m))
    ≡⟨ sym (tabulate-∘ _ id) ⟩
  tabulate  {suc m} (λ b → mapV (raise (suc n))
             (mapV
               (λ d → inject≤
                        (fromℕ (toℕ b * suc n + toℕ d))
                        (i*n+k≤m*n b d))
               (idcauchy (suc n))))
    ≡⟨ finext _ _ (lemma3 n (suc m)) ⟩
  tabulate {suc m} ((λ b → mapV
               (λ d → inject≤
                      (fromℕ (toℕ b * suc n + toℕ d))
                      (i*n+k≤m*n b d))
             (idcauchy (suc n))) ∘ suc)
    ≡⟨ tabulate-∘ _ suc ⟩
  mapV (λ b → mapV
             (λ d → inject≤
                      (fromℕ (toℕ b * suc n + toℕ d))
                      (i*n+k≤m*n b d))
             (idcauchy (suc n)))
    (tabulate {suc m} suc) ∎)
  where open ≡-Reasoning
  
allFin* : (m n : ℕ) → allFin (m * n) ≡ 
          concatV 
            (mapV 
              (λ b → 
                mapV
                  (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                  (idcauchy n))
            (idcauchy m))
allFin* 0 _ = refl 
allFin* (suc m) 0 =
  begin (allFin (suc m * 0)
           ≡⟨ empty-vec {suc m * 0} (*-right-zero (suc m)) ⟩ 
         subst Cauchy (sym (*-right-zero (suc m))) []
           ≡⟨ sym (concat-nil {suc m}) ⟩ 
         concatV (tabulate {suc m} (λ b → []))
           ≡⟨ cong concatV (tabulate-allFin {suc m} (λ b → [])) ⟩
         concatV (mapV (λ b → []) (idcauchy (suc m))) ∎)
  where open ≡-Reasoning
allFin* (suc m) (suc n) =
  begin (allFin (suc n + m * suc n)
           ≡⟨ allFin+ (suc n) (m * suc n) ⟩
         mapV (inject+ (m * suc n)) (allFin (suc n)) ++V
         mapV (raise (suc n)) (allFin (m * suc n))
           ≡⟨ cong
                (λ x →
                  mapV (inject+ (m * suc n)) (allFin (suc n)) ++V
                  mapV (raise (suc n)) x)
                (allFin* m (suc n)) ⟩
         mapV (inject+ (m * suc n)) (allFin (suc n)) ++V
         mapV
           (raise (suc n))
           (concatV 
             (mapV 
               (λ b → 
                 mapV
                   (λ d → inject≤
                            (fromℕ (toℕ b * suc n + toℕ d))
                            (i*n+k≤m*n b d))
                   (idcauchy (suc n)))
               (idcauchy m)))
           ≡⟨ cong
                (_++V_ (mapV (inject+ (m * suc n)) (allFin (suc n))))
                (sym (concat-map
                       (mapV 
                         (λ b → 
                           mapV
                             (λ d → inject≤
                                      (fromℕ (toℕ b * suc n + toℕ d))
                                      (i*n+k≤m*n b d))
                             (idcauchy (suc n)))
                         (idcauchy m))
                       (raise (suc n)))) ⟩ 
         mapV (inject+ (m * suc n)) (allFin (suc n)) ++V
         concatV
           (mapV
             (mapV (raise (suc n)))
             (mapV 
               (λ b → 
                 mapV
                   (λ d → inject≤
                            (fromℕ (toℕ b * suc n + toℕ d))
                            (i*n+k≤m*n b d))
                   (idcauchy (suc n)))
               (idcauchy m)))
           ≡⟨ refl ⟩  
         concatV
           (mapV (inject+ (m * suc n)) (allFin (suc n)) ∷ 
            mapV
              (mapV (raise (suc n)))
              (mapV 
                (λ b → 
                  mapV
                    (λ d → inject≤
                             (fromℕ (toℕ b * suc n + toℕ d))
                             (i*n+k≤m*n b d))
                    (idcauchy (suc n)))
                (idcauchy m)))
           ≡⟨ cong
                 (λ x →
                   concatV
                     ((mapV (inject+ (m * suc n)) (allFin (suc n))) ∷ x))
                 (sym (map-∘
                        (mapV (raise (suc n)))
                        (λ b → 
                          mapV
                            (λ d → inject≤
                                     (fromℕ (toℕ b * suc n + toℕ d))
                                     (i*n+k≤m*n b d))
                            (idcauchy (suc n)))
                        (idcauchy m))) ⟩  
         concatV
           (mapV (inject+ (m * suc n)) (allFin (suc n)) ∷ 
            mapV
              (λ b → mapV
                       (raise (suc n))
                       (mapV
                         (λ d → inject≤
                                  (fromℕ (toℕ b * suc n + toℕ d))
                                  (i*n+k≤m*n b d))
                         (idcauchy (suc n))))
              (idcauchy m))
           ≡⟨ cong
                (λ x →
                  concatV
                    (x ∷
                    mapV
                      (λ b →
                        mapV
                          (raise (suc n))
                          (mapV
                            (λ d → inject≤
                                     (fromℕ (toℕ b * suc n + toℕ d))
                                     (i*n+k≤m*n b d))
                            (idcauchy (suc n))))
                      (idcauchy m)))
                (map-inj-lemma m n) ⟩
         concatV
           (mapV
              (λ d → inject≤
                       (fromℕ (toℕ d))
                       (i*n+k≤m*n {suc m} {suc n} zero d))
              (idcauchy (suc n)) ∷ 
            (mapV
              (λ b → mapV
                       (raise (suc n))
                       (mapV
                         (λ d → inject≤
                                  (fromℕ (toℕ b * suc n + toℕ d))
                                  (i*n+k≤m*n b d))
                         (idcauchy (suc n))))
              (idcauchy m)))
           ≡⟨ cong
                 (λ x →
                   concatV
                     (mapV
                       (λ d → inject≤
                                (fromℕ (toℕ d))
                                (i*n+k≤m*n {suc m} {suc n} zero d))
                       (idcauchy (suc n)) ∷
                     x))
                 (map-raise-lemma m n) ⟩ 
         concatV 
           (mapV
              (λ d → inject≤
                       (fromℕ (toℕ d))
                       (i*n+k≤m*n {suc m} {suc n} zero d))
              (idcauchy (suc n)) ∷ 
            (mapV 
               (λ b → mapV
                        (λ d → inject≤
                                 (fromℕ (toℕ b * suc n + toℕ d))
                                 (i*n+k≤m*n b d))
                        (idcauchy (suc n)))
               (tabulate {m} suc)))
           ≡⟨ refl ⟩ 
         concatV 
           (mapV 
             (λ b → 
               mapV
                 (λ d → inject≤
                          (fromℕ (toℕ b * suc n + toℕ d))
                          (i*n+k≤m*n b d))
                 (idcauchy (suc n)))
             (idcauchy (suc m))) ∎)
  where open ≡-Reasoning

tcomp-id : ∀ {m n} → tcompcauchy (idcauchy m) (idcauchy n) ≡ idcauchy (m * n)
tcomp-id {m} {n} = sym (allFin* m n)

-- Behaviour of parallel multiplicative composition wrt sequential

absurd : (m n q : ℕ) (r : Fin (suc n)) (k : Fin (suc (n + m * suc n))) 
         (k≡r+q*sn : toℕ k ≡ toℕ r + q * suc n) (p : suc m ≤ q) → ⊥
absurd m n q r k k≡r+q*sn p = ¬i+1+j≤i (toℕ k) {toℕ r} k≥k+sr
  where k≥k+sr : toℕ k ≥ toℕ k + suc (toℕ r)
        k≥k+sr =
          begin (toℕ k + suc (toℕ r)
                   ≡⟨ +-suc (toℕ k) (toℕ r) ⟩
                 suc (toℕ k) + toℕ r
                   ≤⟨ cong+r≤ (bounded k) (toℕ r) ⟩ 
                 (suc n + m * suc n) + toℕ r
                   ≡⟨ +-comm (suc n + m * suc n) (toℕ r) ⟩ 
                 toℕ r + (suc n + m * suc n)
                   ≡⟨ refl ⟩ 
                 toℕ r + suc m * suc n
                   ≤⟨ cong+l≤ (cong*r≤ p (suc n)) (toℕ r) ⟩ 
                 toℕ r + q * suc n
                   ≡⟨ sym k≡r+q*sn ⟩
                 toℕ k ∎)
          where open ≤-Reasoning

Fin0-⊥ : Fin 0 → ⊥
Fin0-⊥ ()

fin-project : (m n : ℕ) → Fin (m * n) → Fin m × Fin n
fin-project 0 n ()
fin-project (suc m) 0 k =  ⊥-elim (Fin0-⊥ (subst Fin (*-right-zero (suc m)) k)) 
fin-project (suc m) (suc n) k with (toℕ k) divMod (suc n)
... | result q r k≡r+q*sn = (fromℕ≤ {q} {suc m} (s≤s q≤m) , r)
  where q≤m : q ≤ m
        q≤m with suc m ≤? q
        ... | yes p = ⊥-elim (absurd m n q r k k≡r+q*sn p)
        ... | no ¬p = ≤-pred (≰⇒> ¬p)  

concat-tabulate-[] : ∀ {m n} {f : Fin m →  Fin n} → 
    concatV (tabulate {m} ((λ x → []) ∘ f)) ≡
    subst (λ n → Vec (Fin (m * 0)) n) (sym (*-right-zero m)) []
concat-tabulate-[] {0} = refl
concat-tabulate-[] {suc m} {_} {f} = concat-tabulate-[] {m} {_} {f ∘ suc}

tabulate-⊥ : ∀ {m n} {g : Fin (m * 0) → Fin n} → 
  tabulate g ≡ subst (Vec (Fin n)) (sym (*-right-zero m)) []
tabulate-⊥ {0} = refl
tabulate-⊥ {suc m}{_} {g} = tabulate-⊥ {m}

toℕ-inject+ : ∀ {n k} → (i : Fin n) → toℕ (inject+ k i) ≡ toℕ i
toℕ-inject+ {Data.Nat.zero} ()
toℕ-inject+ {suc n} zero = refl
toℕ-inject+ {suc n} (suc i) = cong suc (toℕ-inject+ i)

first-row :
  (m n : ℕ) → (f : Fin (suc m) × Fin (suc n) → Fin ((suc m) * (suc n))) → 
  tabulate {suc n} (λ x → f (zero , x)) ≡ 
  tabulate {suc n} ((λ k →  f (fin-project (suc m) (suc n) k)) ∘ inject+ (m * suc n))
first-row m n f = 
  finext ( (λ x → f (zero , x)))
            ( (λ k →  f (fin-project (suc m) (suc n) k)) ∘ inject+ (m * suc n))
            pf
    where
      pf : (i : Fin (suc n)) →  f (zero , i) ≡
           f (fin-project (suc m) (suc n) (inject+ (m * suc n) i))
      pf zero = refl
      pf (suc i) with suc (toℕ (inject+ (m * suc n) i)) divMod suc n 
      pf (suc i) | result q r property with suc m ≤? q
      pf (suc i) | result q r property | yes p = 
                ⊥-elim (absurd m n q r (suc (inject+ (m * suc n) i)) property p)
      pf (suc i) | result q r property | no ¬p = {!!}

tabulate-concat : ∀ {m n} →
  (f : Fin m × Fin n → Fin (m * n)) → 
  concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j)))) ≡
  tabulate {m * n} (λ (k : Fin (m * n)) → f (fin-project m n k))
tabulate-concat {0} f = refl
tabulate-concat {suc m} {0} f = 
    begin (concatV (tabulate {suc m} (λ x → []))
      ≡⟨ concat-tabulate-[] {suc m} {suc (suc m)} {inject₁} ⟩
    subst (Vec (Fin (m * 0))) (sym (*-right-zero m)) []
      ≡⟨ sym (tabulate-⊥ {m}) ⟩
    tabulate (λ k → f (⊥-elim (Fin0-⊥ (subst Fin (*-right-zero m) k)))) ∎)
  where open ≡-Reasoning
tabulate-concat {suc m} {suc n} f =
  begin (tabulate {suc n} (λ x → f (zero , x))
         ++V 
         concatV (tabulate {m} (λ i → tabulate {suc n} (λ j → f (suc i , j))))
      ≡⟨ cong₂ _++V_ (first-row m n f) {!!} ⟩
         tabulate {suc n}
           ((λ k →  f (fin-project (suc m) (suc n) k)) ∘ inject+ (m * suc n))
         ++V
         tabulate {m * suc n}
           ((λ k → f (fin-project (suc m) (suc n) k)) ∘ raise (suc n))
      ≡⟨ sym (tabulate-split {suc n} {m * suc n}
               (λ k → f (fin-project (suc m) (suc n) k))) ⟩
         tabulate {suc n + m * suc n}
           (λ k → f (fin-project (suc m) (suc n) k)) ∎) 
  where open ≡-Reasoning

lookup-concat-left : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} → 
  (d : Fin n) (leq : suc (toℕ d) ≤ n + m) (vs : Vec A n) (ws : Vec A m) → 
  lookup (inject≤ (fromℕ (toℕ d)) leq) (vs ++V ws) ≡ lookup d vs
lookup-concat-left zero (s≤s z≤n) (x ∷ vs) ws = refl
lookup-concat-left (suc d) (s≤s leq) (x ∷ vs) ws = lookup-concat-left d leq vs ws 

lookup-concat-right : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} → 
  (j : ℕ) (leq : suc (n + j) ≤ n + m) (leq' : suc j ≤ m)
  (vs : Vec A n) (ws : Vec A m) → 
  lookup (inject≤ (fromℕ (n + j)) leq) (vs ++V ws) ≡
  lookup (inject≤ (fromℕ j) leq') ws
lookup-concat-right {n = 0} j leq leq' [] ws =
  cong
    (λ x → lookup (inject≤ (fromℕ j) x) ws)
    (≤-proof-irrelevance leq leq')
lookup-concat-right {n = suc n} j (s≤s leq) leq' (v ∷ vs) ws =
  lookup-concat-right j leq leq' vs ws 

lookup-concat-right' : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} → 
  (j k : ℕ) (leq : suc ((n + j) + k) ≤ n + m) (leq' : suc (j + k) ≤ m)
  (vs : Vec A n) (ws : Vec A m) → 
  lookup (inject≤ (fromℕ ((n + j) + k)) leq) (vs ++V ws) ≡
  lookup (inject≤ (fromℕ (j + k)) leq') ws
lookup-concat-right' {n = 0} j k leq leq' [] ws =
  cong
    (λ x → lookup (inject≤ (fromℕ (j + k)) x) ws)
    (≤-proof-irrelevance leq leq')
lookup-concat-right' {n = suc n} j k (s≤s leq) leq' (v ∷ vs) ws =
  lookup-concat-right' j k leq leq' vs ws 

helper-leq : (m n : ℕ) → (b : Fin m) → 
  suc (n + toℕ b * suc n) ≤ n + m * suc n
helper-leq m n b =
  begin (suc (n + toℕ b * suc n)
       ≡⟨ cong suc (+-comm n (toℕ b * suc n)) ⟩
         suc (toℕ b * suc n + n)
       ≡⟨ cong (λ x → suc (toℕ b * suc n + x)) (sym (to-from n)) ⟩
         suc (toℕ b * suc n + toℕ (fromℕ n))
       ≤⟨ i*n+k≤m*n b (fromℕ n) ⟩
         m * suc n
       ≤⟨ n≤m+n n (m * suc n) ⟩ 
         n + m * suc n ∎)
  where open ≤-Reasoning

helper-leq' : (m n : ℕ) → (b : Fin m) →
  suc (toℕ b * suc n) ≤ m * suc n
helper-leq' 0 n ()
helper-leq' (suc m) n zero = s≤s z≤n
helper-leq' (suc m) n (suc b) = s≤s (helper-leq m n b) 

lookup-concat-inner : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
  (m n : ℕ) (b : Fin m) (j : B) 
  (leq : suc (toℕ b * suc n) ≤ m * suc n)
  (f : A × B → C) (pm : Vec A m) (pn : Vec B n) → 
  lookup
     (inject≤ (fromℕ (toℕ b * suc n)) leq)
     (concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm))
   ≡ f (lookup b pm , j) 
lookup-concat-inner 0 n () j leq f pm pn
lookup-concat-inner (suc m) n zero j (s≤s z≤n) f (i ∷ pm) pn = refl
lookup-concat-inner (suc m) n (suc b) j (s≤s leq) f (i ∷ pm) pn = 
  begin (lookup 
           (inject≤ (fromℕ (n + toℕ b * suc n)) leq)
           (mapV (λ d → f (i , d)) pn ++V
            concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm))
       ≡⟨ lookup-concat-right (toℕ b * suc n) leq (helper-leq' m n b)
           (mapV (λ d → f (i , d)) pn)
           (concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm)) ⟩ 
         lookup 
           (inject≤ (fromℕ (toℕ b * suc n)) (helper-leq' m n b))
           (concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm))
       ≡⟨ lookup-concat-inner m n b j (helper-leq' m n b) f pm pn ⟩
         f (lookup b pm , j) ∎)
  where open ≡-Reasoning

lookup-concat' : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
  (m n : ℕ) (b : Fin m) (d : Fin n) →
  (leq : suc (toℕ b * n + toℕ d) ≤ m * n) → 
  (f : A × B → C) (pm : Vec A m) (pn : Vec B n) → 
  lookup 
    (inject≤ (fromℕ (toℕ b * n + toℕ d)) leq)
    (concatV (mapV (λ b → mapV (λ d → f (b , d)) pn) pm)) ≡
  f (lookup b pm , lookup d pn)
lookup-concat' 0 n () d leq f pm pn
lookup-concat' (suc m) n zero d leq f (i ∷ pm) pn =
  begin (lookup
           (inject≤ (fromℕ (toℕ d)) leq)
           (concatV (mapV (λ b → mapV (λ d → f (b , d)) pn) (i ∷ pm)))
       ≡⟨ refl ⟩ 
         lookup
           (inject≤ (fromℕ (toℕ d)) leq)
           (concatV (mapV (λ d → f (i , d)) pn ∷
                     mapV (λ b → mapV (λ d → f (b , d)) pn) pm))
       ≡⟨ refl ⟩
         lookup
           (inject≤ (fromℕ (toℕ d)) leq)
           (mapV (λ d → f (i , d)) pn ++V
            concatV (mapV (λ b → mapV (λ d → f (b , d)) pn) pm))
       ≡⟨ lookup-concat-left d leq
            (mapV (λ d → f (i , d)) pn)
            (concatV (mapV (λ b → mapV (λ d → f (b , d)) pn) pm)) ⟩
         lookup d (mapV (λ d → f (i , d)) pn)
       ≡⟨ lookup-map d (λ d → f (i , d)) pn ⟩
         f (i , lookup d pn) ∎)
  where open ≡-Reasoning
lookup-concat' (suc m) 0 (suc b) () leq f (i ∷ pm) pn
lookup-concat' (suc m) (suc n) (suc b) zero (s≤s leq) f (i ∷ pm) (j ∷ pn) =
  begin (lookup
           (inject≤ (fromℕ ((n + toℕ b * suc n) + 0)) leq)
           (mapV (λ d → f (i , d)) pn ++V
            concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm))
       ≡⟨ cong₂D!
            (λ x y →
              lookup
                (inject≤ (fromℕ x) y)
                (mapV (λ d → f (i , d)) pn ++V
                 concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm)))
            (sym (+-right-identity (n + toℕ b * suc n)))
            (≤-proof-irrelevance
              (subst
                 (λ z → suc z ≤ n + m * suc n)
                 (sym (+-right-identity (n + toℕ b * suc n)))
                 (helper-leq m n b))
              leq) ⟩
         lookup
           (inject≤
             (fromℕ (n + toℕ b * suc n))
             (helper-leq m n b))
           (mapV (λ d → f (i , d)) pn ++V
            concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm))
       ≡⟨ lookup-concat-right
             (toℕ b * suc n)
             (helper-leq m n b)
             (helper-leq' m n b)
             (mapV (λ d → f (i , d)) pn)
             (concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm)) ⟩ 
         lookup
           (inject≤ (fromℕ (toℕ b * suc n)) (helper-leq' m n b))
           (concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm))
       ≡⟨ lookup-concat-inner m n b j (helper-leq' m n b) f pm pn ⟩  
         f (lookup b pm , j) ∎)
  where open ≡-Reasoning
lookup-concat' (suc m) (suc n) (suc b) (suc d) (s≤s leq) f (i ∷ pm) (j ∷ pn) = 
  begin (lookup
           (inject≤ (fromℕ ((n + toℕ b * suc n) + toℕ (suc d))) leq)
           (mapV (λ d → f (i , d)) pn ++V
            concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm))
       ≡⟨ lookup-concat-right' (toℕ b * suc n) (toℕ (suc d)) leq (i*n+k≤m*n b (suc d))
            (mapV (λ d → f (i , d)) pn)
            (concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm)) ⟩ 
         lookup
           (inject≤ (fromℕ (toℕ b * suc n + toℕ (suc d))) (i*n+k≤m*n b (suc d)))
           (concatV (mapV (λ b → mapV (λ d → f (b , d)) (j ∷ pn)) pm))
       ≡⟨ lookup-concat' m (suc n) b (suc d) (i*n+k≤m*n b (suc d)) f pm (j ∷ pn) ⟩ 
         f (lookup b pm , lookup d pn) ∎)
  where open ≡-Reasoning

q≡ : (m : ℕ) (q : ℕ) (¬p : ¬ suc m ≤ q) → 
  q ≡ toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p))))
q≡ m q ¬p = sym (toℕ-fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p))))

fin-proj-lem :
  (m n : ℕ) (k : Fin (m * n)) →
  k ≡
  inject≤
    (fromℕ (toℕ (proj₁ (fin-project m n k)) * n +
            toℕ (proj₂ (fin-project m n k))))
    (i*n+k≤m*n
      (proj₁ (fin-project m n k))
      (proj₂ (fin-project m n k)))
fin-proj-lem 0 n ()
fin-proj-lem (suc m) 0 k = ⊥-elim (Fin0-⊥ (subst Fin (*-right-zero (suc m)) k))
fin-proj-lem (suc m) (suc n) k with _divMod_ (toℕ k) (suc n) {_}
... | result q r k≡r+q*sn with suc m ≤? q
... | yes p = ⊥-elim (absurd m n q r k k≡r+q*sn p)
... | no ¬p = toℕ-injective toℕk≡
  where toℕk≡ = begin (toℕ k
                  ≡⟨ k≡r+q*sn ⟩
                       toℕ r + q * suc n
                  ≡⟨ +-comm (toℕ r) (q * suc n) ⟩ 
                       q * suc n + toℕ r
                  ≡⟨ cong
                        (λ x → x * suc n + toℕ r)
                        (q≡ m q ¬p) ⟩ 
                       toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) * suc n + toℕ r
                  ≡⟨ sym (to-from
                           (toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) * suc n + toℕ r)) ⟩
                       toℕ (fromℕ
                             (toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) * suc n + toℕ r))
                  ≡⟨ sym
                       (inject≤-lemma
                         (fromℕ
                           (toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) * suc n + toℕ r))
                         (i*n+k≤m*n (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) r)) ⟩ 
                       toℕ
                         (inject≤
                           (fromℕ
                             (toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) * suc n + toℕ r))
                           (i*n+k≤m*n
                             (fromℕ≤ {q} {suc m} (s≤s (≤-pred (≰⇒> ¬p)))) r)) ∎)
                where open ≡-Reasoning

lookup-concat :
  ∀ {m n} → (k : Fin (m * n)) → (pm qm : Cauchy m) → (pn qn : Cauchy n) →
  let vs = concatV
             (mapV
               (λ b →
                 mapV
                   (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                   pn)
             pm)
      ws = concatV
             (mapV
               (λ b →
                 mapV
                   (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                   qn)
             qm)
  in lookup (lookup k vs) ws
  ≡
  let (b , d) = fin-project m n k
      x = lookup (lookup b pm) qm
      y = lookup (lookup d pn) qn
  in inject≤ (fromℕ (toℕ x * n + toℕ y)) (i*n+k≤m*n x y)
lookup-concat {0} () pm qm pn qn
lookup-concat {suc m} {0} k pm qm [] [] =
  ⊥-elim (Fin0-⊥ (subst Fin (*-right-zero m) k))
lookup-concat {suc m} {suc n} zero (x ∷ pm) (x₁ ∷ qm) (x₂ ∷ pn) (x₃ ∷ qn) =
  begin (lookup 
           (inject≤ (fromℕ (toℕ x * suc n + toℕ x₂)) (i*n+k≤m*n x x₂))
           (concatV
             (mapV
               (λ b →
                 mapV
                   (λ d → inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
                   (x₃ ∷ qn))
               (x₁ ∷ qm)))
       ≡⟨ lookup-concat'
            (suc m) (suc n) x x₂ (i*n+k≤m*n x x₂)
            (λ {(b , d) → inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d)})
            (x₁ ∷ qm) (x₃ ∷ qn) ⟩ 
         inject≤
           (fromℕ (toℕ (lookup x (x₁ ∷ qm)) * suc n + toℕ (lookup x₂ (x₃ ∷ qn))))
           (i*n+k≤m*n (lookup x (x₁ ∷ qm)) (lookup x₂ (x₃ ∷ qn)))
       ≡⟨ refl ⟩ 
         let (b , d) = fin-project (suc m) (suc n) zero
             x = lookup (lookup b (x ∷ pm)) (x₁ ∷ qm)
             y = lookup (lookup d (x₂ ∷ pn)) (x₃ ∷ qn)
         in inject≤ (fromℕ (toℕ x * suc n + toℕ y)) (i*n+k≤m*n x y) ∎)
  where open ≡-Reasoning
lookup-concat {suc m} {suc n} (suc k) (x ∷ pm) (x₁ ∷ qm) (x₂ ∷ pn) (x₃ ∷ qn) =
  begin (let vs = concatV
                    (mapV
                      (λ b →
                        mapV
                          (λ d →
                            inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
                          (x₂ ∷ pn))
                      (x ∷ pm))
             ws = concatV
                    (mapV
                      (λ b →
                        mapV
                          (λ d →
                            inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
                          (x₃ ∷ qn))
                    (x₁ ∷ qm))
         in lookup (lookup (suc k) vs) ws
       ≡⟨ cong (λ z →
                lookup
                  (lookup z
                    (concatV
                      (mapV
                        (λ b →
                          mapV
                            (λ d →
                              inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
                            (x₂ ∷ pn))
                        (x ∷ pm))))
                  (concatV
                    (mapV
                      (λ b →
                        mapV
                          (λ d →
                            inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
                          (x₃ ∷ qn))
                    (x₁ ∷ qm))))
                  (fin-proj-lem (suc m) (suc n) (suc k)) ⟩
         let (b' , d') = fin-project (suc m) (suc n) (suc k)
             vs = concatV
                    (mapV
                      (λ b →
                        mapV
                          (λ d →
                            inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
                          (x₂ ∷ pn))
                      (x ∷ pm))
             ws = concatV
                    (mapV
                      (λ b →
                        mapV
                          (λ d →
                            inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
                          (x₃ ∷ qn))
                    (x₁ ∷ qm))
         in lookup
              (lookup
                (inject≤ (fromℕ (toℕ b' * (suc n) + toℕ d')) (i*n+k≤m*n b' d'))
                vs)
              ws
       ≡⟨ cong
            (λ x → lookup x ws)
            (lookup-concat' (suc m) (suc n) b' d' (i*n+k≤m*n b' d')
              (λ {(b , d) → inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d)})
              (x ∷ pm) (x₂ ∷ pn)) ⟩
         let (b' , d') = fin-project (suc m) (suc n) (suc k)
             ws = concatV
                    (mapV
                      (λ b →
                        mapV
                          (λ d →
                            inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))
                          (x₃ ∷ qn))
                    (x₁ ∷ qm))
         in lookup
              (inject≤
                (fromℕ (toℕ (lookup b' (x ∷ pm)) * suc n + toℕ (lookup d' (x₂ ∷ pn))))
                (i*n+k≤m*n (lookup b' (x ∷ pm)) (lookup d' (x₂ ∷ pn))))
              ws
       ≡⟨ lookup-concat' (suc m) (suc n) (lookup b' (x ∷ pm)) (lookup d' (x₂ ∷ pn))
             (i*n+k≤m*n (lookup b' (x ∷ pm)) (lookup d' (x₂ ∷ pn)))
             (λ {(b , d) → inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d)})
             (x₁ ∷ qm) (x₃ ∷ qn) ⟩
         let (b , d) = fin-project (suc m) (suc n) (suc k)
             r = lookup (lookup b (x ∷ pm)) (x₁ ∷ qm)
             s = lookup (lookup d (x₂ ∷ pn)) (x₃ ∷ qn)
         in inject≤
              (fromℕ (toℕ r * suc n + toℕ s))
              (i*n+k≤m*n r s) ∎)
  where open ≡-Reasoning

tcomp-dist : ∀ {m n} → (pm qm : Cauchy m) → (pn qn : Cauchy n) →
  scompcauchy (tcompcauchy pm pn) (tcompcauchy qm qn) ≡
  tcompcauchy (scompcauchy pm qm) (scompcauchy pn qn)
tcomp-dist {m} {n} pm qm pn qn =
  begin (scompcauchy (tcompcauchy pm pn) (tcompcauchy qm qn)
           ≡⟨ refl ⟩
         tabulate {m * n} (λ k →
           lookup
             (lookup k (concatV 
                         (mapV 
                           (λ b → 
                             mapV (λ d →
                               inject≤
                                 (fromℕ (toℕ b * n + toℕ d))
                                 (i*n+k≤m*n b d)) pn)
                           pm)))
             (concatV 
               (mapV 
                 (λ b → 
                   mapV (λ d →
                     inject≤
                       (fromℕ (toℕ b * n + toℕ d))
                       (i*n+k≤m*n b d)) qn)
                 qm)))
           ≡⟨  finext
                 (λ k →
                   lookup
                     (lookup k (concatV 
                       (mapV 
                         (λ b → 
                           mapV (λ d →
                             inject≤
                               (fromℕ (toℕ b * n + toℕ d))
                                (i*n+k≤m*n b d)) pn)
                         pm)))
                     (concatV 
                       (mapV 
                         (λ b → 
                           mapV (λ d →
                             inject≤
                               (fromℕ (toℕ b * n + toℕ d))
                               (i*n+k≤m*n b d)) qn)
                       qm)))
                 (λ k →
                   let (i , j) = fin-project m n k
                       b = lookup (lookup i pm) qm
                       d = lookup (lookup j pn) qn in 
                   inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                 (λ k → lookup-concat {m} {n} k pm qm pn qn) ⟩
         tabulate {m * n}
           (λ k →
             let (i , j) = fin-project m n k
                 b = lookup (lookup i pm) qm
                 d = lookup (lookup j pn) qn in 
             inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
           ≡⟨  sym (tabulate-concat
                 (λ {(i , j) →
                   let b = lookup (lookup i pm) qm
                       d = lookup (lookup j pn) qn in 
                   inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)})) ⟩
         concatV
           (tabulate {m}
             (λ i →
               tabulate {n}
                 (λ j → 
                   let b = lookup (lookup i pm) qm
                       d = lookup (lookup j pn) qn in 
                   inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))))
           ≡⟨  cong concatV
                 (finext
                   (λ i →
                     tabulate {n}
                       (λ j → 
                         let b = lookup (lookup i pm) qm
                             d = lookup (lookup j pn) qn in 
                         inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)))
                   (λ i →
                     let b = lookup (lookup i pm) qm in 
                     mapV
                       (λ d →
                         inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                       (tabulate (λ i → lookup (lookup i pn) qn)))
                   (λ i →
                     tabulate-∘
                       (let b = lookup (lookup i pm) qm in 
                        λ d →
                          inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                       (λ i → lookup (lookup i pn) qn))) ⟩
         concatV
           (tabulate {m}
             (λ i →
               let b = lookup (lookup i pm) qm in 
               mapV
                 (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                 (tabulate (λ i → lookup (lookup i pn) qn))))
           ≡⟨ cong concatV (tabulate-∘
                (λ b →
                  mapV
                    (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                    (tabulate (λ i → lookup (lookup i pn) qn)))
                 (λ i → lookup (lookup i pm) qm)) ⟩
         concatV
           (mapV
             (λ b →
               mapV
                 (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                 (tabulate (λ i → lookup (lookup i pn) qn)))
             (tabulate (λ i → lookup (lookup i pm) qm)))
           ≡⟨  refl ⟩
         tcompcauchy (scompcauchy pm qm) (scompcauchy pn qn) ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------------
