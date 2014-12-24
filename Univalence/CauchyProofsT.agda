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
open import Perm
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
toℕ-inject+ {0} ()
toℕ-inject+ {suc n} zero = refl
toℕ-inject+ {suc n} (suc i) = cong suc (toℕ-inject+ i)

q≡ : (m : ℕ) (q : ℕ) (¬p : ¬ suc m ≤ q) → 
  q ≡ toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p))))
q≡ m q ¬p = sym (toℕ-fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p))))

absurd2 : (n q : ℕ) (i : Fin (suc n)) (r  : Fin (suc (suc n))) 
  (eq : suc (toℕ i) ≡ toℕ r + suc (suc (n + q * suc (suc n)))) → ⊥
absurd2 n q i r eq = ¬i+1+j≤i (suc (toℕ i)) {toℕ r} leq
  where leq' = begin (suc (toℕ i)
                   ≤⟨ bounded i ⟩
                      suc n
                   ≤⟨ m≤m+n (suc n) (q * suc (suc n)) ⟩
                      suc (n + q * suc (suc n)) ∎)
               where open ≤-Reasoning
        leq = begin (suc (toℕ i) + suc (toℕ r)
                   ≡⟨ +-suc (suc (toℕ i)) (toℕ r) ⟩
                     suc (suc (toℕ i)) + toℕ r
                   ≡⟨ +-comm (suc (suc (toℕ i))) (toℕ r) ⟩
                     toℕ r + suc (suc (toℕ i))
                   ≤⟨ cong+l≤ (s≤s leq') (toℕ r) ⟩
                     toℕ r + suc (suc (n + q * suc (suc n)))
                   ≡⟨ sym eq ⟩ 
                     suc (toℕ i) ∎)
              where open ≤-Reasoning

small-quotient : (n q : ℕ) → (i : Fin n) → (r : Fin (suc n)) → 
  (eq₁ : suc (toℕ i) ≡ toℕ r + q * suc n) → (q ≡ 0) × (toℕ r ≡ suc (toℕ i))
small-quotient 0 _ () _ _
small-quotient (suc n) 0 i r eq = (refl , sym  (trans eq (+-right-identity (toℕ r))))
small-quotient (suc n) (suc q) i r eq = ⊥-elim (absurd2 n q i r eq) 

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
      pf (suc i) | result q r property | no ¬p =
                cong f (cong₂ _,_ (toℕ-injective (sym a₁)) a₂)
        where
           q≡f₁ : q ≡ toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p))))
           q≡f₁ = q≡ m q ¬p
           si≡f₂ : _≡_ {A = ℕ} (suc (toℕ (inject+ (m * suc n) i)))  (suc (toℕ i))
           si≡f₂ = cong suc (toℕ-inject+ {k = m * suc n} i)
           sq : (q ≡ 0) × (toℕ r ≡ suc (toℕ i))
           sq = small-quotient n q i r (trans (sym si≡f₂) property)
           a₁ : toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) ≡ toℕ {suc q} zero
           a₁ = trans (sym q≡f₁) (proj₁ sq)
           a₂ :  (suc i) ≡ r
           a₂ = toℕ-injective (sym (proj₂ sq))

lookup-2d' : (m n : ℕ) (k : Fin (m * n))
  (f : Fin m × Fin n → Fin (m * n)) → 
  lookup k (concatV (tabulate (λ i → tabulate (λ j → f (i , j)))))
  ≡ f (fin-project m n k)
lookup-2d' m n k f =
  let fin-result b d dec dec' = fin-divMod m n k in
  begin (lookup k (concatV (tabulate (λ i → tabulate (λ j → f (i , j)))))
        ≡⟨ cong (λ x → lookup k (concatV x))
            (finext
              (λ i → tabulate (λ j → f (i , j)))
              (λ i → mapV (λ j → f (i , j)) (allFin n))
              (λ i → tabulate-allFin (λ j → f (i , j)))) ⟩ 
         lookup k (concatV (tabulate (λ i → mapV (λ j → f (i , j)) (allFin n))))
        ≡⟨ cong
             (λ x → lookup k (concatV x))
             (tabulate-allFin (λ i → mapV (λ j → f (i , j)) (allFin n))) ⟩ 
         lookup k (concatV (mapV (λ i → mapV (λ j → f (i , j)) (allFin n)) (allFin m)))
        ≡⟨ lookup-2d m n k (allFin m) (allFin n) f ⟩
         f (lookup b (allFin m) , lookup d (allFin n))
        ≡⟨ cong₂ (λ x y → f (x , y)) (lookup-allFin b) (lookup-allFin d) ⟩
         f (b , d) 
        ≡⟨ cong f (sym (inv' (fin-product-iso m n) (b , d))) ⟩
         f (split (fin-product-iso m n) (combine (fin-product-iso m n) (b , d)))
        ≡⟨ refl ⟩ 
         f (fin-project m n (combine (fin-product-iso m n) (b , d)))
        ≡⟨ cong
             (λ x → f (fin-project m n x))
             (sym dec') ⟩ 
         f (fin-project m n k) ∎)
  where open ≡-Reasoning
        open Fin-Product-Iso

tabulate-concat : ∀ {m n} → (f : Fin m × Fin n → Fin (m * n)) → 
  concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j)))) ≡
  tabulate {m * n} (λ (k : Fin (m * n)) → f (fin-project m n k))
tabulate-concat {m} {n} f =
  begin (concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j))))
       ≡⟨ sym (tabulate∘lookup
                (concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j)))))) ⟩
         tabulate (λ i →
           lookup i
             (concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j))))))
       ≡⟨ finext
           (λ i →
             lookup i
               (concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j))))))
           (λ (k : Fin (m * n)) → f (fin-project m n k))
           (λ i → lookup-2d' m n i f) ⟩
         tabulate {m * n} (λ (k : Fin (m * n)) → f (fin-project m n k)) ∎)
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
