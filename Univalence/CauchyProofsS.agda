{-# OPTIONS --without-K #-}

module CauchyProofsS where

-- Proofs about permutations defined in module Cauchy (multiplicative2)

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
-- open import CauchyProofsT

------------------------------------------------------------------------------
-- Main lemma swap⋆idemp

subst-allFin : ∀ {m n} → (eq : m ≡ n) → 
  subst Cauchy eq (allFin m) ≡ allFin n
subst-allFin refl = refl

swap⋆idemp : (m n : ℕ) → 
  scompcauchy 
    (swap⋆cauchy m n) 
    (subst Cauchy (*-comm n m) (swap⋆cauchy n m))
  ≡ 
  allFin (m * n)
swap⋆idemp 0 n = refl
swap⋆idemp 1 0 = refl
swap⋆idemp 1 1 = refl
swap⋆idemp 1 (suc (suc n)) =
  begin (scompcauchy
           (subst Cauchy (sym (+-right-identity (suc (suc n))))
             (allFin (suc (suc n))))
           (subst Cauchy (*-comm (suc (suc n)) 1)
             (subst Cauchy (sym (i*1≡i (suc (suc n)))) (allFin (suc (suc n)))))
         ≡⟨ cong₂ (λ x y → scompcauchy x (subst Cauchy (*-comm (suc (suc n)) 1) y))
              (subst-allFin (sym (+-right-identity (suc (suc n)))))
              (subst-allFin (sym (i*1≡i (suc (suc n))))) ⟩ 
         scompcauchy
           (allFin (suc (suc n) + 0))
           (subst Cauchy (*-comm (suc (suc n)) 1) (allFin (suc (suc n) * 1)))
         ≡⟨ cong (scompcauchy (allFin (suc (suc n) + 0)))
              (subst-allFin (*-comm (suc (suc n)) 1)) ⟩ 
         scompcauchy
           (allFin (suc (suc n) + 0))
           (allFin (1 * suc (suc n)))
         ≡⟨ scomplid (allFin (suc (suc n) + 0)) ⟩
         allFin (1 * suc (suc n)) ∎)
  where open ≡-Reasoning
swap⋆idemp (suc (suc m)) 0 =
  begin (scompcauchy
           (subst Cauchy (sym (*-right-zero (suc (suc m)))) (allFin 0))
           (subst Cauchy (*-comm 0 (suc (suc m))) (allFin 0))
         ≡⟨ cong₂ scompcauchy
              (subst-allFin (sym (*-right-zero (suc (suc m)))))
              (subst-allFin (*-comm 0 (suc (suc m)))) ⟩ 
         scompcauchy
           (allFin (suc (suc m) * 0))
           (allFin (suc (suc m) * 0))
         ≡⟨ scomplid (allFin (suc (suc m) * 0)) ⟩ 
         allFin (suc (suc m) * 0) ∎)
  where open ≡-Reasoning
swap⋆idemp (suc (suc m)) 1 =
  begin (scompcauchy
         (subst Cauchy (sym (i*1≡i (suc (suc m)))) (idcauchy (suc (suc m))))
         (subst Cauchy (*-comm 1 (suc (suc m)))
           (subst Cauchy (sym (+-right-identity (suc (suc m))))
             (idcauchy (suc (suc m)))))
           ≡⟨ cong₂ (λ x y → scompcauchy x (subst Cauchy (*-comm 1 (suc (suc m))) y))
                (subst-allFin (sym (i*1≡i (suc (suc m)))))
                (subst-allFin (sym (+-right-identity (suc (suc m))))) ⟩ 
         scompcauchy
           (allFin (suc (suc m) * 1))
           (subst Cauchy (*-comm 1 (suc (suc m))) (allFin (suc (suc m) + 0)))
           ≡⟨ cong (scompcauchy (allFin (suc (suc m) * 1)))
                 (subst-allFin (*-comm 1 (suc (suc m)))) ⟩ 
         scompcauchy
           (allFin (suc (suc m) * 1))
           (allFin (suc (suc m) * 1))
           ≡⟨ scomplid (allFin (suc (suc m) * 1)) ⟩ 
         allFin (suc (suc m) * 1) ∎)
  where open ≡-Reasoning
swap⋆idemp (suc (suc m)) (suc (suc n)) =
  begin (scompcauchy
           (swap⋆cauchy (suc (suc m)) (suc (suc n)))
           (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
             (swap⋆cauchy (suc (suc n)) (suc (suc m))))
         ≡⟨ refl ⟩
         scompcauchy
           (concatV 
             (mapV 
               (λ b → mapV (λ d → transposeIndex m n b d) (allFin (suc (suc n))))
               (allFin (suc (suc m)))))
           (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
             (concatV 
               (mapV 
                 (λ d → mapV (λ b → transposeIndex n m d b) (allFin (suc (suc m))))
                 (allFin (suc (suc n))))))
         ≡⟨ {!!} ⟩ 
          concatV 
            (mapV 
              (λ b → 
                mapV
                  (λ d → inject≤
                           (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                           (i*n+k≤m*n b d))
                  (idcauchy (suc (suc n))))
              (idcauchy (suc (suc m))))
--         ≡⟨ sym (allFin* (suc (suc m)) (suc (suc n))) ⟩
         ≡⟨ {!!} ⟩ 
         allFin (suc (suc m) * suc (suc n)) ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------------
{--

scompcauchy : ∀ {n} → Cauchy n → Cauchy n → Cauchy n
scompcauchy {n} perm₁ perm₂ = 
  tabulate (λ i → lookup (lookup i perm₁) perm₂)

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

allFin* : (m n : ℕ) → allFin (m * n) ≡ 
          concatV 
            (mapV 
              (λ b → 
                mapV
                  (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                  (idcauchy n))
            (idcauchy m))
--}
