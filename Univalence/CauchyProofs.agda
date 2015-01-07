{-# OPTIONS --without-K #-}

module CauchyProofs where

-- Proofs about permutations defined in module Cauchy (everything
-- except the multiplicative ones which are defined in CauchyProofsT and
-- CauchyProofsS

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

open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  _≥_; z≤n; s≤s; _≟_; _≤?_; ≤-pred; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤; _ℕ-_; _≺_; reduce≥; 
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties using (bounded; inject+-lemma; to-from)
open import Data.Vec.Properties 
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin; tabulate-∘; 
         tabulate-allFin; allFin-map; lookup-++-inject+; lookup-++-≥)
open import Data.Product using (Σ)

open import Data.List 
  using (List; []; _∷_; _∷ʳ_; foldl; replicate; reverse; downFrom; 
         concatMap; gfilter; initLast; InitLast; _∷ʳ'_) 
  renaming (_++_ to _++L_; map to mapL; concat to concatL; zip to zipL)
open import Data.Vec 
  using (Vec; tabulate; []; _∷_; tail; lookup; zip; zipWith; splitAt;
         _[_]≔_; allFin; toList)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import Function using (id; _∘_; _$_; _∋_)

open import Proofs
open import Cauchy
open import Perm

------------------------------------------------------------------------------
-- Proofs about sequential composition

-- sequential composition with id on the right is identity

scomprid : ∀ {n} → (perm : Cauchy n) → scompcauchy perm (idcauchy n) ≡ perm
scomprid {n} perm = 
  begin (scompcauchy perm (idcauchy n)
           ≡⟨ refl ⟩ 
         tabulate (λ i → lookup (lookup i perm) (allFin n))
           ≡⟨ finext 
                (λ i → lookup-allFin (lookup i perm)) ⟩ 
         tabulate (λ i → lookup i perm)
           ≡⟨ tabulate∘lookup perm ⟩ 
         perm ∎)
  where open ≡-Reasoning

-- sequential composition with id on the left is identity

scomplid : ∀ {n} → (perm : Cauchy n) → scompcauchy (idcauchy n) perm ≡ perm
scomplid {n} perm = 
  trans (finext (λ i → cong (λ x → lookup x perm) (lookup-allFin i)))
        (tabulate∘lookup perm)
{-  begin (scompcauchy (idcauchy n) perm 
           ≡⟨ refl ⟩ 
         tabulate (λ i → lookup (lookup i (allFin n)) perm)
           ≡⟨ finext 
                (λ i → lookup (lookup i (allFin n)) perm) 
                (λ i → lookup i perm) 
                (λ i → cong (λ x → lookup x perm) (lookup-allFin i)) ⟩ 
         tabulate (λ i → lookup i perm)
           ≡⟨ tabulate∘lookup perm ⟩ 
         perm ∎)
  where open ≡-Reasoning -}

-- sequential composition is associative

lookupassoc : ∀ {n} → (π₁ π₂ π₃ : Cauchy n) (i : Fin n) → 
  lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃)) ≡
  lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃
lookupassoc π₁ π₂ π₃ i = 
  begin (lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃))
           ≡⟨ lookup∘tabulate (λ j → lookup (lookup j π₂) π₃) (lookup i π₁) ⟩ 
         lookup (lookup (lookup i π₁) π₂) π₃
           ≡⟨ cong 
                (λ x → lookup x π₃) 
                (sym (lookup∘tabulate (λ j → lookup (lookup j π₁) π₂) i)) ⟩ 
         lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃ ∎)
  where open ≡-Reasoning

scompassoc : ∀ {n} → (π₁ π₂ π₃ : Cauchy n) → 
  scompcauchy π₁ (scompcauchy π₂ π₃) ≡ scompcauchy (scompcauchy π₁ π₂) π₃
scompassoc π₁ π₂ π₃ = finext (lookupassoc π₁ π₂ π₃)
{-  begin (scompcauchy π₁ (scompcauchy π₂ π₃)
           ≡⟨ refl ⟩
         tabulate (λ i → 
           lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃)))
           ≡⟨ finext
              (λ i → 
                lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃)))
              (λ i → 
                lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃)
              (λ i → lookupassoc π₁ π₂ π₃ i) ⟩
         tabulate (λ i → 
           lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃)
           ≡⟨ refl ⟩
         scompcauchy (scompcauchy π₁ π₂) π₃ ∎)
  where open ≡-Reasoning
-}
------------------------------------------------------------------------------
-- Proofs about additive permutations

lookup-subst' : ∀ {m m'} 
  (i : Fin m) (xs : Vec (Fin m') m) (eq : m ≡ m') (eq' : m' ≡ m)
  (irr : sym eq ≡ eq') → 
  lookup 
    (subst Fin eq i) 
    (subst Cauchy eq (subst (λ s → Vec (Fin s) m) eq' xs)) ≡
  lookup i xs
lookup-subst' i xs refl .refl refl = refl

allFin+ : (m n : ℕ) → allFin (m + n) ≡ 
          mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
allFin+ 0 n = 
  begin (allFin n
           ≡⟨ refl ⟩ 
         tabulate {n} (id ∘ id)
           ≡⟨ tabulate-∘ id id ⟩ 
         mapV id (allFin n) ∎)
  where open ≡-Reasoning
allFin+ (suc m) n = 
  begin (allFin (suc (m + n))
           ≡⟨ allFin-map (m + n) ⟩ 
         zero ∷ mapV suc (allFin (m + n))
           ≡⟨ cong (λ x → zero ∷ mapV suc x) (allFin+ m n) ⟩ 
         zero ∷ 
           mapV suc (mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n))
           ≡⟨ cong 
                (_∷_ zero) 
                (map-++-commute suc (mapV (inject+ n) (allFin m))) ⟩
         zero ∷ (mapV suc (mapV (λ i → (inject+ {m} n i)) (allFin m))) ++V
                  mapV suc (mapV (λ i → (raise {n} m i)) (allFin n))
           ≡⟨ cong 
                (_∷_ zero) 
                (cong₂ _++V_ 
                  (sym (map-∘ suc (inject+ n) (allFin m))) 
                  (sym (map-∘ suc (raise m) (allFin n)))) ⟩ 
         zero ∷ (mapV (λ i → suc (inject+ {m} n i)) (allFin m) ++V 
                 mapV (λ i → suc (raise {n} m i)) (allFin n))
           ≡⟨ refl ⟩ 
         (zero ∷ mapV (λ i → inject+ n (suc i)) (allFin m)) ++V 
         mapV (raise (suc m)) (allFin n)
           ≡⟨ cong 
                (λ x → (zero ∷ x) ++V mapV (raise (suc m)) (allFin n))
                (map-∘ (inject+ n) suc (allFin m)) ⟩ 
         (zero ∷ mapV (inject+ n) (mapV suc (allFin m))) ++V 
         mapV (raise (suc m)) (allFin n)
           ≡⟨ refl ⟩ 
         mapV (inject+ n) (zero ∷ mapV suc (allFin m)) ++V
         mapV (raise (suc m)) (allFin n) 
           ≡⟨ cong 
                 (λ x → mapV (inject+ n) (zero ∷ x) ++V 
                        mapV (raise (suc m)) (allFin n))
                 (sym (tabulate-allFin {m} suc)) ⟩ 
         mapV (inject+ n) (zero ∷ tabulate {m} suc) ++V
         mapV (raise (suc m)) (allFin n) 
           ≡⟨ refl ⟩ 
         mapV (inject+ n) (allFin (suc m)) ++V 
         mapV (raise (suc m)) (allFin n) ∎)
  where open ≡-Reasoning

-- swap+ is idempotent
--
-- outline of swap+idemp proof
--
-- allFin (m + n) ≡ mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
-- zero-m : Vec (Fin (m + n)) m ≡ mapV (inject+ n) (allFin m) 
-- m-sum  : Vec (Fin (m + n)) n ≡ mapV (raise m) (allFin n)
-- allFin (n + m) ≡ mapV (inject+ m) (allFin n) ++V mapV (raise n) (allFin m)
-- zero-n : Vec (Fin (n + m)) n ≡ mapV (inject+ m) (allFin n) 
-- n-sum  : Vec (Fin (n + m)) m ≡ mapV (raise n) (allFin m)
-- 
-- first swap re-arranges allFin (n + m) to n-sum ++V zero-n
-- second swap re-arranges allfin (m + n) to m-sum ++V zero-m
-- 
-- for i = 0, ..., m-1, we have inject+ n i : Fin (m + n)
-- lookup (lookup (inject+ n i) (n-sum ++V zero-n)) (m-sum ++V zero-m) ==> 
-- lookup (lookup i n-sum) (m-sum ++V zero-m) ==>
-- lookup (raise n i) (m-sum ++V zero-m) ==> 
-- lookup i zero-m ==>
-- inject+ n i
-- 
-- for i = m, ..., m+n-1, we have raise m i : Fin (m + n)
-- lookup (lookup (raise m i) (n-sum ++V zero-n)) (m-sum ++V zero-m) ==> 
-- lookup (lookup i zero-n) (m-sum ++V zero-m) ==> 
-- lookup (inject+ m i) (m-sum ++V zero-m) ==> 
-- lookup i m-sum ==> 
-- raise m i

tabulate-++ : ∀ {m n a} {A : Set a} → (f : Fin (m + n) → A) → 
  tabulate {m + n} f ≡ 
  tabulate {m} (f ∘ inject+ n) ++V tabulate {n} (f ∘ raise m)
tabulate-++ {m} {n} {a} f = 
  begin (tabulate {m + n} f 
           ≡⟨ tabulate-allFin f ⟩ 
         mapV f (allFin (m + n))
           ≡⟨ cong (mapV f) (allFin+ m n) ⟩ 
         mapV f (mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n))
           ≡⟨ map-++-commute f (mapV (inject+ n) (allFin m)) ⟩ 
         mapV f (mapV (inject+ n) (allFin m)) ++V 
         mapV f (mapV (raise m) (allFin n))
           ≡⟨ cong₂ _++V_ 
                (sym (map-∘ f (inject+ n) (allFin m)))
                (sym (map-∘ f (raise m) (allFin n))) ⟩ 
         mapV (f ∘ inject+ n) (allFin m) ++V 
         mapV (f ∘ raise m) (allFin n)
           ≡⟨ cong₂ _++V_
                (sym (tabulate-allFin {m} (f ∘ inject+ n)))
                (sym (tabulate-allFin {n} (f ∘ raise m))) ⟩ 
         tabulate {m} (f ∘ inject+ n) ++V 
         tabulate {n} (f ∘ raise m) ∎)
  where open ≡-Reasoning

swap+idemp : (m n : ℕ) → 
  scompcauchy 
    (swap+cauchy m n) 
    (subst Cauchy (+-comm n m) (swap+cauchy n m))
  ≡ 
  allFin (m + n)
swap+idemp m n =
  begin (tabulate (λ i → 
           lookup 
             (lookup i 
               (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ≡⟨ tabulate-++ {m} {n} 
              (λ i → 
                lookup 
                  (lookup i 
                    (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                      (mapV (raise n) (allFin m) ++V 
                       mapV (inject+ m) (allFin n))))
                  (subst Cauchy (+-comm n m) 
                    (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                      (mapV (raise m) (allFin n) ++V 
                       mapV (inject+ n) (allFin m))))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (lookup (inject+ n i)
               (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (lookup (raise m i)
               (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ≡⟨ cong₂ _++V_
              (finext {m}
                (λ i → 
                  cong 
                    (λ x →
                      lookup x
                        (subst Cauchy (+-comm n m) 
                          (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                            (mapV (raise m) (allFin n) ++V 
                             mapV (inject+ n) (allFin m)))))
                    (lookup-subst 
                       (inject+ n i)
                       (mapV (raise n) (allFin m) ++V 
                        mapV (inject+ m) (allFin n))
                       (+-comm n m))))
              (finext {n}
                (λ i → 
                 cong
                    (λ x → 
                      lookup x
                      (subst Cauchy (+-comm n m) 
                        (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                          (mapV (raise m) (allFin n) ++V 
                           mapV (inject+ n) (allFin m)))))
                    (lookup-subst 
                       (raise m i)
                       (mapV (raise n) (allFin m) ++V 
                        mapV (inject+ m) (allFin n))
                       (+-comm n m)))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (subst Fin (+-comm n m) 
               (lookup (inject+ n i)
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (subst Fin (+-comm n m)
               (lookup (raise m i)
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))

         ≡⟨ cong₂ _++V_
              (finext {m}
                (λ i → cong 
                          (λ x → 
                            lookup
                              (subst Fin (+-comm n m) x)
                              (subst Cauchy (+-comm n m) 
                                (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                                  (mapV (raise m) (allFin n) ++V 
                                   mapV (inject+ n) (allFin m)))))
                          (lookup-++-inject+ 
                            (mapV (raise n) (allFin m))
                            (mapV (inject+ m) (allFin n))
                            i)))
              (finext {n}
                (λ i → cong
                          (λ x → 
                            lookup
                              (subst Fin (+-comm n m) x)
                              (subst Cauchy (+-comm n m) 
                                (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                                  (mapV (raise m) (allFin n) ++V 
                                   mapV (inject+ n) (allFin m)))))
                          (lookup-++-raise
                            (mapV (raise n) (allFin m))
                            (mapV (inject+ m) (allFin n))
                            i))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (subst Fin (+-comm n m) 
               (lookup i (mapV (raise n) (allFin m))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (subst Fin (+-comm n m)
               (lookup i (mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ≡⟨ cong₂ _++V_
              (finext {m}
                (λ i → 
                  cong
                     (λ x → 
                       lookup (subst Fin (+-comm n m) x)
                       (subst Cauchy (+-comm n m) 
                         (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                           (mapV (raise m) (allFin n) ++V 
                            mapV (inject+ n) (allFin m)))))
                     (trans 
                       (lookup-map i (raise n) (allFin m))
                       (cong (raise n) (lookup-allFin i)))))
              (finext {n}
                (λ i → 
                  cong
                    (λ x → 
                       lookup (subst Fin (+-comm n m) x)
                       (subst Cauchy (+-comm n m) 
                         (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                           (mapV (raise m) (allFin n) ++V 
                            mapV (inject+ n) (allFin m)))))
                     (trans 
                       (lookup-map i (inject+ m) (allFin n))
                       (cong (inject+ m) (lookup-allFin i))))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (subst Fin (+-comm n m) (raise n i))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (subst Fin (+-comm n m) (inject+ m i))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ≡⟨ cong₂ _++V_
             (finext {m}
               (λ i → 
                 lookup-subst' 
                    (raise n i)
                    (mapV (raise m) (allFin n) ++V 
                     mapV (inject+ n) (allFin m))
                     (+-comm n m)
                     (+-comm m n)
                     (proof-irrelevance (sym (+-comm n m)) (+-comm m n))))
             (finext {n}
               (λ i → 
                 lookup-subst'
                    (inject+ m i)
                    (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m))
                    (+-comm n m)
                    (+-comm m n)
                    (proof-irrelevance (sym (+-comm n m)) (+-comm m n)))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (raise n i)
             (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (inject+ m i)
             (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))
         ≡⟨ cong₂ _++V_
              (finext 
                (lookup-++-raise
                   (mapV (raise m) (allFin n))
                   (mapV (inject+ n) (allFin m))))
              (finext 
                 (lookup-++-inject+ 
                    (mapV (raise m) (allFin n)) 
                    (mapV (inject+ n) (allFin m)))) ⟩ 
         tabulate {m} (λ i → lookup i (mapV (inject+ n) (allFin m)))
         ++V
         tabulate {n} (λ i → lookup i (mapV (raise m) (allFin n)))
         ≡⟨ cong₂ _++V_ 
              (tabulate∘lookup (mapV (inject+ n) (allFin m)))
              (tabulate∘lookup (mapV (raise m) (allFin n))) ⟩ 
         mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
         ≡⟨ sym (allFin+ m n) ⟩
         allFin (m + n) ∎)
  where open ≡-Reasoning

-- Behaviour of parallel additive composition wrt sequential

-- a direct proof is hard, but this is really a statement about vectors

lookup-left : ∀ {m n} → (i : Fin m) → (pm : Cauchy m) → (pn : Cauchy n) → 
  lookup (inject+ n i) (mapV (inject+ n) pm ++V mapV (raise m) pn) 
  ≡ inject+ n (lookup i pm)
lookup-left {m} {n} i pm pn = look-left i (inject+ n) (raise m) pm pn

-- as is this

lookup-right : ∀ {m n} → (i : Fin n) → (pm : Cauchy m) → (pn : Cauchy n) → 
  lookup (raise m i) (mapV (inject+ n) pm ++V mapV (raise m) pn) 
  ≡ raise m (lookup i pn)
lookup-right {m} {n} i pm pn = look-right i (inject+ n) (raise m) pm pn

pcomp-dist : ∀ {m n} → (pm qm : Cauchy m) → (pn qn : Cauchy n) → 
    scompcauchy (pcompcauchy pm pn) (pcompcauchy qm qn) ≡
    pcompcauchy (scompcauchy pm qm) (scompcauchy pn qn)
pcomp-dist {m} {n} pm qm pn qn =
  begin (scompcauchy (pcompcauchy pm pn) (pcompcauchy qm qn)
           ≡⟨ refl ⟩
         tabulate (λ i → 
           lookup 
             (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
             (mapV (inject+ n) qm ++V mapV (raise m) qn))
            ≡⟨ tabulate-allFin (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn)) ⟩
         mapV (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (allFin (m + n))
            ≡⟨ cong 
                 (λ x → 
                   mapV (λ i → 
                     lookup 
                       (lookup i 
                         (mapV (inject+ n) pm ++V mapV (raise m) pn))
                       (mapV (inject+ n) qm ++V mapV (raise m) qn)) 
                     x) 
                 (allFin+ m n) ⟩
         mapV (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n))
            ≡⟨ map-++-commute 
                 (λ i → 
                   lookup 
                     (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn)) 
                 (mapV (inject+ n) (allFin m)) ⟩
         mapV (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (mapV (inject+ n) (allFin m)) 
         ++V 
         mapV (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (mapV (raise m) (allFin n))
            ≡⟨ cong₂ _++V_ 
                 (sym (map-∘ 
                   (λ i → lookup 
                     (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn))
                   (inject+ n) 
                   (allFin m)))
                 (sym (map-∘ 
                   (λ i → lookup 
                     (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn)) 
                   (raise m) 
                   (allFin n))) ⟩ 
         mapV (λ i → 
                lookup 
                  (lookup (inject+ n i) 
                    (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (allFin  m)
         ++V 
         mapV (λ i → 
                lookup 
                  (lookup (raise m i) 
                    (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (allFin n)
            ≡⟨ cong₂ _++V_ 
                 (sym (tabulate-allFin {m} (λ i → 
                   lookup 
                     (lookup (inject+ n i) 
                       (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn))))
                 (sym (tabulate-allFin {n} (λ i → 
                   lookup 
                     (lookup (raise m i) 
                       (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn))))  ⟩ 
         tabulate {m} (λ i → 
                lookup 
                  (lookup (inject+ n i) 
                    (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
         ++V 
         tabulate {n} (λ i → 
                lookup 
                  (lookup (raise m i) 
                    (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
            ≡⟨ cong₂ _++V_
                 (finext 
                   (λ i → cong 
                            (λ x → 
                              lookup x 
                                (mapV (inject+ n) qm ++V mapV (raise m) qn))
                            (lookup-left i pm pn)))
                 (finext 
                   (λ i → cong
                            (λ x → 
                              lookup x 
                                (mapV (inject+ n) qm ++V mapV (raise m) qn))
                            (lookup-right i pm pn))) ⟩
         tabulate (λ i → lookup (inject+ n (lookup i pm))
                           (mapV (inject+ n) qm ++V mapV (raise m) qn)) ++V
         tabulate (λ i → lookup (raise m (lookup i pn))
                           (mapV (inject+ n) qm ++V mapV (raise m) qn))
           ≡⟨ cong₂ _++V_
                 (finext (λ i → lookup-left (lookup i pm) qm qn))
                 (finext (λ i → lookup-right (lookup i pn) qm qn))
                   ⟩ 
         tabulate (λ i → (inject+ n) (lookup (lookup i pm) qm)) ++V
         tabulate (λ i → (raise m) (lookup (lookup i pn) qn))
            ≡⟨ cong₂ _++V_ 
               (tabulate-∘ (inject+ n) (λ i → lookup (lookup i pm) qm)) 
               (tabulate-∘ (raise m) (λ i → lookup (lookup i pn) qn)) ⟩ 
         mapV (inject+ n) (tabulate (λ i → lookup (lookup i pm) qm)) ++V 
         mapV (raise m) (tabulate (λ i → lookup (lookup i pn) qn))
            ≡⟨ refl ⟩
         pcompcauchy (scompcauchy pm qm) (scompcauchy pn qn) ∎)
  where open ≡-Reasoning

-- a kind of inverse for splitAt

unSplit : {m n : ℕ} {A : Set} → (f : Fin (m + n) → A) → 
  tabulate {m} (f ∘ (inject+ n)) ++V tabulate {n} (f ∘ (raise m)) ≡ tabulate f
unSplit {0} {n} f = refl
unSplit {suc m} f = cong (λ x → (f zero) ∷ x) (unSplit {m} (f ∘ suc))

pcomp-id : ∀ {m n} → pcompcauchy (idcauchy m) (idcauchy n) ≡ idcauchy (m + n)
pcomp-id {m} {n} = 
  begin (mapV (inject+ n) (idcauchy m) ++V (mapV (raise m) (idcauchy n))
    ≡⟨ refl ⟩
  mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
    ≡⟨ cong₂ _++V_ 
       (sym (tabulate-allFin {m} (inject+ n))) 
       (sym (tabulate-allFin (raise m))) ⟩
  tabulate {m} (inject+ n) ++V tabulate {n} (raise m)
    ≡⟨ unSplit {m} {n} id ⟩
  idcauchy (m + n) ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------------
