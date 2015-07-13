{-# OPTIONS --without-K #-}

module CauchyProofs where

-- Proofs about permutations defined in module Cauchy (everything
-- except the multiplicative ones which are defined in CauchyProofsT and
-- CauchyProofsS

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Data.Nat.Properties
  using (m≤m+n; n≤m+n; n≤1+n; cancel-*-right-≤; ≰⇒>; ¬i+1+j≤i)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)

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

open import Data.Vec 
  using (Vec; tabulate; []; _∷_; tail; lookup; zip; zipWith; splitAt;
         _[_]≔_; allFin; toList)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import Function using (id; _∘_; _$_; _∋_; flip)

open import Proofs
open import Cauchy

------------------------------------------------------------------------------
-- Proofs about sequential composition

-- sequential composition with id on the right is identity

scomprid : ∀ {n} → (perm : Cauchy n) → scompcauchy perm (idcauchy n) ≡ perm
scomprid {n} perm = 
  begin (scompcauchy perm (idcauchy n)
           ≡⟨ refl ⟩ 
         tabulate (λ i → lookup (lookup i perm) (allFin n))
           ≡⟨ finext (λ i → lookup-allFin (lookup i perm)) ⟩ 
         tabulate (λ i → lookup i perm)
           ≡⟨ tabulate∘lookup perm ⟩ 
         perm ∎)
  where open ≡-Reasoning

-- sequential composition with id on the left is identity

scomplid : ∀ {n} → (perm : Cauchy n) → scompcauchy (idcauchy n) perm ≡ perm
scomplid {n} perm = 
  trans (finext (λ i → cong (λ x → lookup x perm) (lookup-allFin i)))
        (tabulate∘lookup perm)

-- sequential composition is associative
scompassoc : ∀ {n} → (π₁ π₂ π₃ : Cauchy n) → 
  scompcauchy π₁ (scompcauchy π₂ π₃) ≡ scompcauchy (scompcauchy π₁ π₂) π₃
scompassoc π₁ π₂ π₃ = finext (lookupassoc π₁ π₂ π₃)

------------------------------------------------------------------------------
-- Proofs about additive permutations

lookup-subst2 : ∀ {m m'}
  (i : Fin m) (xs : Vec (Fin m) m) (eq : m ≡ m') →
  lookup (subst Fin eq i)
              (subst Cauchy eq xs) ≡ subst Fin eq (lookup i xs)
lookup-subst2 i xs refl = refl

allFin+ : (m n : ℕ) → allFin (m + n) ≡ 
          mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
allFin+ m n = trans (tabulate-split {m} {n})
   (cong₂ _++V_ (tabulate-allFin {m} (inject+  n)) (tabulate-allFin {n} (raise m)))

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

swap+-left : (m n : ℕ) → ∀ (i : Fin m) → 
  let q = subst Cauchy (+-comm n m) (swap+cauchy n m) in
  lookup (lookup (inject+ n i) (swap+cauchy m n)) q ≡ inject+ n i
swap+-left m n i = 
  let q = subst Cauchy (+-comm n m) (swap+cauchy n m) in
  begin (
  lookup (lookup (inject+ n i) (swap+cauchy m n)) q
    ≡⟨ cong (flip lookup q) ( (lookup-++-inject+ (tabulate {m} (id+ {m} {n} ∘ raise n)) 
                                                                          (tabulate {n} (id+ {m} {n} ∘ inject+ m)) i)) ⟩
  lookup (lookup i (tabulate (λ x → subst Fin (+-comm n m) (raise n x)))) q
    ≡⟨ cong (flip lookup q) (lookup∘tabulate (λ x → subst Fin (+-comm n m) (raise n x)) i) ⟩ 
  lookup (subst Fin (+-comm n m) (raise n i)) q
    ≡⟨  lookup-subst2 (raise n i) (swap+cauchy n m) (+-comm n m) ⟩
  subst Fin (+-comm n m) (lookup (raise n i) (swap+cauchy n m))
    ≡⟨  cong (subst Fin (+-comm n m))
                   (lookup-++-raise (tabulate {n} (id+ {n} ∘ raise m)) (tabulate {m} (id+ {n} ∘ inject+ n)) i) ⟩
  subst Fin (+-comm n m)
    (lookup i (tabulate (λ z → subst Fin (+-comm m n) (inject+ n z))))
    ≡⟨  subst-lookup-tabulate-inject+ i ⟩
  inject+ n i ∎) 
  where open ≡-Reasoning

swap+-right : (m n : ℕ) → (i : Fin n) →
  let q = subst Cauchy (+-comm n m) (swap+cauchy n m) in
  lookup (lookup (raise m i) (swap+cauchy m n)) q ≡ raise m i
swap+-right m n i =
  let q = subst Cauchy (+-comm n m) (swap+cauchy n m) in
  begin (
  lookup (lookup (raise m i) (swap+cauchy m n)) q
    ≡⟨ cong (flip lookup q) ( (lookup-++-raise (tabulate {m} (id+ {m} {n} ∘ raise n)) 
                                                                       (tabulate {n} (id+ {m} {n} ∘ inject+ m)) i)) ⟩
  lookup (lookup i (tabulate (λ x → subst Fin (+-comm n m) (inject+ m x)))) q
    ≡⟨ cong (flip lookup q) (lookup∘tabulate (λ x → subst Fin (+-comm n m) (inject+ m x)) i) ⟩ 
  lookup (subst Fin (+-comm n m) (inject+ m i)) q
    ≡⟨  lookup-subst2 (inject+ m i) (swap+cauchy n m) (+-comm n m) ⟩
  subst Fin (+-comm n m) (lookup (inject+ m i) (swap+cauchy n m))
    ≡⟨  cong (subst Fin (+-comm n m))
                   (lookup-++-inject+ (tabulate {n} (id+ {n} ∘ raise m)) (tabulate {m} (id+ {n} ∘ inject+ n)) i) ⟩
  subst Fin (+-comm n m)
    (lookup i (tabulate (λ z → subst Fin (+-comm m n) (raise m z))))
    ≡⟨  subst-lookup-tabulate-raise i ⟩
  raise m i ∎) 
  where open ≡-Reasoning

swap+idemp : (m n : ℕ) → 
  scompcauchy 
    (swap+cauchy m n) 
    (subst Cauchy (+-comm n m) (swap+cauchy n m))
  ≡ 
  allFin (m + n)
swap+idemp m n =
  let q = subst Cauchy (+-comm n m) (swap+cauchy n m) in
  begin 
    (tabulate (λ i → lookup (lookup i (swap+cauchy m n)) q)
         ≡⟨ tabulate-split {m} {n} ⟩ 
     tabulate {m} (λ i → lookup (lookup (inject+ n i) (swap+cauchy m n)) q)
         ++V
     tabulate {n} (λ i → lookup (lookup (raise m i) (swap+cauchy m n)) q)
         ≡⟨ cong₂ _++V_ (finext (swap+-left m n)) 
                                     (finext (swap+-right m n)) ⟩
     tabulate {m} (inject+ n) ++V tabulate {n} (raise m)
         ≡⟨ unSplit {m} {n} id ⟩
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

--- find a better name
look-left' : ∀ {m n} → (pm qm : Cauchy m) → (pn qn : Cauchy n) → 
      (i : Fin m) →
      (lookup (lookup (inject+ n i) (pcompcauchy pm pn)) (pcompcauchy qm qn))
      ≡ inject+ n (lookup (lookup i pm) qm)
look-left' {m} {n} pm qm pn qn i = 
  let pp = pcompcauchy pm pn in
  let qq = pcompcauchy qm qn in
  begin (
    lookup (lookup (inject+ n i) pp) qq
          ≡⟨ cong (flip lookup qq) (lookup-++-inject+ (mapV (inject+ n) pm) (mapV (raise m) pn) i) ⟩
    lookup (lookup i (mapV (inject+ n) pm)) qq
          ≡⟨ cong (flip lookup qq) (lookup-map i (inject+ n) pm) ⟩
    lookup (inject+ n (lookup i pm)) qq
         ≡⟨ lookup-left (lookup i pm) qm qn ⟩
    inject+ n (lookup (lookup i pm) qm) ∎)
  where open ≡-Reasoning

look-right' : ∀ {m n} → (pm qm : Cauchy m) → (pn qn : Cauchy n) → 
      (i : Fin n) →
      (lookup (lookup (raise m i) (pcompcauchy pm pn)) (pcompcauchy qm qn))
      ≡ raise m (lookup (lookup i pn) qn)
look-right' {m} {n} pm qm pn qn i = 
  let pp = pcompcauchy pm pn in
  let qq = pcompcauchy qm qn in
  begin (
    lookup (lookup (raise m i) pp) qq
          ≡⟨ cong (flip lookup qq) (lookup-++-raise (mapV (inject+ n) pm) (mapV (raise m) pn) i) ⟩
    lookup (lookup i (mapV (raise m) pn)) qq
          ≡⟨ cong (flip lookup qq) (lookup-map i (raise m) pn) ⟩
    lookup (raise m (lookup i pn)) qq
         ≡⟨ lookup-right (lookup i pn) qm qn ⟩
    raise m (lookup (lookup i pn) qn) ∎)
  where open ≡-Reasoning

pcomp-dist : ∀ {m n} → (pm qm : Cauchy m) → (pn qn : Cauchy n) → 
    scompcauchy (pcompcauchy pm pn) (pcompcauchy qm qn) ≡
    pcompcauchy (scompcauchy pm qm) (scompcauchy pn qn)
pcomp-dist {m} {n} pm qm pn qn =
  let pp = pcompcauchy pm pn in
  let qq = pcompcauchy qm qn in
  let look = λ i → lookup (lookup i pp) qq in
  begin (scompcauchy pp qq
           ≡⟨ refl ⟩
         tabulate look
           ≡⟨ tabulate-split {m} {n} ⟩
         splitV+ {m} {n} {f = look}
           ≡⟨ cong₂ _++V_ (finext {m} (look-left' pm qm pn qn)) 
                                      (finext {n} (look-right' pm qm pn qn)) ⟩
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
