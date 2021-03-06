{-# OPTIONS --without-K #-}

module Perm where

-- Definitions for permutations in the Cauchy representation

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Unary using (Pred)
  renaming (Decidable to UnaryDecidable)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat.Properties
  using (cancel-+-left; n∸n≡0; +-∸-assoc; m+n∸n≡m; 1+n≰n; m≤m+n;
         n≤m+n; n≤1+n; cancel-*-right-≤; ≰⇒>; ¬i+1+j≤i)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)
open import Data.Nat.DivMod using (DivMod; result; _divMod_; _div_; _mod_)
open import Relation.Binary using (Rel; Decidable; Setoid)
open import Relation.Binary.Core using (REL; Transitive; _⇒_)

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
  using (bounded; to-from; inject+-lemma; inject≤-lemma; toℕ-injective;
         toℕ-raise; toℕ-fromℕ≤)
open import Data.Vec.Properties 
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin; tabulate-∘; 
         tabulate-allFin; allFin-map; lookup-++-inject+; lookup-++-≥;
         lookup-++-<)
open import Data.Product using (Σ; swap)

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
open import Function using (id; _∘_; _$_; flip)
open import Data.Maybe using (Maybe; just; nothing)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Proofs
open import Cauchy

------------------------------------------------------------------------------
-- What JC thinks will actually work
-- we need injectivity.  surjectivity ought to be provable.

Permutation : ℕ → Set
Permutation n = Σ (Cauchy n) (λ v → ∀ {i j} → lookup i v ≡ lookup j v → i ≡ j)

------------------------------------------------------------------------------
-- Iso between Fin (m * n) and Fin m × Fin n

absurd-quotient : (m n q : ℕ) (r : Fin (suc n)) (k : Fin (suc (n + m * suc n))) 
         (k≡r+q*sn : toℕ k ≡ toℕ r + q * suc n) (p : suc m ≤ q) → ⊥
absurd-quotient m n q r k k≡r+q*sn p = ¬i+1+j≤i (toℕ k) {toℕ r} k≥k+sr
  where k≥k+sr : toℕ k ≥ toℕ k + suc (toℕ r)
        k≥k+sr = begin (toℕ k + suc (toℕ r)
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
        ... | yes p = ⊥-elim (absurd-quotient m n q r k k≡r+q*sn p)
        ... | no ¬p = ≤-pred (≰⇒> ¬p)  

fin-proj-lem : (m n : ℕ) (k : Fin (m * n)) →
  k ≡ let (b , d) = fin-project m n k in
      inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)
fin-proj-lem 0 n ()
fin-proj-lem (suc m) 0 k = ⊥-elim (Fin0-⊥ (subst Fin (*-right-zero (suc m)) k))
fin-proj-lem (suc m) (suc n) k with _divMod_ (toℕ k) (suc n) {_}
... | result q r k≡r+q*sn with suc m ≤? q
... | yes p = ⊥-elim (absurd-quotient m n q r k k≡r+q*sn p)
... | no ¬p = toℕ-injective toℕk≡
  where q≡ : (m : ℕ) (q : ℕ) (¬p : ¬ suc m ≤ q) → 
             q ≡ toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p))))
        q≡ m q ¬p = sym (toℕ-fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p))))
        toℕk≡ = begin (toℕ k
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

fin-proj-lem2 : (m n : ℕ) (b : Fin m) (d : Fin n) → 
  (b , d) ≡ fin-project m n 
              (inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
fin-proj-lem2 m 0 b ()
fin-proj-lem2 0 (suc n) () d 
fin-proj-lem2 (suc m) (suc n) b d with
 (toℕ (inject≤ (fromℕ (toℕ b * suc n + toℕ d)) (i*n+k≤m*n b d))) divMod (suc n)
... | result q r eq =
  begin ((b , d)
        ≡⟨ cong₂ _,_
            (toℕ-injective
              (sym
                (trans
                  (toℕ-fromℕ≤ (s≤s (trans≤ (refl′ (proj₁ eq')) (bounded' m b))))
                  (proj₁ eq'))) )
            (sym (proj₂ eq')) ⟩
        (fromℕ≤ (s≤s (trans≤ (refl′ (proj₁ eq')) (bounded' m b))) , r)
        ≡⟨ cong₂ _,_ (cong fromℕ≤ (≤-proof-irrelevance _ _)) refl ⟩ 
        (fromℕ≤ _ , r) ∎)
  where open ≡-Reasoning
        eq' : q ≡ toℕ b × r ≡ d
        eq' = swap
                (addMul-lemma′ q (toℕ b) n r d
                  (trans
                    (trans (+-comm (q * suc n) (toℕ r)) (sym eq))
                    (trans (inject≤-lemma _ _) (to-from _))))
 
-- The actual isomorphism

record Fin-Product-Iso (m n : ℕ) : Set where
  constructor iso
  field
    split   : Fin (m * n) → Fin m × Fin n
    combine : Fin m × Fin n → Fin (m * n)
    inv     : (i : Fin (m * n)) → combine (split i) ≡ i
    inv'    : (bd : Fin m × Fin n) → split (combine bd) ≡ bd
    
fin-product-iso : (m n : ℕ) → Fin-Product-Iso m n
fin-product-iso m n =
  iso
    (fin-project m n)
    (λ {(b , d) → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)})
    (λ k → sym (fin-proj-lem m n k))
    ((λ {(b , d) → sym (fin-proj-lem2 m n b d)}))

record Fin-DivMod (m n : ℕ) (i : Fin (m * n)) : Set where
  constructor fin-result
  field
    b    : Fin m
    d    : Fin n
    dec  : toℕ i ≡ toℕ d + toℕ b * n
    dec' : i ≡ inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)

fin-divMod : (m n : ℕ) (i : Fin (m * n)) → Fin-DivMod m n i
fin-divMod m n i = fin-result b d dec dec'
  where
    bd = Fin-Product-Iso.split (fin-product-iso m n) i
    b = proj₁ bd
    d = proj₂ bd
    dec' = sym (Fin-Product-Iso.inv (fin-product-iso m n) i)
    dec = begin (toℕ i
                ≡⟨ cong toℕ (sym (inv (fin-product-iso m n) i)) ⟩
                toℕ (inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                ≡⟨ inject≤-lemma (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d) ⟩ 
                toℕ (fromℕ (toℕ b * n + toℕ d))
                ≡⟨ to-from (toℕ b * n + toℕ d) ⟩ 
                toℕ b * n + toℕ d
                ≡⟨ +-comm (toℕ b * n) (toℕ d) ⟩ 
                toℕ d + toℕ b * n ∎)
          where open ≡-Reasoning
                open Fin-Product-Iso

fin-addMul-lemma : (m n : ℕ) (b b' : Fin m) (d d' : Fin n) → 
  toℕ b * n + toℕ d ≡ toℕ b' * n + toℕ d' → b ≡ b' × d ≡ d'
fin-addMul-lemma m 0 _ _ ()
fin-addMul-lemma m (suc n) b b' d d' p =
  let (d≡ , b≡) = addMul-lemma′ (toℕ b) (toℕ b') n d d' p
  in (toℕ-injective b≡ , d≡)

------------------------------------------------------------------------------
-- Vec lemmas

fi≡fj : {m : ℕ} → (i j : Fin m) (f : Fin m → Fin m) →
        (p : lookup i (tabulate f) ≡ lookup j (tabulate f)) → (f i ≡ f j)
fi≡fj i j f p = trans
                  (sym (lookup∘tabulate f i))
                  (trans p (lookup∘tabulate f j))

lookup-bounded : (m n : ℕ) (i : Fin n) (v : Vec (Fin m) n) → toℕ (lookup i v) < m
lookup-bounded m 0 () v
lookup-bounded m (suc n) zero (x ∷ v) = bounded x
lookup-bounded m (suc n) (suc i) (x ∷ v) = lookup-bounded m n i v 

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

lookup-2d : (m n : ℕ) (i : Fin (m * n)) (α : Cauchy m) (β : Cauchy n) →
  (h : (Fin m × Fin n) → Fin (m * n)) → 
  lookup i (concatV (mapV (λ b → mapV (λ d → h (b , d)) β) α)) ≡
  let fin-result b d _ _ = fin-divMod m n i in h (lookup b α , lookup d β)
lookup-2d m n i α β h =
  let fin-result b d dec dec' = fin-divMod m n i in 
  begin (lookup i (concatV (mapV (λ b → mapV (λ d → h (b , d)) β) α))
         ≡⟨ cong
              (λ x → lookup x (concatV (mapV (λ b → mapV (λ d → h (b , d)) β) α)))
              dec' ⟩
         lookup
           (inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
           (concatV (mapV (λ b → mapV (λ d → h (b , d)) β) α))
         ≡⟨ lookup-concat' m n b d (i*n+k≤m*n b d) h α β ⟩
         h (lookup b α , lookup d β) ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------------
-- Elementary permutations in the Cauchy representation 

emptyperm : Permutation 0
emptyperm = (emptycauchy , f)
  where f : {i j : Fin 0} → (lookup i emptycauchy ≡ lookup j emptycauchy) → (i ≡ j)
        f {()}

idperm : (n : ℕ) → Permutation n
idperm n = (idcauchy n , λ {i} {j} p → fi≡fj i j id p)

-- Sequential composition

scompperm : ∀ {n} → Permutation n → Permutation n → Permutation n
scompperm {n} (α , f) (β , g) =
  (scompcauchy α β ,
   λ {i} {j} p → f (g (fi≡fj i j (λ i → lookup (lookup i α) β) p)))
         
-- swap the first m elements with the last n elements
-- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
-- ==> 
-- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

swap+cauchy< : (m n : ℕ) (i : Fin (m + n)) (i< : toℕ i < m) →
  lookup i (swap+cauchy m n) ≡ id+ {m} (raise n (fromℕ≤ i<))
swap+cauchy< m n i i< =
  let j = fromℕ≤ i< in
  let eq = inj₁-≡ i i< in
  begin 
    (lookup i (splitVOp+ {m} {n} {f = id+ {m}}) 
         ≡⟨ cong (flip lookup (splitVOp+ {m} {n} {f = id+ {m}})) eq ⟩
    lookup (inject+ n j)  (splitVOp+ {m} {n} {f = id+ {m}})
         ≡⟨ lookup-++-inject+  (tabulate (id+ {m} ∘ raise n)) (tabulate (id+ {m} ∘ inject+ m)) j ⟩
     lookup j (tabulate {m} (id+ {m} ∘ raise n))
          ≡⟨ lookup∘tabulate (id+ {m} ∘ raise n) j ⟩
     id+ {m} (raise n j) ∎)
  where open ≡-Reasoning

swap+cauchy≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) → 
  lookup i (swap+cauchy m n) ≡ subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥))
swap+cauchy≥ m n i i≥ =
  let j = reduce≥ i i≥ in
  let eq = inj₂-≡ i i≥ in
  let v = splitVOp+ {m} {f = id+ {m}} in
  begin (
    lookup i v
        ≡⟨ cong (flip lookup v) eq ⟩
    lookup (raise m j) v
        ≡⟨ lookup-++-raise (tabulate (id+ {m} ∘ raise n)) (tabulate (id+ {m} ∘ inject+ m)) j ⟩
    lookup j (tabulate (id+ {m} ∘ inject+ m))
        ≡⟨ lookup∘tabulate (id+ {m} ∘ inject+ m) j ⟩
    id+ {m} (inject+ m j) ∎)
  where open ≡-Reasoning

swap+perm' : (m n : ℕ) (i j : Fin (m + n))
  (p : lookup i (swap+cauchy m n) ≡ lookup j (swap+cauchy m n)) → (i ≡ j)
swap+perm' m n i j p with toℕ i <? m | toℕ j <? m 
... | yes i< | yes j< = toℕ-injective (cancel-+-left n {toℕ i} {toℕ j} ni≡nj)
  where ni≡nj = begin (n + toℕ i
                     ≡⟨ sym (raise< m n i i<)  ⟩
                       toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<)))
                     ≡⟨ cong toℕ (sym (swap+cauchy< m n i i<)) ⟩
                       toℕ (lookup i (swap+cauchy m n))
                     ≡⟨ cong toℕ p ⟩
                       toℕ (lookup j (swap+cauchy m n))
                     ≡⟨ cong toℕ (swap+cauchy< m n j j<) ⟩
                       toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ j<)))
                     ≡⟨ raise< m n j j< ⟩
                       n + toℕ j ∎)
               where open ≡-Reasoning
... | yes i< | no j≥ = ⊥-elim (1+n≰n contra')
  where contra : n + toℕ i ≡ toℕ j ∸ m
        contra = begin (n + toℕ i
                       ≡⟨ sym (raise< m n i i<) ⟩
                       toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<)))
                       ≡⟨ cong toℕ (sym (swap+cauchy< m n i i<)) ⟩ 
                       toℕ (lookup i (swap+cauchy m n))
                       ≡⟨ cong toℕ p ⟩
                       toℕ (lookup j (swap+cauchy m n))
                       ≡⟨ cong toℕ (swap+cauchy≥ m n j (≤-pred (≰⇒> j≥))) ⟩
                       toℕ (subst Fin (+-comm n m)
                             (inject+ m (reduce≥ j (≤-pred (≰⇒> j≥)))))
                       ≡⟨ inject≥ m n j (≤-pred (≰⇒> j≥)) ⟩
                       toℕ j ∸ m ∎)
                 where open ≡-Reasoning
        contra' : suc (m + n) ≤ m + n
        contra' = begin (suc (m + n)
                        ≤⟨ m≤m+n (suc (m + n)) (toℕ i) ⟩
                        suc (m + n) + toℕ i
                        ≡⟨ +-assoc (suc m) n (toℕ i) ⟩ 
                        suc (m + (n + toℕ i))
                        ≡⟨ cong (λ x → suc m + x) contra ⟩ 
                        suc (m + (toℕ j ∸ m))
                        ≡⟨ cong suc (sym (+-∸-assoc m (≤-pred (≰⇒> j≥))))  ⟩ 
                        suc ((m + toℕ j) ∸ m)
                        ≡⟨ cong (λ x → suc (x ∸ m)) (+-comm m (toℕ j)) ⟩ 
                        suc ((toℕ j + m) ∸ m)
                        ≡⟨ cong suc (m+n∸n≡m (toℕ j) m) ⟩
                        suc (toℕ j)
                        ≤⟨ bounded j ⟩
                        m + n ∎)
                  where open ≤-Reasoning
... | no i≥ | yes j< = ⊥-elim (1+n≰n contra')
  where contra : n + toℕ j ≡ toℕ i ∸ m
        contra = begin (n + toℕ j
                       ≡⟨ sym (raise< m n j j<) ⟩
                       toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ j<)))
                       ≡⟨ cong toℕ (sym (swap+cauchy< m n j j<)) ⟩ 
                       toℕ (lookup j (swap+cauchy m n))
                       ≡⟨ cong toℕ (sym p) ⟩
                       toℕ (lookup i (swap+cauchy m n))
                       ≡⟨ cong toℕ (swap+cauchy≥ m n i (≤-pred (≰⇒> i≥))) ⟩
                       toℕ (subst Fin (+-comm n m)
                             (inject+ m (reduce≥ i (≤-pred (≰⇒> i≥)))))
                       ≡⟨ inject≥ m n i (≤-pred (≰⇒> i≥)) ⟩
                       toℕ i ∸ m ∎)
                 where open ≡-Reasoning
        contra' : suc (m + n) ≤ m + n
        contra' = begin (suc (m + n)
                        ≤⟨ m≤m+n (suc (m + n)) (toℕ j) ⟩
                        suc (m + n) + toℕ j
                        ≡⟨ +-assoc (suc m) n (toℕ j) ⟩ 
                        suc (m + (n + toℕ j))
                        ≡⟨ cong (λ x → suc m + x) contra ⟩ 
                        suc (m + (toℕ i ∸ m))
                        ≡⟨ cong suc (sym (+-∸-assoc m (≤-pred (≰⇒> i≥))))  ⟩ 
                        suc ((m + toℕ i) ∸ m)
                        ≡⟨ cong (λ x → suc (x ∸ m)) (+-comm m (toℕ i)) ⟩ 
                        suc ((toℕ i + m) ∸ m)
                        ≡⟨ cong suc (m+n∸n≡m (toℕ i) m) ⟩
                        suc (toℕ i)
                        ≤⟨ bounded i ⟩
                        m + n ∎)
                  where open ≤-Reasoning
... | no i≥ | no j≥ = ∸≡ m n i j (≤-pred (≰⇒> i≥)) (≤-pred (≰⇒> j≥)) ri≡rj
  where ri≡rj = begin (toℕ i ∸ m
                       ≡⟨ sym (inject≥ m n i (≤-pred (≰⇒> i≥))) ⟩ 
                       toℕ (subst Fin (+-comm n m)
                             (inject+ m (reduce≥ i (≤-pred (≰⇒> i≥)))))
                       ≡⟨ cong toℕ (sym (swap+cauchy≥ m n i (≤-pred (≰⇒> i≥)))) ⟩
                       toℕ (lookup i (swap+cauchy m n))
                       ≡⟨ cong toℕ p ⟩
                       toℕ (lookup j (swap+cauchy m n))
                       ≡⟨ cong toℕ (swap+cauchy≥ m n j (≤-pred (≰⇒> j≥)))  ⟩
                       toℕ (subst Fin (+-comm n m)
                             (inject+ m (reduce≥ j (≤-pred (≰⇒> j≥)))))
                       ≡⟨ inject≥ m n j (≤-pred (≰⇒> j≥)) ⟩ 
                       toℕ j ∸ m ∎)
                where open ≡-Reasoning

swap+perm : (m n : ℕ) → Permutation (m + n)
swap+perm m n = (swap+cauchy m n , λ {i} {j} p → swap+perm' m n i j p)

-- Parallel additive composition 
-- append both permutations but adjust the indices in the second
-- permutation by the size of the first type so that it acts on the
-- second part of the vector

pcompperm' : (m n : ℕ) (i j : Fin (m + n))
  (α : Cauchy m) (β : Cauchy n)
  (p : lookup i (pcompcauchy α β) ≡ lookup j (pcompcauchy α β))
  (f : {i j : Fin m} → lookup i α ≡ lookup j α → i ≡ j)
  (g : {i j : Fin n} → lookup i β ≡ lookup j β → i ≡ j) → i ≡ j
pcompperm' m n i j α β p f g with toℕ i <? m | toℕ j <? m
... | yes i< | yes j< = fromℕ≤-inj m (m + n) i j i< j< (f (toℕ-injective li≡lj))
  where li≡lj = begin (toℕ (lookup (fromℕ≤ i<) α)
                       ≡⟨ inject+-lemma n (lookup (fromℕ≤ i<) α) ⟩
                       toℕ (inject+ n (lookup (fromℕ≤ i<) α))
                       ≡⟨ cong toℕ (sym (lookup-map (fromℕ≤ i<) (inject+ n) α)) ⟩
                       toℕ (lookup (fromℕ≤ i<) (mapV (inject+ n) α))
                       ≡⟨ cong toℕ (sym (lookup-++-<
                                      (mapV (inject+ n) α)
                                      (mapV (raise m) β)
                                      i i<)) ⟩
                       toℕ (lookup i (mapV (inject+ n) α ++V mapV (raise m) β))
                       ≡⟨ cong toℕ p ⟩
                       toℕ (lookup j (mapV (inject+ n) α ++V mapV (raise m) β))
                       ≡⟨ cong toℕ (lookup-++-<
                                     (mapV (inject+ n) α)
                                     (mapV (raise m) β)
                                     j j<) ⟩
                       toℕ (lookup (fromℕ≤ j<) (mapV (inject+ n) α))
                       ≡⟨ cong toℕ (lookup-map (fromℕ≤ j<) (inject+ n) α) ⟩
                       toℕ (inject+ n (lookup (fromℕ≤ j<) α))
                       ≡⟨ sym (inject+-lemma n (lookup (fromℕ≤ j<) α)) ⟩
                       toℕ (lookup (fromℕ≤ j<) α) ∎)
                where open ≡-Reasoning
... | yes i< | no j≥ = ⊥-elim (1+n≰n contra')
  where contra = begin (toℕ (lookup (fromℕ≤ i<) α)
                       ≡⟨ inject+-lemma n (lookup (fromℕ≤ i<) α) ⟩
                       toℕ (inject+ n (lookup (fromℕ≤ i<) α))
                       ≡⟨ cong toℕ (sym (lookup-map (fromℕ≤ i<) (inject+ n) α)) ⟩
                       toℕ (lookup (fromℕ≤ i<) (mapV (inject+ n) α))
                       ≡⟨ cong toℕ (sym (lookup-++-<
                                      (mapV (inject+ n) α)
                                      (mapV (raise m) β)
                                      i i<)) ⟩
                       toℕ (lookup i (mapV (inject+ n) α ++V mapV (raise m) β))
                       ≡⟨ cong toℕ p ⟩
                       toℕ (lookup j (mapV (inject+ n) α ++V mapV (raise m) β))
                       ≡⟨ cong toℕ (lookup-++-≥
                                     (mapV (inject+ n) α)
                                     (mapV (raise m) β)
                                     j (≤-pred (≰⇒> j≥))) ⟩
                       toℕ (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) (mapV (raise m) β))
                       ≡⟨ cong toℕ
                           (lookup-map (reduce≥ j (≤-pred (≰⇒> j≥))) (raise m) β) ⟩
                       toℕ (raise m (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) β))
                       ≡⟨ toℕ-raise m (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) β) ⟩ 
                       m + toℕ (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) β) ∎)
                 where open ≡-Reasoning
        contra' = begin (suc (toℕ (lookup (fromℕ≤ i<) α))
                        ≤⟨ lookup-bounded m m (fromℕ≤ i<) α ⟩ 
                        m 
                        ≤⟨ m≤m+n m (toℕ (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) β)) ⟩ 
                        m + toℕ (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) β)
                        ≡⟨ sym contra ⟩ 
                        toℕ (lookup (fromℕ≤ i<) α) ∎)
                  where open ≤-Reasoning
... | no i≥ | yes j< = ⊥-elim (1+n≰n contra')
  where contra = begin (m + toℕ (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) β)
                       ≡⟨ sym (toℕ-raise m (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) β)) ⟩ 
                       toℕ (raise m (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) β))
                       ≡⟨ cong toℕ
                           (sym (lookup-map (reduce≥ i (≤-pred (≰⇒> i≥))) (raise m) β)) ⟩
                       toℕ (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) (mapV (raise m) β))
                       ≡⟨ cong toℕ (sym (lookup-++-≥
                                      (mapV (inject+ n) α)
                                      (mapV (raise m) β)
                                      i (≤-pred (≰⇒> i≥)))) ⟩
                       toℕ (lookup i (mapV (inject+ n) α ++V mapV (raise m) β))
                       ≡⟨ cong toℕ p ⟩
                       toℕ (lookup j (mapV (inject+ n) α ++V mapV (raise m) β))
                       ≡⟨ cong toℕ (lookup-++-<
                                     (mapV (inject+ n) α)
                                     (mapV (raise m) β)
                                     j j<) ⟩
                       toℕ (lookup (fromℕ≤ j<) (mapV (inject+ n) α))
                       ≡⟨ cong toℕ (lookup-map (fromℕ≤ j<) (inject+ n) α) ⟩
                       toℕ (inject+ n (lookup (fromℕ≤ j<) α))
                       ≡⟨ sym (inject+-lemma n (lookup (fromℕ≤ j<) α)) ⟩
                        toℕ (lookup (fromℕ≤ j<) α) ∎)
                 where open ≡-Reasoning
        contra' = begin (suc (toℕ (lookup (fromℕ≤ j<) α))
                        ≤⟨ lookup-bounded m m (fromℕ≤ j<) α ⟩ 
                        m 
                        ≤⟨ m≤m+n m (toℕ (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) β)) ⟩ 
                        m + toℕ (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) β)
                        ≡⟨ contra ⟩ 
                        toℕ (lookup (fromℕ≤ j<) α) ∎)
                  where open ≤-Reasoning
... | no i≥ | no j≥ =
  reduce≥-inj m n i j (≤-pred (≰⇒> i≥)) (≤-pred (≰⇒> j≥))
    (g (toℕ-injective (cancel-+-left m li≡lj)))
  where li≡lj = begin (m + toℕ (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) β)
                       ≡⟨ sym (toℕ-raise m (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) β)) ⟩ 
                       toℕ (raise m (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) β))
                       ≡⟨ cong toℕ
                           (sym (lookup-map (reduce≥ i (≤-pred (≰⇒> i≥))) (raise m) β)) ⟩
                       toℕ (lookup (reduce≥ i (≤-pred (≰⇒> i≥))) (mapV (raise m) β))
                       ≡⟨ cong toℕ (sym (lookup-++-≥
                                      (mapV (inject+ n) α)
                                      (mapV (raise m) β)
                                      i (≤-pred (≰⇒> i≥)))) ⟩
                       toℕ (lookup i (mapV (inject+ n) α ++V mapV (raise m) β))
                       ≡⟨ cong toℕ p ⟩
                       toℕ (lookup j (mapV (inject+ n) α ++V mapV (raise m) β))
                       ≡⟨ cong toℕ (lookup-++-≥
                                     (mapV (inject+ n) α)
                                     (mapV (raise m) β)
                                     j (≤-pred (≰⇒> j≥))) ⟩
                       toℕ (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) (mapV (raise m) β))
                       ≡⟨ cong toℕ
                           (lookup-map (reduce≥ j (≤-pred (≰⇒> j≥))) (raise m) β) ⟩
                       toℕ (raise m (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) β))
                       ≡⟨ toℕ-raise m (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) β) ⟩ 
                       m + toℕ (lookup (reduce≥ j (≤-pred (≰⇒> j≥))) β) ∎)
                where open ≡-Reasoning

pcompperm : ∀ {m n} → Permutation m → Permutation n → Permutation (m + n)
pcompperm {m} {n} (α , f) (β , g) = 
  (pcompcauchy α β , λ {i} {j} p → pcompperm' m n i j α β p f g)

-- Tensor multiplicative composition
-- Transpositions in α correspond to swapping entire rows
-- Transpositions in β correspond to swapping entire columns

tcompperm' : (m n : ℕ) (i j : Fin (m * n)) (α : Cauchy m) (β : Cauchy n) 
  (f : {i j : Fin m} → lookup i α ≡ lookup j α → i ≡ j)
  (g : {i j : Fin n} → lookup i β ≡ lookup j β → i ≡ j) 
  (p : lookup i (tcompcauchy α β) ≡ lookup j (tcompcauchy α β)) → (i ≡ j)
tcompperm' m n i j α β f g p =
  let fin-result bi di deci deci' = fin-divMod m n i
      fin-result bj dj decj decj' = fin-divMod m n j
      (lookb≡ , lookd≡) = fin-addMul-lemma
                            m n (lookup bi α) (lookup bj α)
                            (lookup di β) (lookup dj β) sp
      (b≡ , d≡) = (f {bi} {bj} lookb≡ , g {di} {dj} lookd≡)
      bn+d≡ = cong₂ (λ b d → toℕ d + toℕ b * n) b≡ d≡
  in toℕ-injective (trans deci (trans bn+d≡ (sym decj)))
  where sp = let fin-result bi di deci deci' = fin-divMod m n i
                 fin-result bj dj decj decj' = fin-divMod m n j in 
             begin (let b' = lookup bi α
                        d' = lookup di β
                     in toℕ b' * n + toℕ d'
                   ≡⟨ sym (to-from _) ⟩
                   toℕ
                     (let b' = lookup bi α
                          d' = lookup di β
                      in fromℕ (toℕ b' * n + toℕ d'))
                   ≡⟨ sym (inject≤-lemma _ _) ⟩ 
                   toℕ
                     (let b' = lookup bi α
                          d' = lookup di β
                      in inject≤
                           (fromℕ (toℕ b' * n + toℕ d'))
                           (i*n+k≤m*n b' d'))
                   ≡⟨ cong toℕ
                        (sym (lookup-2d m n i α β
                             (λ {(b , d) → inject≤
                                             (fromℕ (toℕ b * n + toℕ d))
                                             (i*n+k≤m*n b d)}))) ⟩ 
                   toℕ (lookup i (tcompcauchy α β))
                   ≡⟨ cong toℕ p ⟩
                   toℕ (lookup j (tcompcauchy α β))
                   ≡⟨ cong toℕ
                        (lookup-2d m n j α β
                          (λ {(b , d) → inject≤
                                          (fromℕ (toℕ b * n + toℕ d))
                                          (i*n+k≤m*n b d)})) ⟩ 
                   toℕ
                     (let b' = lookup bj α
                          d' = lookup dj β
                      in inject≤
                           (fromℕ (toℕ b' * n + toℕ d'))
                           (i*n+k≤m*n b' d'))
                   ≡⟨ inject≤-lemma _ _ ⟩ 
                   toℕ
                     (let b' = lookup bj α
                          d' = lookup dj β
                      in fromℕ (toℕ b' * n + toℕ d'))
                   ≡⟨ to-from _ ⟩ 
                   let b' = lookup bj α
                       d' = lookup dj β
                   in toℕ b' * n + toℕ d' ∎)
             where open ≡-Reasoning

tcompperm : ∀ {m n} → Permutation m → Permutation n → Permutation (m * n)
tcompperm {m} {n} (α , f) (β , g) =
  (tcompcauchy α β , λ {i} {j} p → tcompperm' m n i j α β f g p)

-- swap⋆ 
-- 
-- This is essentially the classical problem of in-place matrix transpose:
-- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
-- Given m and n, the desired permutation in Cauchy representation is:
-- P(i) = m*n-1 if i=m*n-1
--      = m*i mod m*n-1 otherwise

transpose≡ : (m n : ℕ) (i j : Fin (m * n)) (bi bj : Fin m) (di dj : Fin n)
             (deci : toℕ i ≡ toℕ di + toℕ bi * n)
             (decj : toℕ j ≡ toℕ dj + toℕ bj * n)
             (tpr : transposeIndex m n bi di ≡ transposeIndex m n bj dj) → (i ≡ j)
transpose≡ m n i j bi bj di dj deci decj tpr =
  let (d≡ , b≡) = fin-addMul-lemma n m di dj bi bj stpr
      d+bn≡ = cong₂ (λ x y → toℕ x + toℕ y * n) d≡ b≡
  in toℕ-injective (trans deci (trans d+bn≡ (sym decj)))
  where stpr = begin (toℕ di * m + toℕ bi
                      ≡⟨ sym (to-from _) ⟩
                      toℕ (fromℕ (toℕ di * m + toℕ bi))
                      ≡⟨ sym (inject≤-lemma _ _) ⟩
                      toℕ (inject≤
                        (fromℕ (toℕ di * m + toℕ bi))
                        (trans≤
                          (i*n+k≤m*n di bi)
                          (refl′ (*-comm n m))))
                      ≡⟨ cong toℕ tpr ⟩
                      toℕ (inject≤
                        (fromℕ (toℕ dj * m + toℕ bj))
                        (trans≤
                          (i*n+k≤m*n dj bj)
                          (refl′ (*-comm n m))))
                      ≡⟨ inject≤-lemma _ _ ⟩
                      toℕ (fromℕ (toℕ dj * m + toℕ bj))
                      ≡⟨ to-from _ ⟩
                      toℕ dj * m + toℕ bj ∎)
               where open ≡-Reasoning

swap⋆perm' : (m n : ℕ) (i j : Fin (m * n))
             (p : lookup i (swap⋆cauchy m n) ≡ lookup j (swap⋆cauchy m n)) → (i ≡ j)
swap⋆perm' m n i j p =
  let fin-result bi di deci _ = fin-divMod m n i 
      fin-result bj dj decj _ = fin-divMod m n j
  in transpose≡ m n i j bi bj di dj deci decj pr
  where pr = let fin-result bi di _ _ = fin-divMod m n i 
                 fin-result bj dj _ _ = fin-divMod m n j in
             begin (transposeIndex m n bi di
                    ≡⟨ cong₂ (transposeIndex m n)
                         (sym (lookup-allFin bi)) (sym (lookup-allFin di)) ⟩
                    transposeIndex m n (lookup bi (allFin m)) (lookup di (allFin n))
                    ≡⟨ sym (lookup-2d m n i (allFin m) (allFin n)
                             (λ {(b , d) → transposeIndex m n b d})) ⟩
                    lookup i
                      (concatV (mapV
                        (λ b → mapV (λ d → transposeIndex m n b d) (allFin n))
                        (allFin m)))
                    ≡⟨ p ⟩ 
                    lookup j
                      (concatV (mapV
                        (λ b → mapV (λ d → transposeIndex m n b d) (allFin n))
                        (allFin m)))
                    ≡⟨ lookup-2d m n j (allFin m) (allFin n)
                         (λ {(b , d) → transposeIndex m n b d}) ⟩
                    transposeIndex m n (lookup bj (allFin m)) (lookup dj (allFin n))
                    ≡⟨ cong₂ (transposeIndex m n)
                         (lookup-allFin bj) (lookup-allFin dj) ⟩
                    transposeIndex m n bj dj ∎)
             where open ≡-Reasoning

swap⋆perm : (m n : ℕ) → Permutation (m * n)
swap⋆perm m n = (swap⋆cauchy m n , λ {i} {j} p → swap⋆perm' m n i j p)

------------------------------------------------------------------------------
