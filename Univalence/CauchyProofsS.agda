{-# OPTIONS --without-K #-}

module CauchyProofsS where

-- Proofs about permutations defined in module Cauchy (multiplicative2)

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat.Properties
  using (m≤m+n; n≤m+n; n≤1+n; cancel-+-left; cancel-*-right; strictTotalOrder; 
         cancel-*-right-≤; ≰⇒>; ¬i+1+j≤i; 1+n≰n; ≤⇒pred≤)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)
open import Data.Nat.DivMod using (DivMod; result; _divMod_; _div_; _mod_)
open import Relation.Binary
  using (Rel; Decidable; Setoid; StrictTotalOrder; IsStrictTotalOrder;
         tri<; tri≈; tri>)
open import Relation.Binary.Core using (Transitive; _⇒_)

open import Data.String using (String)
  renaming (_++_ to _++S_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; false; true; _∨_)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  _≥_; z≤n; s≤s; _≟_; _≤?_; ≤-pred; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤; _ℕ-_; _≺_; reduce≥; 
         raise; inject+; inject₁; inject≤; _≻toℕ_; #_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties
  using (bounded; inject+-lemma; to-from; toℕ-injective; inject≤-lemma;
         toℕ-fromℕ≤; fromℕ≤-toℕ)
open import Data.Vec.Properties 
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin; tabulate-∘; 
         tabulate-allFin; allFin-map; lookup-++-inject+; lookup-++-≥;
         module UsingVectorEquality)
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
open import Function using (id; _∘_; _$_; _∋_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import DivModUtils using (mod-lemma) 
open import Proofs
open import Cauchy
open import Perm
open import CauchyProofs
open import CauchyProofsT

------------------------------------------------------------------------------
-- Main lemma swap⋆idemp

subst-allFin : ∀ {m n} → (eq : m ≡ n) → subst Cauchy eq (allFin m) ≡ allFin n
subst-allFin refl = refl

concat-simplify : {A : Set} → (m n : ℕ) → (f : Fin (suc m) → Vec A (suc n)) → 
  concatV (mapV f (allFin (suc m))) ≡
  f zero ++V concatV (mapV (f ∘ suc) (allFin m))
concat-simplify m n f = 
  begin (concatV (mapV f (allFin (suc m)))
        ≡⟨ cong
            (λ x → concatV (mapV f x))
            (allFin-map m) ⟩ 
         concatV (mapV f (zero ∷ mapV suc (allFin m)))
        ≡⟨ refl ⟩
         concatV (f zero ∷ mapV f (mapV suc (allFin m)))
        ≡⟨ cong (λ x → concatV (f zero ∷ x)) (sym (map-∘ f suc (allFin m))) ⟩
          f zero ++V concatV (mapV (λ a → f (suc a)) (allFin m)) ∎)
  where open ≡-Reasoning

concat-simplify-inject : {A : Set} → (m n : ℕ) (i : Fin (suc (suc n))) →
  (f : Fin (suc (suc m)) → Vec A (suc (suc n))) → 
  lookup
    (inject+ (suc m * suc (suc n)) i)
    (concatV (mapV f (allFin (suc (suc m))))) ≡
  lookup i (f zero)
concat-simplify-inject m n i f = 
  begin (lookup
           (inject+ (suc m * suc (suc n)) i)
           (concatV (mapV f (allFin (suc (suc m)))))
        ≡⟨ cong
             (lookup (inject+ (suc m * suc (suc n)) i))
             (concat-simplify (suc m) (suc n) f) ⟩ 
         lookup
           (inject+ (suc m * suc (suc n)) i)
           (f zero ++V concatV (mapV (λ a → f (suc a)) (allFin (suc m))))
        ≡⟨ lookup-++-inject+ 
             (f zero) (concatV (mapV (λ a → f (suc a)) (allFin (suc m)))) i ⟩
          lookup i (f zero) ∎)
  where open ≡-Reasoning

concat-simplify-raise : {A : Set} → (m n : ℕ) (i : Fin (suc m * suc (suc n))) → 
  (f : Fin (suc (suc m)) → Vec A (suc (suc n))) → 
  lookup
    (raise (suc (suc n)) i)
    (concatV (mapV f (allFin (suc (suc m))))) ≡
  lookup i (concatV (mapV (λ a → f (suc a)) (allFin (suc m))))
concat-simplify-raise m n i f =
  begin (lookup
           (raise (suc (suc n)) i)
           (concatV (mapV f (allFin (suc (suc m)))))
        ≡⟨ cong
            (lookup (raise (suc (suc n)) i))
            (concat-simplify (suc m) (suc n) f) ⟩ 
         lookup
           (raise (suc (suc n)) i)
           (f zero ++V concatV (mapV (λ a → f (suc a)) (allFin (suc m))))
         ≡⟨ lookup-++-raise
             (f zero) (concatV (mapV (λ a → f (suc a)) (allFin (suc m)))) i ⟩ 
         lookup i (concatV (mapV (λ a → f (suc a)) (allFin (suc m)))) ∎) 
  where open ≡-Reasoning

lookup-subst-1 : ∀ {m m'} 
  (i : Fin m') (xs : Vec (Fin m) m) (eq : m ≡ m') (eq' : m' ≡ m)
  (irr : sym eq ≡ eq') → 
  lookup i (subst (λ s → Vec (Fin s) s) eq xs) ≡ 
  subst Fin eq (lookup (subst Fin eq' i) xs)
lookup-subst-1 i xs refl .refl refl = refl 

subst-inject-mod : ∀ {n m m'} → (eq : suc (suc m) ≡ suc (suc m')) → 
  subst Fin eq (inject≤ (n mod (suc m)) (i≤si (suc m))) ≡
  inject≤ (n mod (suc m')) (i≤si (suc m'))
subst-inject-mod refl = refl
  
cmp = IsStrictTotalOrder.compare
        (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)

max-b-d : (m n : ℕ) → (b : Fin (suc (suc m))) (d : Fin (suc (suc n))) →
  (p= : suc (toℕ b * suc (suc n) + toℕ d) ≡ suc (suc m) * suc (suc n)) → 
  (toℕ b ≡ suc m × toℕ d ≡ suc n)
max-b-d m n b d p= with cmp (toℕ b) (suc m) | cmp (toℕ d) (suc n)
max-b-d m n b d p= | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ = ⊥-elim (1+n≰n contra)
  where contra = begin (1 + suc (toℕ b * suc (suc n) + toℕ d)
                        ≡⟨ cong suc (sym (+-suc (toℕ b * suc (suc n)) (toℕ d))) ⟩
                        1 + (toℕ b * suc (suc n) + suc (toℕ d))
                        ≡⟨ sym (+-suc (toℕ b * suc (suc n)) (suc (toℕ d))) ⟩
                        toℕ b * suc (suc n) + suc (suc (toℕ d))
                        ≤⟨ cong+l≤ (s≤s a₁) (toℕ b * suc (suc n)) ⟩ 
                        toℕ b * suc (suc n) + suc (suc n)
                        ≡⟨ +-comm (toℕ b * suc (suc n)) (suc (suc n)) ⟩ 
                        suc (toℕ b) * suc (suc n)
                        ≤⟨ cong*r≤ (≰⇒> ¬c) (suc (suc n)) ⟩ 
                        suc (suc m) * suc (suc n)
                        ≡⟨ sym p= ⟩ 
                        suc (toℕ b * suc (suc n) + toℕ d) ∎)
                 where open ≤-Reasoning
max-b-d m n b d p= | tri< a ¬b= ¬c | tri≈ ¬a d= ¬c₁ =
  ⊥-elim (¬b= (cancel-+-left 1
    (cancel-*-right (suc (toℕ b)) (suc (suc m)) {suc n} contra)))
  where
    contra : suc (toℕ b) * suc (suc n) ≡ suc (suc m) * suc (suc n)
    contra = begin (suc (toℕ b) * suc (suc n)
                   ≡⟨  refl ⟩
                   suc (suc n) + toℕ b * suc (suc n)
                   ≡⟨  +-comm (suc (suc n)) (toℕ b * suc (suc n)) ⟩
                   toℕ b * suc (suc n) + suc (suc n)
                   ≡⟨  +-suc (toℕ b * suc (suc n)) (suc n) ⟩
                   suc (toℕ b * suc (suc n) + suc n)
                   ≡⟨  cong (λ x → suc (toℕ b * suc (suc n) + x)) (sym d=) ⟩
                   suc (toℕ b * suc (suc n) + toℕ d)
                   ≡⟨  p= ⟩
                   suc (suc m) * suc (suc n) ∎)
             where open ≡-Reasoning
max-b-d m n b d p= | tri< a ¬b ¬c | tri> ¬a ¬b₁ c =
  ⊥-elim (1+n≰n (trans≤ (bounded d) c))
max-b-d m n b d p= | tri≈ ¬a b= ¬c | tri< a ¬d= ¬c₁ =
  ⊥-elim (¬d= (cancel-+-left 1
    (cancel-+-left (suc m * suc (suc n)) contra))) 
  where
     contra : suc m * suc (suc n) + suc (toℕ d) ≡ suc m * suc (suc n) + suc (suc n)
     contra = begin (suc m * suc (suc n) + suc (toℕ d)
                    ≡⟨ cong (λ x → x * suc (suc n) + suc (toℕ d)) (sym b=) ⟩ 
                    toℕ b * suc (suc n) + suc (toℕ d)
                    ≡⟨ +-suc (toℕ b * suc (suc n)) (toℕ d) ⟩ 
                    suc (toℕ b * suc (suc n) + toℕ d)
                    ≡⟨ p= ⟩ 
                    suc (suc m) * suc (suc n)
                    ≡⟨ +-comm (suc (suc n)) (suc m * suc (suc n)) ⟩
                    suc m * suc (suc n) + suc (suc n) ∎)
              where open ≡-Reasoning
max-b-d m n b d p= | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ = (b₁ , b₂)
max-b-d m n b d p= | tri≈ ¬a b₁ ¬c | tri> ¬a₁ ¬b c =
  ⊥-elim (1+n≰n (trans≤ (bounded d) c))
max-b-d m n b d p= | tri> ¬a ¬b c | tri< a ¬b₁ ¬c =
  ⊥-elim (1+n≰n (trans≤ (bounded b) c))
max-b-d m n b d p= | tri> ¬a ¬b c | tri≈ ¬a₁ b₁ ¬c =
  ⊥-elim (1+n≰n (trans≤ (bounded b) c))
max-b-d m n b d p= | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ =
  ⊥-elim (1+n≰n (trans≤ (bounded d) c₁)) 

subst-fin : (a b : ℕ) → (eq : suc a ≡ suc b) → subst Fin eq (fromℕ a) ≡ fromℕ b
subst-fin a .a refl = refl

lookup-fromℕ-allFin : {A : Set} → (n : ℕ) → (f : Fin (suc n) → A) → 
  lookup (fromℕ n) (tabulate {suc n} f) ≡ f (fromℕ n)
lookup-fromℕ-allFin 0 f = refl
lookup-fromℕ-allFin (suc n) f = lookup-fromℕ-allFin n (f ∘ suc) 
             
fin=1 : (m n : ℕ) → 
  fromℕ (suc m + suc n * suc (suc m)) ≡
  fromℕ (suc (m + suc (suc (m + n * suc (suc m)))))
fin=1 m n = toℕ-injective p
  where p = begin (toℕ (fromℕ (suc m + suc n * suc (suc m)))
                 ≡⟨ to-from (suc m + suc n * suc (suc m)) ⟩
                   suc m + suc n * suc (suc m)
                 ≡⟨ refl ⟩
                   suc (m + suc (suc (m + n * suc (suc m))))
                ≡⟨ sym (to-from (suc (m + suc (suc (m + n * suc (suc m)))))) ⟩
                   toℕ (fromℕ (suc (m + suc (suc (m + n * suc (suc m)))))) ∎)
            where open ≡-Reasoning

concat-map-map-tabulate : (m n : ℕ) → (f : Fin m × Fin n → Fin (m * n)) → 
  concatV (mapV (λ b → mapV (λ d → f (b , d)) (allFin n)) (allFin m)) ≡ 
  tabulate (λ k → f (fin-project m n k))
concat-map-map-tabulate m n f =
  begin (concatV (mapV (λ b → mapV (λ d → f (b , d)) (allFin n)) (allFin m))
       ≡⟨ cong concatV (sym (tabulate-∘ (λ b → mapV (λ d → f (b , d)) (allFin n)) id)) ⟩
         concatV (tabulate (λ b → mapV (λ d → f (b , d)) (allFin n)))
       ≡⟨ cong concatV
            (finext (λ b → sym (tabulate-∘ (λ d → f (b , d)) id))) ⟩
         concatV (tabulate (λ b → tabulate (λ d → f (b , d))))
       ≡⟨ tabulate-concat f ⟩
         tabulate (λ k → f (fin-project m n k)) ∎)
  where open ≡-Reasoning

fin-project-2 : (n m : ℕ) →
 fin-project (suc (suc n)) (suc (suc m)) (fromℕ (suc m + suc n * suc (suc m)))
 ≡ (fromℕ (suc n) , fromℕ (suc m))
fin-project-2 n m with toℕ (fromℕ (suc m + suc n * suc (suc m))) divMod (suc (suc m))
fin-project-2 n m | result q r k≡r+q*sn with suc (suc n) ≤? q
fin-project-2 n m | result q r k≡r+q*sn | yes p =
  ⊥-elim (absurd (suc n) (suc m) q r (fromℕ (suc m + suc n * suc (suc m))) k≡r+q*sn p)
fin-project-2 n m | result q r k≡r+q*sn | no ¬p = 
  let (b= , d=) = max-b-d n m (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) r pr
  in cong₂ _,_
       (toℕ-injective (trans b= (sym (to-from (suc n)))))
       (toℕ-injective (trans d= (sym (to-from (suc m)))))
  where 
        pr : suc (toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) * suc (suc m) + toℕ r) ≡
             suc (suc n) * suc (suc m)
        pr = 
          begin (_
-- agda bug?
-- replacing _ by the actual term:
-- suc (toℕ (fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) * suc (suc m) + toℕ r)
-- gives an occurs check error
                 ≡⟨ cong
                      (λ x → suc (x * suc (suc m) + toℕ r))
                      (toℕ-fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) ⟩ 
                 suc (q * suc (suc m) + toℕ r)
                 ≡⟨ cong suc (+-comm (q * suc (suc m)) (toℕ r)) ⟩
                 suc (toℕ r + q * suc (suc m))
                 ≡⟨ cong suc (sym k≡r+q*sn) ⟩ 
                 suc (suc (toℕ (fromℕ (m + suc (suc (m + n * suc (suc m)))))))
                 ≡⟨ cong
                     (λ x → suc (suc x))
                     (to-from (m + suc (suc (m + n * suc (suc m))))) ⟩ 
                 suc (suc n) * suc (suc m) ∎)
          where open ≡-Reasoning

-- index (b,d) in matrix becomes (d,b) in transpose
-- And yes, it is obvious:
-- (b*n+d)*m = b*n*m + d*m            -- expand
--           = b*(n*m -1) + b*1 + d*m -- add 0 = b*1 - b*1
--           = b + d*m                -- modulus

num-lem : (m n : ℕ) → (b : Fin (suc (suc m))) → (d : Fin (suc (suc n))) →
  (((toℕ b * suc (suc n)) + toℕ d) * (suc (suc m))) ≡
  (toℕ d * suc (suc m) + toℕ b) + toℕ b * suc (m + suc n * suc (suc m))
num-lem m n b d = 
  begin (((toℕ b * suc (suc n)) + toℕ d) * suc (suc m)
        ≡⟨ distribʳ-*-+ (suc (suc m)) (toℕ b * suc (suc n)) (toℕ d) ⟩ 
         (toℕ b * suc (suc n)) * suc (suc m) + toℕ d * suc (suc m)
        ≡⟨ cong
            (λ x → x + toℕ d * suc (suc m))
            (trans
              (*-assoc (toℕ b) (suc (suc n)) (suc (suc m)))
              (*-comm (toℕ b) (suc (suc n) * suc (suc m)))) ⟩ 
         (suc (suc n) * suc (suc m)) * toℕ b + toℕ d * suc (suc m)
        ≡⟨ refl ⟩ 
         suc (suc m + suc n * suc (suc m)) * toℕ b + toℕ d * suc (suc m)
        ≡⟨ refl ⟩ 
         (toℕ b + (suc m + suc n * suc (suc m)) * toℕ b) + toℕ d * suc (suc m)
         ≡⟨ cong
              (λ x → x + toℕ d * suc (suc m))
              (+-comm (toℕ b) ((suc m + suc n * suc (suc m)) * toℕ b)) ⟩ 
         ((suc m + suc n * suc (suc m)) * toℕ b + toℕ b) + toℕ d * suc (suc m)
        ≡⟨ +-assoc
            ((suc m + suc n * suc (suc m)) * toℕ b)
            (toℕ b)
            (toℕ d * suc (suc m)) ⟩ 
         (suc m + suc n * suc (suc m)) * toℕ b + (toℕ b + toℕ d * suc (suc m))
        ≡⟨ cong₂ _+_
            (*-comm (suc m + suc n * suc (suc m)) (toℕ b))
            (+-comm (toℕ b) (toℕ d * suc (suc m))) ⟩ 
        toℕ b * (suc m + suc n * suc (suc m)) + (toℕ d * suc (suc m) + toℕ b) 
        ≡⟨ +-comm
             (toℕ b * (suc m + suc n * suc (suc m)))
             (toℕ d * suc (suc m) + toℕ b) ⟩ 
        (toℕ d * suc (suc m) + toℕ b) + toℕ b * (suc m + suc n * suc (suc m)) ∎)
  where open ≡-Reasoning

mod-lem : (m n : ℕ) → (b : Fin (suc (suc m))) → (d : Fin (suc (suc n))) →
      (leq : suc (toℕ d * suc (suc m) + toℕ b) ≤ suc m + suc n * suc (suc m)) → 
      ((((toℕ b * suc (suc n)) + toℕ d) * (suc (suc m)))
        mod (suc m + suc n * suc (suc m)))
    ≡ inject≤ (fromℕ (toℕ d * suc (suc m) + toℕ b)) leq
mod-lem m n b d leq = 
  begin (((((toℕ b * suc (suc n)) + toℕ d) * (suc (suc m)))
               mod (suc m + suc n * suc (suc m)))
         ≡⟨ cong
             (λ x → x mod (suc m + suc n * suc (suc m)))
             (num-lem m n b d) ⟩ 
         (((toℕ d * suc (suc m) + toℕ b) + (toℕ b * (suc m + suc n * suc (suc m))))
               mod (suc m + suc n * suc (suc m)))
          ≡⟨ cong
              (λ x → ((x + (toℕ b * (suc m + suc n * suc (suc m))))
                     mod (suc m + suc n * suc (suc m))))
             (trans
                (sym (to-from (toℕ d * suc (suc m) + toℕ b)))
                (sym (inject≤-lemma (fromℕ (toℕ d * suc (suc m) + toℕ b)) leq) )) ⟩ 
         (((toℕ (inject≤ (fromℕ (toℕ d * suc (suc m) + toℕ b)) leq)) +
           (toℕ b * (suc m + suc n * suc (suc m))))
           mod (suc m + suc n * suc (suc m)))
          ≡⟨ mod-lemma (toℕ b) (m + suc n * suc (suc m))
              (inject≤ (fromℕ (toℕ d * suc (suc m) + toℕ b)) leq) ⟩ 
         inject≤ (fromℕ (toℕ d * suc (suc m) + toℕ b)) leq ∎)
  where open ≡-Reasoning

not-max-b-d : (m n : ℕ) (b : Fin (suc (suc m))) (d : Fin (suc (suc n)))
  (p≠ : ¬ suc (toℕ b * suc (suc n) + toℕ d) ≡ suc (suc m) * suc (suc n)) →
   suc (toℕ b * suc (suc n) + toℕ d) ≤ suc n + suc m * suc (suc n)
not-max-b-d m n b d p≠ with
      cmp (suc (toℕ b * suc (suc n) + toℕ d)) (suc (suc m) * suc (suc n))
... | tri< a ¬b ¬c = ≤-pred a
... | tri≈ ¬a b≡ ¬c = ⊥-elim (p≠ b≡) 
... | tri> ¬a ¬b c = ⊥-elim (1+n≰n contra)
  where contra = begin (suc (suc (suc m) * suc (suc n))
                       ≤⟨ c ⟩
                        suc (toℕ b * suc (suc n) + toℕ d)
                       ≡⟨ sym (+-suc (toℕ b * suc (suc n)) (toℕ d)) ⟩
                        toℕ b * suc (suc n) + suc (toℕ d)
                       ≤⟨ cong+l≤ (bounded d) (toℕ b * suc (suc n)) ⟩
                        toℕ b * suc (suc n) + suc (suc n)
                       ≤⟨ cong+r≤
                           (cong*r≤ (bounded' (suc m) b) (suc (suc n)))
                           (suc (suc n)) ⟩
                        suc m * suc (suc n) + suc (suc n)
                       ≡⟨ +-comm (suc m * suc (suc n)) (suc (suc n)) ⟩
                        suc (suc m) * suc (suc n) ∎)
                 where open ≤-Reasoning

not-max-b-d' : (m n : ℕ) (b : Fin (suc (suc m))) (d : Fin (suc (suc n)))
  (p≠ : ¬ suc (toℕ b * suc (suc n) + toℕ d) ≡ suc (suc m) * suc (suc n)) →
  (¬ suc (toℕ d * suc (suc m) + toℕ b) ≡ suc (suc n) * suc (suc m))
not-max-b-d' m n b d p≠ with
  (suc (toℕ d * suc (suc m) + toℕ b)) ≟ (suc (suc n) * suc (suc m))
... | no ¬w = ¬w
... | yes w =
  let (d≡sn , b≡sm) = max-b-d n m d b w in ⊥-elim (p≠ (contra b≡sm d≡sn))
  where contra : (b≡sm : toℕ b ≡ suc m) (d≡sn : toℕ d ≡ suc n) →
                 suc (toℕ b * suc (suc n) + toℕ d) ≡ suc (suc m) * suc (suc n)
        contra b≡sm d≡sn =
          begin (suc (toℕ b * suc (suc n) + toℕ d)
                ≡⟨ cong₂ (λ x y → suc (x * suc (suc n) + y)) b≡sm d≡sn ⟩ 
                 suc (suc m * suc (suc n) + suc n)
                ≡⟨ sym (+-suc (suc m * suc (suc n)) (suc n)) ⟩ 
                 suc m * suc (suc n) + suc (suc n)
                ≡⟨  +-comm (suc m * suc (suc n)) (suc (suc n)) ⟩ 
                 suc (suc m) * suc (suc n) ∎)
          where open ≡-Reasoning

inject-mod : (m n : ℕ) (b : Fin (suc (suc m))) (d : Fin (suc (suc n))) 
     (leq : suc (toℕ b * suc (suc n) + toℕ d) ≤ suc n + suc m * suc (suc n)) → 
        inject≤
          (((toℕ d * suc (suc m) + toℕ b) * suc (suc n)) mod
             (suc n + suc m * suc (suc n)))
          (i≤si (suc n + suc m * suc (suc n)))
      ≡ inject≤
           (fromℕ (toℕ b * suc (suc n) + toℕ d))
           (i*n+k≤m*n b d) 
inject-mod m n b d leq = 
   begin (inject≤
            (((toℕ d * suc (suc m) + toℕ b) * suc (suc n)) mod
             (suc n + suc m * suc (suc n)))
            (i≤si (suc n + suc m * suc (suc n)))
        ≡⟨ cong₂D!
             inject≤ 
             (sym (mod-lem n m d b leq))
             (≤-proof-irrelevance
               (subst
                 (λ _ →
                   suc n + suc m * suc (suc n) ≤ suc (suc n + suc m * suc (suc n)))
                 (sym (mod-lem n m d b leq))
                 (i≤si (suc n + suc m * suc (suc n))))
               (i≤si (suc n + suc m * suc (suc n)))) ⟩
          inject≤
            (inject≤ (fromℕ (toℕ  b * suc (suc n) + toℕ d)) leq)
            (i≤si (suc n + suc m * suc (suc n)))
        ≡⟨ toℕ-injective
            (trans
              (inject≤-lemma
                (inject≤ (fromℕ (toℕ b * suc (suc n) + toℕ d)) leq)
                (i≤si (suc n + suc m * suc (suc n))))
              (trans
                (inject≤-lemma (fromℕ (toℕ b * suc (suc n) + toℕ d)) leq)
                (sym (inject≤-lemma
                       (fromℕ (toℕ b * suc (suc n) + toℕ d))
                       (i*n+k≤m*n b d))))) ⟩ 
         inject≤
           (fromℕ (toℕ b * suc (suc n) + toℕ d))
           (i*n+k≤m*n b d) ∎)
   where open ≡-Reasoning

fin-project-3 : (m n : ℕ) (b : Fin (suc (suc m))) (d : Fin (suc (suc n))) →
  (p≠ : ¬ suc (toℕ d * suc (suc m) + toℕ b) ≡ suc (suc n) * suc (suc m)) → 
  fin-project (suc (suc n)) (suc (suc m))
    (inject≤
      ((((toℕ b * suc (suc n)) + toℕ d) * (suc (suc m))) mod
       (suc m + suc n * suc (suc m)))
      (i≤si (suc m + suc n * suc (suc m))))
  ≡ (d , b)
fin-project-3 m n b d p≠ with
  (toℕ (inject≤
         ((((toℕ b * suc (suc n)) + toℕ d) * (suc (suc m))) mod
          (suc m + suc n * suc (suc m)))
         (i≤si (suc m + suc n * suc (suc m))))) divMod (suc (suc m))
fin-project-3 m n b d p≠ | result q r k≡r+q*sn with suc (suc n) ≤? q
fin-project-3 m n b d p≠ | result q r k≡r+q*sn | yes p =
  ⊥-elim (absurd (suc n) (suc m) q r
           (inject≤
             ((((toℕ b * suc (suc n)) + toℕ d) * (suc (suc m))) mod
               (suc m + suc n * suc (suc m)))
             (i≤si (suc m + suc n * suc (suc m))))
             k≡r+q*sn
             p)
fin-project-3 m n b d p≠ | result q r k≡r+q*sn | no ¬p =
  let (r≡b , q≡d) = addMul-lemma′ q (toℕ d) (suc m) r b (sym simplified)
  in cong₂ _,_ (toℕ-injective (trans (toℕ-fromℕ≤ (s≤s (≤-pred (≰⇒> ¬p)))) q≡d)) r≡b 
  where simplified : toℕ d * suc (suc m) + toℕ b ≡ q * suc (suc m) + toℕ r
        simplified = begin (toℕ d * suc (suc m) + toℕ b
                            ≡⟨ sym (to-from (toℕ d * suc (suc m) + toℕ b)) ⟩ 
                           toℕ (fromℕ (toℕ d * suc (suc m) + toℕ b))
                           ≡⟨ sym (inject≤-lemma
                                    (fromℕ (toℕ d * suc (suc m) + toℕ b))
                                    (i*n+k≤m*n d b)) ⟩
                           toℕ (inject≤
                             (fromℕ (toℕ d * suc (suc m) + toℕ b))
                             (i*n+k≤m*n d b))
                           ≡⟨ cong toℕ
                                (sym (inject-mod n m d b (not-max-b-d n m d b p≠))) ⟩
                           toℕ (inject≤
                             ((((toℕ b * suc (suc n)) + toℕ d) * (suc (suc m))) mod
                               (suc m + suc n * suc (suc m)))
                             (i≤si (suc m + suc n * suc (suc m))))
                           ≡⟨ k≡r+q*sn ⟩
                           toℕ r + q * suc (suc m)
                           ≡⟨ +-comm (toℕ r) (q * suc (suc m)) ⟩ 
                           q * suc (suc m) + toℕ r ∎)
                     where open ≡-Reasoning

transpose2 : (m n : ℕ) (i : Fin (m * n)) → 
  let fin-result b d dec dec' = fin-divMod m n i
      fin-result bt dt dect dec't =
        fin-divMod n m (subst Fin (*-comm m n) (transposeIndex m n b d)) in
  toℕ (transposeIndex n m bt dt) ≡ toℕ i
transpose2 m n i =
  let fin-result b d dec dec' = fin-divMod m n i
      fin-result bt dt dect dec't =
        fin-divMod n m (subst Fin (*-comm m n) (transposeIndex m n b d))
      (dbt≡ , bdt≡) = fin-addMul-lemma n m d bt b dt pr
  in fpr
  where pr = let fin-result b d dec dec' = fin-divMod m n i
                 fin-result bt dt dect dec't =
                   fin-divMod n m (subst Fin (*-comm m n) (transposeIndex m n b d)) in
             begin (toℕ d * m + toℕ b
                   ≡⟨ sym (to-from _) ⟩ 
                   toℕ (fromℕ (toℕ d * m + toℕ b))
                   ≡⟨ sym (inject≤-lemma _ _) ⟩ 
                   toℕ (transposeIndex m n b d)
                   ≡⟨ sym (toℕ-fin (m * n) (n * m) (*-comm m n)
                           (transposeIndex m n b d)) ⟩
                   toℕ (subst Fin (*-comm m n) (transposeIndex m n b d))
                   ≡⟨ dect ⟩
                   toℕ dt + toℕ bt * m
                   ≡⟨ +-comm (toℕ dt) (toℕ bt * m) ⟩
                   toℕ bt * m + toℕ dt ∎)
             where open ≡-Reasoning
        fpr = let fin-result b d dec dec' = fin-divMod m n i
                  fin-result bt dt dect dec't =
                    fin-divMod n m (subst Fin (*-comm m n) (transposeIndex m n b d))
                  (dbt≡ , bdt≡) = fin-addMul-lemma n m d bt b dt pr in
              begin (toℕ (transposeIndex n m bt dt)
                   ≡⟨ inject≤-lemma _ _ ⟩
                     toℕ (fromℕ (toℕ dt * n + toℕ bt))
                   ≡⟨ to-from _ ⟩ 
                     toℕ dt * n + toℕ bt
                   ≡⟨ cong₂ (λ x y → toℕ x * n + toℕ y)
                        (sym bdt≡) (sym dbt≡) ⟩ 
                     toℕ b * n + toℕ d
                   ≡⟨ +-comm (toℕ b * n) (toℕ d) ⟩ 
                     toℕ d + toℕ b * n
                   ≡⟨ sym dec ⟩ 
                     toℕ i ∎)
              where open ≡-Reasoning

lookup-transpose : (m n : ℕ) (i : Fin (m * n)) → 
  lookup
    (lookup i
      (concatV
        (mapV (λ b → mapV (λ d → transposeIndex m n b d) (allFin n))
        (allFin m))))
    (subst Cauchy (*-comm n m)
      (concatV
        (mapV (λ d → mapV (λ b → transposeIndex n m d b) (allFin m))
        (allFin n))))
  ≡ i
lookup-transpose m n i =
  let fin-result b d dec dec' = fin-divMod m n i 
      fin-result bt dt dect dect' =
        fin-divMod n m (subst Fin (*-comm m n) (transposeIndex m n b d)) in
  begin (lookup
          (lookup i
            (concatV
              (mapV (λ b → mapV (λ d → transposeIndex m n b d) (allFin n))
              (allFin m))))
            (subst Cauchy (*-comm n m)
              (concatV
                (mapV (λ d → mapV (λ b → transposeIndex n m d b) (allFin m))
                (allFin n))))
       ≡⟨ cong (λ x → lookup x
                 (subst Cauchy (*-comm n m)
                   (concatV
                     (mapV
                        (λ d → mapV (λ b → transposeIndex n m d b) (allFin m))
                        (allFin n)))))
           (trans (lookup-2d m n i (allFin m) (allFin n)
                    (λ {(b , d) → transposeIndex m n b d}))
                  (cong₂ (transposeIndex m n)
                    (lookup-allFin b) (lookup-allFin d))) ⟩
         lookup
            (transposeIndex m n b d)
            (subst Cauchy (*-comm n m)
              (concatV
                (mapV (λ d → mapV (λ b → transposeIndex n m d b) (allFin m))
                (allFin n))))
       ≡⟨ lookup-subst-1
           (transposeIndex m n b d)
           (concatV
             (mapV
               (λ d → mapV (λ b → transposeIndex n m d b) (allFin m))
               (allFin n)))
           (*-comm n m)
           (*-comm m n)
           (proof-irrelevance (sym (*-comm n m)) (*-comm m n)) ⟩
         subst Fin (*-comm n m)
           (lookup
             (subst Fin (*-comm m n) (transposeIndex m n b d))
             (concatV
               (mapV
                 (λ d → mapV (λ b → transposeIndex n m d b) (allFin m))
                 (allFin n))))
       ≡⟨ cong (λ x → subst Fin (*-comm n m) x)
            (trans
              (lookup-2d n m (subst Fin (*-comm m n) (transposeIndex m n b d))
                (allFin n) (allFin m)
                (λ {(d , b) → transposeIndex n m d b}))
              (cong₂ (transposeIndex n m)
                (lookup-allFin bt) (lookup-allFin dt))) ⟩
         subst Fin (*-comm n m) (transposeIndex n m bt dt)
       ≡⟨ toℕ-injective
           (trans
             (toℕ-fin (n * m) (m * n) (*-comm n m) (transposeIndex n m bt dt))
             (transpose2 m n i)) ⟩
         i ∎)
  where open ≡-Reasoning

swap⋆idemp : (m n : ℕ) → 
  scompcauchy 
    (swap⋆cauchy m n) 
    (subst Cauchy (*-comm n m) (swap⋆cauchy n m))
  ≡ 
  allFin (m * n)
swap⋆idemp m n =
  begin (scompcauchy
           (concatV 
             (mapV 
               (λ b → mapV (λ d → transposeIndex m n b d) (allFin n))
               (allFin m)))
           (subst Cauchy (*-comm n m)
             (concatV 
               (mapV 
                 (λ d → mapV (λ b → transposeIndex n m d b) (allFin m))
                 (allFin n))))
         ≡⟨ refl ⟩
         tabulate (λ i →
           lookup
             (lookup i 
               (concatV 
                 (mapV 
                   (λ b → mapV (λ d → transposeIndex m n b d) (allFin n))
                   (allFin m))))
             (subst Cauchy (*-comm n m)
               (concatV 
                 (mapV 
                   (λ d → mapV (λ b → transposeIndex n m d b) (allFin m))
                   (allFin n)))))
         ≡⟨ finext (lookup-transpose m n) ⟩
         allFin (m * n) ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------------
