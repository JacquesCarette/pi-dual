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
  using (m≤m+n; n≤m+n; n≤1+n; cancel-+-left; cancel-*-right; strictTotalOrder; 
         cancel-*-right-≤; ≰⇒>; ¬i+1+j≤i; 1+n≰n)
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
  using (bounded; inject+-lemma; to-from; toℕ-injective; inject≤-lemma; toℕ-fromℕ≤)
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

open import Proofs
open import Cauchy
open import CauchyProofs
-- open import CauchyProofsT
open import CauchyProofsT_TEMP
postulate
  tabulate-concat : ∀ {m n} →
    (f : Fin m × Fin n → Fin (m * n)) → 
    concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j)))) ≡
    tabulate {m * n} (λ (k : Fin (m * n)) → f (fin-project m n k))

------------------------------------------------------------------------------
-- Main lemma swap⋆idemp

subst-allFin : ∀ {m n} → (eq : m ≡ n) → subst Cauchy eq (allFin m) ≡ allFin n
subst-allFin refl = refl

concat-simplify : {A : Set} → (m n : ℕ) → (f : Fin (suc m) → Vec A (suc n)) → 
  concatV (mapV f (allFin (suc m))) ≡
  f zero ++V concatV (mapV (λ a → f (suc a)) (allFin m))
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
  
transposeIndex' : (m n : ℕ) → (b : Fin (suc (suc m))) (d : Fin (suc (suc n))) →
  (toℕ b ≡ suc m × toℕ d ≡ suc n) →
  transposeIndex m n b d ≡ fromℕ (suc n + suc m * suc (suc n))
transposeIndex' m n b d (b≡ , d≡)
  with suc (toℕ b * suc (suc n) + toℕ d) ≟ suc (suc m) * suc (suc n)
transposeIndex' m n b d (b≡ , d≡) | yes i= = refl
transposeIndex' m n b d (b≡ , d≡) | no i≠ = ⊥-elim (i≠ contra)
  where contra = begin (suc (toℕ b * suc (suc n) + toℕ d)
                       ≡⟨ cong₂ (λ x y → suc (x * suc (suc n) + y)) b≡ d≡ ⟩ 
                        suc (suc m * suc (suc n) + suc n)
                       ≡⟨ sym (+-suc (suc m * suc (suc n)) (suc n)) ⟩ 
                        suc m * suc (suc n) + suc (suc n)
                       ≡⟨ +-comm (suc m * suc (suc n)) (suc (suc n)) ⟩ 
                        suc (suc n) + suc m * suc (suc n) 
                       ≡⟨ refl ⟩ 
                        suc (suc m) * suc (suc n) ∎)
                 where open ≡-Reasoning

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

-- buried in Data.Nat

refl′ : _≡_ ⇒ _≤_
refl′ {0} refl = z≤n
refl′ {suc m} refl = s≤s (refl′ refl)

{--

subst-transpose : (m n : ℕ) (b : Fin (suc (suc m))) (d : Fin (suc (suc n))) → 
    subst Fin (*-comm (suc (suc m)) (suc (suc n))) (transposeIndex m n b d)
  ≡ transposeIndex n m d b
subst-transpose m n b d
  with suc (toℕ b * suc (suc n) + toℕ d) ≟ suc (suc m) * suc (suc n)
subst-transpose m n b d | yes p= =
  begin (subst Fin (*-comm (suc (suc m)) (suc (suc n)))
          (fromℕ (suc n + suc m * suc (suc n)))
         ≡⟨ subst-fin 
              (suc n + suc m * suc (suc n))
              (suc m + suc n * suc (suc m))
              (*-comm (suc (suc m)) (suc (suc n))) ⟩ 
         fromℕ (suc m + suc n * suc (suc m))
         ≡⟨ sym (transposeIndex' n m d b (swap (max-b-d m n b d p=))) ⟩
         transposeIndex n m d b ∎)
  where open ≡-Reasoning
subst-transpose m n b d | no p≠  =
  begin (subst Fin (*-comm (suc (suc m)) (suc (suc n)))
           (inject≤ 
             (((toℕ b * suc (suc n) + toℕ d) * (suc (suc m)))
                mod (suc n + suc m * suc (suc n)))
             (i≤si (suc n + suc m * suc (suc n)))) 
         ≡⟨ subst-inject-mod {((toℕ b * suc (suc n) + toℕ d) * (suc (suc m)))} 
              (*-comm (suc (suc m)) (suc (suc n))) ⟩ 
         inject≤ 
           (((toℕ b * suc (suc n) + toℕ d) * (suc (suc m)))
              mod (suc m + suc n * suc (suc m))) 
           (i≤si (suc m + suc n * suc (suc m)))
         ≡⟨ {!!} ⟩ 
         transposeIndex n m d b ∎)

If ¬ (suc (toℕ b * suc (suc n) + toℕ d) ≡ suc (suc m) * suc (suc n))
then 
transposeIndex m n b d = 
  inject≤ 
    ((i * (suc (suc m))) mod (suc n + suc m * suc (suc n)))
    (i≤si (suc n + suc m * suc (suc n)))

---

If ¬ (suc (toℕ d * suc (suc m) + toℕ b) ≡ suc (suc n) * suc (suc m))
then
transposeIndex n m d b = 
  inject≤ 
    ((i * (suc (suc n))) mod (suc m + suc n * suc (suc m)))
    (i≤si (suc m + suc n * suc (suc m)))
  where open ≡-Reasoning
--}

lastV : {ℓ : Level} {A : Set ℓ} {n : ℕ} → Vec A (suc n) → A
lastV (x ∷ []) = x
lastV (_ ∷ x ∷ xs) = lastV (x ∷ xs)

last-map : {A B : Set} → (n : ℕ) → (xs : Vec A (suc n)) → (f : A → B) → 
         lastV (mapV f xs) ≡ f (lastV xs)
last-map 0 (x ∷ []) f = refl
last-map (suc n) (_ ∷ x ∷ xs) f = last-map n (x ∷ xs) f 

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
            (finext
               (λ b → mapV (λ d → f (b , d)) (allFin n))
               (λ b → tabulate (λ d → f (b , d)))
               (λ b → sym (tabulate-∘ (λ d → f (b , d)) id))) ⟩
         concatV (tabulate (λ b → tabulate (λ d → f (b , d))))
       ≡⟨ tabulate-concat f ⟩
         tabulate (λ k → f (fin-project m n k)) ∎)
  where open ≡-Reasoning

fin-project-2 : (n m : ℕ) →
 fin-project (suc (suc n)) (suc (suc m)) (fromℕ (suc m + suc n * suc (suc m)))
 ≡ (fromℕ (suc n) , fromℕ (suc m))
fin-project-2 n m with toℕ (fromℕ (suc m + suc n * suc (suc m))) divMod (suc (suc m))
fin-project-2 n m | result q r k≡r+q*sn = {!!}

subst-lookup-transpose : (m n : ℕ) (b : Fin (suc (suc m))) (d : Fin (suc (suc n))) → 
  subst Fin (*-comm (suc (suc n)) (suc (suc m))) 
    (lookup
      (subst Fin (*-comm (suc (suc m)) (suc (suc n)))
        (transposeIndex m n b d))
      (concatV
        (mapV
          (λ b → mapV (λ d → transposeIndex n m b d) (allFin (suc (suc m))))
          (allFin (suc (suc n))))))
  ≡ inject≤
      (fromℕ (toℕ b * suc (suc n) + toℕ d))
      (i*n+k≤m*n b d)
subst-lookup-transpose m n b d
  with suc (toℕ b * suc (suc n) + toℕ d) ≟ suc (suc m) * suc (suc n)
subst-lookup-transpose m n b d | yes p= =
  let (b= , d=) = max-b-d m n b d p= in 
  begin (subst Fin (*-comm (suc (suc n)) (suc (suc m))) 
          (lookup
            (subst Fin (*-comm (suc (suc m)) (suc (suc n)))
              (fromℕ (suc n + suc m * suc (suc n))))
            (concatV
              (mapV
                (λ b → mapV (λ d → transposeIndex n m b d) (allFin (suc (suc m))))
                (allFin (suc (suc n))))))
        ≡⟨ cong (λ x → subst Fin (*-comm (suc (suc n)) (suc (suc m)))
                          (lookup x
                             (concatV
                               (mapV
                                 (λ b →
                                   mapV
                                     (λ d → transposeIndex n m b d)
                                     (allFin (suc (suc m))))
                                 (allFin (suc (suc n)))))))
                 (subst-fin
                   (suc n + suc m * suc (suc n))
                   (suc m + suc n * suc (suc m))
                   (*-comm (suc (suc m)) (suc (suc n)))) ⟩ 
        subst Fin (*-comm (suc (suc n)) (suc (suc m)))
          (lookup
            (fromℕ (suc m + suc n * suc (suc m)))
            (concatV
              (mapV
                (λ b → mapV (λ d → transposeIndex n m b d) (allFin (suc (suc m))))
                (allFin (suc (suc n))))))
        ≡⟨ cong
             (λ x → subst Fin (*-comm (suc (suc n)) (suc (suc m)))
               (lookup (fromℕ (suc m + suc n * suc (suc m))) x))
             (concat-map-map-tabulate (suc (suc n)) (suc (suc m))
               (λ {(b , d) → transposeIndex n m b d})) ⟩
        subst Fin (*-comm (suc (suc n)) (suc (suc m)))
          (lookup
            (fromℕ (suc m + suc n * suc (suc m)))
            (tabulate (λ k →
              let (b , d) = fin-project (suc (suc n)) (suc (suc m)) k in
              transposeIndex n m b d)))
        ≡⟨ cong (subst Fin (*-comm (suc (suc n)) (suc (suc m))))
             (lookup-fromℕ-allFin
               (suc m + suc n * suc (suc m))
               (λ k →
                  let (b , d) = fin-project (suc (suc n)) (suc (suc m)) k in
                  transposeIndex n m b d)) ⟩
        subst Fin (*-comm (suc (suc n)) (suc (suc m)))
          (let (b , d) = fin-project (suc (suc n)) (suc (suc m))
                           (fromℕ (suc m + suc n * suc (suc m)))
           in transposeIndex n m b d)
        ≡⟨ cong
             (λ x →
               subst Fin (*-comm (suc (suc n)) (suc (suc m)))
                 (let (b , d) = x in transposeIndex n m b d))
             (fin-project-2 n m) ⟩ 
        subst Fin (*-comm (suc (suc n)) (suc (suc m)))
          (transposeIndex n m (fromℕ (suc n)) (fromℕ (suc m)))
        ≡⟨ cong (subst Fin (*-comm (suc (suc n)) (suc (suc m))))
             (transposeIndex' n m (fromℕ (suc n)) (fromℕ (suc m))
               (to-from (suc n) , to-from (suc m))) ⟩
        subst Fin (*-comm (suc (suc n)) (suc (suc m)))
          (fromℕ (suc m + suc n * suc (suc m)))
        ≡⟨ subst-fin
             (suc (m + suc (suc (m + n * suc (suc m)))))
             (suc (n + suc (suc (n + m * suc (suc n)))))
             (*-comm (suc (suc n)) (suc (suc m))) ⟩
        fromℕ (suc (n + suc (suc (n + m * suc (suc n)))))
        ≡⟨ sym (fin=1 n m) ⟩ 
        fromℕ (suc n + suc m * suc (suc n))
        ≡⟨ toℕ-injective
            (trans (to-from (suc n + suc m * suc (suc n)))
            (trans (+-comm (suc n) (suc m * suc (suc n)))
            (trans (sym (to-from (suc m * suc (suc n) + suc n)))
            (sym (inject≤-lemma
              (fromℕ (suc m * suc (suc n) + suc n))
              (refl′
                (trans (sym (+-suc (suc m * suc (suc n)) (suc n)))
                (+-comm (suc m * suc (suc n)) (suc (suc n)))))))))) ⟩
        inject≤
          (fromℕ (suc m * suc (suc n) + suc n))
          (refl′ (trans
                   (sym (+-suc (suc m * suc (suc n)) (suc n)))
                   (+-comm (suc m * suc (suc n)) (suc (suc n)))))
       ≡⟨ cong₂D!
            (λ x y → inject≤ (fromℕ x) y)
            (cong₂ (λ x y → x * suc (suc n) + y) b= d=)
            (≤-proof-irrelevance
              (subst (λ z → suc z ≤ suc (suc n) + suc m * suc (suc n))
                (cong₂ (λ x y → x * suc (suc n) + y) b= d=)
                (i*n+k≤m*n b d))
              (refl′
                (trans
                  (sym (cong suc (cong suc (+-suc (n + m * suc (suc n)) (suc n)))))
                  (+-comm (suc m * suc (suc n)) (suc (suc n)))))) ⟩ 
        inject≤
          (fromℕ (toℕ b * suc (suc n) + toℕ d))
          (i*n+k≤m*n b d) ∎)
  where open ≡-Reasoning

{--
        ≡⟨ {!!} ⟩
        inject≤
          (fromℕ (toℕ b * suc (suc n) + suc n))
          (refl′ (trans
                   (sym (+-suc (toℕ b * suc (suc n)) (suc n)))
                   (+-comm (toℕ b * suc (suc n)) (suc (suc n)))))
        ≡⟨ {!cong₂D!
             (λ x y → inject≤ (fromℕ x) y)
             (cong₂ (λ x y → x * suc (suc n) + y) b= d=)
             (≤-proof-irrelevance
               (subst Fin
                 (cong₂ (λ x y → x * suc (suc n) + y) b= d=)
                 (simplify-≤
                   (refl′ (trans
                     (sym (+-suc (suc m * suc (suc n)) (suc n)))
                     (+-comm (suc m * suc (suc n)) (suc (suc n)))))
                   (cong₂ (λ x y → suc (x * suc (suc n) + y)) (sym b=) (sym d=))
                   refl))
               (refl′ (trans
                   (sym (+-suc (suc m * suc (suc n)) (suc n)))
                   (+-comm (suc m * suc (suc n)) (suc (suc n))))))!} ⟩ 
        inject≤
          (fromℕ (toℕ b * suc (suc n) + toℕ d))
          (simplify-≤
            (refl′ (trans
                   (sym (+-suc (suc m * suc (suc n)) (suc n)))
                   (+-comm (suc m * suc (suc n)) (suc (suc n)))))
            (cong₂ (λ x y → suc (x * suc (suc n) + y)) (sym b=) (sym d=))
            refl)
       ≡⟨ cong
             (inject≤ (fromℕ (toℕ b * suc (suc n) + toℕ d)))
             (≤-proof-irrelevance
               (simplify-≤
                 (refl′ (trans
                        (sym (+-suc (suc m * suc (suc n)) (suc n)))
                        (+-comm (suc m * suc (suc n)) (suc (suc n)))))
                 (cong₂ (λ x y → suc (x * suc (suc n) + y)) (sym b=) (sym d=))
                 refl)
             (i*n+k≤m*n b d)) ⟩ 
        inject≤
          (fromℕ (toℕ b * suc (suc n) + toℕ d))
          (i*n+k≤m*n b d) ∎)
  where open ≡-Reasoning
m  : ℕ
n  : ℕ
b  : Fin (suc (suc m))
d  : Fin (suc (suc n))
p= : suc (toℕ b * suc (suc n) + toℕ d) ≡ suc (suc m) * suc (suc n)

fin-proj-lem :
  (m n : ℕ) (k : Fin (m * n)) →
  k ≡
  inject≤
    (fromℕ (toℕ (proj₁ (fin-project m n k)) * n +
            toℕ (proj₂ (fin-project m n k))))
    (i*n+k≤m*n
      (proj₁ (fin-project m n k))
      (proj₂ (fin-project m n k)))

k ≡
let (b , d) = fin-project m n k in 
inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)
--}        
subst-lookup-transpose m n b d | no p≠ = {!!} 

lookup-swap-2 :
  (m n : ℕ) (b : Fin (suc (suc m))) (d : Fin (suc (suc n))) → 
  lookup
    (transposeIndex m n b d)
    (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
      (concatV
        (mapV
          (λ b → mapV (λ d → transposeIndex n m b d) (allFin (suc (suc m))))
          (allFin (suc (suc n)))))) ≡
  inject≤
    (fromℕ (toℕ b * suc (suc n) + toℕ d))
    (i*n+k≤m*n b d)
lookup-swap-2 m n b d = 
  begin (lookup
           (transposeIndex m n b d)
           (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
             (concatV
               (mapV
                 (λ b → mapV (λ d → transposeIndex n m b d) (allFin (suc (suc m))))
                 (allFin (suc (suc n))))))
         ≡⟨ lookup-subst-1
              (transposeIndex m n b d)
              (concatV
                (mapV
                  (λ b → mapV (λ d → transposeIndex n m b d) (allFin (suc (suc m))))
                  (allFin (suc (suc n)))))
              (*-comm (suc (suc n)) (suc (suc m)))
              (*-comm (suc (suc m)) (suc (suc n)))
              (proof-irrelevance
                (sym (*-comm (suc (suc n)) (suc (suc m))))
                (*-comm (suc (suc m)) (suc (suc n)))) ⟩ 
         subst Fin (*-comm (suc (suc n)) (suc (suc m))) 
           (lookup
             (subst Fin (*-comm (suc (suc m)) (suc (suc n)))
               (transposeIndex m n b d))
             (concatV
               (mapV
                 (λ b → mapV (λ d → transposeIndex n m b d) (allFin (suc (suc m))))
                 (allFin (suc (suc n))))))
         ≡⟨ subst-lookup-transpose m n b d ⟩ 
         inject≤
           (fromℕ (toℕ b * suc (suc n) + toℕ d))
           (i*n+k≤m*n b d) ∎)
  where open ≡-Reasoning

lookup-swap-1 :
  (m n : ℕ) → (b  : Fin (suc (suc m))) → (d  : Fin (suc (suc n))) → 
  lookup
    (lookup
      (inject≤
        (fromℕ (toℕ b * suc (suc n) + toℕ d))
        (i*n+k≤m*n b d))
      (concatV
        (mapV (λ b₁ → mapV (transposeIndex m n b₁) (allFin (suc (suc n))))
        (allFin (suc (suc m))))))
    (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
      (concatV
        (mapV (λ b₁ → mapV (transposeIndex n m b₁) (allFin (suc (suc m))))
        (allFin (suc (suc n)))))) ≡
  lookup
    (inject≤
      (fromℕ (toℕ b * suc (suc n) + toℕ d))
      (i*n+k≤m*n b d))
    (concatV
      (mapV
        (λ b₁ →
          mapV
            (λ d₁ → inject≤ (fromℕ (toℕ b₁ * suc (suc n) + toℕ d₁)) (i*n+k≤m*n b₁ d₁))
            (allFin (suc (suc n))))
        (allFin (suc (suc m)))))
lookup-swap-1 m n b d =
  begin (lookup
           (lookup
             (inject≤
               (fromℕ (toℕ b * suc (suc n) + toℕ d))
               (i*n+k≤m*n b d))
             (concatV
               (mapV (λ b₁ → mapV (transposeIndex m n b₁) (allFin (suc (suc n))))
               (allFin (suc (suc m))))))
           (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
             (concatV
               (mapV (λ b₁ → mapV (transposeIndex n m b₁) (allFin (suc (suc m))))
               (allFin (suc (suc n))))))
         ≡⟨ cong
               (λ x → lookup x
                 (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
                   (concatV
                   (mapV (λ b₁ → mapV (transposeIndex n m b₁) (allFin (suc (suc m))))
                         (allFin (suc (suc n)))))))
               (lookup-concat' (suc (suc m)) (suc (suc n)) b d (i*n+k≤m*n b d)
                  (λ {(b , d) → transposeIndex m n b d})
                  (allFin (suc (suc m))) (allFin (suc (suc n)))) ⟩ 
         lookup
           (transposeIndex m n
             (lookup b (allFin (suc (suc m))))
             (lookup d (allFin (suc (suc n)))))
           (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
             (concatV
               (mapV (λ b₁ → mapV (transposeIndex n m b₁) (allFin (suc (suc m))))
               (allFin (suc (suc n))))))
         ≡⟨ cong₂
              (λ x y → lookup (transposeIndex m n x y)
                         (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
                           (concatV
                             (mapV
                               (λ b₁ →
                                 mapV (transposeIndex n m b₁) (allFin (suc (suc m))))
                               (allFin (suc (suc n)))))))
              (lookup-allFin b)
              (lookup-allFin d) ⟩ 
         lookup
           (transposeIndex m n b d)
           (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
             (concatV
               (mapV (λ b₁ → mapV (transposeIndex n m b₁) (allFin (suc (suc m))))
               (allFin (suc (suc n))))))
         ≡⟨ lookup-swap-2 m n b d ⟩ 
           inject≤
             (fromℕ (toℕ b * suc (suc n) + toℕ d))
             (i*n+k≤m*n b d)
         ≡⟨ sym (cong₂
                   (λ x y → let b' = x
                                d' = y in 
                            inject≤
                              (fromℕ (toℕ b' * suc (suc n) + toℕ d'))
                              (i*n+k≤m*n b' d'))
                   (lookup-allFin b)
                   (lookup-allFin d)) ⟩
           let b' = lookup b (allFin (suc (suc m)))
               d' = lookup d (allFin (suc (suc n))) in 
           inject≤
             (fromℕ (toℕ b' * suc (suc n) + toℕ d'))
             (i*n+k≤m*n b' d')
         ≡⟨ sym (lookup-concat' (suc (suc m)) (suc (suc n)) b d (i*n+k≤m*n b d)
                   (λ {(b , d) →
                     inject≤
                        (fromℕ (toℕ b * suc (suc n) + toℕ d))
                        (i*n+k≤m*n b d)})
                   (allFin (suc (suc m))) (allFin (suc (suc n)))) ⟩ 
         lookup
           (inject≤
             (fromℕ (toℕ b * suc (suc n) + toℕ d))
             (i*n+k≤m*n b d))
           (concatV
             (mapV
               (λ b₁ →
                 mapV
                   (λ d₁ →
                     inject≤ (fromℕ (toℕ b₁ * suc (suc n) + toℕ d₁)) (i*n+k≤m*n b₁ d₁))
                   (allFin (suc (suc n))))
               (allFin (suc (suc m))))) ∎)
  where open ≡-Reasoning

lookup-swap : (m n : ℕ) (i : Fin (suc (suc m) * suc (suc n))) →
  let vs = allFin (suc (suc m))
      ws = allFin (suc (suc n)) in 
  lookup
    (lookup i (concatV (mapV (λ b → mapV (transposeIndex m n b) ws) vs)))
    (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
      (concatV (mapV (λ b → mapV (transposeIndex n m b) vs) ws)))
  ≡ lookup i
      (concatV
         (mapV
           (λ b → mapV
                    (λ d → inject≤
                             (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                             (i*n+k≤m*n b d))
                    ws)
           vs))
lookup-swap m n i =
  let vs = allFin (suc (suc m))
      ws = allFin (suc (suc n)) in 
  begin (lookup
           (lookup i (concatV (mapV (λ b → mapV (transposeIndex m n b) ws) vs)))
           (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
             (concatV (mapV (λ b → mapV (transposeIndex n m b) vs) ws)))
         ≡⟨ cong
              (λ x →
                lookup
                  (lookup x (concatV (mapV (λ b → mapV (transposeIndex m n b) ws) vs)))
                  (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
                    (concatV (mapV (λ b → mapV (transposeIndex n m b) vs) ws))))
              (fin-proj-lem (suc (suc m)) (suc (suc n)) i) ⟩
         let (b , d) = fin-project (suc (suc m)) (suc (suc n)) i in
         lookup
           (lookup
             (inject≤
                (fromℕ (toℕ b * suc (suc n) + toℕ d))
                (i*n+k≤m*n b d))
             (concatV (mapV (λ b → mapV (transposeIndex m n b) ws) vs)))
           (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
             (concatV (mapV (λ b → mapV (transposeIndex n m b) vs) ws)))
         ≡⟨ cong
               (λ x → let (b , d) = fin-project (suc (suc m)) (suc (suc n)) i in x)
               (lookup-swap-1 m n b d) ⟩ 
         let (b , d) = fin-project (suc (suc m)) (suc (suc n)) i in
         lookup
          (inject≤
            (fromℕ (toℕ b * suc (suc n) + toℕ d))
            (i*n+k≤m*n b d))
           (concatV
             (mapV
               (λ b → mapV
                        (λ d → inject≤
                                 (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                                 (i*n+k≤m*n b d))
                        ws)
               vs))
         ≡⟨ cong
              (λ x →
                lookup x
                  (concatV
                    (mapV
                      (λ b → mapV
                               (λ d → inject≤
                                        (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                                        (i*n+k≤m*n b d))
                               ws)
                      vs)))
              (sym (fin-proj-lem (suc (suc m)) (suc (suc n)) i)) ⟩
         lookup i
           (concatV
             (mapV
               (λ b → mapV
                        (λ d → inject≤
                                 (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                                 (i*n+k≤m*n b d))
                        ws)
               vs)) ∎)
  where open ≡-Reasoning

tabulate-lookup-concat : (m n : ℕ) →
  let vec = (λ m n f → 
                concatV
                  (mapV
                    (λ b → mapV (f m n b) (allFin (suc (suc n))))
                    (allFin (suc (suc m))))) in 
  tabulate {suc (suc m) * suc (suc n)} (λ i →
    lookup
      (lookup i (vec m n transposeIndex))
      (subst Cauchy (*-comm (suc (suc n)) (suc (suc m))) (vec n m transposeIndex)))
  ≡
  vec m n (λ m n b d → inject≤
                         (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                         (i*n+k≤m*n b d))
tabulate-lookup-concat m n = 
  let vec = (λ m n f → 
                concatV
                  (mapV
                    (λ b → mapV (f m n b) (allFin (suc (suc n))))
                    (allFin (suc (suc m))))) in 
  begin (tabulate {suc (suc m) * suc (suc n)} (λ i →
           lookup
             (lookup i (vec m n transposeIndex))
             (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
               (vec n m transposeIndex)))
         ≡⟨ finext _ _ (λ i → lookup-swap m n i) ⟩ 
         tabulate {suc (suc m) * suc (suc n)} (λ i →
           lookup i (vec m n (λ m n b d →
                               inject≤
                                 (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                                 (i*n+k≤m*n b d))))
         ≡⟨ tabulate∘lookup (vec m n (λ m n b d →
                                       inject≤
                                         (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                                         (i*n+k≤m*n b d)))  ⟩
         vec m n (λ m n b d → inject≤
                                (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                                (i*n+k≤m*n b d)) ∎)
  where open ≡-Reasoning

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
           ≡⟨ cong₂ 
                (λ x y → scompcauchy x (subst Cauchy (*-comm 1 (suc (suc m))) y))
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
         ≡⟨ refl ⟩ 
           tabulate {suc (suc m) * suc (suc n)} (λ i →
             lookup
               (lookup i
                 (concatV 
                   (mapV 
                     (λ b →
                       mapV
                         (λ d → transposeIndex m n b d)
                         (allFin (suc (suc n))))
                     (allFin (suc (suc m))))))
               (subst Cauchy (*-comm (suc (suc n)) (suc (suc m)))
                 (concatV 
                   (mapV 
                     (λ d →
                       mapV
                         (λ b → transposeIndex n m d b)
                         (allFin (suc (suc m))))
                     (allFin (suc (suc n)))))))
         ≡⟨ tabulate-lookup-concat m n ⟩ 
          concatV 
            (mapV 
              (λ b → 
                mapV
                  (λ d → inject≤
                           (fromℕ (toℕ b * (suc (suc n)) + toℕ d))
                           (i*n+k≤m*n b d))
                  (allFin (suc (suc n))))
              (allFin (suc (suc m))))
         ≡⟨ sym (allFin* (suc (suc m)) (suc (suc n))) ⟩
         allFin (suc (suc m) * suc (suc n)) ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------------
