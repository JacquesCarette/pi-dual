{-# OPTIONS --without-K #-}

module Perm where

-- Definitions for permutations in the Cauchy representation

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Data.Nat.Properties
  using (cancel-+-left; ≰⇒>; n∸n≡0; +-∸-assoc; m+n∸n≡m; 1+n≰n; m≤m+n)
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
  z≤n; s≤s; _≟_; _≤?_; ≤-pred; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤; _ℕ-_; _≺_; reduce≥; 
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties
  using (bounded; inject+-lemma; toℕ-injective; toℕ-raise; toℕ-fromℕ≤)
open import Data.Vec.Properties 
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin; tabulate-∘; 
         tabulate-allFin; allFin-map; lookup-++-inject+; lookup-++-≥;
         lookup-++-<)
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
-- Shorthand

fi≡fj : {m : ℕ} → (i j : Fin m) (f : Fin m → Fin m) →
        (p : lookup i (tabulate f) ≡ lookup j (tabulate f)) → (f i ≡ f j)
fi≡fj i j f p = trans
                  (sym (lookup∘tabulate f i))
                  (trans p (lookup∘tabulate f j))

-- Elementary permutations in the Cauchy representation 

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

toℕ-fin : (m n : ℕ) → (eq : m ≡ n) (fin : Fin m) → toℕ (subst Fin eq fin) ≡ toℕ fin
toℕ-fin m .m refl fin = refl

raise< : (m n : ℕ) (i : Fin (m + n)) (i< : toℕ i < m) → 
         toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<))) ≡ n + toℕ i
raise< m n i i< =
  begin (toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<)))
         ≡⟨ toℕ-fin (n + m) (m + n) (+-comm n m) (raise n (fromℕ≤ i<)) ⟩
         toℕ (raise n (fromℕ≤ i<))
         ≡⟨ toℕ-raise n (fromℕ≤ i<) ⟩
         n + toℕ (fromℕ≤ i<)
         ≡⟨ cong (λ x → n + x) (toℕ-fromℕ≤ i<) ⟩ 
         n + toℕ i ∎)
  where open ≡-Reasoning

toℕ-reduce≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) →
               toℕ (reduce≥ i i≥) ≡ toℕ i ∸ m
toℕ-reduce≥ 0 n i _ = refl 
toℕ-reduce≥ (suc m) n zero ()
toℕ-reduce≥ (suc m) n (suc i) (s≤s i≥) = toℕ-reduce≥ m n i i≥

inject≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) →
        toℕ (subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥))) ≡ toℕ i ∸ m
inject≥ m n i i≥ =
  begin (toℕ (subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥)))
         ≡⟨ toℕ-fin (n + m) (m + n) (+-comm n m) (inject+ m (reduce≥ i i≥)) ⟩
         toℕ (inject+ m (reduce≥ i i≥))
         ≡⟨ sym (inject+-lemma m (reduce≥ i i≥)) ⟩
         toℕ (reduce≥ i i≥) 
         ≡⟨ toℕ-reduce≥ m n i i≥ ⟩ 
         toℕ i ∸ m ∎)
  where open ≡-Reasoning

∸≡ : (m n : ℕ) (i j : Fin (m + n)) (i≥ : m ≤ toℕ i) (j≥ : m ≤ toℕ j) →
  toℕ i ∸ m ≡ toℕ j ∸ m → i ≡ j
∸≡ m n i j i≥ j≥ p = toℕ-injective pr
  where pr = begin (toℕ i
                    ≡⟨ sym (m+n∸n≡m (toℕ i) m) ⟩
                    (toℕ i + m) ∸ m
                    ≡⟨ cong (λ x → x ∸ m) (+-comm (toℕ i) m) ⟩ 
                    (m + toℕ i) ∸ m
                    ≡⟨ +-∸-assoc m i≥ ⟩
                    m + (toℕ i ∸ m)
                    ≡⟨ cong (λ x → m + x) p ⟩
                    m + (toℕ j ∸ m)
                    ≡⟨ sym (+-∸-assoc m j≥) ⟩
                    (m + toℕ j) ∸ m
                    ≡⟨ cong (λ x → x ∸ m) (+-comm m (toℕ j)) ⟩
                    (toℕ j + m) ∸ m
                    ≡⟨ m+n∸n≡m (toℕ j) m ⟩
                    toℕ j ∎)
             where open ≡-Reasoning

swap+cauchy< : (m n : ℕ) (i : Fin (m + n)) (i< : toℕ i < m) →
  lookup i (swap+cauchy m n) ≡ subst Fin (+-comm n m) (raise n (fromℕ≤ i<))
swap+cauchy< m n i i< =
  begin (lookup i
          (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
            (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n)))
         ≡⟨ lookup-subst i
              (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))
              (+-comm n m) ⟩
         subst Fin (+-comm n m)
           (lookup i (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n)))
         ≡⟨ cong (subst Fin (+-comm n m))
              (lookup-++-<
                (mapV (raise n) (allFin m))
                (mapV (inject+ m) (allFin n))
                i i<) ⟩
         subst Fin (+-comm n m)
           (lookup (fromℕ≤ i<) (mapV (raise n) (allFin m)))
         ≡⟨ cong (subst Fin (+-comm n m))
              (lookup-map (fromℕ≤ i<) (raise n) (allFin m)) ⟩
         subst Fin (+-comm n m) (raise n (lookup (fromℕ≤ i<) (allFin m)))
         ≡⟨ cong
              (λ x → subst Fin (+-comm n m) (raise n x))
              (lookup-allFin (fromℕ≤ i<)) ⟩ 
         subst Fin (+-comm n m) (raise n (fromℕ≤ i<)) ∎)
  where open ≡-Reasoning

swap+cauchy≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) → 
  lookup i (swap+cauchy m n) ≡ subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥))
swap+cauchy≥ m n i i≥ =
  begin (lookup i 
          (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
            (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n)))
         ≡⟨ lookup-subst i
              (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))
              (+-comm n m) ⟩
         subst Fin (+-comm n m)
           (lookup i (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n)))
         ≡⟨ cong (subst Fin (+-comm n m))
              (lookup-++-≥
                (mapV (raise n) (allFin m))
                (mapV (inject+ m) (allFin n))
                i i≥) ⟩
         subst Fin (+-comm n m)
           (lookup (reduce≥ i i≥) (mapV (inject+ m) (allFin n)))
         ≡⟨ cong (subst Fin (+-comm n m))
             (lookup-map (reduce≥ i i≥) (inject+ m) (allFin n)) ⟩
         subst Fin (+-comm n m) (inject+ m (lookup (reduce≥ i i≥) (allFin n)))
         ≡⟨ cong (λ x → subst Fin (+-comm n m) (inject+ m x))
             (lookup-allFin (reduce≥ i i≥)) ⟩
         subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥)) ∎)
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

cancel-right∸ : (m n k : ℕ) (k≤m : k ≤ m) (k≤n : k ≤ n) → (m ∸ k ≡ n ∸ k) → m ≡ n
cancel-right∸ m n k k≤m k≤n mk≡nk =
  begin (m
         ≡⟨ sym (m+n∸n≡m m k) ⟩
         (m + k) ∸ k
         ≡⟨ cong (λ x → x ∸ k) (+-comm m k) ⟩
         (k + m) ∸ k
         ≡⟨ +-∸-assoc k k≤m ⟩
         k + (m ∸ k)
         ≡⟨ cong (λ x → k + x) mk≡nk ⟩
         k + (n ∸ k)
         ≡⟨ sym (+-∸-assoc k k≤n) ⟩
         (k + n) ∸ k
         ≡⟨ cong (λ x → x ∸ k) (+-comm k n) ⟩
         (n + k) ∸ k
         ≡⟨ m+n∸n≡m n k ⟩
         n ∎)
  where open ≡-Reasoning

lookup-bounded : (m n : ℕ) (i : Fin n) (v : Vec (Fin m) n) → toℕ (lookup i v) < m
lookup-bounded m 0 () v
lookup-bounded m (suc n) zero (x ∷ v) = bounded x
lookup-bounded m (suc n) (suc i) (x ∷ v) = lookup-bounded m n i v 

fromℕ≤-inj : (m n : ℕ) (i j : Fin n) (i< : toℕ i < m) (j< : toℕ j < m) → 
  fromℕ≤ i< ≡ fromℕ≤ j< → i ≡ j
fromℕ≤-inj m n i j i< j< fi≡fj =
  toℕ-injective
    (trans (sym (toℕ-fromℕ≤ i<)) (trans (cong toℕ fi≡fj) (toℕ-fromℕ≤ j<)))

reduce≥-inj : (m n : ℕ) (i j : Fin (m + n)) (i≥ : m ≤ toℕ i) (j≥ : m ≤ toℕ j) →
  reduce≥ i i≥ ≡ reduce≥ j j≥ → i ≡ j
reduce≥-inj m n i j i≥ j≥ ri≡rj =
  toℕ-injective
    (cancel-right∸ (toℕ i) (toℕ j) m i≥ j≥
      (trans (sym (toℕ-reduce≥ m n i i≥))
      (trans (cong toℕ ri≡rj) (toℕ-reduce≥ m n j j≥))))

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

tcompperm : ∀ {m n} → Permutation m → Permutation n → Permutation (m * n)
tcompperm {m} {n} (α , f) (β , j) = (tcompcauchy α β , λ {i} {j} p → {!!})

{--
tcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m * n)
tcompcauchy {m} {n} α β = 
  concatV 
    (mapV 
      (λ b → 
         mapV (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)) β)
      α)

m : ℕ
n : ℕ
i : Fin (m * n)
j : Fin (m * n)
α : Cauchy m
β : Cauchy n
f : lookup i α ≡ lookup j α → i ≡ j
j : lookup i β ≡ lookup j β → i ≡ j
p : lookup i (tcompcauchy α β) ≡ lookup j (tcompcauchy α β)
--}

-- swap⋆ 
-- 
-- This is essentially the classical problem of in-place matrix transpose:
-- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
-- Given m and n, the desired permutation in Cauchy representation is:
-- P(i) = m*n-1 if i=m*n-1
--      = m*i mod m*n-1 otherwise

swap⋆perm : (m n : ℕ) → Permutation (m * n)
swap⋆perm m n = (swap⋆cauchy m n , λ {i} {j} p → {!!}) 

{--
m : ℕ
n : ℕ
i : Fin (m * n)
j : Fin (m * n)
p : lookup i (swap⋆cauchy m n) ≡ lookup j (swap⋆cauchy m n)

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
--}

------------------------------------------------------------------------------
