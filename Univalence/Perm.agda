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

swap+perm : (m n : ℕ) → Permutation (m + n)
swap+perm m n = (swap+cauchy m n , λ {i} {j} p → {!!})

-- Parallel additive composition 
-- append both permutations but adjust the indices in the second
-- permutation by the size of the first type so that it acts on the
-- second part of the vector

pcompperm : ∀ {m n} → Permutation m → Permutation n → Permutation (m + n)
pcompperm {m} {n} (α , f) (β , g) = (pcompcauchy α β , λ {i} {j} p → {!!}) 

-- Tensor multiplicative composition
-- Transpositions in α correspond to swapping entire rows
-- Transpositions in β correspond to swapping entire columns

tcompperm : ∀ {m n} → Permutation m → Permutation n → Permutation (m * n)
tcompperm {m} {n} (α , f) (β , j) = (tcompcauchy α β , λ {i} {j} p → {!!})

-- swap⋆ 
-- 
-- This is essentially the classical problem of in-place matrix transpose:
-- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
-- Given m and n, the desired permutation in Cauchy representation is:
-- P(i) = m*n-1 if i=m*n-1
--      = m*i mod m*n-1 otherwise

swap⋆perm : (m n : ℕ) → Permutation (m * n)
swap⋆perm m n = (swap⋆cauchy m n , λ {i} {j} p → {!!}) 

------------------------------------------------------------------------------
