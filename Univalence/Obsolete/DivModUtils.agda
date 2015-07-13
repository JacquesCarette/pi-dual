{-# OPTIONS --without-K #-}

-- Copied from "https://code.google.com/p/agda/issues/attachmentText?id=846&aid=8460000000&name=DivModUtils.agda&token=GDo1rQ6ldpTKOCjtbzSWPu19HL0%3A1373287197978"

module DivModUtils where

open import Data.Nat
open import Data.Bool
open import Data.Nat.DivMod
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ≤)
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Relation.Binary
open import Data.Empty
open import Relation.Nullary.Negation
open ≡-Reasoning
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open DecTotalOrder decTotalOrder
  using () renaming (refl to ≤-refl; antisym to ≤-antisym)
import Algebra
open Algebra.CommutativeSemiring commutativeSemiring using (+-comm; +-assoc)

------------------------------------------------------------------------------

i+[j∸m]≡i+j∸m : ∀ i j m → m ≤ j → i + (j ∸ m) ≡ i + j ∸ m
i+[j∸m]≡i+j∸m i zero zero lt = refl
i+[j∸m]≡i+j∸m i zero (suc m) ()
i+[j∸m]≡i+j∸m i (suc j) zero lt = refl
i+[j∸m]≡i+j∸m i (suc j) (suc m) (s≤s m≤j) = begin
  i + (j ∸ m)             ≡⟨ i+[j∸m]≡i+j∸m i j m m≤j ⟩
  suc (i + j) ∸ suc m     ≡⟨ cong (λ y → y ∸ suc m) $
                            solve 2
                              (λ i' j' → con 1 :+ (i' :+ j') := i' :+ (con 1 :+ j'))
                              refl i j ⟩
  (i + suc j) ∸ suc m ∎
  where open SemiringSolver
  
-- Following code taken from
-- https://github.com/copumpkin/derpa/blob/master/REPA/Index.agda#L210

-- the next few bits are lemmas to prove uniqueness of euclidean division

-- first : for nonzero divisors, a nonzero quotient would require a larger
-- dividend than is consistent with a zero quotient, regardless of
-- remainders.

large : ∀ {d} {r : Fin (suc d)} x (r′ : Fin (suc d)) → toℕ r ≢ suc x * suc d + toℕ r′
large {d} {r} x r′ pf = irrefl pf (
    start
      suc (toℕ r)
    ≤⟨ bounded r ⟩
      suc d
    ≤⟨ m≤m+n (suc d) (x * suc d) ⟩
      suc d + x * suc d -- same as (suc x * suc d)
    ≤⟨ m≤m+n (suc x * suc d) (toℕ r′) ⟩
      suc x * suc d + toℕ r′ -- clearer in two steps, and we'd need assoc anyway
    □)
  where
  open ≤-Reasoning
  open Relation.Binary.StrictTotalOrder Data.Nat.Properties.strictTotalOrder

-- a raw statement of the uniqueness, in the arrangement of terms that's
-- easiest to work with computationally

addMul-lemma′ : ∀ x x′ d (r r′ : Fin (suc d)) →
  x * suc d + toℕ r ≡ x′ * suc d + toℕ r′ → r ≡ r′ × x ≡ x′
addMul-lemma′ zero zero d r r′ hyp = (toℕ-injective hyp) , refl
addMul-lemma′ zero (suc x′) d r r′ hyp = ⊥-elim (large x′ r′ hyp)
addMul-lemma′ (suc x) zero d r r′ hyp = ⊥-elim (large x r (sym hyp))
addMul-lemma′ (suc x) (suc x′) d r r′ hyp
                      rewrite +-assoc (suc d) (x * suc d) (toℕ r)
                            | +-assoc (suc d) (x′ * suc d) (toℕ r′)
                      with addMul-lemma′ x x′ d r r′ (cancel-+-left (suc d) hyp)
... | pf₁ , pf₂ = pf₁ , cong suc pf₂

-- and now rearranged to the order that Data.Nat.DivMod uses

addMul-lemma : ∀ x x′ d (r r′ : Fin (suc d)) →
  toℕ r + x * suc d ≡ toℕ r′ + x′ * suc d → r ≡ r′ × x ≡ x′
addMul-lemma x x′ d r r′ hyp rewrite +-comm (toℕ r) (x * suc d)
                                   | +-comm (toℕ r′) (x′ * suc d)
  = addMul-lemma′ x x′ d r r′ hyp
  
DivMod-lemma : ∀ x d (r : Fin (suc d)) → (res : DivMod (toℕ r + x * suc d) (suc d)) →
  res ≡ result x r refl
DivMod-lemma x d r (result q r′ eq) with addMul-lemma x q d r r′ eq
DivMod-lemma x d r (result .x .r eq) | refl , refl =
  cong (result x r) (proof-irrelevance eq refl)

divMod-lemma : ∀ x d (r : Fin (suc d)) →
  (toℕ r + x * suc d) divMod suc d ≡ result x r refl
divMod-lemma x d r with (toℕ r + x * suc d) divMod suc d
divMod-lemma x d r | q rewrite DivMod-lemma x d r q = refl

mod-lemma : ∀ x d (r : Fin (suc d)) → (toℕ r + x * suc d) mod suc d ≡ r
mod-lemma x d r rewrite divMod-lemma x d r = refl

------------------------------------------------------------------------------
