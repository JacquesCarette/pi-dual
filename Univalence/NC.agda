{-# OPTIONS --without-K #-}

module NC where

open import Data.Empty
open import Data.Unit
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product
import Data.Fin as F
open import Data.Vec
import Data.List as L
open import Function renaming (_∘_ to _○_)


open import FT
open import FT-Nat
open import HoTT using (refl; pathInd; _≡_; ap)
open import Equivalences
open import TypeEquivalences using (path⊎)
open import Path2Equiv
open import LeftCancellation

fromNormalNat : (n : ℕ) → ⟦ n ⟧ℕ → F.Fin n
fromNormalNat zero ()
fromNormalNat (suc n) (inj₁ tt) = F.zero
fromNormalNat (suc n) (inj₂ x) = F.suc (fromNormalNat n x)

toNormalNat : (n : ℕ) → F.Fin n → ⟦ n ⟧ℕ
toNormalNat zero ()
toNormalNat (suc n) F.zero = inj₁ tt
toNormalNat (suc n) (F.suc f) = inj₂ (toNormalNat n f)

equivToVec : {n : ℕ} → ⟦ n ⟧ℕ ≃ ⟦ n ⟧ℕ → Vec (F.Fin n) n
equivToVec {n} (f , _) = tabulate ((fromNormalNat n) ○ f ○ (toNormalNat n))

-- Swap the thing here with the next thing; size of the type must be at least 2
swapi : {n : ℕ} → F.Fin n → (fromℕ (suc (suc n))) ⇛ (fromℕ (suc (suc n)))
swapi F.zero =
  (assocl₊⇛) ◎ (swap₊⇛ ⊕ id⇛) ◎ (assocr₊⇛)
swapi (F.suc n) = id⇛ ⊕ swapi n

upFrom : {lim : ℕ} → (m : F.Fin lim) → F.Fin′ m → L.List (F.Fin lim)
upFrom max min = {!!}
-- fails due to --without-K
-- with max F.- (F.suc min)
-- ... | F.zero = []
-- ... | _ = min ∷ (upFrom max (F.suc min))

-- TODO: verify that this is actually correct
-- Idea: To swap n < m with each other, swap n, n + 1, ... , m - 1, m, then go back down, so that m and n are swapped and everything else is in the same spot
swapmn : {lim : ℕ} → (m : F.Fin lim) → F.Fin′ m → (fromℕ (suc (suc lim))) ⇛ (fromℕ (suc (suc lim)))
swapmn m n = L.foldr (λ i p → p ◎ swapi i) (L.foldl (λ p i → p ◎ swapi i) (swapi m) (upFrom m n)) (upFrom m n) 

-- Do a fold along the vector with buildPath to compute the path. Only add
-- something to the path if the item it maps to is strictly greater than the
-- index it's at---this eliminates duplication, and lets us compose the
-- combinators nicely.


-- TODO: this really needs to be the function for some sort of indexed fold that doesn't seem to be in the standard library
buildPath : (max : ℕ) → {n : ℕ} → F.Fin max → (fromℕ n) ⇛ (fromℕ n) → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
buildPath max {remSize} elem oldPath = {!!} -- with (F.fromℕ (max F.ℕ-ℕ (suc remSize)) < elem)
-- ... | p = ?

makePath' : {max : ℕ} → (i : F.Fin max) → (j : F.Fin max) → (fromℕ (suc (suc max)) ⇛ (fromℕ (suc (suc max))) → (fromℕ (suc (suc max))) ⇛ (fromℕ (suc (suc max))))
makePath' i j p with F.compare i j
makePath' .(F.inject i') j p | F.less .j i' = swapmn j i' ◎ p
makePath' i .i p | F.equal .i = p
makePath' i .(F.inject j') p | F.greater .i j' = p

{-- cleaner version of makePath' that again seems to be broken by --without-K 
makePath : {max : ℕ} → (i : F.Fin max) → Vec (F.Fin max) max
         → (fromℕ max) ⇛ (fromℕ max)
makePath {zero} i [] = id⇛
makePath {suc zero} i (j ∷ []) = id⇛
makePath {suc (suc max)} i (j ∷ rest) = ?
--}

vecToPath : {n : ℕ} → Vec (F.Fin n) n → (fromℕ n) ⇛ (fromℕ n)
vecToPath = {!!} -- writing this to use makePath' should also run into --without-K
-- foldr (λ n → (fromℕ n) ⇛ (fromℕ n)) (buildPath n) id⇛ -- (buildPath n) id

