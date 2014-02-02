module NCCorrectness where

open import Data.Vec
open import Data.Fin hiding (fromℕ)
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Sum

open import Function renaming (_∘_ to _○_)

open import FT
open import FT-Nat
open import NC
open import HoTT



-- open import NC

-- Correctness proofs for normal combinators, to be used in a univalence proof

-- TODO: define the "meaning" of a combinator (ideally somewhere else)
-- There seem to be a few functions that evaluate a combinator; we should probably just
-- choose one and call it "evalComb" or something so we have something to work with here.

-- To show: equivToVec and vecToEquiv preserve meaning
-- To show: equivToVec ∘ vecToEquiv is the identity, on the nose
-- To show: a similar property for the composition in the other direction?

-- To show: vecToComb and combToVec preserve meaning (so normalizing like this is safe)


lookupTab : {A : Set} → {n : ℕ} → {f : Fin n → A} → (i : Fin n) → lookup i (tabulate f) ≡ (f i)
lookupTab {f = f} zero = refl (f zero)
lookupTab (suc i) = lookupTab i

valToFinToVal : {n : ℕ} → (i : Fin n) → valToFin (finToVal i) ≡ i
valToFinToVal zero = refl zero
valToFinToVal (suc n) = ap suc (valToFinToVal n)

finToValToFin : {n : ℕ} → (v : ⟦ fromℕ n ⟧) → finToVal (valToFin v) ≡ v
finToValToFin {zero} ()
finToValToFin {suc n} (inj₁ tt)  = refl (inj₁ tt)
finToValToFin {suc n} (inj₂ v) = ap inj₂ (finToValToFin v)

--  Might want to take a ⟦ fromℕ n ⟧ instead of a Fin n as the second argument here?
combToVecWorks : {n : ℕ} → (c : (fromℕ n) ⇛ (fromℕ n)) → (i : Fin n) → (evalComb c (finToVal i)) ≡ evalVec (combToVec c) i
combToVecWorks c i = (! (finToValToFin _)) ∘ (ap finToVal (! (lookupTab i)))

-- The trickier one

liftFin : {A : Set} → {n : ℕ} → (Fin n → A) → A → Fin (suc n) → A
liftFin f x zero = x
liftFin f x (suc n) = f n

_!!_ : {A : Set} → {n : ℕ} → Vec A n → Fin n → A
_!!_ v i = lookup i v

data vecRep : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (Fin n) n → Set where
  vr-id    : {n : ℕ} → vecRep (id⇛ {fromℕ n}) (upTo n)
  vr-swap  : {n : ℕ}
           → vecRep {suc (suc n)} (swapi {suc n} zero)
                    ((suc zero) ∷ zero ∷ (Data.Vec.map (λ i → suc (suc i)) (upTo n)))
  vr-comp  : {n : ℕ} → {c₁ c₂ : (fromℕ n) ⇛ (fromℕ n)} → {v₁ v₂ : Vec (Fin n) n}
           → vecRep c₁ v₁ → vecRep c₂ v₂
           → vecRep (c₁ ◎ c₂) (tabulate {n} (λ i → (lookup (lookup i v₂) v₁)))
  vr-plus : {n : ℕ} → {c : (fromℕ n) ⇛ (fromℕ n)} → {v : Vec (Fin n) n}
          → vecRep {n} c v
          → vecRep {suc n} (id⇛ ⊕ c) (tabulate (liftFin (λ i → suc (v !! i)) zero))

vecToCombWorks : {n : ℕ} → (v : Vec (Fin n) n) → (i : Fin n) → (evalVec v i) ≡ (evalComb (vecToComb v) (finToVal i))
vecToCombWorks = {!!}










