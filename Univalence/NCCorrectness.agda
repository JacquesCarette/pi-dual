module NCCorrectness where

open import Data.Unit
open import Data.Vec
open import Data.Fin hiding (fromℕ)
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Sum hiding ( map )

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

map!! : {A B : Set} → {n : ℕ} → (f : A → B) → (v : Vec A n) → (i : Fin n)
      → (map f v) !! i ≡ f (v !! i)
map!! {n = zero} f [] ()
map!! {n = suc n} f (x ∷ xs) zero = refl (f x)
map!! {n = suc n} f (x ∷ xs) (suc i) = map!! f xs i

foldrWorks : {A : Set} → {m : ℕ} → (B : ℕ → Set) → (P : (n : ℕ) → Vec A n → B n → Set)
           → (_⊕_ : {n : ℕ} → A → B n → B (suc n)) → (base : B zero)
           → ({n : ℕ} → (a : A) → (v : Vec A n) → (b : B n) → P n v b
              → P (suc n) (a ∷ v) (a ⊕ b))
           → P zero [] base
           → (v : Vec A m)
           → P m v (foldr B _⊕_ base v)
foldrWorks B P combine base pcombine pbase [] = pbase
foldrWorks B P combine base pcombine pbase (x ∷ v) =
  pcombine x v (foldr B combine base v) (foldrWorks B P combine base pcombine pbase v)

-- IDEA: reformulate evaluation as a relation between a combinator and its output vector?
-- Would simplify the correctness condition we're trying to prove 

-- Correctness specifically for the subset of combinators used in vecToComb
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
          → vecRep {suc n} (id⇛ ⊕ c) (zero ∷ (Data.Vec.map suc v))

vecRepWorks : {n : ℕ} → {c : (fromℕ n) ⇛ (fromℕ n)} → {v : Vec (Fin n) n} → vecRep c v → (i : Fin n) → (evalVec v i) ≡ (evalComb c (finToVal i))
vecRepWorks vr-id i = ap finToVal (lookupTab i)
vecRepWorks vr-swap i = {!!}
vecRepWorks (vr-comp vr vr₁) i = {!!}
vecRepWorks {suc n} (vr-plus vr) zero = refl (inj₁ tt)
vecRepWorks (vr-plus {c = c} {v = v} vr) (suc i) =
  evalVec (zero ∷ map suc v) (suc i) ≡⟨ ap finToVal (map!! suc v i) ⟩
  inj₂ (finToVal (v !! i)) ≡⟨ ap inj₂ (vecRepWorks vr i) ⟩
  (evalComb (id⇛ ⊕ c) (finToVal (suc i)) ∎)

vecToCombWorks : {n : ℕ} → (v : Vec (Fin n) n) → (i : Fin n) → (evalVec v i) ≡ (evalComb (vecToComb v) (finToVal i))
vecToCombWorks {n} v =
  foldrWorks
    {fromℕ n ⇛ fromℕ n}
    {n}
    (λ i → fromℕ n ⇛ fromℕ n)
    -- I think we need to rewrite vecToComb using an indexed fold to have all the information
    -- here that we need for the correctness proof [Z]
    (λ n′ v c → (i : Fin n′) → {!!}) -- (evalVec {n′} v i) ≡ (evalComb c (finToVal i)))
    _◎_
    id⇛
    {!!}
    {!!}
    (zipWith makeSingleComb v (upTo n))










