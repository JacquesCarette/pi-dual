{- This is a copy of Sane, but building upon a rather different notion of permutation -}
module Sane2 where

import Data.Fin as F
--
-- open import Data.Empty
open import Data.Unit
-- open import Data.Unit.Core
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _>_ )
open import Data.Sum using (inj₁ ; inj₂ ; _⊎_)
-- open import Data.Product renaming (map to _×→_)
open import Data.Vec
open import Function using ( id ) renaming (_∘_ to _○_) 
open import Relation.Binary  -- to make certain goals look nicer
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; trans ; subst ; module ≡-Reasoning )
open ≡-Reasoning

-- start re-splitting things up, as this is getting out of hand
open import FT -- Finite Types
open import VecHelpers
open import NatSimple
open import Eval
open import Permutations

-- not sure where else to put this [Z][A]
hetType : {A B : Set} → (a : A) → A ≡ B → B
hetType a refl = a

-- construct a combinator which represents the swapping of the i-th and 
-- (i+1)-th 'bit' of a finite type.  
-- Best to think of this as an 'elementary permutation', in the same way
-- we have 'elementary matrices' (which turn out to be permutations when they
-- are unitary).
swapi : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapi {zero}  ()
swapi {suc n} F.zero    = assocl₊⇛ ◎ (swap₊⇛ ⊕ id⇛) ◎ assocr₊⇛
swapi {suc n} (F.suc i) = id⇛ ⊕ swapi {n} i

swapiPerm : {n : ℕ} → F.Fin n → Permutation (suc n)
swapiPerm {zero} ()
swapiPerm {suc n} F.zero = F.suc F.zero ∷ idP
swapiPerm {suc n} (F.suc i) = F.zero ∷ swapiPerm {n} i

-- swapUpTo i permutes the combinator left by one up to i 
-- if possible values are X a b c Y d e, swapUpTo 3's possible outputs 
-- are a b c X Y d e
swapUpTo : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapUpTo F.zero    = id⇛
swapUpTo (F.suc i) = (id⇛ ⊕ swapUpTo i) ◎ swapi F.zero

-- The permutation we need:
-- [i, i-1, i-2, ..., i-i, 0, 0, 0, ...]
swapUpToPerm : {n : ℕ} → F.Fin n → Permutation (suc n)
swapUpToPerm F.zero    = idP
swapUpToPerm (F.suc j) = (F.inject₁ (F.suc j)) ∷ swapUpToPerm j

-- swapDownFrom i permutes the combinator right by one up to i (the reverse
-- of swapUpTo)
swapDownFrom : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapDownFrom F.zero    = id⇛
swapDownFrom (F.suc i) = swapi F.zero ◎ (id⇛ ⊕ swapDownFrom i)

-- The permutation we need:
-- [1, 1, 1, ..., 1, 0, 0, 0, ...]
-- |--i-1 times---|
swapDownFromPerm : {n : ℕ} → F.Fin n → Permutation (suc n)
swapDownFromPerm F.zero = idP
swapDownFromPerm (F.suc i) = (F.suc F.zero) ∷ swapDownFromPerm i

-- TODO: verify that this is actually correct
-- Idea: To swap n < m with each other, swap n, n + 1, ... , m - 1, m, then
-- go back down, so that m and n are swapped and everything else is in the
-- same spot
-- makeSingleComb {combinator size} (arrayElement) (arrayIndex),
-- gives a combinator which 'does' that, assuming i<j, else id⇛
makeSingleComb : {n : ℕ} → F.Fin n → F.Fin n → (fromℕ n) ⇛ (fromℕ n)
makeSingleComb F.zero   F.zero     = id⇛
makeSingleComb F.zero   (F.suc i)  = id⇛
makeSingleComb (F.suc j) F.zero   = swapDownFrom j ◎ swapi j ◎ swapUpTo j
makeSingleComb (F.suc j) (F.suc i) = id⇛ ⊕ makeSingleComb j i

-- swapm i returns a combinator that swaps 0 and i
swapm : {n : ℕ} → F.Fin n → (fromℕ n) ⇛ (fromℕ n)
swapm F.zero = id⇛
swapm (F.suc i) = swapDownFrom i ◎ swapi i ◎ swapUpTo i

swapOne : {n : ℕ} → (i : F.Fin n) → Permutation n
swapOne F.zero = idP
swapOne {suc zero} (F.suc ())
swapOne {suc (suc n)} (F.suc i) = (F.suc F.zero) ∷ swapOne i

-- which should correspond to this permutation!!
swapmPerm : {n : ℕ} → F.Fin n → Permutation n
swapmPerm F.zero = idP
swapmPerm {suc n} (F.suc i) = F.suc i ∷ swapOne i

-- Correctness: after putting together i indices, the partial combinator c' is
-- represented by the vector [1, 2, ... , n - (i +1)] ++ (last i v)
--
-- Might want to bake in the correctness proof here---have the output be a
-- combinator c, a vector v, and a proof that vecRep c v, then we just prove
-- that the vector at the end is just the vector from the beginning
--
-- Or just put them together and prove that they're related by vecRep with
-- foldrWorks and that the end vector is the input vector; this is probably simpler
-- (and is the approach currently reflected in the code below)

-- swapInd i j returns a vector v′ where v′[i] = j, v′[j] = i, and v′[k] = k
-- where k != j and k != i

zeroIfEq : {n n′ : ℕ} → F.Fin n → F.Fin n → F.Fin (suc n′) → F.Fin (suc n′)
zeroIfEq F.zero    F.zero   ret = F.zero
zeroIfEq F.zero   (F.suc j) ret = ret
zeroIfEq (F.suc i) F.zero   ret = ret
zeroIfEq (F.suc i) (F.suc j) ret = zeroIfEq i j ret

{-
swapIndFn : {n : ℕ} → F.Fin n → F.Fin n → (F.Fin n → F.Fin n)
swapIndFn               F.zero     j          F.zero   = j
swapIndFn               (F.suc i)  F.zero     F.zero   = F.suc i
swapIndFn               (F.suc i) (F.suc j)   F.zero   = F.zero
swapIndFn               F.zero     F.zero    (F.suc x) = F.suc x
swapIndFn {suc zero}    F.zero   (F.suc ()) (F.suc x)
swapIndFn {suc (suc n)} F.zero   (F.suc j)  (F.suc x) = zeroIfEq j x (F.suc x)
swapIndFn               (F.suc i)  F.zero    (F.suc x) = zeroIfEq i x (F.suc x)
swapIndFn               (F.suc i) (F.suc j)  (F.suc x) = F.suc (swapIndFn i j x)

swapInd : {n : ℕ} → F.Fin n → F.Fin n → Vec (F.Fin n) n
swapInd i j = tabulate (swapIndFn i j)

swapIndVec : {n : ℕ} → F.Fin n → F.Fin n → Vec (F.Fin n) n → Vec (F.Fin n) n
swapIndVec i j v = tabulate (λ k → v !! swapIndFn i j k)

-- vecRep c v relates a combinator c over normal types to the output
-- vector it results in. This works only over a subset of combinators
-- used in decompilation.
data vecRep : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (F.Fin n) n → Set where
  vr-id    : {n : ℕ} → vecRep (id⇛ {fromℕ n}) (upTo n)
  vr-swap  : {n : ℕ} → vecRep {suc (suc n)} (swapi {suc n} F.zero) swap01
  vr-comp  : {n : ℕ} {c₁ c₂ : (fromℕ n) ⇛ (fromℕ n)} {v₁ v₂ : Vec (F.Fin n) n} → 
    vecRep c₁ v₁ → vecRep c₂ v₂ → 
    vecRep (c₁ ◎ c₂) (v₁ ∘̬ v₂)
  vr-plus : {n : ℕ} → {c : (fromℕ n) ⇛ (fromℕ n)} → {v : Vec (F.Fin n) n} → 
    vecRep {n} c v → 
    vecRep {suc n} (id⇛ ⊕ c) (F.zero ∷ (vmap F.suc v))

-- the library definition of + on Fin isn't what we want here, ugh
_+F_ : {m n : ℕ} → F.Fin (suc m) → F.Fin n → F.Fin (m + n)
_+F_ {m} {zero} F.zero ()
_+F_ {m} {suc n} F.zero j = inj+ {suc n} {m} j
_+F_ {zero} {n} (F.suc ()) _
_+F_ {suc m} {n} (F.suc i) j = F.suc (i +F j)

vecToComb : {n : ℕ} → Vec (F.Fin n) n → (fromℕ n) ⇛ (fromℕ n)
vecToComb {n} vec = 
  foldr (λ i → fromℕ n ⇛ fromℕ n) _◎_ id⇛ (map (λ i → makeSingleComb (vec !! i) i) (upTo n))
-}
finToVal : {n : ℕ} → F.Fin n → ⟦ fromℕ n ⟧
finToVal F.zero = inj₁ tt
finToVal (F.suc n) = inj₂ (finToVal n)

valToFin : {n : ℕ} → ⟦ fromℕ n ⟧ → F.Fin n
valToFin {zero} ()
valToFin {suc n} (inj₁ tt) = F.zero
valToFin {suc n} (inj₂ v) = F.suc (valToFin v)

finToValToFin : {n : ℕ} → (v : ⟦ fromℕ n ⟧) → finToVal (valToFin v) ≡ v
finToValToFin {zero} ()
finToValToFin {suc n} (inj₁ tt)  = refl -- (inj₁ tt)
finToValToFin {suc n} (inj₂ v) = cong inj₂ (finToValToFin v)

valToFinToVal : {n : ℕ} → (i : F.Fin n) → valToFin (finToVal i) ≡ i
valToFinToVal F.zero = refl -- F.zero
valToFinToVal (F.suc i) = cong F.suc (valToFinToVal i)

{-
combToVec : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (F.Fin n) n
combToVec c = tabulate (valToFin ○ (evalComb c) ○ finToVal)

--  Might want to take a ⟦ fromℕ n ⟧ instead of a Fin n as the second
--  argument here?
combToVecWorks : {n : ℕ} → (c : (fromℕ n) ⇛ (fromℕ n)) → 
  (i : F.Fin n) → (evalComb c (finToVal i)) ≡ evalVec (combToVec c) i
combToVecWorks c i = (sym (finToValToFin _)) ∘ (cong finToVal (sym (lookupTab i)))

-- This lemma is the hammer that will let us use vecRep to (hopefully) simply
-- prove some lemmas about the helper functions used in vecToComb, then apply
-- vecRepWorks at the end to make sure they all "do the right thing"
vecRepWorks : {n : ℕ} → {c : (fromℕ n) ⇛ (fromℕ n)} → {v : Vec (F.Fin n) n} → 
  vecRep c v → (i : F.Fin n) → (evalVec v i) ≡ (evalComb c (finToVal i))
vecRepWorks vr-id i = cong finToVal (lookupTab i)
vecRepWorks vr-swap F.zero = refl -- (inj₂ (inj₁ tt))
vecRepWorks vr-swap (F.suc F.zero) = refl -- (inj₁ tt)
vecRepWorks {suc (suc n)} vr-swap (F.suc (F.suc i)) = cong finToVal (lookupTab i)
vecRepWorks (vr-comp {n} {c₁} {c₂} {v₁} {v₂} vr vr₁) i = begin
  finToVal (lookup i (tabulate (λ j → lookup (lookup j v₁) v₂))) 
 ≡⟨ cong finToVal (lookup∘tabulate i (λ j → lookup (lookup j v₁) v₂)) ⟩ 
  finToVal (lookup (lookup i v₁) v₂) 
 ≡⟨ cong (λ x → finToVal (lookup x v₂)) (lookupToEvalVec i v₁) ⟩ 
  finToVal (lookup (valToFin (evalVec v₁ i)) v₂) 
 ≡⟨ cong (λ x → finToVal (lookup (valToFin x) v₂)) (vecRepWorks vr i) ⟩ 
  finToVal (lookup (valToFin (evalComb c₁ (finToVal i))) v₂)
 ≡⟨ cong finToVal (lookupToEvalVec (valToFin (evalComb c₁ (finToVal i))) v₂) ⟩ 
  finToVal (valToFin (evalVec v₂ (valToFin (evalComb c₁ (finToVal i)))))
 ≡⟨ finToValToFin (evalVec v₂ (valToFin (evalComb c₁ (finToVal i)))) ⟩ 
 evalVec v₂ (valToFin (evalComb c₁ (finToVal i)))
 ≡⟨ vecRepWorks vr₁ (valToFin (evalComb c₁ (finToVal i))) ⟩ 
 evalComb c₂ (finToVal (valToFin (evalComb c₁ (finToVal i))))
 ≡⟨ cong (evalComb c₂) (finToValToFin (evalComb c₁ (finToVal i))) ⟩ 
 evalComb (c₁ ◎ c₂) (finToVal i) ∎
vecRepWorks {suc n} (vr-plus vr) F.zero = refl -- (inj₁ tt)
vecRepWorks (vr-plus {c = c} {v = v} vr) (F.suc i) = begin
  evalVec (F.zero ∷ vmap F.suc v) (F.suc i)  ≡⟨ cong finToVal (map!! F.suc v i) ⟩
  inj₂ (finToVal (v !! i))                  ≡⟨ cong inj₂ (vecRepWorks vr i) ⟩
  (evalComb (id⇛ ⊕ c) (finToVal (F.suc i)) ∎)


------------------------------------------------------------------
-- Goal: 

lemma1 : {n : ℕ} (v : Vec (F.Fin n) n) → (i : F.Fin n) → 
    (evalVec v i) ≡ (evalComb (vtc′ v) (finToVal i))
lemma1 v i = sym (vecToCombWorks v i)

lemma2 : {n : ℕ} (c : (fromℕ n) ⇛ (fromℕ n)) → (i : F.Fin n) → 
    (evalComb c (finToVal i)) ≡ evalVec (combToVec c) i
lemma2 c i = combToVecWorks c i

----------------------------------------------------------------
-}

combToPermi : {n : ℕ} (c : fromℕ (suc n) ⇛ fromℕ (suc n))
                      (i : F.Fin (suc n)) →
                      Permutation (suc (n F.ℕ-ℕ i))
combToPermi c F.zero = {!max - evalCombB c max ∷ []!}
combToPermi c (F.suc i) = ? ∷ ? -- combToPermi c (F.inject₁ i)


-- Suppose we have some combinator c, its output vector v, and the corresponding
-- permutation p. We construct p by looking at how many places each element is
-- displaced from its index in v *to the right* (if it's where it "should" be or
-- to the left, just return 0).

-- In other words, if v[i] = j, then p[j] = j - i. That is, if j is in location
-- i, j - i is how many spaces to the right (if any) j appears from its own
-- index. Note that if v[i] = j, then c(i) = j, and inv(c)(j) = i. This suggests
-- that if I can write a tabulate function for permutations, the permutation for
-- a combinator c will be "tabulate (∩ -> i - (evalCombB c i))", modulo type
-- coercions.
combToPerm : {n : ℕ} → (fromℕ n ⇛ fromℕ n) → Permutation n
combToPerm {zero} c = []
combToPerm {suc n} c = {!!}

permToComb : {n : ℕ} → Permutation n → (fromℕ n ⇛ fromℕ n)
permToComb [] = id⇛
permToComb (F.zero ∷ p) = id⇛ ⊕ permToComb p
permToComb (F.suc n ∷ p) = swapm (F.suc n) ◎ (id⇛ ⊕ permToComb p)

swap01 : (n : ℕ) → Permutation n 
swap01 zero = []
swap01 (suc zero) = F.zero ∷ []
swap01 (suc (suc n)) = F.suc (F.zero) ∷ idP

tests01 : Vec (F.Fin five) five
tests01 = permute (swap01 five) (allFin five)

tests02 : (fromℕ five ⇛ fromℕ five)
tests02 = permToComb (swap01 five)

tests03 : Vec ⟦ PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE ZERO)))) ⟧ five
tests03 = tabulate (λ i → evalComb tests02 (finToVal i))

vmap-insert : {n : ℕ} {A B : Set} {x : A} → (v : Vec A n) → (f : A → B) → (i : F.Fin (suc n)) → vmap f (insert v i x) ≡ insert (vmap f v) i (f x)
vmap-insert {zero} [] f F.zero = refl
vmap-insert {zero} [] f (F.suc ())
vmap-insert {suc n} v f F.zero = refl
vmap-insert {suc n} {x = x} (y ∷ v) f (F.suc i) = cong (_∷_ (f y)) (vmap-insert v f i)

vmap-permute : {n : ℕ} {A B : Set} → (p : Permutation n) → (v : Vec A n) → (f : A → B) → vmap f (permute p v) ≡ permute p (vmap f v)
vmap-permute {zero} [] [] f = refl
vmap-permute {suc n} (i ∷ p) (x ∷ v) f = trans (vmap-insert (permute p v) f i) (cong (λ y → insert y i (f x)) (vmap-permute p v f))

evalPerm : {n : ℕ} → Permutation n → F.Fin n → F.Fin n
evalPerm {zero} _ ()
evalPerm {suc n} p k = lookup k (permute p (allFin (suc n)))

testP5 : Vec (F.Fin five) five
testP5 = permute (swapmPerm (F.inject (F.fromℕ three))) (allFin five)

pushVal : {n : ℕ} → (j : ⟦ fromℕ n ⟧) → {k : F.Fin n} → valToFin j ≡ k → j ≡ finToVal k
pushVal j pf = trans (sym (finToValToFin j)) (cong finToVal pf)

swapiCorrect : {n : ℕ} → (i : F.Fin n) → (j : F.Fin (1 + n)) → evalComb (swapi i) (finToVal j) ≡ finToVal (evalPerm (swapiPerm i) j)
swapiCorrect {zero} () _
swapiCorrect {suc n} F.zero F.zero = refl
swapiCorrect {suc zero} F.zero (F.suc F.zero) = refl
swapiCorrect {suc zero} F.zero (F.suc (F.suc ()))
swapiCorrect {suc zero} (F.suc ()) j
swapiCorrect {suc (suc n)} (F.suc i) F.zero = refl
swapiCorrect {suc (suc n)} F.zero (F.suc F.zero) = refl
swapiCorrect {suc (suc n)} F.zero (F.suc (F.suc j)) = cong finToVal
  let F2 = F.suc ○ F.suc in
  begin
    F2 j
                                 ≡⟨ cong F2 (sym (lookupTab {f = id} j)) ⟩
    F2 (lookup j (tabulate id))
                                 ≡⟨ sym (map!! F2 (tabulate id) j) ⟩
    lookup j (vmap F2 (tabulate id))
                                 ≡⟨ cong (lookup j) (mapTab F2 id) ⟩
    lookup j (tabulate F2)
                                 ≡⟨ cong (lookup j) (sym (idP-id (tabulate F2))) ⟩
    lookup j (permute idP (tabulate F2)) ∎ 
swapiCorrect {suc (suc n)} (F.suc i) (F.suc j) =
  begin
   evalComb (swapi (F.suc i)) (finToVal (F.suc j))
                                   ≡⟨ refl ⟩
   inj₂ (evalComb (swapi i) (finToVal j))
                                   ≡⟨ cong inj₂ (swapiCorrect {suc n} i j) ⟩
   inj₂ (finToVal (evalPerm (swapiPerm i) j))
                                   ≡⟨ refl ⟩
   inj₂ (finToVal (lookup j (permute (swapiPerm i) (tabulate id))))
                                   ≡⟨ refl ⟩
   finToVal (F.suc (lookup j (permute (swapiPerm i) (tabulate id))))
                                   ≡⟨ cong finToVal (sym (map!! F.suc (permute (swapiPerm i) (tabulate id)) j)) ⟩
   finToVal (lookup j (vmap F.suc (permute (swapiPerm i) (tabulate id))))
                                   ≡⟨ cong (λ x → finToVal (lookup j x)) (vmap-permute (swapiPerm i) (tabulate id) F.suc) ⟩
   finToVal (lookup j (permute (swapiPerm i) (vmap F.suc (tabulate id))))
                                   ≡⟨ cong (λ x → finToVal (lookup j (permute (swapiPerm i) x))) (mapTab F.suc id) ⟩
   finToVal (lookup j (permute (swapiPerm i) (tabulate F.suc))) ∎


swapmCorrect : {n : ℕ} → (i j : F.Fin n) → valToFin (evalComb (swapm i) (finToVal j)) ≡ evalPerm (swapmPerm i) j
swapmCorrect {zero} () _
swapmCorrect {suc n} F.zero j = begin
    valToFin (finToVal j)
                              ≡⟨ valToFinToVal j ⟩
    j
                              ≡⟨ sym (lookupTab {f = id} j) ⟩
    lookup j (tabulate id)
                              ≡⟨ sym (cong (lookup j) (idP-id (tabulate id))) ⟩
    lookup j (permute idP (tabulate id)) ∎
swapmCorrect {suc zero} (F.suc ()) F.zero
swapmCorrect {suc (suc n)} (F.suc i) F.zero =
    -- this isn't really the right way to do it (need to deal with swapDownFrom first), 
    -- but it shows how to use swapiCorrect and pushVal together.  
    let k = (evalComb (swapDownFrom i) (inj₁ tt)) in
    begin
    valToFin (evalComb (swapm (F.suc i)) (inj₁ tt)) 
                             ≡⟨ refl ⟩
    valToFin (evalComb (swapUpTo i) (evalComb (swapi i) k))
                             ≡⟨ {!!} ⟩
    valToFin (evalComb (swapUpTo i) (evalComb (swapi i) (finToVal (valToFin k))))
                             ≡⟨ cong (λ x → valToFin (evalComb (swapUpTo i) x)) (swapiCorrect i (valToFin k)) ⟩
    valToFin (evalComb (swapUpTo i) (finToVal (evalPerm (swapiPerm i) (valToFin k))))
                             ≡⟨ {!!} ⟩
    {!!} ∎
swapmCorrect {suc n} (F.suc i) (F.suc j) = {!!}

lemma1 : {n : ℕ} (p : Permutation n) → (i : F.Fin n) → 
    valToFin (evalComb (permToComb p) (finToVal i)) ≡ evalPerm p i 
lemma1 {zero} [] ()
lemma1 {suc n} (F.zero ∷ p) F.zero = refl
lemma1 {suc zero} (F.zero ∷ p) (F.suc ())
lemma1 {suc (suc n)} (F.zero ∷ p) (F.suc i) =  begin
    F.suc (valToFin (evalComb (permToComb p) (finToVal i))) 
         ≡⟨ cong F.suc (lemma1 p i) ⟩
    F.suc (evalPerm p i)
         ≡⟨ refl ⟩
    F.suc (lookup i (permute p (tabulate id)))
         ≡⟨ sym (map!! F.suc (permute p (tabulate id)) i) ⟩
    lookup i (vmap F.suc (permute p (tabulate id)))
         ≡⟨ cong (lookup i) (vmap-permute p (tabulate id) F.suc) ⟩
    lookup i (permute p (vmap F.suc (tabulate id)))
         ≡⟨ cong (λ x -> lookup i (permute p x)) (mapTab F.suc id) ⟩ 
    evalPerm (F.zero ∷ p) (F.suc i) ∎
lemma1 {suc n} (F.suc j ∷ p) i = {!!}

lemma2 : {n : ℕ} (c : (fromℕ n) ⇛ (fromℕ n)) → (i : F.Fin n) → 
    (evalComb c (finToVal i)) ≡ finToVal (evalPerm (combToPerm c) i)
lemma2 c i = {!!}

aPerm : Permutation six
aPerm = (F.suc (F.suc (F.suc F.zero))) ∷ (F.suc F.zero) ∷ (F.suc F.zero) ∷ F.zero ∷ F.zero ∷ F.zero ∷ []

test5 : Vec (F.Fin six) six
test5 = permute aPerm (tabulate id)
