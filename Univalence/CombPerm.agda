{- Basic combinators, basic permutations, and their relation -}
module CombPerm where

import Data.Fin as F
--
open import Data.Unit
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _>_ )
open import Data.Sum using (inj₁ ; inj₂ ; _⊎_)
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

-- This should really go elsewhere!
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

swapiAct : {n : ℕ} {A : Set} → (i : F.Fin n) → (v : Vec A (suc n)) →
    permute (swapiPerm i) v ≡ insert (remove (F.inject₁ i) v) (F.suc i) (v !! (F.inject₁ i))
swapiAct {zero} () v
swapiAct {suc n} F.zero (x ∷ y ∷ v) = cong (λ z → y ∷ x ∷ z) (idP-id v)
swapiAct {suc n} (F.suc i) (x ∷ v) = cong (_∷_ x) (swapiAct i v)
 
-- swapUpTo i permutes the combinator left by one up to i 
-- if possible values are X a b c Y d e, swapUpTo 3's possible outputs 
-- are a b c X Y d e
swapUpTo : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapUpTo F.zero    = id⇛
swapUpTo (F.suc i) = (id⇛ ⊕ swapUpTo i) ◎ swapi F.zero

-- 1 i times, 0 for the rest
1iP : {n : ℕ} → F.Fin n → Permutation (suc n)
1iP F.zero = idP
1iP (F.suc i) = (F.suc F.zero) ∷ 1iP i

-- The permutation we need:
-- [i, 0, 0, 0, 0, ...]
swapUpToPerm : {n : ℕ} → F.Fin n → Permutation (suc n)
swapUpToPerm F.zero    = idP
swapUpToPerm (F.suc j) = (F.inject₁ (F.suc j)) ∷ idP

-- swapDownFrom i permutes the combinator right by one up to i (the reverse
-- of swapUpTo)
swapDownFrom : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapDownFrom F.zero    = id⇛
swapDownFrom (F.suc i) = swapi F.zero ◎ (id⇛ ⊕ swapDownFrom i)

-- The permutation we need:
-- [1, 1, 1, ..., 1, 0, 0, 0, ...]
-- |--i-1 times---|
swapDownFromPerm : {n : ℕ} → F.Fin n → Permutation (suc n)
swapDownFromPerm = 1iP
-- swapDownFromPerm F.zero = idP
-- swapDownFromPerm (F.suc i) = (F.suc F.zero) ∷ swapDownFromPerm i

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

permToComb : {n : ℕ} → Permutation n → (fromℕ n ⇛ fromℕ n)
permToComb [] = id⇛
permToComb (F.zero ∷ p) = id⇛ ⊕ permToComb p
permToComb (F.suc n ∷ p) = swapm (F.suc n) ◎ (id⇛ ⊕ permToComb p)

swap01 : (n : ℕ) → Permutation n 
swap01 zero = []
swap01 (suc zero) = F.zero ∷ []
swap01 (suc (suc n)) = F.suc (F.zero) ∷ idP

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

push-f-through : {n : ℕ} {A B : Set} → (f : A → B) → (j : F.Fin n) → (p : Permutation n) → (g : F.Fin n → A) → f (lookup j (permute p (tabulate g))) ≡ lookup j (permute p (tabulate (f ○ g)))
push-f-through {zero} f () p g
push-f-through {suc n} f j p g = begin
   f (lookup j (permute p (tabulate g)))            ≡⟨ sym (map!! f (permute p (tabulate g)) j) ⟩
   lookup j (vmap f (permute p (tabulate g)))       ≡⟨ cong (lookup j) (vmap-permute p (tabulate g) f) ⟩
   lookup j (permute p (vmap f (tabulate g)))       ≡⟨ cong (λ x → lookup j (permute p x)) (mapTab f g) ⟩
   lookup j (permute p (tabulate (f ○ g))) ∎
 
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
                                 ≡⟨ cong (λ x → F2 (lookup j x)) (sym (idP-id (tabulate id))) ⟩
    F2 (lookup j (permute idP (tabulate id)))
                                 ≡⟨ push-f-through F2 j idP id ⟩
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
                                   ≡⟨ cong finToVal (push-f-through F.suc j (swapiPerm i) id) ⟩
   finToVal (lookup j (permute (swapiPerm i) (tabulate F.suc))) ∎


-- JC: Need seriously better names for the next 3 lemmas!!
lookup-insert : {n : ℕ} {A : Set} → (v : Vec A (suc n)) → {i : F.Fin (suc n)} → {a : A} → lookup F.zero (insert v (F.suc i) a) ≡ lookup F.zero v
lookup-insert (x ∷ v) = refl

lookup-insert′ : {n : ℕ} {A : Set} (i : F.Fin (suc n)) {a : A} → (v : Vec A n) → lookup i (insert v i a) ≡ a
lookup-insert′ F.zero [] = refl
lookup-insert′ (F.suc ()) []
lookup-insert′ F.zero (x ∷ v) = refl
lookup-insert′ (F.suc i) (x ∷ v) = lookup-insert′ i v

-- this is what is needed in swaDownCorrect, but would be true for any j < i instead of F.suc F.zero < F.suc i
lookup-insert′′ : {n : ℕ} {A : Set} {a : A} → (i : F.Fin n) → (v : Vec A (suc n)) → lookup (F.suc i) v ≡ lookup (F.suc (F.suc i)) (insert v (F.suc F.zero) a)
lookup-insert′′ {zero} () v
lookup-insert′′ {suc n} i (x ∷ v) = refl

lookup-idP-id : {n : ℕ} → (i : F.Fin n) → lookup i (permute idP (tabulate id)) ≡ i
lookup-idP-id i = trans (cong (lookup i) (idP-id (tabulate id))) (lookupTab i)

swapUpToAct : {n : ℕ} {A : Set} → (i : F.Fin n) → (v : Vec A (suc n)) → 
              permute (swapUpToPerm i) v ≡
                insert (remove F.zero v) (F.inject₁ i) (v !! F.zero)
swapUpToAct F.zero v = trans (idP-id v) (remove0 v)
swapUpToAct (F.suc i) (x ∷ v) = cong (λ z → insert z (F.suc (F.inject₁ i)) x) (idP-id v)

swapDownFromVec : {n : ℕ} {A : Set} → (i : F.Fin (suc n)) → Vec A (suc n) →
                  Vec A (suc n)
swapDownFromVec i v = (v !! i) ∷ remove i v

swapDownFromAct : {n : ℕ} → {A : Set} → (i : F.Fin n) → (v : Vec A (suc n)) →
                  permute (swapDownFromPerm i) v ≡
                    swapDownFromVec (F.inject₁ i) v
swapDownFromAct {zero} () _
swapDownFromAct {suc n} F.zero (x ∷ v) =
  begin
    permute (swapDownFromPerm F.zero) (x ∷ v)
      ≡⟨ refl ⟩
    permute idP (x ∷ v)
      ≡⟨ idP-id (x ∷ v) ⟩
    swapDownFromVec F.zero (x ∷ v) ∎
swapDownFromAct {suc zero} (F.suc ()) _
swapDownFromAct {suc (suc n)} (F.suc i) (x ∷ y ∷ v) =
  begin
    permute (swapDownFromPerm (F.suc i)) (x ∷ y ∷ v)
      ≡⟨ refl ⟩
    permute (F.suc F.zero ∷ 1iP i) (x ∷ y ∷ v)
      ≡⟨ refl ⟩
    insert (permute (swapDownFromPerm i) (y ∷ v)) (F.suc F.zero) x
      ≡⟨ cong (λ q → insert q (F.suc F.zero) x) (swapDownFromAct i (y ∷ v)) ⟩
    insert (swapDownFromVec (F.inject₁ i) (y ∷ v)) (F.suc F.zero) x
      ≡⟨ refl ⟩
    ((y ∷ v) !! (F.inject₁ i)) ∷ x ∷ remove (F.inject₁ i) (y ∷ v)
      ≡⟨ refl ⟩
    swapDownFromVec (F.inject₁ (F.suc i)) (x ∷ y ∷ v) ∎

swapmVec : {n : ℕ} {A : Set} → F.Fin n → Vec A n → Vec A n
swapmVec {zero} () _
swapmVec {suc n} F.zero v = v
swapmVec {suc zero} (F.suc ()) _
swapmVec {suc (suc n)} (F.suc i) (x ∷ v) =
  (v !! i) ∷ (insert (remove i v) i x)

swapOneVec : {n : ℕ} {A : Set} → F.Fin n → Vec A n → Vec A n
swapOneVec {zero} () _
swapOneVec {suc n} F.zero v = v
swapOneVec {suc n} (F.suc i) v = (v !! (F.suc i)) ∷ (remove (F.suc i) v)

swapOneAct : {n : ℕ} {A : Set} → (i : F.Fin n) → (v : Vec A n) →
           permute (swapOne i) v ≡ swapOneVec i v
swapOneAct {zero} () _
swapOneAct {suc n} F.zero (x ∷ v) = cong (_∷_ x) (idP-id v)
swapOneAct {suc zero} (F.suc ()) v
swapOneAct {suc (suc n)} (F.suc F.zero) (x ∷ y ∷ v) = cong (λ z → y ∷ x ∷ z) (idP-id v)
swapOneAct {suc (suc n)} (F.suc (F.suc i)) (x ∷ v) = 
  begin
    permute (swapOne (F.suc (F.suc i))) (x ∷ v)
        ≡⟨ refl ⟩
    insert (permute (swapOne (F.suc i)) v) (F.suc F.zero) x
        ≡⟨ cong (λ y → insert y (F.suc F.zero) x) (swapOneAct (F.suc i) v) ⟩
    insert (swapOneVec (F.suc i) v) (F.suc F.zero) x
        ≡⟨ refl ⟩ -- lots of β reduction
    ((x ∷ v) !! (F.suc (F.suc i))) ∷ (remove (F.suc (F.suc i)) (x ∷ v))
        ≡⟨ refl ⟩
    swapOneVec (F.suc (F.suc i)) (x ∷ v)
  ∎

swapmAct : {n : ℕ} {A : Set} → (i : F.Fin n) → (v : Vec A n) →
           permute (swapmPerm i) v ≡ swapmVec i v
swapmAct {zero} () _
swapmAct {suc n} F.zero (x ∷ v) =
  begin
    permute (swapmPerm F.zero) (x ∷ v)
      ≡⟨ idP-id (x ∷ v) ⟩
    swapmVec F.zero (x ∷ v) ∎
swapmAct {suc zero} (F.suc ()) _
swapmAct {suc (suc n)} (F.suc F.zero) (x ∷ y ∷ v) = cong (λ z → y ∷ x ∷ z) (idP-id v)
swapmAct {suc (suc n)} (F.suc (F.suc i)) (x ∷ y ∷ v) =
  begin
    permute (swapmPerm (F.suc (F.suc i))) (x ∷ y ∷ v)
      ≡⟨ refl ⟩
    permute (F.suc (F.suc i) ∷ swapOne (F.suc i)) (x ∷ y ∷ v)
      ≡⟨ refl ⟩
    insert (permute (swapOne (F.suc i)) (y ∷ v)) (F.suc (F.suc i)) x
      ≡⟨ cong (λ z → insert z (F.suc (F.suc i)) x) (swapOneAct (F.suc i) (y ∷ v)) ⟩
    insert (swapOneVec (F.suc i) (y ∷ v)) (F.suc (F.suc i)) x
      ≡⟨ refl ⟩  -- by lots of beta on both sides
    ((y ∷ v) !! (F.suc i)) ∷ (insert (remove (F.suc i) (y ∷ v)) (F.suc i) x)
      ≡⟨ refl ⟩
    swapmVec (F.suc (F.suc i)) (x ∷ y ∷ v) ∎
  
swapi≡swap01 : {n : ℕ} → (j : F.Fin (suc (suc n))) →  evalComb (assocl₊⇛ ◎ (swap₊⇛ ⊕ id⇛) ◎ assocr₊⇛) (finToVal j) ≡ finToVal (evalPerm (swap01 (suc (suc n))) j)
swapi≡swap01 F.zero = refl
swapi≡swap01 (F.suc F.zero) = refl
swapi≡swap01 (F.suc (F.suc j)) = sym (trans 
    (cong (λ x → finToVal (lookup j x)) (idP-id _)) 
    (cong finToVal (lookupTab j)))

-- this is the raw swap01 vector
swap01vec : {n : ℕ} → Vec (F.Fin (2 + n)) (2 + n)
swap01vec = F.suc F.zero ∷ F.zero ∷ tabulate (F.suc ○ F.suc)

-- this is the one we 'naturally' get via permutation
swap01vec′ : (n : ℕ) → Vec (F.Fin (2 + n)) (2 + n)
swap01vec′ n = permute (swap01 (suc (suc n))) (tabulate id)

-- but they are the same!
swap01Correct : (n : ℕ) → swap01vec′ n ≡ swap01vec {n}
swap01Correct zero = refl
swap01Correct (suc n) = cong (λ x → F.suc F.zero ∷ F.zero ∷ x) (idP-id _)

newlemma6 : {m n : ℕ} → (i : F.Fin n) → (v : Vec (F.Fin m) n) →
            (vmap F.suc (insert (vmap F.suc v) (F.inject₁ i) F.zero)) ∘̬′ swap01vec
          ≡ insert (vmap F.suc (vmap F.suc v)) (F.inject₁ i) F.zero
newlemma6 F.zero (x ∷ v) =
  let suc2v = vmap F.suc (vmap F.suc v) in
  begin
  vmap F.suc (insert (vmap F.suc (x ∷ v)) F.zero F.zero) ∘̬′ swap01vec
    ≡⟨ refl ⟩
  (F.suc F.zero ∷ F.suc (F.suc x) ∷ suc2v) ∘̬′ swap01vec
    ≡⟨ refl ⟩
  F.zero ∷ ((F.suc (F.suc x) ∷ suc2v) ∘̬′ swap01vec)
    ≡⟨ refl ⟩
  F.zero ∷ ((tabulate (F.suc ○ F.suc)) !! x) ∷ (suc2v ∘̬′ swap01vec)
    ≡⟨ cong (λ x → F.zero ∷ x ∷ suc2v ∘̬′ swap01vec) (lookupTab x) ⟩
  F.zero ∷ F.suc (F.suc x) ∷ (suc2v ∘̬′ swap01vec)
    ≡⟨ cong (λ q → F.zero ∷ F.suc (F.suc x) ∷ q) (map2+id v) ⟩
  F.zero ∷ F.suc (F.suc x) ∷ suc2v
    ≡⟨ refl ⟩
  insert (vmap F.suc (vmap F.suc (x ∷ v))) F.zero F.zero ∎
newlemma6 (F.suc i) (x ∷ v) =
  let v′ = insert (vmap F.suc v) (F.inject₁ i) F.zero in
  begin
  vmap F.suc (insert (vmap F.suc (x ∷ v)) (F.inject₁ (F.suc i)) F.zero) ∘̬′ swap01vec
    ≡⟨ refl ⟩
  (tabulate (F.suc ○ F.suc) !! x) ∷ ((vmap F.suc v′) ∘̬′ swap01vec)
    ≡⟨ cong (λ q → q ∷ ((vmap F.suc v′) ∘̬′ swap01vec)) (lookupTab x) ⟩
  F.suc (F.suc x) ∷ ((vmap F.suc v′) ∘̬′ swap01vec)
    ≡⟨ cong (_∷_ (F.suc (F.suc x))) (newlemma6 i v) ⟩
  F.suc (F.suc x) ∷ insert (vmap F.suc (vmap F.suc v)) (F.inject₁ i) F.zero
    ≡⟨ refl ⟩
  insert (vmap F.suc (vmap F.suc (x ∷ v))) (F.inject₁ (F.suc i)) F.zero ∎
  

---
--- testing

tests01 : Vec (F.Fin five) five
tests01 = permute (swap01 five) (allFin five)

tests02 : (fromℕ five ⇛ fromℕ five)
tests02 = permToComb (swap01 five)

tests03 : Vec ⟦ PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE ZERO)))) ⟧ five
tests03 = tabulate (λ i → evalComb tests02 (finToVal i))

l6test1 : _
l6test1 = (vmap F.suc (insert (tabulate {4} F.suc) (F.suc (F.suc F.zero)) F.zero)) ∘̬ (F.suc F.zero ∷ F.zero ∷ tabulate (F.suc ○ F.suc))

l6test1b : _
l6test1b = permute (swapUpToPerm {5} (F.suc (F.suc (F.suc F.zero)))) (tabulate id)

test1a : Vec _ 5 -- Vec (F.Fin 5) 5
--test1a = (insert (tabulate {4} F.suc) (F.suc F.zero) F.zero)
test1a = (vmap F.suc (insert (tabulate {4} F.suc) (F.suc F.zero) F.zero))
       ∘̬ (F.suc F.zero ∷ F.zero ∷ tabulate (λ x → F.suc (F.suc x)))

test1b : Vec _ 5
test1b = insert (tabulate (F.suc ○ F.suc)) (F.suc F.zero) F.zero

aPerm : Permutation six
aPerm = (F.suc (F.suc (F.suc F.zero))) ∷ (F.suc F.zero) ∷ (F.suc F.zero) ∷ F.zero ∷ F.zero ∷ F.zero ∷ []

test5 : Vec (F.Fin six) six
test5 = permute aPerm (tabulate id)

combToVec : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (F.Fin n) n
combToVec c = tabulate (valToFin ○ (evalComb c) ○ finToVal)

test6a : Vec (F.Fin six) six
test6a = combToVec (swapUpTo (F.suc F.zero))

test6b : Vec (F.Fin six) six
test6b = permute (swapUpToPerm (F.suc F.zero)) (tabulate id)

test7a : Vec (F.Fin six) six
test7a = combToVec (swapUpTo (F.zero))

test7b : Vec (F.Fin six) six
test7b = permute (swapUpToPerm (F.zero)) (tabulate id)

test8a : Vec (F.Fin six) six
test8a = combToVec (swapUpTo (F.suc (F.suc (F.suc (F.zero)))))

test8b : Vec (F.Fin six) six
test8b = permute (swapUpToPerm (F.suc (F.suc (F.suc F.zero)))) (tabulate id)

test9 : Vec (F.Fin six) six
test9 = permute (swapOne (F.suc (F.suc (F.suc F.zero)))) (tabulate id)

test10 : Vec (F.Fin six) six
test10 = permute (swapmPerm (F.suc (F.suc (F.suc F.zero)))) (tabulate id)
