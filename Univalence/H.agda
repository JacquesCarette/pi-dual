-- high-level structure of proof

module H where

import Data.Fin as F
open import Data.Unit
open import Data.Nat
open import Data.Vec
open import Data.Sum
open import Function renaming (_∘_ to _○_) 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import FT
open import Eval
open import NatSimple

------------------------------------------------------------------------------
{--
We have two views of the type 4:

* semantically this is the set {0,1,2,3}
* syntactically this is the pi-type 
    PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE ZERO)))
  whose elements are:
    inj₁ tt
    inj₂ (inj₁ tt)
    inj₂ (inj₂ (inj₁ tt))
    inj₂ (inj₂ (inj₂ (inj₁ tt)))

The following two functions map between a semantic value and a syntactic
element.

The two functions are inverses.

--}

finToVal : {n : ℕ} → F.Fin n → ⟦ fromℕ n ⟧
finToVal F.zero = inj₁ tt
finToVal (F.suc n) = inj₂ (finToVal n)

valToFin : {n : ℕ} → ⟦ fromℕ n ⟧ → F.Fin n
valToFin {zero} ()
valToFin {suc n} (inj₁ tt) = F.zero
valToFin {suc n} (inj₂ v) = F.suc (valToFin v)

finToValToFin : {n : ℕ} → (v : ⟦ fromℕ n ⟧) → finToVal (valToFin v) ≡ v
finToValToFin {zero} ()
finToValToFin {suc n} (inj₁ tt)  = refl 
finToValToFin {suc n} (inj₂ v) = cong inj₂ (finToValToFin v)

{--

We have two views of permutations:
* semantically they are vectors 'v' such that 'i' maps to (v !! i)
     _bijectively_.
* syntactically they are pi-combinators

The semantic view is very simple as shown below.

--}

evalVec : {n : ℕ} → Vec (F.Fin n) n → F.Fin n → ⟦ fromℕ n ⟧
evalVec vec i = finToVal (lookup i vec)

_!!_ : {A : Set} → {n : ℕ} → Vec A n → F.Fin n → A
_!!_ v i = lookup i v

lookupTab : {A : Set} {n : ℕ} {f : F.Fin n → A} →  (i : F.Fin n) → 
            (tabulate f) !! i ≡ (f i)
lookupTab {f = f} F.zero   = refl
lookupTab        (F.suc i) = lookupTab i

{-- 

A pi-combinator 'c : 4 => 4' can be converted to a 
vector 'v' = combToVec c where:

v !! i = valToFin (evalComb c (finToVal i))

The following lemma shows that:
  evaluating a syntactic combinator on a syntactic value
is the same as 
  mapping to a semantic vector and doing a lookup

This establishes the easy part of the equivalence between semantic 
permutations and syntactic ones.

--}

combToVec : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (F.Fin n) n
combToVec c = tabulate (valToFin ○ (evalComb c) ○ finToVal)

lemma2 : {n : ℕ} (c : (fromℕ n) ⇛ (fromℕ n)) → (i : F.Fin n) → 
         (evalComb c (finToVal i)) ≡ evalVec (combToVec c) i
lemma2 c i = 
  (sym (finToValToFin _)) ∘ 
  (cong finToVal (sym (lookupTab {f = λ i → valToFin (evalComb c (finToVal i))} i)))

------------------------------------------------------------------------------
