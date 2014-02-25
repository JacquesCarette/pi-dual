module H where

import Data.Fin as F
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Function renaming (_∘_ to _○_) 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import FT
open import Eval
open import NatSimple using (fromℕ; normal; normalize)

------------------------------------------------------------------------------
{--
We have two views of the type 4:

* semantically as the set {0,1,2,3} 
* syntactically as a family of pi-types with a canonical representative:
    PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE ZERO)))
  whose elements are:
    inj₁ tt
    inj₂ (inj₁ tt)
    inj₂ (inj₂ (inj₁ tt))
    inj₂ (inj₂ (inj₂ (inj₁ tt)))

The following two functions map between a semantic value and a syntactic
element from the canonical representative.

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

_!!_ : {A : Set} → {n : ℕ} → Vec A n → F.Fin n → A
_!!_ v i = lookup i v

evalVec : {n : ℕ} → Vec (F.Fin n) n → F.Fin n → ⟦ fromℕ n ⟧
evalVec vec i = finToVal (vec !! i)

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
combToVec c = tabulate (valToFin ○ evalComb c ○ finToVal)

lemma2 : {n : ℕ} (c : (fromℕ n) ⇛ (fromℕ n)) → (i : F.Fin n) → 
         (evalComb c (finToVal i)) ≡ evalVec (combToVec c) i
lemma2 c i = begin
    (evalComb c ○ finToVal) i
  ≡⟨ sym (finToValToFin _) ⟩
    finToVal ((valToFin ○ evalComb c ○ finToVal) i)
  ≡⟨ cong finToVal (sym (lookupTab {f = valToFin ○ evalComb c ○ finToVal} i)) ⟩
    finToVal ((tabulate (valToFin ○ evalComb c ○ finToVal)) !!  i)
  ≡⟨ refl ⟩ 
    evalVec (combToVec c) i
  ∎

{--

We need another lemma:

combToVec c = combToVec c'

if c and c' have the same normalized types

lemma2a : {A : FT} (c : A ⇛ A) (a : ⟦ normalize A ⟧) →
  let c′ = sym⇛ (normal A) ◎ c ◎ normal A in
    evalComb c′ a ≡ evalVec (combToVec c′) (valToFin a)
lemma2a (swap₊⇛ {b}) a = {!!}
lemma2a swap⋆⇛ a = {!!}
lemma2a id⇛ a = {!!}
lemma2a (sym⇛ c) a = {!!}
lemma2a (c ◎ c₁) a = {!!}
lemma2a (c ⊕ c₁) a = {!!}
lemma2a (c ⊗ c₁) a = {!!}

--}

unite₊ : {A : Set} → ⊥ ⊎ A → A
unite₊ (inj₁ ())
unite₊ (inj₂ y) = y

uniti₊ : {A : Set} → A → ⊥ ⊎ A
uniti₊ a = inj₂ a

swap₊ : {A B : Set} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

unite⋆ : {A : Set} → ⊤ × A → A
unite⋆ (tt , x) = x

uniti⋆ : {A : Set} → A → ⊤ × A
uniti⋆ x = tt , x

swap⋆ : {A B : Set} → A × B → B × A
swap⋆ (a , b) = (b , a)

assocl₊ : {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
assocl₊ (inj₁ a) = inj₁ (inj₁ a)
assocl₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
assocl₊ (inj₂ (inj₂ c)) = inj₂ c

assocr₊ : {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
assocr₊ (inj₁ (inj₁ a)) = inj₁ a
assocr₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
assocr₊ (inj₂ c) = inj₂ (inj₂ c)

assocl⋆ : {A B C : Set} → (A × (B × C)) → ((A × B) × C)
assocl⋆ (a , (b , c)) = ((a , b) , c)

assocr⋆ : {A B C : Set} → ((A × B) × C) → (A × (B × C))
assocr⋆ ((a , b) , c) = (a , (b , c))

distz : { A : Set} → (⊥ × A) → ⊥
distz (() , _)

factorz : {A : Set} → ⊥ → (⊥ × A)
factorz ()

dist : {A B C : Set} → ((A ⊎ B) × C) → (A × C) ⊎ (B × C)
dist (inj₁ x , c) = inj₁ (x , c)
dist (inj₂ y , c) = inj₂ (y , c)

factor : {A B C : Set} → (A × C) ⊎ (B × C) → ((A ⊎ B) × C)
factor (inj₁ (a , c)) = inj₁ a , c
factor (inj₂ (b , c)) = inj₂ b , c

path2Fun : {b₁ b₂ : FT} → (b₁ ⇛ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
path2Fun unite₊⇛ = unite₊
path2Fun uniti₊⇛ = uniti₊
path2Fun swap₊⇛ = swap₊
path2Fun assocl₊⇛ = assocl₊
path2Fun assocr₊⇛ = assocr₊
path2Fun unite⋆⇛ = unite⋆
path2Fun uniti⋆⇛ = uniti⋆
path2Fun swap⋆⇛ = swap⋆
path2Fun assocl⋆⇛ = assocl⋆
path2Fun assocr⋆⇛ = assocr⋆
path2Fun distz⇛ = distz
path2Fun factorz⇛ = factorz
path2Fun dist⇛ = dist
path2Fun factor⇛ = factor
path2Fun id⇛ = id
path2Fun (sym⇛ c) = {!!}
path2Fun (c ◎ c₁) = {!!}
path2Fun (c ⊕ c₁) = {!!}
path2Fun (c ⊗ c₁) = {!!}

normalV : {b : FT} → ⟦ b ⟧ → ⟦ normalize b ⟧
normalV {b} = path2Fun (normal b)


lemma2a : {b₁ b₂ : FT} → (c : b₁ ⇛ b₂) → (v₁ : ⟦ b₁ ⟧) →
          let c' = sym⇛ (normal b₁) ◎ c ◎ normal b₂ in 
          normalV (evalComb c v₁) ≡ evalComb c' (normalV v₁)
lemma2a = {!!}


------------------------------------------------------------------------------
