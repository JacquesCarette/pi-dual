-- This contains material which used to be in the Sane module, but is no
-- longer used.  It is not junk, so it is kept here, as we may need to
-- resurrect it.

module Obsolete where

import Data.Fin as F
--
open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Data.Vec
open import Function renaming (_∘_ to _○_) 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- start re-splitting things up, as this is getting out of hand
open import FT -- Finite Types
open import VecHelpers
open import NatSimple
open import Eval

open import Sane

{--
  foldrWorks
    {fromℕ n ⇛ fromℕ n}
    {n}
    (λ i → fromℕ n ⇛ fromℕ n)
    -- I think we need to rewrite vecToComb using an indexed fold to have all
    -- the information here that we need for the correctness proof [Z]
    (λ n′ v c → (i : F.Fin n′) → {!!}) 
    -- (evalVec {n′} v i) ≡ (evalComb c (finToVal i)))
    _◎_
    id⇛
    {!!} -- combination lemma
    {!!} -- base case lemma
    (zipWith makeSingleComb v (upTo n))
--}

lemma3 : {n : ℕ} → 
         (v : Vec (F.Fin n) n) → (i : F.Fin n) → 
         (evalComb (vecToComb v) (finToVal i)) ≡ 
           foldl 
             (λ _ → ⟦ fromℕ n ⟧) 
             (λ h i₁ → i₁ h) 
             (finToVal i)
             (replicate 
               (λ x₂ → evalComb (makeSingleComb (lookup x₂ v) x₂)) ⊛
               tabulate (λ x → x))
lemma3 {n} v i = begin
   evalComb (vecToComb v) (finToVal i)
 ≡⟨ evalComb∘foldr 
     (finToVal i) 
     (map (λ i → makeSingleComb (v !! i) i) (upTo n)) ⟩
   foldl 
     (λ _ → ⟦ fromℕ n ⟧) 
     (λ j c → evalComb c j) 
     (finToVal i) 
     (map (λ i → makeSingleComb (v !! i) i) (upTo n)) 
 ≡⟨ foldl∘map (λ j c → evalComb c j) (finToVal i) makeSingleComb v (upTo n) ⟩
      foldl 
        (λ _ → ⟦ fromℕ n ⟧) 
        (λ h i₁ → i₁ h) 
        (finToVal i)
        (replicate 
          (λ x₂ → evalComb (makeSingleComb (lookup x₂ v) x₂)) ⊛
          tabulate id)
 ∎
