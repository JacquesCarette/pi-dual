module PiNF-semantics where

open import Data.Nat hiding (_⊔_; suc; _+_; _*_)
open import Data.Vec 
open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality hiding (sym)
open import Relation.Binary.Core
open import Algebra
import Algebra.FunctionProperties as FunctionProperties
open import Algebra.FunctionProperties.Core 
open import Algebra.Structures

open import PiNF-syntax
open import PiNF-algebra

------------------------------------------------------------------------------
-- Define module over a ring (the types bot, top, disjoint union, and product
-- do form a ring as shown in the type-iso library) 

module MR (C : CommutativeSemiringWithoutAnnihilatingZero Level.zero Level.zero) where

  open Data.Nat using (ℕ; zero; suc; _*_)
  open Data.Vec using ([]; _∷_; map; _++_)
  open CommutativeSemiringWithoutAnnihilatingZero using (Carrier; _+_)

  R-module : Set → ℕ → Set
  R-module c dim = Vec c dim 

{--
  zeroV : ∀ {b : Set} → R-module b 0
  zeroV = []

  tensorV : {b₁ b₂ : Set } {m₁ m₂ : ℕ} → 
            R-module b₁ m₁ → R-module b₂ m₂ → 
            R-module (b₁ × b₂) (m₁ * m₂)
  tensorV [] _ = []
  tensorV (x ∷ xs) ys = (map (λ y → (x , y)) ys) ++ (tensorV xs ys)
--}

  addV : {n : ℕ} → R-module (Carrier C) n → R-module (Carrier C) n
                 → R-module (Carrier C) n
  addV x y = Data.Vec.zipWith (_+_ C) x y    
open MR

------------------------------------------------------------------------------
