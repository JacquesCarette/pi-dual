module PiNF-semantics where

open import Data.Nat hiding (_⊔_; suc; _+_; _*_)
open import Data.Vec 
open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality hiding (sym; [_])
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

R-module : ℕ → Set → Set
R-module dim c = Vec c dim 

-- The only element of (R-module 0) is the zero vector

zeroV : ∀ {A : Set} → R-module 0 A
zeroV = []

-- (R-module 1 A) is isomorphic to A

v-R1 : ∀ {A : Set} → A → R-module 1 A
v-R1 a = [ a ]

R1-v : ∀ {A : Set} → R-module 1 A → A
R1-v (a ∷ []) = a

-- 


module MR (C : CommutativeSemiringWithoutAnnihilatingZero Level.zero Level.zero) where

  open Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open Data.Vec using ([]; _∷_; map; _++_)
  open CommutativeSemiringWithoutAnnihilatingZero 
    using (Carrier; _≈_; 0#; 1#)
    renaming (_+_ to _+r_; _*_ to _*r_)

{--
  zeroV : ∀ {b : Set} → R-module b 0
  zeroV = []

  tensorV : {b₁ b₂ : Set } {m₁ m₂ : ℕ} → 
            R-module b₁ m₁ → R-module b₂ m₂ → 
            R-module (b₁ × b₂) (m₁ * m₂)
  tensorV [] _ = []
  tensorV (x ∷ xs) ys = (map (λ y → (x , y)) ys) ++ (tensorV xs ys)

  addV : {n : ℕ} → R-module (Carrier C) n → R-module (Carrier C) n
                 → R-module (Carrier C) n
  addV x y = Data.Vec.zipWith (_+r_ C) x y

--}

open MR

------------------------------------------------------------------------------
