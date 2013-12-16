{-# OPTIONS --without-K #-}
module Cat where

import Level as L
open import Data.Fin
open import Data.Nat
open import Data.Product
open import Data.List
open import Function renaming (_∘_ to _○_)

open import HoTT
open import FT
import Equivalences as E 

{--
1. postulate path2equiv
2. show that (FT, path) is equivalent to (FinSet, bijections) as categories
3. show that [[ ]]: (B, <->) -> (Set, function) is a functor
   [where (Set is Agda's Set)].
--}

------------------------------------------------------------------
-- Categories (adapated from:
-- http://wiki.portal.chalmers.se/agda/uploads/Main.Libraries/20110915Category.agda)

record Setoid (a b : L.Level) : Set (L.suc (a L.⊔ b)) where
  infix 2 _∼_
  field
    object : Set a
    _∼_ : object → object → Set b
    refl∼ : {x : object} → x ∼ x
    sym∼ : {x y : object} → x ∼ y → y ∼ x
    trans∼ : {x y z : object} → y ∼ z → x ∼ y → x ∼ z

record　Fun∼ {a b} (X Y : Setoid a b) : Set (a L.⊔ b) where
  field
    function : Setoid.object X → Setoid.object Y
    respects∼ : {x0 x1 : Setoid.object X} → (let open Setoid X in x0 ∼ x1) →
            (let open Setoid Y in function x0 ∼ function x1)

FunSetoid : ∀ {a b} → Setoid a b → Setoid a b → Setoid (a L.⊔ b) (a L.⊔ b)
FunSetoid X Y = record { object = Fun∼ X Y
                    ; _∼_ = λ F → λ G → (x : Setoid.object X) →
                        Setoid._∼_  Y (Fun∼.function F x) (Fun∼.function G x)
                    ; refl∼ = λ x → Setoid.refl∼ Y
                    ; sym∼ = λ p → λ x → Setoid.sym∼ Y (p x)
                    ; trans∼ = λ g∼h → λ f∼g → λ x →
                               Setoid.trans∼ Y (g∼h x) (f∼g x)
                    }

strictSetoid : ∀ {a} → Set a → Setoid a a
strictSetoid A = record
  { object = A
  ; _∼_ = _≡_
  ; refl∼ = λ {x} → refl x
  ; sym∼ = !
  ; trans∼ = λ q p → p ∘ q
  }

∥_∥ : ∀ {a b c} {X : Set a} → (h : X → X → Setoid b c) → (x y : X) → Set b
∥ h ∥ x y = Setoid.object (h x y)

record Cat (a b c : L.Level) : Set (L.suc (a L.⊔ b L.⊔ c)) where
  field
    object : Set a
    hom : object → object → Setoid b c
    identity : (x : object) → ∥ hom ∥ x x
    comp : {x y z : object} → ∥ hom ∥ y z → ∥ hom ∥ x y → ∥ hom ∥ x z
    comp∼ : {x y z : object} →
             {g0 g1 : ∥ hom ∥ y z} → {f0 f1 : ∥ hom ∥ x y} →
             (g0∼g1 : let open Setoid (hom y z) in g0 ∼ g1) →
             (f0∼f1 : let open Setoid (hom x y) in f0 ∼ f1) →
             let open Setoid (hom x z) in comp g0 f0 ∼ comp g1 f1
    associativity∼ : {w x y z : object} →
      (f : ∥ hom ∥ y z) → (g : ∥ hom ∥ x y) → (h : ∥ hom ∥ w x) →
      let open Setoid (hom w z) in comp (comp f g) h ∼ comp f (comp g h)
    left-identity∼ : {x y : object} → (f : ∥ hom ∥ x y) →
      let open Setoid (hom x y) in comp (identity y) f ∼ f
    right-identity∼ : {x y : object} → (f : ∥ hom ∥ x y) →
      let open Setoid (hom x y) in comp f (identity x) ∼ f

ob : ∀ {a b c} → Cat a b c → Set a
ob C = Cat.object C

------------------------------------------------------------------
-- category (FinSet,bijections)

record FinBijection : Set where
  field 
    f : Σ[ m ∈ ℕ ] (Fin m) → Σ[ n ∈ ℕ ] (Fin n)
    g : Σ[ n ∈ ℕ ] (Fin n) → Σ[ m ∈ ℕ ] (Fin m)
    injective  : {x y : Σ[ m ∈ ℕ ] (Fin m)} → f x ≡ f y → x ≡ y
    surjective : {x : Σ[ n ∈ ℕ ] (Fin n)} → f (g x) ≡ x

idBijection : (M : Σ[ m ∈ ℕ ] (Fin m)) → FinBijection 
idBijection M = record {
    f = id ;
    g = id ;
    injective = λ p → p ;
    surjective = λ {M} → refl M 
  } 

-- two bijections are the "same" if they agree modulo ≡ 
Bijection∼ : FinBijection → FinBijection → Set
Bijection∼ M N = 
  (let open FinBijection M in f) E.∼ (let open FinBijection N in f)

-- the set of all morphisms between m and n taken modulo ≡
BijectionSetoid : (M : Σ[ m ∈ ℕ ] (Fin m)) → (N : Σ[ n ∈ ℕ ] (Fin n)) → 
                  Setoid L.zero L.zero
BijectionSetoid M N = record {
    object = FinBijection ; 
    _∼_ = Bijection∼ ; 
    refl∼ = λ {B} → E.refl∼ {f = FinBijection.f B} ; 
    sym∼ = λ {B₁} {B₂} → 
             E.sym∼ {f = FinBijection.f B₁} {g = FinBijection.f B₂} ;
    trans∼ = λ {B₁} {B₂} {B₃} F G → 
               E.trans∼ {f = FinBijection.f B₁}
                        {g = FinBijection.f B₂} 
                        {h = FinBijection.f B₃}
                        G F
    }

FinCat : Cat L.zero L.zero L.zero
FinCat = record {
          object = Σ[ n ∈ ℕ ] (Fin n) ; 
          hom = λ M N → BijectionSetoid M N ;
          identity = λ M → idBijection M ; 
          comp = {!!} ;
          comp∼ = {!!} ;
          associativity∼  = {!!} ;
          left-identity∼  = {!!} ;
          right-identity∼ = {!!} 
      }



------------------------------------------------------------------
-- category (FT,path)

-- evaluation

evalF : {b₁ b₂ : FT} → (b₁ ⇛ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
evalF c v = {!!} 

evalB : {b₁ b₂ : FT} → (b₁ ⇛ b₂) → ⟦ b₂ ⟧ → ⟦ b₁ ⟧
evalB c v = {!!} 

-- equivalence of combinators

_∼c_ : {b₁ b₂ : FT} → (c₁ c₂ : b₁ ⇛ b₂) → Set
_∼c_ {b₁} {b₂} c₁ c₂ = (v : ⟦ b₁ ⟧) → evalF c₁ v ≡ evalF c₂ v

-- equivalence class of paths between two types

paths : FT → FT → Setoid L.zero L.zero 
paths b₁ b₂ = record {
               object = List (b₁ ⇛ b₂) ;
               _∼_ = {!!} ;
               refl∼  = {!!} ;
               sym∼ = {!!} ;
               trans∼ = {!!} 
             } 

FTCat : Cat L.zero L.zero L.zero
FTCat = record {
          object = FT ;
          hom = {!!} ;
          identity = {!!} ;
          comp = {!!} ;
          comp∼ = {!!} ;
          associativity∼  = {!!} ;
          left-identity∼  = {!!} ;
          right-identity∼ = {!!} 
      }



------------------------------------------------------------------
