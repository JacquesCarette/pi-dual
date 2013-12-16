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
-- M, N, L are finite sets
-- F, G, H are bijections

-- bijections between two sets M and N
record Bijection (M N : Set) : Set where
  field 
    f : M → N
    g : N → M
    injective  : {x y : M} → f x ≡ f y → x ≡ y
    surjective : {x : N} → f (g x) ≡ x

-- there is a bijection from each set to itself
idBijection : (M : Set) → Bijection M M
idBijection M = record {
    f = id ;
    g = id ;
    injective = id ; 
    surjective = λ {x} → refl x
  } 

-- composition of bijections
∘Bijection : {M N L : Set} → Bijection N L → Bijection M N → Bijection M L
∘Bijection G F = record {
    f = Bijection.f G ○ Bijection.f F ;
    g = Bijection.g F ○ Bijection.g G ;
    injective = λ {x} {y} α → 
                  Bijection.injective F (Bijection.injective G α) ;
    surjective = λ {x} → 
      Bijection.f G (Bijection.f F (Bijection.g F (Bijection.g G x)))
        ≡⟨ ap (λ x → Bijection.f G x) (Bijection.surjective F) ⟩
      Bijection.f G (Bijection.g G x) 
        ≡⟨ Bijection.surjective G ⟩ 
      x ∎
  } 

-- two bijections are the "same" if they agree modulo ≡ 
Bijection∼ : {M N : Set} → Bijection M N → Bijection M N → Set
Bijection∼ F G = (Bijection.f F) E.∼ (Bijection.f G)

-- the set of all bijections between two sets M and N taken modulo ≡
BijectionSetoid : (M N : Set) → Setoid L.zero L.zero
BijectionSetoid M N = record {
    object = Bijection M N ;
    _∼_ = Bijection∼ ; 
    refl∼ = λ {F} → E.refl∼ {f = Bijection.f F} ; 
    sym∼ = λ {F} {G} → 
             E.sym∼ {f = Bijection.f F} {g = Bijection.f G} ;
    trans∼ = λ {F} {G} {H} P Q → 
               E.trans∼ {f = Bijection.f F}
                        {g = Bijection.f G} 
                        {h = Bijection.f H}
                        Q P 
    }

FinCat : Cat L.zero L.zero L.zero
FinCat = record {
          object = Σ[ n ∈ ℕ ] (Fin n) ; 
          hom = λ M N → {!!}  ; -- BijectionSetoid M N ;
          identity = λ M → idBijection {!M!} ; -- idBijection (Σ[ m ∈ ℕ ] (Fin m)) ; 
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
