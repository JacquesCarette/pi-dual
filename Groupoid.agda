{-# OPTIONS --without-K #-}

-- Inspired by Thorsten Altenkirch's definition of Groupoids 
-- see his OmegaCats repo on github.  And copumpkin's definition of
-- Category (see his categories repo, also on github).

module Groupoid where

open import Level
open import Data.Empty
open import Data.Sum
open import Data.Product using (_×_)
open import Relation.Binary

-- 1-groupoids are those where the various laws hold up to ≈.
record 1Groupoid : Set₁ where
  infixr 9 _∘_
  infixr 5 _↝_
  infix  4 _≈_
  field
    set : Set₀
    _↝_ : set → set → Set
    _≈_ : ∀ {A B} → A ↝ B → A ↝ B → Set
    id : ∀ {x} → x ↝ x
    _∘_ : ∀ {x y z} → y ↝ z → x ↝ y → x ↝ z
    _⁻¹ : ∀ {x y} → x ↝ y → y ↝ x
    lneutr : ∀ {x y}(α : x ↝ y) → id ∘ α ≈ α
    rneutr : ∀ {x y}(α : x ↝ y) → α ∘ id ≈ α
    assoc : ∀ {w x y z}(α : y ↝ z)(β : x ↝ y)(δ : w ↝ x) → (α ∘ β) ∘ δ ≈ α ∘ (β ∘ δ)
    equiv : ∀ {x y} → IsEquivalence (_≈_ {x} {y})
    linv : ∀ {x y}(α : x ↝ y) → α ⁻¹ ∘ α ≈ id {x}
    rinv : ∀ {x y}(α : x ↝ y) → α ∘ α ⁻¹ ≈ id {y}
    ∘-resp-≈ : ∀ {x y z} {f h : y ↝ z} {g i : x ↝ y} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

_[_,_] : (C : 1Groupoid) → 1Groupoid.set C → 1Groupoid.set C → Set
_[_,_] = 1Groupoid._↝_

open 1Groupoid

private
  _⇛_ : {X Y : 1Groupoid} → set X ⊎ set Y → set X ⊎ set Y → Set
  _⇛_ {X} (inj₁ x) (inj₁ y) = _↝_ X x y
  _⇛_ (inj₁ _) (inj₂ _) = ⊥
  _⇛_ (inj₂ _) (inj₁ _) = ⊥
  _⇛_ {Y = Y} (inj₂ x) (inj₂ y) = _↝_ Y x y

  mk≈ : {X Y : 1Groupoid} {A B : set X ⊎ set Y} → _⇛_ {X} {Y} A B → _⇛_ {X} {Y} A B → Set
  mk≈ {X} {Y} {inj₁ z} {inj₁ z'} a b = _≈_ X a b
  mk≈ {X} {Y} {inj₁ x} {inj₂ y}  () ()
  mk≈ {X} {Y} {inj₂ y} {inj₁ x}  () ()
  mk≈ {X} {Y} {inj₂ y} {inj₂ y'} a b = _≈_ Y a b

  id⇛ : {X Y : 1Groupoid} {x : set X ⊎ set Y} → _⇛_ {X} {Y} x x
  id⇛ {X} {Y} {inj₁ x} = id X
  id⇛ {X} {Y} {inj₂ y} = id Y

  _∙G_ : {X Y : 1Groupoid} {x y z : set X ⊎ set Y} → _⇛_ {X} {Y} y z → _⇛_ {X} {Y} x y → _⇛_ {X} {Y} x z
  _∙G_ {X} {Y} {inj₁ _} {inj₁ _} {inj₁ _} a b = _∘_ X a b
  _∙G_ {X} {Y} {inj₁ _} {inj₁ _} {inj₂ _} () b
  _∙G_ {X} {Y} {inj₁ x} {inj₂ y} a ()
  _∙G_ {X} {Y} {inj₂ y} {inj₁ x} a ()
  _∙G_ {X} {Y} {inj₂ y} {inj₂ y₁} {inj₁ x} () b
  _∙G_ {X} {Y} {inj₂ _} {inj₂ _} {inj₂ _} a b = _∘_ Y a b

  inv : {X Y : 1Groupoid} {x y : set X ⊎ set Y} → _⇛_ {X} {Y} x y → _⇛_ {X} {Y} y x
  inv {X} {_} {inj₁ _} {inj₁ _} a = _⁻¹ X a
  inv {x = inj₁ _} {inj₂ _} ()
  inv {x = inj₂ _} {inj₁ _} ()
  inv {_} {Y} {inj₂ _} {inj₂ _} a = _⁻¹ Y a

_⊎G_ : 1Groupoid → 1Groupoid → 1Groupoid
A ⊎G B = record 
  { set = A.set ⊎ B.set
  ; _↝_ = _⇛_
  ; _≈_ = λ {A₁ B₁} → mk≈ {A} {B} {A₁}   
  ; id = λ {x} → id⇛ {x = x}
  ; _∘_ = λ {x} → _∙G_ {A} {B} {x}
  ; _⁻¹ = λ {x} → inv {A} {B} {x}
  ; lneutr = {!!}
  ; rneutr = {!!}
  ; assoc = {!!}
  ; equiv = {!!}
  ; linv = {!!}
  ; rinv = {!!}
  ; ∘-resp-≈ = {!!} }
  where
    module A = 1Groupoid A
    module B = 1Groupoid B