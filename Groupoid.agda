{-# OPTIONS --without-K #-}

-- Inspired by Thorsten Altenkirch's definition of Groupoids 
-- see his OmegaCats repo on github.  And copumpkin's definition of
-- Category (see his categories repo, also on github).

module Groupoid where

open import Level
open import Data.Empty
open import Data.Sum
open import Data.Product using (_×_)
open import Relation.Binary using (IsEquivalence; Reflexive)

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

_⊎G_ : 1Groupoid → 1Groupoid → 1Groupoid
A ⊎G B = record 
  { set = A.set ⊎ B.set
  ; _↝_ =  _⇛_
  ; _≈_ = λ {x} → mk≈ {x}   
  ; id = λ {x} → id⇛ {x}
  ; _∘_ = λ {x} → _∙G_ {x = x}
  ; _⁻¹ = λ {x} → inv {x = x}
  ; lneutr = λ {x} → lid⇛ {x}
  ; rneutr = λ {x} → rid⇛ {x}
  ; assoc = λ {x} → assoc∙ {x}
  ; equiv = λ {x} → equiv≈ {x}
  ; linv = λ {x} → linv⇛ {x}
  ; rinv = λ {x} → rinv⇛ {x}
  ; ∘-resp-≈ = {!!} }
  where
    module A = 1Groupoid A
    module B = 1Groupoid B
    C : Set
    C = set A ⊎ set B

    _⇛_ : set A ⊎ set B → set A ⊎ set B → Set
    _⇛_ (inj₁ x) (inj₁ y) = A._↝_ x y
    _⇛_ (inj₁ _) (inj₂ _) = ⊥
    _⇛_ (inj₂ _) (inj₁ _) = ⊥
    _⇛_ (inj₂ x) (inj₂ y) = B._↝_ x y

    mk≈ : {x y : set A ⊎ set B} → x ⇛ y → x ⇛ y → Set
    mk≈ {inj₁ z} {inj₁ z'} a b = A._≈_ a b
    mk≈ {inj₁ x} {inj₂ y}  () ()
    mk≈ {inj₂ y} {inj₁ x}  () ()
    mk≈ {inj₂ y} {inj₂ y'} a b = B._≈_ a b

    id⇛ : {x : set A ⊎ set B} → x ⇛ x
    id⇛ {inj₁ _} = id A
    id⇛ {inj₂ _} = id B

    _∙G_ : {x y z : set A ⊎ set B} → y ⇛ z → x ⇛ y → x ⇛ z
    _∙G_ {inj₁ _} {inj₁ _} {inj₁ _} a b = A._∘_ a b
    _∙G_ {inj₁ _} {inj₁ _} {inj₂ _} () b
    _∙G_ {inj₁ x} {inj₂ y} a ()
    _∙G_ {inj₂ y} {inj₁ x} a ()
    _∙G_ {inj₂ y} {inj₂ y₁} {inj₁ x} () b
    _∙G_ {inj₂ _} {inj₂ _} {inj₂ _} a b = B._∘_ a b

    inv : {x y : set A ⊎ set B} → x ⇛ y → y ⇛ x
    inv {inj₁ _} {inj₁ _} a = A._⁻¹ a
    inv {inj₁ _} {inj₂ _} ()
    inv {inj₂ _} {inj₁ _} ()
    inv {inj₂ _} {inj₂ _} a = B._⁻¹ a

    lid⇛ : {x y : set A ⊎ set B} (α : x ⇛ y) → mk≈ {x} (_∙G_ {x} (id⇛ {y}) α) α
    lid⇛ {inj₁ _} {inj₁ _} a = A.lneutr a
    lid⇛ {inj₁ _} {inj₂ _} ()
    lid⇛ {inj₂ _} {inj₁ _} ()
    lid⇛ {inj₂ _} {inj₂ _} a = B.lneutr a

    rid⇛ : {x y : A.set ⊎ B.set} (α : x ⇛ y) → mk≈ {x} (_∙G_ {x} α (id⇛ {x})) α
    rid⇛ {inj₁ _} {inj₁ _} = A.rneutr
    rid⇛ {inj₁ _} {inj₂ _} ()
    rid⇛ {inj₂ _} {inj₁ _} ()
    rid⇛ {inj₂ _} {inj₂ _} = B.rneutr

    assoc∙ : {w x y z : A.set ⊎ B.set} (α : y ⇛ z) (β : x ⇛ y) (δ : w ⇛ x) → 
             mk≈ {w} {z} (_∙G_ {w} (_∙G_ {x} α β) δ) (_∙G_ {w} α (_∙G_ {w} β δ))
    assoc∙ {inj₁ x} {inj₁ x₁} {inj₁ x₂} {inj₁ x₃} = A.assoc
    assoc∙ {inj₁ x} {inj₁ x₁} {inj₁ x₂} {inj₂ y} () _ _
    assoc∙ {inj₁ x} {inj₁ x₁} {inj₂ y} _ () _
    assoc∙ {inj₁ x} {inj₂ y} _ _ ()
    assoc∙ {inj₂ y} {inj₁ x} _ _ ()
    assoc∙ {inj₂ y} {inj₂ y₁} {inj₁ x} _ () _
    assoc∙ {inj₂ y} {inj₂ y₁} {inj₂ y₂} {inj₁ x} () _ _
    assoc∙ {inj₂ y} {inj₂ y₁} {inj₂ y₂} {inj₂ y₃} = B.assoc

    linv⇛ : {x y : A.set ⊎ B.set} (α : x ⇛ y) → mk≈ {x} (_∙G_ {x} (inv {x} α) α) (id⇛ {x})
    linv⇛ {inj₁ _} {inj₁ _} = A.linv
    linv⇛ {inj₁ x} {inj₂ y} ()
    linv⇛ {inj₂ y} {inj₁ x} ()
    linv⇛ {inj₂ _} {inj₂ _} = B.linv

    rinv⇛ : {x y : A.set ⊎ B.set} (α : x ⇛ y) → mk≈ {y} (_∙G_ {y} α (inv {x} α)) (id⇛ {y})
    rinv⇛ {inj₁ _} {inj₁ _} = A.rinv
    rinv⇛ {inj₁ x} {inj₂ y} ()
    rinv⇛ {inj₂ y} {inj₁ x} ()
    rinv⇛ {inj₂ _} {inj₂ _} = B.rinv

    refl≈ : {x y : C} → Reflexive (mk≈ {x} {y})
    refl≈ {inj₁ _} {inj₁ _} = IsEquivalence.refl A.equiv
    refl≈ {inj₁ _} {inj₂ _} {()}
    refl≈ {inj₂ _} {inj₁ _} {()}
    refl≈ {inj₂ y} {inj₂ y₁} = IsEquivalence.refl B.equiv

    equiv≈ : {x y : C} → IsEquivalence (mk≈ {x} {y})
    equiv≈ {x} {y} = record { refl = refl≈ {x}; sym = {!!}; trans = {!!} }