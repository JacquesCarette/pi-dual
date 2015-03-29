{-# OPTIONS --without-K #-}

-- From nlab: FinSet is the category of finite sets and all functions
-- between them: the full subcategory of Set on finite sets. It is
-- easy (and thus common) to make FinSet skeletal; there is one object
-- for each natural number n (including n=0), and a morphism from m to
-- n is an m-tuple (f0,…,fm−1) of numbers satisfying 0≤fi<n. This
-- amounts to identifying n with the set {0,…,n−1}. (Sometimes {1,…,n}
-- is used instead.) This is exactly what we do below.

module SkFinSetCategory where

{-
open import Data.Nat
open import Data.Vec renaming (map to mapV; _++_ to _++V_; concat to concatV)

open import Equiv using (p∘!p≡id)
open import TypeEquiv using (swap₊; swap⋆)
open import VectorLemmas using (_!!_; concat-map; map-map-map; lookup-map; map-∘)
open import FinEquiv using (module Plus; module Times; module PlusTimes)
-}

------------------------------------------------------------------------------
-- Categorical structure

import Level
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin; inject+; raise; zero; suc)
open import Function using (_∘_; id)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)
open import Relation.Binary.PropositionalEquality.Core using (isEquivalence)

open import Categories.Category using (Category; module Category)
open import Categories.Functor using (Functor; module Functor)
open import Categories.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation
  using (module NaturalTransformation)
  renaming (id to idn)
open import Categories.Monoidal using (Monoidal)
open import Categories.Monoidal.Helpers using (module MonoidalHelperFunctors)
open import Categories.Monoidal.Braided using (Braided; module Braided) 

open import SymmetricMonoidalCategory

open import FinVec
open F

-- Objects are natural numbers which are proxies for finite sets of
-- the given size; morphisms between m and n are finite functions, Vec
-- (Fin n) m, mapping each element of Fin m to an element in Fin
-- n. Two morphisms are considered the same if they are ≡ to each other.

finVecC : Category Level.zero Level.zero Level.zero
finVecC = record {
  Obj       = ℕ ;
  _⇒_       = FinVec ;
  _≡_       = _≡_ ;
  id        = 1C ; 
  _∘_       = _∘̂_ ;
  assoc     = λ { {f = f} {g = g} {h = h} → sym (∘̂-assoc h g f) } ;
  identityˡ = λ { {f = f} → ∘̂-lid f } ;
  identityʳ = λ { {f = f} → ∘̂-rid f } ;
  equiv     = isEquivalence ; 
  ∘-resp-≡  = cong₂ _∘̂_ 
  }

⊕-bifunctor : Bifunctor finVecC finVecC finVecC
⊕-bifunctor = record { 
  F₀           = λ { (m , n) → m + n } ;
  F₁           = λ { (f , g) →  f ⊎c g } ; 
  identity     = λ { { (m , n) } → 1C⊎1C≡1C {m} {n} } ;
  homomorphism = λ { {(x₁ , x₂)} {(y₁ , y₂)} {(z₁ , z₂)} {(x₁y₁ , x₂y₂)} {(y₁z₁ , y₂z₂)} →
                   sym (⊎c-distrib {p₁ = y₁z₁} {p₂ = y₂z₂} {p₃ = x₁y₁} {p₄ = x₂y₂}) } ;
  F-resp-≡     = λ { {(x₁ , x₂)} {(y₁ , y₂)} {(p₁ , p₂)} {(p₃ , p₄)} (p₁≡p₃ , p₂≡p₄) →
                   cong₂ _⊎c_ p₁≡p₃ p₂≡p₄ } 
  }

⊗-bifunctor : Bifunctor finVecC finVecC finVecC
⊗-bifunctor = record { 
  F₀           = λ { (m , n) → m * n } ;
  F₁           = λ { (f , g) →  f ×c g } ; 
  identity     = λ { { (m , n) } → 1C×1C≡1C {m} {n} } ;
  homomorphism = λ { {(x₁ , x₂)} {(y₁ , y₂)} {(z₁ , z₂)} {(x₁y₁ , x₂y₂)} {(y₁z₁ , y₂z₂)} →
                   sym (×c-distrib {p₁ = y₁z₁} {p₂ = y₂z₂} {p₃ = x₁y₁} {p₄ = x₂y₂}) } ;
  F-resp-≡     = λ { {(x₁ , x₂)} {(y₁ , y₂)} {(p₁ , p₂)} {(p₃ , p₄)} (p₁≡p₃ , p₂≡p₄) →
                   cong₂ _×c_ p₁≡p₃ p₂≡p₄ } 
  }

{-- 
CommutativeSquare f g h i = h ∘ f ≡ i ∘ g

Functor (C D): 
  F₀           : C.Obj → D.Obj
  F₁           : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]
  identity     : ∀ {A} → D [ F₁ (C.id {A}) ≡ D.id ]
  homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                  → D [ F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ] ]
  F-resp-≡     : ∀ {A B} {F G : C [ A , B ]} → C [ F ≡ G ] → D [ F₁ F ≡ F₁ G ]

NaturalTransformation (F G : Functor C D):
  η       : ∀ X → D [ F₀ X , G₀ X ]
  commute : ∀ {X Y} (f : C [ X , Y ]) → D.CommutativeSquare (F₁ f) (η X) (η Y) (G₁ f)

NaturalIsomorphism (F G : Functor C D):
  F⇒G  : NaturalTransformation F G
  F⇐G  : NaturalTransformation G F
  iso  : ∀ X → Iso (⇒.η X) (⇐.η X)

Monoidal (C : Category):
  identityˡ : NaturalIsomorphism id⊗x x
  identityʳ : NaturalIsomorphism x⊗id x
  assoc     : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]
  triangle  : TriangleLeftSide ≡ⁿ (TriangleRightSide ∘₁ TriangleTopSide)
  pentagon  : (PentagonNESide ∘₁ PentagonNWSide) ≡ⁿ 
              (PentagonSESide ∘₁ (PentagonSSide ∘₁ PentagonSWSide))
--}

private module CFV = Category finVecC
private module MFunctors = MonoidalHelperFunctors finVecC ⊕-bifunctor 0
private module Fid⊗x = Functor MFunctors.id⊗x
private module Fx = Functor MFunctors.x

finVecAdditiveM : Monoidal finVecC -- power = Fin 1 (so apply everything to zero)
finVecAdditiveM = record {
  ⊗  = ⊕-bifunctor ; 
  id = 0 ;
  identityˡ = record {
    F⇒G = record { -- F, G : (0C ⊎ x) ⇒ x  
      η       = λ X → 1C ; 
      commute = λ f → trans (∘̂-lid (1C ⊎c f zero)) (trans 1C₀⊎x≡x (sym (∘̂-rid (f zero)))) -- ntp ηY ∘̂ (0C ⊎ f) ≡ f ∘̂ ηX
    } ;
    F⇐G = record { 
      η       = λ _ → 1C ;
      commute = λ f → trans (∘̂-lid (f zero)) (trans (sym 1C₀⊎x≡x) (sym (∘̂-rid (1C ⊎c f zero))))  
    } ;
    iso = λ X → record { isoˡ = ∘̂-rid 1C ; isoʳ = ∘̂-lid 1C }
  } ;
  identityʳ = record {
    F⇒G = record {
      η       = λ X → uniti+ ;
      commute = λ f → {!idʳ⊕ {x = f zero}!} 
    } ;
    F⇐G = record { 
      η       = λ X → unite+ ;
      commute = λ f → {!!} 
    } ;
    iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  } ;
  assoc = record { F⇒G = record { η = λ X → assocl+ {m = X zero}
                                ; commute = λ f → {!!} }
                 ; F⇐G = record { η = λ X → assocr+ {m = X zero}
                                ; commute = {!!} }
                 ; iso = λ X → record { isoˡ = assocr+∘̂assocl+~id {m = X zero}
                                      ; isoʳ = assocl+∘̂assocr+~id {m = X zero} } } ;
  triangle = {!!} ;
  pentagon = {!!} 
  }
--  where
--  private module FVC = Category finVecC
--  private module MFunctors = MonoidalHelperFunctors finVecC ⊕-bifunctor 0
--  private module FF = Functor MFunctors.id⊗x
--  private module GF = Functor MFunctors.x
  
                                           
{--
-- Commutative semiring structure

import Level
open import Algebra
open import Algebra.Structures
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (subst; sym; trans; cong₂)

open F

_cauchy≃_ : (m n : ℕ) → Set
m cauchy≃ n = FinVec m n

id-iso : {m : ℕ} → FinVec m m
id-iso = 1C

private
  postulate sym-iso : {m n : ℕ} → FinVec m n → FinVec n m

trans-iso : {m n o : ℕ} → FinVec m n → FinVec n o → FinVec m o 
trans-iso c₁ c₂ = c₂ ∘̂ c₁

cauchy≃IsEquiv : IsEquivalence {Level.zero} {Level.zero} {ℕ} _cauchy≃_
cauchy≃IsEquiv = record {
  refl = id-iso ; 
  sym = sym-iso ; 
  trans = trans-iso
  }

cauchyPlusIsSG : IsSemigroup {Level.zero} {Level.zero} {ℕ} _cauchy≃_ _+_
cauchyPlusIsSG = record {
  isEquivalence = cauchy≃IsEquiv ; 
  assoc = λ m n o → assocl+ {m} {n} {o} ; 
  ∙-cong = _⊎c_ 
  }

cauchyTimesIsSG : IsSemigroup {Level.zero} {Level.zero} {ℕ} _cauchy≃_ _*_
cauchyTimesIsSG = record {
  isEquivalence = cauchy≃IsEquiv ;
  assoc = λ m n o → assocl* {m} {n} {o} ;
  ∙-cong = _×c_
  }

cauchyPlusIsCM : IsCommutativeMonoid _cauchy≃_ _+_ 0
cauchyPlusIsCM = record {
  isSemigroup = cauchyPlusIsSG ;
  identityˡ = λ m → 1C ;
  comm = λ m n → swap+cauchy n m 
  }

cauchyTimesIsCM : IsCommutativeMonoid _cauchy≃_ _*_ 1
cauchyTimesIsCM = record {
  isSemigroup = cauchyTimesIsSG ;
  identityˡ = λ m → uniti* {m} ;
  comm = λ m n → swap⋆cauchy n m
  }

cauchyIsCSR : IsCommutativeSemiring _cauchy≃_ _+_ _*_ 0 1
cauchyIsCSR = record {
  +-isCommutativeMonoid = cauchyPlusIsCM ;
  *-isCommutativeMonoid = cauchyTimesIsCM ; 
  distribʳ = λ o m n → factor*+ {m} {n} {o} ; 
  zeroˡ = λ m → 0C
  }

cauchyCSR : CommutativeSemiring Level.zero Level.zero
cauchyCSR = record {
  Carrier = ℕ ;
  _≈_ = _cauchy≃_ ;
  _+_ = _+_ ;
  _*_ = _*_ ;
  0# = 0 ;
  1# = 1 ;
  isCommutativeSemiring = cauchyIsCSR
  }

------------------------------------------------------------------------------
-- Groupoid structure

open import Groupoid

private
  postulate linv : {m n : ℕ} (c : FinVec m n) → (sym-iso c) ∘̂ c ≡ 1C
  postulate rinv : {m n : ℕ} (c : FinVec m n) → c ∘̂ (sym-iso c) ≡ 1C

G : 1Groupoid
G = record {
  set = ℕ ; 
  _↝_ = _cauchy≃_ ; 
  _≈_ = _≡_ ; 
  id  = id-iso ;
  _∘_ = λ c₁ c₂ → trans-iso c₂ c₁ ; 
  _⁻¹ = sym-iso ; 
  lneutr = ∘̂-lid ; 
  rneutr = ∘̂-rid ; 
  assoc  = λ c₁ c₂ c₃ → sym (∘̂-assoc c₁ c₂ c₃) ; 
  equiv = record { 
            refl  = refl ; 
            sym   = sym ; 
            trans = trans 
          } ;
  linv = linv ; 
  rinv = rinv ; 
  ∘-resp-≈ = cong₂ _∘̂_ 
  }
--}

------------------------------------------------------------------------------
