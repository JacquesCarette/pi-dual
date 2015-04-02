{-# OPTIONS --without-K #-}
module TypeEquiv where

open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Function renaming (_∘_ to _○_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Equiv

------------------------------------------------------------------------------
-- Type Equivalences

-- for each type combinator, define two functions that are inverses, and
-- establish an equivalence.  These are all in the 'semantic space' with
-- respect to Pi combinators.

-- swap₊

swap₊ : {A B : Set} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

swapswap₊ : {A B : Set} → swap₊ ○ swap₊ {A} {B} ∼ id
swapswap₊ (inj₁ a) = refl
swapswap₊ (inj₂ b) = refl

swap₊equiv : {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
swap₊equiv = (swap₊ , mkqinv swap₊ swapswap₊ swapswap₊)

-- unite₊ and uniti₊

unite₊ : {A : Set} → ⊥ ⊎ A → A
unite₊ (inj₁ ())
unite₊ (inj₂ y) = y

uniti₊ : {A : Set} → A → ⊥ ⊎ A
uniti₊ a = inj₂ a

uniti₊∘unite₊ : {A : Set} → uniti₊ ○ unite₊ ∼ id {A = ⊥ ⊎ A}
uniti₊∘unite₊ (inj₁ ())
uniti₊∘unite₊ (inj₂ y) = refl

-- this is so easy, Agda can figure it out by itself (see below)

unite₊∘uniti₊ : {A : Set} → unite₊ ○ uniti₊ ∼ id {A = A}
unite₊∘uniti₊ _ = refl

unite₊equiv : {A : Set} → (⊥ ⊎ A) ≃ A
unite₊equiv = (unite₊ , mkqinv uniti₊ refl∼ uniti₊∘unite₊)

uniti₊equiv : {A : Set} → A ≃ (⊥ ⊎ A)
uniti₊equiv = uniti₊ , mkqinv unite₊ uniti₊∘unite₊ unite₊∘uniti₊

-- unite₊′ and uniti₊′

unite₊′ : {A : Set} → A ⊎ ⊥ → A
unite₊′ (inj₁ x) = x
unite₊′ (inj₂ ())

uniti₊′ : {A : Set} → A → A ⊎ ⊥
uniti₊′ a = inj₁ a

uniti₊′∘unite₊′ : {A : Set} → uniti₊′ ○ unite₊′ ∼ id {A = A ⊎ ⊥}
uniti₊′∘unite₊′ (inj₁ _) = refl
uniti₊′∘unite₊′ (inj₂ ())

-- this is so easy, Agda can figure it out by itself (see below)

unite₊′∘uniti₊′ : {A : Set} → unite₊′ ○ uniti₊′ ∼ id {A = A}
unite₊′∘uniti₊′ _ = refl

unite₊′equiv : {A : Set} → (A ⊎ ⊥) ≃ A
unite₊′equiv = (unite₊′ , mkqinv uniti₊′ refl∼ uniti₊′∘unite₊′)

uniti₊′equiv : {A : Set} → A ≃ (A ⊎ ⊥)
uniti₊′equiv = uniti₊′ , mkqinv unite₊′ uniti₊′∘unite₊′ unite₊′∘uniti₊′


-- unite⋆ and uniti⋆

unite⋆ : {A : Set} → ⊤ × A → A
unite⋆ (tt , x) = x

uniti⋆ : {A : Set} → A → ⊤ × A
uniti⋆ x = tt , x

uniti⋆∘unite⋆ : {A : Set} → uniti⋆ ○ unite⋆ ∼ id {A = ⊤ × A}
uniti⋆∘unite⋆ (tt , x) = refl

unite⋆equiv : {A : Set} → (⊤ × A) ≃ A
unite⋆equiv = unite⋆ , mkqinv uniti⋆ refl∼ uniti⋆∘unite⋆

uniti⋆equiv : {A : Set} → A ≃ (⊤ × A)
uniti⋆equiv = uniti⋆ , mkqinv unite⋆ uniti⋆∘unite⋆ refl∼

-- unite⋆′ and uniti⋆′

unite⋆′ : {A : Set} → A × ⊤ → A
unite⋆′ (x , tt) = x

uniti⋆′ : {A : Set} → A → A × ⊤
uniti⋆′ x = x , tt

uniti⋆′∘unite⋆′ : {A : Set} → uniti⋆′ ○ unite⋆′ ∼ id {A = A × ⊤}
uniti⋆′∘unite⋆′ (x , tt) = refl

unite⋆′equiv : {A : Set} → (A × ⊤) ≃ A
unite⋆′equiv = unite⋆′ , mkqinv uniti⋆′ refl∼ uniti⋆′∘unite⋆′

uniti⋆′equiv : {A : Set} → A ≃ (A × ⊤)
uniti⋆′equiv = uniti⋆′ , mkqinv unite⋆′ uniti⋆′∘unite⋆′ refl∼

-- swap⋆

swap⋆ : {A B : Set} → A × B → B × A
swap⋆ (a , b) = (b , a)

swapswap⋆ : {A B : Set} → swap⋆ ○ swap⋆ ∼ id {A = A × B}
swapswap⋆ (a , b) = refl 

swap⋆equiv : {A B : Set} → (A × B) ≃ (B × A)
swap⋆equiv = swap⋆ , mkqinv swap⋆ swapswap⋆ swapswap⋆

-- assocl₊ and assocr₊

assocl₊ : {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
assocl₊ (inj₁ a) = inj₁ (inj₁ a)
assocl₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
assocl₊ (inj₂ (inj₂ c)) = inj₂ c

assocr₊ : {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
assocr₊ (inj₁ (inj₁ a)) = inj₁ a
assocr₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
assocr₊ (inj₂ c) = inj₂ (inj₂ c)

assocl₊∘assocr₊ : {A B C : Set} → assocl₊ ○ assocr₊ ∼ id {A = ((A ⊎ B) ⊎ C)}
assocl₊∘assocr₊ (inj₁ (inj₁ a)) = refl
assocl₊∘assocr₊ (inj₁ (inj₂ b)) = refl
assocl₊∘assocr₊ (inj₂ c) = refl

assocr₊∘assocl₊ : {A B C : Set} → assocr₊ ○ assocl₊ ∼ id {A = (A ⊎ (B ⊎ C))}
assocr₊∘assocl₊ (inj₁ a) = refl
assocr₊∘assocl₊ (inj₂ (inj₁ b)) = refl
assocr₊∘assocl₊ (inj₂ (inj₂ c)) = refl

assocl₊equiv : {A B C : Set} → (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
assocl₊equiv = 
  assocl₊ , mkqinv assocr₊ assocl₊∘assocr₊ assocr₊∘assocl₊

assocr₊equiv : {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
assocr₊equiv = 
  assocr₊ , mkqinv assocl₊ assocr₊∘assocl₊ assocl₊∘assocr₊

-- assocl⋆ and assocr⋆

assocl⋆ : {A B C : Set} → (A × (B × C)) → ((A × B) × C)
assocl⋆ (a , (b , c)) = ((a , b) , c)

assocr⋆ : {A B C : Set} → ((A × B) × C) → (A × (B × C))
assocr⋆ ((a , b) , c) = (a , (b , c))

assocl⋆∘assocr⋆ : {A B C : Set} → assocl⋆ ○ assocr⋆ ∼ id {A = ((A × B) × C)}
assocl⋆∘assocr⋆ = refl∼

assocr⋆∘assocl⋆ : {A B C : Set} → assocr⋆ ○ assocl⋆ ∼ id {A = (A × (B × C))}
assocr⋆∘assocl⋆ = refl∼

assocl⋆equiv : {A B C : Set} → (A × (B × C)) ≃ ((A × B) × C)
assocl⋆equiv = 
  assocl⋆ , mkqinv assocr⋆ assocl⋆∘assocr⋆ assocr⋆∘assocl⋆

assocr⋆equiv : {A B C : Set} → ((A × B) × C) ≃ (A × (B × C))
assocr⋆equiv = 
  assocr⋆ , mkqinv assocl⋆ assocr⋆∘assocl⋆ assocl⋆∘assocr⋆

-- distz and factorz

distz : { A : Set} → (⊥ × A) → ⊥
distz (() , _)

factorz : {A : Set} → ⊥ → (⊥ × A)
factorz ()
 
distz∘factorz : {A : Set} → distz ○ factorz {A} ∼ id
distz∘factorz ()

factorz∘distz : {A : Set} → factorz {A} ○ distz ∼ id
factorz∘distz (() , proj₂)

distzequiv : {A : Set} → (⊥ × A) ≃ ⊥
distzequiv {A} = 
  distz , mkqinv factorz (distz∘factorz {A}) factorz∘distz

factorzequiv : {A : Set} → ⊥ ≃ (⊥ × A)
factorzequiv {A} = 
  factorz , mkqinv distz factorz∘distz (distz∘factorz {A})

-- dist and factor

dist : {A B C : Set} → ((A ⊎ B) × C) → (A × C) ⊎ (B × C)
dist (inj₁ x , c) = inj₁ (x , c)
dist (inj₂ y , c) = inj₂ (y , c)

factor : {A B C : Set} → (A × C) ⊎ (B × C) → ((A ⊎ B) × C)
factor (inj₁ (a , c)) = inj₁ a , c
factor (inj₂ (b , c)) = inj₂ b , c

dist∘factor : {A B C : Set} → dist {A} {B} {C} ○ factor ∼ id
dist∘factor (inj₁ x) = refl
dist∘factor (inj₂ y) = refl

factor∘dist : {A B C : Set} → factor {A} {B} {C} ○ dist ∼ id
factor∘dist (inj₁ x , c) = refl
factor∘dist (inj₂ y , c) = refl

distequiv : {A B C : Set} → ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
distequiv = dist , mkqinv factor dist∘factor factor∘dist

factorequiv : {A B C : Set} →  ((A × C) ⊎ (B × C)) ≃ ((A ⊎ B) × C)
factorequiv = factor , (mkqinv dist factor∘dist dist∘factor)

-- identity equivalence 

idequiv : {A : Set} → A ≃ A
idequiv = id≃

------------------------------------------------------------------------------
-- Commutative semiring structure

import Level
open import Algebra
open import Algebra.Structures
open import Relation.Binary.Core

typesPlusIsSG : IsSemigroup {Level.suc Level.zero} {Level.zero} {Set} _≃_ _⊎_
typesPlusIsSG = record {
  isEquivalence = ≃IsEquiv ;
  assoc = λ t₁ t₂ t₃ → assocr₊equiv {t₁} {t₂} {t₃} ;
  ∙-cong = path⊎
  }

typesTimesIsSG : IsSemigroup {Level.suc Level.zero} {Level.zero} {Set} _≃_ _×_
typesTimesIsSG = record {
  isEquivalence = ≃IsEquiv ;
  assoc = λ t₁ t₂ t₃ → assocr⋆equiv {t₁} {t₂} {t₃} ;
  ∙-cong = path×
  }

typesPlusIsCM : IsCommutativeMonoid _≃_ _⊎_ ⊥
typesPlusIsCM = record {
  isSemigroup = typesPlusIsSG ;
  identityˡ = λ t → unite₊equiv {t} ;
  comm = λ t₁ t₂ → swap₊equiv {t₁} {t₂}
  }

typesTimesIsCM : IsCommutativeMonoid _≃_ _×_ ⊤
typesTimesIsCM = record {
  isSemigroup = typesTimesIsSG ;
  identityˡ = λ t → unite⋆equiv {t} ;
  comm = λ t₁ t₂ → swap⋆equiv {t₁} {t₂}
  }

typesIsCSR : IsCommutativeSemiring _≃_ _⊎_ _×_ ⊥ ⊤
typesIsCSR = record {
  +-isCommutativeMonoid = typesPlusIsCM ;
  *-isCommutativeMonoid = typesTimesIsCM ;
  distribʳ = λ t₁ t₂ t₃ → distequiv {t₂} {t₃} {t₁} ; 
  zeroˡ = λ t → distzequiv {t}
  }

typesCSR : CommutativeSemiring (Level.suc Level.zero) Level.zero
typesCSR = record {
  Carrier = Set ;
  _≈_ = _≃_ ;
  _+_ = _⊎_ ;
  _*_ = _×_ ;
  0# = ⊥ ;
  1# = ⊤ ;
  isCommutativeSemiring = typesIsCSR
  }

------------------------------------------------------------------------------
