{-# OPTIONS --without-K #-}

module TypeEquivCat where

open import Level using (zero; suc)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (Rel)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; proj₁; proj₂;_×_)
open import Data.Unit
open import Data.Empty

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism

open import Equiv
open import TypeEquiv

-- see EquivSetoid for some additional justification
-- basically we need g to "pin down" the inverse.
record _≋_ {A B : Set} (a b : A ≃ B) : Set where
  constructor eq
  field
    f≡ : ∀ x → a ⋆ x P.≡ b ⋆ x
    g≡ : ∀ x → (sym≃ a) ⋆ x P.≡ (sym≃ b) ⋆ x
 
id≋ : ∀ {A B : Set} {x : A ≃ B} → x ≋ x
id≋ = record { f≡ = λ x → P.refl ; g≡ = λ x → P.refl }

sym≋ : ∀ {A B : Set} {x y : A ≃ B} → x ≋ y → y ≋ x
sym≋ (eq f≡ g≡) = eq (λ a → P.sym (f≡ a)) (λ b → P.sym (g≡ b))

trans≋ : ∀ {A B : Set} {x y z : A ≃ B} → x ≋ y → y ≋ z → x ≋ z
trans≋ (eq f≡ g≡) (eq h≡ i≡) =
   eq (λ a → P.trans (f≡ a) (h≡ a)) (λ b → P.trans (g≡ b) (i≡ b))

TypeEquivCat : Category (suc zero) zero zero
TypeEquivCat = record
  { Obj = Set
  ; _⇒_ = _≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = _●_
  ; assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ }
  ; ∘-resp-≡ = {!!}
  }

TypeEquivGroupoid : Groupoid TypeEquivCat
TypeEquivGroupoid = record 
  { _⁻¹ = sym≃ 
  ; iso = λ {_} {_} {f} → record { isoˡ = eq (λ x → qinv.β (proj₂ f) x) {!!} 
                                                   ; isoʳ = {!!} } 
  }

⊎-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
⊎-bifunctor = record
  { F₀ = λ {( x , y) → x ⊎ y}
  ; F₁ = λ {(x , y) → path⊎ x y}
  ; identity = eq {!!} {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!}
  }

×-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
×-bifunctor = {!!}

module ⊎h = MonoidalHelperFunctors TypeEquivCat ⊎-bifunctor ⊥

0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊎x≡x = record 
  { F⇒G = record { η = λ X → unite₊equiv ; commute = λ f → eq {!!} {!!} } 
  ; F⇐G = record { η = λ X → uniti₊equiv ; commute = {!!} } 
  ; iso = λ X → record { isoˡ = eq {!!} {!!} ; isoʳ = {!!} } }

CPM⊎ : Monoidal TypeEquivCat
CPM⊎ = record
  { ⊗ = ⊎-bifunctor
   ; id = ⊥
   ; identityˡ = 0⊎x≡x
   ; identityʳ = {!!}
   ; assoc = {!!}
   ; triangle = {!!}
   ; pentagon = {!!}
   }

CPM× : Monoidal TypeEquivCat
CPM× = record
  { ⊗ = ×-bifunctor
  ; id = ⊤
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; assoc = {!!}
  ; triangle = {!!}
  ; pentagon = {!!}
  }
