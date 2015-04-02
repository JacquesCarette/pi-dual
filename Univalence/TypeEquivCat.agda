{-# OPTIONS --without-K #-}

module TypeEquivCat where

open import Level using (zero; suc)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (Rel)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_,_; proj₁; proj₂;_×_; Σ)
open import Data.Unit
open import Data.Empty
import Function as F

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism

open import Equiv
open import TypeEquiv

-- see EquivSetoid for some additional justification
-- basically we need g to "pin down" the inverse, else we
-- get lots of unsolved metas.
record _≋_ {A B : Set} (eq₁ eq₂ : A ≃ B) : Set where
  constructor eq
  field
    f≡ : ∀ x → eq₁ ⋆ x P.≡ eq₂ ⋆ x
    g≡ : ∀ x → (sym≃ eq₁) ⋆ x P.≡ (sym≃ eq₂) ⋆ x
 
id≋ : ∀ {A B : Set} {x : A ≃ B} → x ≋ x
id≋ = record { f≡ = λ x → P.refl ; g≡ = λ x → P.refl }

sym≋ : ∀ {A B : Set} {x y : A ≃ B} → x ≋ y → y ≋ x
sym≋ (eq f≡ g≡) = eq (λ a → P.sym (f≡ a)) (λ b → P.sym (g≡ b))

flip≋ : {A B : Set} {x y : A ≃ B} → x ≋ y → (sym≃ x) ≋ (sym≃ y)
flip≋ (eq f≡ g≡) = eq g≡ f≡

trans≋ : ∀ {A B : Set} {x y z : A ≃ B} → x ≋ y → y ≋ z → x ≋ z
trans≋ (eq f≡ g≡) (eq h≡ i≡) =
   eq (λ a → P.trans (f≡ a) (h≡ a)) (λ b → P.trans (g≡ b) (i≡ b))

●-resp-≋ : {A B C : Set} {f h : B ≃ C} {g i : A ≃ B} → f ≋ h → g ≋ i →
  (f ● g) ≋ (h ● i)
●-resp-≋ {f = f , _} {_ , mkqinv h⁻¹ _ _} {_ , mkqinv g⁻¹ _ _} {i , _}
  (eq f≡ g≡) (eq h≡ i≡) =
  eq (λ x → P.trans (P.cong f (h≡ x)) (f≡ (i x)))
     (λ x → P.trans (P.cong g⁻¹ (g≡ x)) (i≡ (h⁻¹ x)))

-- underlying it all, it uses ∘ and ≡ 
●-assoc : {A B C D : Set} {f : A ≃ B} {g : B ≃ C} {h : C ≃ D} →
      ((h ● g) ● f) ≋ (h ● (g ● f))
●-assoc = eq (λ x → P.refl) (λ x → P.refl)

TypeEquivCat : Category (suc zero) zero zero
TypeEquivCat = record
  { Obj = Set
  ; _⇒_ = _≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = _●_
  ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → ●-assoc {A} {B} {C} {D} {f} {g} {h}
  ; identityˡ = eq (λ _ → P.refl) (λ _ → P.refl)
  ; identityʳ = eq (λ _ → P.refl) (λ _ → P.refl)
  ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ }
  ; ∘-resp-≡ = ●-resp-≋
  }

TypeEquivGroupoid : Groupoid TypeEquivCat
TypeEquivGroupoid = record 
  { _⁻¹ = sym≃ 
  ; iso = λ { {_} {_} {f , mkqinv g α β} → record
    { isoˡ = eq β β
    ; isoʳ = eq α α
    } }
  }

map⊎idid≡id : {A B : Set} → (x : A ⊎ B) → map⊎ F.id F.id x P.≡ x
map⊎idid≡id (inj₁ x) = P.refl
map⊎idid≡id (inj₂ y) = P.refl

map⊎-∘ : {A B C D E F : Set} → {f : A → C} {g : B → D} {h : C → E} {i : D → F} →
  ∀ x → map⊎ (h F.∘ f) (i F.∘ g) x P.≡ map⊎ h i (map⊎ f g x)
map⊎-∘ (inj₁ x) = P.refl
map⊎-∘ (inj₂ y) = P.refl

map⊎-resp-≡ : {A B C D : Set} → {f₀ g₀ : A ≃ B} {f₁ g₁ : C ≃ D} →
  {e₁ : f₀ ≋ g₀} → {e₂ : f₁ ≋ g₁} →  
  (x : A ⊎ C) → map⊎ (proj₁ f₀) (proj₁ f₁) x P.≡ map⊎ (proj₁ g₀) (proj₁ g₁) x
map⊎-resp-≡ {e₁ = eq f≡ _} (inj₁ x) = P.cong inj₁ (f≡ x)
map⊎-resp-≡ {e₂ = eq f≡ _} (inj₂ y) = P.cong inj₂ (f≡ y)

⊎-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
⊎-bifunctor = record
  { F₀ = λ {( x , y) → x ⊎ y}
  ; F₁ = λ {(x , y) → path⊎ x y}
  ; identity = eq map⊎idid≡id map⊎idid≡id
  ; homomorphism = eq map⊎-∘ map⊎-∘
  ; F-resp-≡ = λ { (e₁ , e₂) → eq (map⊎-resp-≡ {e₁ = e₁} {e₂}) (map⊎-resp-≡ {e₁ = flip≋ e₁} {flip≋ e₂}) }
  }

path×-resp-≡ : {A B C D : Set} → {f₀ g₀ : A ≃ B} {f₁ g₁ : C ≃ D} →
  {e₁ : f₀ ≋ g₀} → {e₂ : f₁ ≋ g₁} →  
  (x : A × C) → (proj₁ f₀ (proj₁ x) , proj₁ f₁ (proj₂ x)) P.≡
                (proj₁ g₀ (proj₁ x) , proj₁ g₁ (proj₂ x))
path×-resp-≡ {e₁ = eq f≡ g≡} {eq h≡ i≡} (a , c) = P.cong₂ _,_ (f≡ a) (h≡ c)

×-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
×-bifunctor = record
  { F₀ = λ {( x , y) → x × y}
  ; F₁ = λ {(x , y) → path× x y }
  ; identity = eq (λ x → P.refl) (λ x → P.refl) -- η for products gives this
  ; homomorphism = eq (λ x → P.refl) (λ x → P.refl) -- again η for products!
  ; F-resp-≡ = λ { (e₁ , e₂) → eq (path×-resp-≡ {e₁ = e₁} {e₂}) ((path×-resp-≡ {e₁ = flip≋ e₁} {flip≋ e₂}))}
  }

module ⊎h = MonoidalHelperFunctors TypeEquivCat ⊎-bifunctor ⊥

0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊎x≡x = record 
  { F⇒G = record
    { η = λ X → unite₊equiv
    ; commute = λ f → eq {!!} (λ x → P.refl) } 
  ; F⇐G = record
    { η = λ X → uniti₊equiv
    ; commute = λ f → eq (λ x → P.refl) {!!} } 
  ; iso = λ X → record
    { isoˡ = eq {!!} {!!}
    ; isoʳ = eq (λ _ → P.refl) (λ _ → P.refl)
    }
  }

-- this needs a "flipped" unite₊equiv and uniti₊equiv, which are not written
x⊎0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊎0≡x = record
  { F⇒G = record { η = λ X → {!!} ; commute = {!!} }
  ; F⇐G = record { η = λ X → {!!} ; commute = {!!} }
  ; iso = λ X → {!!}
  }

[x⊎y]⊎z≡x⊎[y⊎z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
[x⊎y]⊎z≡x⊎[y⊎z] = record
  { F⇒G = record
    { η = λ X → assocr₊equiv
    ; commute = λ f → eq {!!} {!!}
    }
  ; F⇐G = record
    { η = λ X → assocl₊equiv
    ; commute = λ f → {!!}
    }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  }

CPM⊎ : Monoidal TypeEquivCat
CPM⊎ = record
  { ⊗ = ⊎-bifunctor
   ; id = ⊥
   ; identityˡ = 0⊎x≡x
   ; identityʳ = x⊎0≡x
   ; assoc = [x⊎y]⊎z≡x⊎[y⊎z]
   ; triangle = eq (λ x → {!!}) (λ x → {!!})
   ; pentagon = eq (λ x → {!!}) (λ x → {!!})
   }

module ×h = MonoidalHelperFunctors TypeEquivCat ×-bifunctor ⊤

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
