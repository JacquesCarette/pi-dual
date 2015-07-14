{-# OPTIONS --without-K #-}

module CPermCat where

open import Level using (zero)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin renaming (zero to 0F) hiding (_+_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as P

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism

open import ConcretePermutation

CPermCat : Category zero zero zero
CPermCat = record
  { Obj = ℕ
  ; _⇒_ = CPerm
  ; _≡_ = P._≡_ 
  ; id = idp
  ; _∘_ = transp
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → P.sym (assocp {p₁ = h} {g} {f})
  ; identityˡ = lidp
  ; identityʳ = ridp
  ; equiv = P.isEquivalence
  ; ∘-resp-≡ = λ { {_} {_} {_} {f} {.f} {g} {.g} P.refl P.refl → P.refl} -- transp-resp-≡
  }

CPermGroupoid : Groupoid CPermCat
CPermGroupoid = record 
  { _⁻¹ = symp 
  ; iso = λ {_} {_} {f} → record { isoˡ = rinv f ; isoʳ = linv f } 
  }

⊎p-bifunctor : Bifunctor CPermCat CPermCat CPermCat
⊎p-bifunctor = record
  { F₀ = λ { (n , m) → n + m }
  ; F₁ = λ { (p₁ , p₂) → p₁ ⊎p p₂ }
  ; identity = λ { {m , n} → 1p⊎1p≡1p {m} {n}}
  ; homomorphism = λ { {m₁ , m₂} {n₁ , n₂} {o₁ , o₂} {p₁ , p₂} {q₁ , q₂} → P.sym (⊎p-distrib {n₁} {n₂} {m₁} {m₂} {o₁} {o₂} {q₁} {q₂} {p₁} {p₂}) }
  ; F-resp-≡ = λ { (p₁≡p₃ , p₂≡p₄) → P.cong₂ _⊎p_ p₁≡p₃ p₂≡p₄ }
  }

×p-bifunctor : Bifunctor CPermCat CPermCat CPermCat
×p-bifunctor = record
  { F₀ = λ { (m , n) → m * n}
  ; F₁ = λ { (p₁ , p₂) → p₁ ×p p₂ }
  ; identity = λ { {m , n} → 1p×1p≡1p {m} }
  ; homomorphism = λ { {_} {_} {_} {p₁ , p₂} {q₁ , q₂} → ×p-distrib {p₁ = q₁} {q₂} {p₁} {p₂}}
  ; F-resp-≡ = λ {(p₁≡p₃ , p₂≡p₄) → P.cong₂ _×p_ p₁≡p₃ p₂≡p₄ }
  }

-- the 0 below is the id from CPermMonoidal
module ⊎h = MonoidalHelperFunctors CPermCat ⊎p-bifunctor 0

0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊎x≡x = record
  { F⇒G = record { η = λ _ → unite+p ; commute = λ f → unite+p∘[0⊎x]≡x∘unite+p (f 0F) }
  ; F⇐G = record { η = λ _ → uniti+p ; commute = λ f → uniti+p∘x≡[0⊎x]∘uniti+p (f 0F) }
  ; iso = λ X → record { isoˡ = linv uniti+p ; isoʳ = linv unite+p } }

x⊎0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊎0≡x = record
  { F⇒G = record { η = λ _ → uniti+rp ; commute = λ f → p≡ {!!} }
  ; F⇐G = record { η = λ _ → unite+rp ; commute = λ f → {!!} }
  ; iso = λ X → record { isoˡ = linv unite+rp ; isoʳ = linv uniti+rp } }

CPM⊎ : Monoidal CPermCat
CPM⊎ = record
  { ⊗ = ⊎p-bifunctor
   ; id = 0
   ; identityˡ = 0⊎x≡x
   ; identityʳ = x⊎0≡x
   ; assoc = {!!}
   ; triangle = {!!}
   ; pentagon = {!!}
   }

CPM× : Monoidal CPermCat
CPM× = record
  { ⊗ = ×p-bifunctor
  ; id = 1
  ; identityˡ = record 
    { F⇒G = record { η = λ X → uniti*p {X 0F} ; commute = λ f → {!!} } 
    ; F⇐G = record { η = λ X → unite*p ; commute = {!!} } 
    ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} } 
    }
  ; identityʳ = {!!}
  ; assoc = {!!}
  ; triangle = {!!}
  ; pentagon = {!!}
  }
