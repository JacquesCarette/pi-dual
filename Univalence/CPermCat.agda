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
open import CauchyEquiv

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
  { F⇒G = record { η = λ _ → idp ; commute = λ f → p≡ {!!} }
  ; F⇐G = record { η = λ _ → idp ; commute = λ f → p≡ (P.trans (F.∘̂-lid (CPerm.π (f 0F))) (P.trans (P.sym (F.cauchyext (CPerm.π (f 0F)))) (P.sym (F.∘̂-rid (F.liftCauchy (CPerm.π (f 0F))))))) }
  ; iso = λ X → record { isoˡ = lidp ; isoʳ = ridp } }

CPermMonoidal : Monoidal CPermCat
CPermMonoidal = record
  { ⊗ = ⊎p-bifunctor
   ; id = 0
   ; identityˡ = 0⊎x≡x
   ; identityʳ = {!!}
   ; assoc = {!!}
   ; triangle = {!!}
   ; pentagon = {!!}
   }
