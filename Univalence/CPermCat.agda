{-# OPTIONS --without-K #-}

module CPermCat where

open import Level using (zero)
open import Data.Nat using (ℕ;_+_)
open import Data.Fin renaming (zero to 0F) hiding (_+_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as P

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal

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
  ; ∘-resp-≡ = transp-resp-≡
  }

CPermGroupoid : Groupoid CPermCat
CPermGroupoid = record 
  { _⁻¹ = symp 
  ; iso = λ {_} {_} {f} → record { isoˡ = rinv f ; isoʳ = linv f } 
  }

CPermMonoidal : Monoidal CPermCat
CPermMonoidal = record
  { ⊗ = record
          { F₀ = λ { (n , m) → n + m }
          ; F₁ = λ { (p₁ , p₂) → p₁ ⊎p p₂ }
          ; identity = λ { {m , n} → 1p⊎1p≡1p {m} {n}}
          ; homomorphism = λ { {m} {n} {o} {p₁ , p₂} {q₁ , q₂} → p≡ {!!} }
          ; F-resp-≡ = {!!}
          }
   ; id = 0
   ; identityˡ = record { F⇒G = record { η = λ X → idp {X 0F} ; commute = {!!} } ; F⇐G = {!!} ; iso = {!!} }
   ; identityʳ = {!!}
   ; assoc = {!!}
   ; triangle = {!!}
   ; pentagon = {!!}
   }
