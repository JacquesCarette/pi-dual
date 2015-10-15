{-# OPTIONS --without-K #-}

module Pi0Semiring where

import Level

open import PiU
open import PiLevel0

open import Algebra using (CommutativeSemiring)
open import Algebra.Structures
  using (IsSemigroup; IsCommutativeMonoid; IsCommutativeSemiring)
  
------------------------------------------------------------------------------
-- Commutative semiring structure of U

typesPlusIsSG : IsSemigroup _⟷_ PLUS
typesPlusIsSG = record {
  isEquivalence = record { refl = id⟷ ; sym = ! ; trans = _◎_ } ;
  assoc = λ t₁ t₂ t₃ → assocr₊ {t₁} {t₂} {t₃} ;
  ∙-cong = _⊕_
  }

typesTimesIsSG : IsSemigroup _⟷_ TIMES
typesTimesIsSG = record {
  isEquivalence = record { refl = id⟷ ; sym = ! ; trans = _◎_ } ;
  assoc = λ t₁ t₂ t₃ → assocr⋆ {t₁} {t₂} {t₃} ;
  ∙-cong = _⊗_
  }

typesPlusIsCM : IsCommutativeMonoid _⟷_ PLUS ZERO
typesPlusIsCM = record {
  isSemigroup = typesPlusIsSG ;
  identityˡ = λ t → unite₊l {t} ;
  comm = λ t₁ t₂ → swap₊ {t₁} {t₂}
  }

typesTimesIsCM : IsCommutativeMonoid _⟷_ TIMES ONE
typesTimesIsCM = record {
  isSemigroup = typesTimesIsSG ;
  identityˡ = λ t → unite⋆l {t} ;
  comm = λ t₁ t₂ → swap⋆ {t₁} {t₂}
  }

typesIsCSR : IsCommutativeSemiring _⟷_ PLUS TIMES ZERO ONE
typesIsCSR = record {
  +-isCommutativeMonoid = typesPlusIsCM ;
  *-isCommutativeMonoid = typesTimesIsCM ;
  distribʳ = λ t₁ t₂ t₃ → dist {t₂} {t₃} {t₁} ; 
  zeroˡ = λ t → absorbr {t}
  }

typesCSR : CommutativeSemiring Level.zero Level.zero
typesCSR = record {
  Carrier = U ;
  _≈_ = _⟷_ ;
  _+_ = PLUS ;
  _*_ = TIMES ;
  0# = ZERO ;
  1# = ONE ;
  isCommutativeSemiring = typesIsCSR
  }

------------------------------------------------------------------------------
