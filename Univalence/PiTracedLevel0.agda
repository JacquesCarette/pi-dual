{-# OPTIONS --without-K #-}

module PiTracedLevel0 where

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------------
-- Level 0 of Pi (with trace)
--
-- ZERO is a type with no elements
-- ONE is a type with one element 'tt'
-- PLUS ONE ONE is a type with elements 'false' and 'true'
-- and so on for all finite types built from ZERO, ONE, PLUS, and TIMES
-- 
-- We also have that U is a type with elements ZERO, ONE, PLUS ONE ONE, 
--   TIMES BOOL BOOL, etc.

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

infix  30 _⟷_
infixr 50 _◎_

-- Combinators, permutations, or paths depending on the perspective

data _⟷_ : U → U → Set where
  unite₊  : {t : U} → PLUS ZERO t ⟷ t
  uniti₊  : {t : U} → t ⟷ PLUS ZERO t
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆  : {t : U} → t ⟷ TIMES ONE t
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr  : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → 
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) 
  factor  : {t₁ t₂ t₃ : U} → 
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)
  trace   : {t t₁ t₂ : U} → (PLUS t₁ t ⟷ PLUS t₂ t) → (t₁ ⟷ t₂)

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊    = uniti₊
! uniti₊    = unite₊
! swap₊     = swap₊
! assocl₊   = assocr₊
! assocr₊   = assocl₊
! unite⋆    = uniti⋆
! uniti⋆    = unite⋆
! swap⋆     = swap⋆
! assocl⋆   = assocr⋆
! assocr⋆   = assocl⋆
! absorbl     = factorzr
! absorbr     = factorzl
! factorzl  = absorbr
! factorzr = absorbl
! dist      = factor 
! factor    = dist
! id⟷      = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁ 
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)
! (trace c) = trace (! c)

------------------------------------------------------------------------------
-- Cat

open import Level using () renaming (zero to lzero)
open import Data.Unit
open import Relation.Binary.Core using (IsEquivalence)
open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric
open import Categories.RigCategory
open import Categories.Monoidal.Traced

triv≡ : {t₁ t₂ : U} → (f g : t₁ ⟷ t₂) → Set
triv≡ _ _ = ⊤

triv≡Equiv : {t₁ t₂ : U} → IsEquivalence (triv≡ {t₁} {t₂})
triv≡Equiv = record 
  { refl = tt
  ; sym = λ _ → tt
  ; trans = λ _ _ → tt
  }

PiCat : Category lzero lzero lzero
PiCat = record
  { Obj = U
  ; _⇒_ = _⟷_
  ; _≡_ = triv≡ 
  ; id = id⟷
  ; _∘_ = λ y⟷z x⟷y → x⟷y ◎ y⟷z 
  ; assoc = tt 
  ; identityˡ = tt 
  ; identityʳ = tt 
  ; equiv = triv≡Equiv 
  ; ∘-resp-≡ = λ _ _ → tt 
  }

-- and a groupoid

PiGroupoid : Groupoid PiCat
PiGroupoid = record 
  { _⁻¹ = ! 
  ; iso = record { isoˡ = tt ; isoʳ = tt } 
  }

-- additive bifunctor and monoidal structure
⊕-bifunctor : Bifunctor PiCat PiCat PiCat
⊕-bifunctor = record
  { F₀ = λ {(u , v) → PLUS u v}
  ; F₁ = λ {(x⟷y , z⟷w) → x⟷y ⊕ z⟷w }
  ; identity = tt
  ; homomorphism = tt
  ; F-resp-≡ = λ _ → tt
  }

module ⊎h = MonoidalHelperFunctors PiCat ⊕-bifunctor ZERO

0⊕x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊕x≡x = record 
  { F⇒G = record
    { η = λ X → unite₊
    ; commute = λ _ → tt } 
  ; F⇐G = record
    { η = λ X → uniti₊
    ; commute = λ _ → tt } 
  ; iso = λ X → record { isoˡ = tt; isoʳ = tt }
  }

x⊕0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊕0≡x = record
  { F⇒G = record
    { η = λ X → swap₊ ◎ unite₊  -- !!!
    ; commute = λ _ → tt
    }
  ; F⇐G = record
    { η = λ X → uniti₊ ◎ swap₊
    ; commute = λ _ → tt
    }
  ; iso = λ X → record 
    { isoˡ = tt
    ; isoʳ = tt
    }
  }

[x⊕y]⊕z≡x⊕[y⊕z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
[x⊕y]⊕z≡x⊕[y⊕z] = record
  { F⇒G = record
    { η = λ X → assocr₊
    ; commute = λ f → tt
    }
  ; F⇐G = record
    { η = λ X → assocl₊
    ; commute = λ _ → tt
    }
  ; iso = λ X → record
    { isoˡ = tt
    ; isoʳ = tt
    }
  }

M⊕ : Monoidal PiCat
M⊕ = record
  { ⊗ = ⊕-bifunctor
  ; id = ZERO
  ; identityˡ = 0⊕x≡x
  ; identityʳ = x⊕0≡x
  ; assoc = [x⊕y]⊕z≡x⊕[y⊕z]
  ; triangle = tt
  ; pentagon = tt
  }

-- multiplicative bifunctor and monoidal structure
⊗-bifunctor : Bifunctor PiCat PiCat PiCat
⊗-bifunctor =  record
  { F₀ = λ {(u , v) → TIMES u v}
  ; F₁ = λ {(x⟷y , z⟷w) → x⟷y ⊗ z⟷w }
  ; identity = tt
  ; homomorphism = tt
  ; F-resp-≡ = λ _ → tt
  }

module ⊗h = MonoidalHelperFunctors PiCat ⊗-bifunctor ONE

1⊗x≡x : NaturalIsomorphism ⊗h.id⊗x ⊗h.x
1⊗x≡x = record 
  { F⇒G = record
    { η = λ X → unite⋆
    ; commute = λ _ → tt } 
  ; F⇐G = record
    { η = λ X → uniti⋆
    ; commute = λ _ → tt } 
  ; iso = λ X → record { isoˡ = tt; isoʳ = tt }
  }

x⊗1≡x : NaturalIsomorphism ⊗h.x⊗id ⊗h.x
x⊗1≡x = record
  { F⇒G = record
    { η = λ X → swap⋆ ◎ unite⋆  -- !!!
    ; commute = λ _ → tt
    }
  ; F⇐G = record
    { η = λ X → uniti⋆ ◎ swap⋆
    ; commute = λ _ → tt
    }
  ; iso = λ X → record 
    { isoˡ = tt
    ; isoʳ = tt
    }
  }

[x⊗y]⊗z≡x⊗[y⊗z] : NaturalIsomorphism ⊗h.[x⊗y]⊗z ⊗h.x⊗[y⊗z]
[x⊗y]⊗z≡x⊗[y⊗z] = record
  { F⇒G = record
    { η = λ X → assocr⋆
    ; commute = λ f → tt
    }
  ; F⇐G = record
    { η = λ X → assocl⋆
    ; commute = λ _ → tt
    }
  ; iso = λ X → record
    { isoˡ = tt
    ; isoʳ = tt
    }
  }

M⊗ : Monoidal PiCat
M⊗ = record
  { ⊗ = ⊗-bifunctor
  ; id = ONE
  ; identityˡ = 1⊗x≡x
  ; identityʳ = x⊗1≡x
  ; assoc = [x⊗y]⊗z≡x⊗[y⊗z]
  ; triangle = tt
  ; pentagon = tt
  }

x⊕y≡y⊕x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
x⊕y≡y⊕x = record 
  { F⇒G = record { η = λ X → swap₊ ; commute = λ f → tt } 
  ; F⇐G = record { η = λ X → swap₊ ; commute = λ f → tt } 
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt } }

BM⊕ : Braided M⊕
BM⊕ = record { braid = x⊕y≡y⊕x ; hexagon₁ = tt ; hexagon₂ = tt }

x⊗y≡y⊗x : NaturalIsomorphism ⊗h.x⊗y ⊗h.y⊗x
x⊗y≡y⊗x = record 
  { F⇒G = record { η = λ X → swap⋆ ; commute = λ f → tt } 
  ; F⇐G = record { η = λ X → swap⋆ ; commute = λ f → tt } 
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt } }

BM⊗ : Braided M⊗
BM⊗ = record { braid = x⊗y≡y⊗x ; hexagon₁ = tt ; hexagon₂ = tt }

SBM⊕ : Symmetric BM⊕
SBM⊕ = record { symmetry = tt }

-- trace

Pi0Traced : Traced SBM⊕
Pi0Traced = record {
    trace = trace
  ; vanish_id = tt
  ; vanish_⊗ = tt
  ; superpose = tt
  ; yank = tt 
  }

--

SBM⊗ : Symmetric BM⊗
SBM⊗ = record { symmetry = tt }

module r = BimonoidalHelperFunctors SBM⊕ BM⊗

x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
x⊗0≡0 = record 
  { F⇒G = record { η = λ X → absorbl ; commute = λ f → tt } 
  ; F⇐G = record { η = λ X → factorzr ; commute = λ f → tt } 
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt } 
  }

0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
0⊗x≡0 = record
  { F⇒G = record { η = λ X → absorbr ; commute = λ f → tt }
  ; F⇐G = record { η = λ X → factorzl ; commute = λ f → tt }
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt }
  }

x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record -- this probably says we need distl/distr
  { F⇒G = record { η = λ X → swap⋆ ◎ dist ◎ (swap⋆ ⊕ swap⋆) ; commute = λ f → tt }
  ; F⇐G = record { η = λ X → (swap⋆ ⊕ swap⋆) ◎ factor ◎ swap⋆ ; commute = λ f → tt }
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record { η = λ X → dist ; commute = λ f → tt }
  ; F⇐G = record { η = λ X → factor ; commute = λ f → tt }
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt }
  }

Pi0Rig : RigCategory SBM⊕ BM⊗
Pi0Rig = record 
  { distribₗ = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
  ; distribᵣ = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z] 
  ; annₗ = x⊗0≡0 
  ; annᵣ = 0⊗x≡0 
  }

------------------------------------------------------------------------------

