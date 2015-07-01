{-# OPTIONS --without-K #-}

module Pi0Cat where

-- Proving that Pi with trivial 2 paths structure is a symmetric rig groupoid
--
-- U is a collection of types
--
-- Between any two types, there could be zero, one, or many
-- identifications. If there is more than one idenfication we force
-- them to be the same; so 'id' and 'not' at BOOL ⟷ BOOL are the same
-- and U effectively collapses to the set of natural numbers
-- 
-- Definition 3.1.1.
-- A type A is a set if for all x,y : A and all p,q : x=y, we have p=q.

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

-- explicit using clause, to show what parts are used. 
-- in the order they were needed below, too.
open import PiLevel0 using (U; _⟷_; id⟷; _◎_; !;
  PLUS; _⊕_; ZERO; unite₊l; uniti₊l; unite₊r; uniti₊r; swap₊; assocr₊; assocl₊;
  TIMES; _⊗_; ONE; unite⋆l; uniti⋆l; unite⋆r; uniti⋆r; swap⋆; assocr⋆; assocl⋆;
  absorbl; absorbr; factorzl; factorzr;
  dist; factor; distl; factorl)

------------------------------------------------------------------------------
-- Trivial equivalence; equates all morphisms of the same type so for
-- example id and not : BOOL ⟷ BOOL are equated

triv≡ : {t₁ t₂ : U} → (f g : t₁ ⟷ t₂) → Set
triv≡ _ _ = ⊤

triv≡Equiv : {t₁ t₂ : U} → IsEquivalence (triv≡ {t₁} {t₂})
triv≡Equiv = record 
  { refl = tt
  ; sym = λ _ → tt
  ; trans = λ _ _ → tt
  }

-- It is a category...

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
    { η = λ X → unite₊l
    ; commute = λ _ → tt } 
  ; F⇐G = record
    { η = λ X → uniti₊l
    ; commute = λ _ → tt } 
  ; iso = λ X → record { isoˡ = tt; isoʳ = tt }
  }

x⊕0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊕0≡x = record
  { F⇒G = record
    { η = λ X → unite₊r
    ; commute = λ _ → tt
    }
  ; F⇐G = record
    { η = λ X → uniti₊r
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
    { η = λ X → unite⋆l
    ; commute = λ _ → tt } 
  ; F⇐G = record
    { η = λ X → uniti⋆l
    ; commute = λ _ → tt } 
  ; iso = λ X → record { isoˡ = tt; isoʳ = tt }
  }

x⊗1≡x : NaturalIsomorphism ⊗h.x⊗id ⊗h.x
x⊗1≡x = record
  { F⇒G = record
    { η = λ X → unite⋆r
    ; commute = λ _ → tt
    }
  ; F⇐G = record
    { η = λ X → uniti⋆r
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

SBM⊗ : Symmetric BM⊗
SBM⊗ = record { symmetry = tt }

module r = BimonoidalHelperFunctors BM⊕ BM⊗

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
  { F⇒G = record { η = λ X → distl ; commute = λ f → tt }
  ; F⇐G = record { η = λ X → factorl ; commute = λ f → tt }
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record { η = λ X → dist ; commute = λ f → tt }
  ; F⇐G = record { η = λ X → factor ; commute = λ f → tt }
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt }
  }

Pi0Rig : RigCategory SBM⊕ SBM⊗
Pi0Rig = record 
  { distribₗ = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
  ; distribᵣ = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z] 
  ; annₗ = 0⊗x≡0 
  ; annᵣ = x⊗0≡0
  ; laplazaI = tt
  ; laplazaII = tt
  ; laplazaIV = tt
  ; laplazaVI = tt
  ; laplazaX = tt
  ; laplazaXI = tt
  ; laplazaXIII = tt
  ; laplazaXV = tt
  ; laplazaXVI = tt
  ; laplazaXVII = tt
  ; laplazaXIX = tt
  }
------------------------------------------------------------------------------

