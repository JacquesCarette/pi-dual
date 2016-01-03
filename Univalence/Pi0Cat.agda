{-# OPTIONS --without-K #-}

module Pi0Cat where

-- Proving that Pi at level 0 symmetric rig groupoid

open import Level using () renaming (zero to lzero)
open import Data.Unit using (tt)
open import Data.Product using (_,_)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Monoidal using (Monoidal)
open import Categories.Monoidal.Helpers using (module MonoidalHelperFunctors)
open import Categories.Bifunctor using (Bifunctor)
open import Categories.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Monoidal.Braided using (Braided)
open import Categories.Monoidal.Symmetric using (Symmetric)
open import Categories.RigCategory
  using (RigCategory; module BimonoidalHelperFunctors)

open import PiU using (U; PLUS; ZERO; TIMES; ONE)
open import PiLevel0 using (_⟷_; !; triv≡; triv≡Equiv; 
  id⟷; _◎_;
  _⊕_; unite₊l; uniti₊l; unite₊r; uniti₊r; swap₊; assocr₊; assocl₊;
  _⊗_; unite⋆l; uniti⋆l; unite⋆r; uniti⋆r; swap⋆; assocr⋆; assocl⋆;
  absorbl; absorbr; factorzl; factorzr;
  dist; factor; distl; factorl)

------------------------------------------------------------------------------
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
BM⊕ = record { braid = x⊕y≡y⊕x ; unit-coh = tt; hexagon₁ = tt ; hexagon₂ = tt }

x⊗y≡y⊗x : NaturalIsomorphism ⊗h.x⊗y ⊗h.y⊗x
x⊗y≡y⊗x = record 
  { F⇒G = record { η = λ X → swap⋆ ; commute = λ f → tt } 
  ; F⇐G = record { η = λ X → swap⋆ ; commute = λ f → tt } 
  ; iso = λ X → record { isoˡ = tt ; isoʳ = tt } }

BM⊗ : Braided M⊗
BM⊗ = record { braid = x⊗y≡y⊗x ; unit-coh = tt; hexagon₁ = tt ; hexagon₂ = tt }

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
  ; laplazaIX = tt
  ; laplazaX = tt
  ; laplazaXI = tt
  ; laplazaXIII = tt
  ; laplazaXV = tt
  ; laplazaXVI = tt
  ; laplazaXVII = tt
  ; laplazaXIX = tt
  ; laplazaXXIII = tt
  }

------------------------------------------------------------------------------

