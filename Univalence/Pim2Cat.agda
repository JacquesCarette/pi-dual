{-# OPTIONS --without-K #-}

module Pim2Cat where

open import Level using (zero)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; isEquivalence) 

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
open import PiLevelm2 using (_⟷_; collapse)

-- We will define a rig category whose objects are Pi types and whose
-- morphisms are the trivial equivalence that identifies all Pi types;
-- and where the equivalence of morphisms is propositional equality ≡

------------------------------------------------------------------------------
-- First it is a category

triv : {A B : U} → (f : A ⟷ B) → (collapse P.≡ f)
triv collapse = P.refl 

Pim2Cat : Category zero zero zero
Pim2Cat = record
  { Obj = U
  ; _⇒_ = _⟷_
  ; _≡_ = P._≡_
  ; id = collapse
  ; _∘_ = λ _ _ → collapse
  ; assoc = P.refl 
  ; identityˡ = λ {A} {B} {f} → triv f
  ; identityʳ = λ {A} {B} {f} → triv f
  ; equiv = P.isEquivalence
  ; ∘-resp-≡ = λ _ _ → P.refl
  }

-- and a groupoid

Pim2Groupoid : Groupoid Pim2Cat
Pim2Groupoid = record 
  { _⁻¹ = λ _ → collapse
  ; iso = record { isoˡ = P.refl; isoʳ = P.refl }
  }

-- The additive structure is monoidal

PLUS-bifunctor : Bifunctor Pim2Cat Pim2Cat Pim2Cat
PLUS-bifunctor = record
  { F₀ = λ {( x , y) → PLUS x y}
  ; F₁ = λ {(x , y) → collapse}
  ; identity = P.refl
  ; homomorphism = P.refl
  ; F-resp-≡ = λ { (e₁ , e₂) → P.refl }
  }
  
module PLUSh = MonoidalHelperFunctors Pim2Cat PLUS-bifunctor ZERO

0PLUSx≡x : NaturalIsomorphism PLUSh.id⊗x PLUSh.x
0PLUSx≡x = record 
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

xPLUS0≡x : NaturalIsomorphism PLUSh.x⊗id PLUSh.x
xPLUS0≡x = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl 
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

[xPLUSy]PLUSz≡xPLUS[yPLUSz] : NaturalIsomorphism PLUSh.[x⊗y]⊗z PLUSh.x⊗[y⊗z]
[xPLUSy]PLUSz≡xPLUS[yPLUSz] = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

CPMPLUS : Monoidal Pim2Cat
CPMPLUS = record
  { ⊗ = PLUS-bifunctor
   ; id = ZERO
   ; identityˡ = 0PLUSx≡x
   ; identityʳ = xPLUS0≡x
   ; assoc = [xPLUSy]PLUSz≡xPLUS[yPLUSz]
   ; triangle = P.refl
   ; pentagon = P.refl
   }

-- The multiplicative structure is also monoidal

TIMES-bifunctor : Bifunctor Pim2Cat Pim2Cat Pim2Cat
TIMES-bifunctor = record
  { F₀ = λ {( x , y) → TIMES x y}
  ; F₁ = λ {(x , y) → collapse }
  ; identity = P.refl
  ; homomorphism = P.refl
  ; F-resp-≡ = λ { (e₁ , e₂) → P.refl}
  }

module TIMESh = MonoidalHelperFunctors Pim2Cat TIMES-bifunctor ONE

1TIMESy≡y : NaturalIsomorphism TIMESh.id⊗x TIMESh.x
1TIMESy≡y = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

yTIMES1≡y : NaturalIsomorphism TIMESh.x⊗id TIMESh.x
yTIMES1≡y = record
  { F⇒G = record 
    { η = λ X → collapse
    ;  commute = λ f → P.refl
    }
  ; F⇐G = record 
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record 
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

[xTIMESy]TIMESz≡xTIMES[yTIMESz] :
  NaturalIsomorphism TIMESh.[x⊗y]⊗z TIMESh.x⊗[y⊗z]
[xTIMESy]TIMESz≡xTIMES[yTIMESz] = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

CPMTIMES : Monoidal Pim2Cat
CPMTIMES = record
  { ⊗ = TIMES-bifunctor
  ; id = ONE
  ; identityˡ = 1TIMESy≡y
  ; identityʳ = yTIMES1≡y
  ; assoc = [xTIMESy]TIMESz≡xTIMES[yTIMESz]
  ; triangle = P.refl
  ; pentagon = P.refl
  }

-- The monoidal structures are symmetric

xPLUSy≈yPLUSx : NaturalIsomorphism PLUSh.x⊗y PLUSh.y⊗x
xPLUSy≈yPLUSx = record 
  { F⇒G = record 
    { η = λ X → collapse
    ; commute = λ f → P.refl
    } 
  ; F⇐G = record 
    { η = λ X → collapse
    ; commute = λ f → P.refl
    } 
  ; iso = λ X → record 
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

BMPLUS : Braided CPMPLUS
BMPLUS = record 
  { braid = xPLUSy≈yPLUSx
  ; unit-coh = P.refl
  ; hexagon₁ = P.refl
  ; hexagon₂ = P.refl
  }

xTIMESy≈yTIMESx : NaturalIsomorphism TIMESh.x⊗y TIMESh.y⊗x
xTIMESy≈yTIMESx = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record 
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

BMTIMES : Braided CPMTIMES
BMTIMES = record 
  { braid = xTIMESy≈yTIMESx
  ; unit-coh = P.refl
  ; hexagon₁ = P.refl
  ; hexagon₂ = P.refl
  }

SBMPLUS : Symmetric BMPLUS
SBMPLUS = record { symmetry = P.refl }

SBMTIMES : Symmetric BMTIMES
SBMTIMES = record { symmetry = P.refl }

-- And finally the multiplicative structure distributes over the
-- additive one

module r = BimonoidalHelperFunctors BMPLUS BMTIMES

x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record { isoˡ = P.refl
                       ; isoʳ = P.refl }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record { isoˡ = P.refl
                       ; isoʳ = P.refl }
  }
  
x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
x⊗0≡0 = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
0⊗x≡0 = record
  { F⇒G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; F⇐G = record
    { η = λ X → collapse
    ; commute = λ f → P.refl
    }
  ; iso = λ X → record
    { isoˡ = P.refl
    ; isoʳ = P.refl
    }
  }

TERig : RigCategory SBMPLUS SBMTIMES
TERig = record
  { distribₗ = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
  ; distribᵣ = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z]
  ; annₗ = 0⊗x≡0
  ; annᵣ = x⊗0≡0
  ; laplazaI = P.refl
  ; laplazaII = P.refl
  ; laplazaIV = P.refl
  ; laplazaVI = P.refl
  ; laplazaIX = P.refl
  ; laplazaX = P.refl
  ; laplazaXI = P.refl 
  ; laplazaXIII = P.refl
  ; laplazaXV = P.refl
  ; laplazaXVI = P.refl
  ; laplazaXVII = P.refl
  ; laplazaXIX = P.refl
  ; laplazaXXIII = P.refl
  }

------------------------------------------------------------------------------
