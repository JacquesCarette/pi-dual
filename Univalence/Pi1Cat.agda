{-# OPTIONS --without-K #-}

module Pi1Cat where

-- Proving that Pi with one level of interesting 2 path structure is a
-- symmetric rig groupoid
--
-- U is a collection of types
--
-- Between any two types, there could be zero, one, or many
-- identifications. If there is more than one idenfication, any two
-- idenfications can themselves have no identifications between them
-- (id and not at BOOL ⟷ BOOL) or they can have exactly one
-- identification between them (id and id∘id). Effectively, two types
-- may be identified by several permutations. These permutations can
-- be expressed in different ways but permutations that have the same
-- extensional behavior are identified and permutations that have
-- different extensional behavior are not identified. Interesting the
-- identifications between permutations are essentially the coherent
-- conditions of monoidal categories. The following quote is
-- enlightening:
--
-- What Mac Lane does can be described in logical terms in the
-- following manner. On the one hand, he has an axiomatization, and,
-- on the other hand, he has a model category where arrows are
-- permutations; then he shows that his axiomatization is complete
-- with respect to this model. It is no wonder that his coherence
-- problem reduces to the completeness problem for the usual
-- axiomatization of symmetric groups. (p.3 of
-- http://www.mi.sanu.ac.rs/~kosta/coh.pdf)
-- 
-- Definition 3.1.7. A type A is a 1-type if for all x, y : A and p, q
-- : x = y and r, s : p = q, we have r = s.

open import Level using () renaming (zero to lzero)
open import Relation.Binary.Core using (IsEquivalence)
open import Data.Product using (_,_)
open import Data.Fin using (Fin; zero; suc)

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric
open import Categories.RigCategory

open import PiLevel0
  using (U; _⟷_; id⟷; _◎_;
        !; !!;
        PLUS; _⊕_; ZERO;
        unite₊l; uniti₊l; unite₊r; uniti₊r;
        swap₊;
        assocr₊; assocl₊;
        TIMES; _⊗_; ONE;
        unite⋆l; uniti⋆l; unite⋆r; uniti⋆r;
        swap⋆;
        assocr⋆; assocl⋆;
        absorbl; absorbr; factorzl; factorzr;
        dist; factor; distl; factorl)

open import PiLevel1

------------------------------------------------------------------------------
-- The equality of morphisms is derived from the coherence conditions
-- of the appropriate categories

⇔Equiv : {t₁ t₂ : U} → IsEquivalence (_⇔_ {t₁} {t₂})
⇔Equiv = record 
  { refl = id⇔
  ; sym = 2!
  ; trans = trans⇔ 
  }

PiCat : Category lzero lzero lzero
PiCat = record
  { Obj = U
  ; _⇒_ = _⟷_
  ; _≡_ = _⇔_
  ; id = id⟷
  ; _∘_ = λ y⟷z x⟷y → x⟷y ◎ y⟷z 
  ; assoc = assoc◎l 
  ; identityˡ = idr◎l 
  ; identityʳ = idl◎l 
  ; equiv = ⇔Equiv 
  ; ∘-resp-≡ = λ f g → g ⊡ f 
  }

PiGroupoid : Groupoid PiCat
PiGroupoid = record 
  { _⁻¹ = ! 
  ; iso = record { isoˡ = linv◎l ; isoʳ = rinv◎l } 
  }

-- additive bifunctor and monoidal structure
⊕-bifunctor : Bifunctor PiCat PiCat PiCat
⊕-bifunctor = record
  { F₀ = λ {(u , v) → PLUS u v}
  ; F₁ = λ {(x⟷y , z⟷w) → x⟷y ⊕ z⟷w }
  ; identity = id⟷⊕id⟷⇔
  ; homomorphism = hom⊕◎⇔
  ; F-resp-≡ = λ {(x , y) → resp⊕⇔ x y}
  }

module ⊎h = MonoidalHelperFunctors PiCat ⊕-bifunctor ZERO

-- note how powerful linv◎l/rinv◎l are in iso below
0⊕x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊕x≡x = record 
  { F⇒G = record { η = λ X → unite₊l ; commute = λ f → unite₊l⇔r } 
  ; F⇐G = record { η = λ X → uniti₊l ; commute = λ f → uniti₊l⇔r } 
  ; iso = λ X → record { isoˡ = linv◎l; isoʳ = rinv◎l }
  }

x⊕0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊕0≡x = record
  { F⇒G = record { η = λ X → unite₊r ; commute = λ f → unite₊r⇔r }
  ; F⇐G = record { η = λ X → uniti₊r ; commute = λ f → uniti₊r⇔r }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }


[x⊕y]⊕z≡x⊕[y⊕z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
[x⊕y]⊕z≡x⊕[y⊕z] = record
  { F⇒G = record
    { η = λ X → assocr₊
    ; commute = λ f → assocr⊕r
    }
  ; F⇐G = record
    { η = λ X → assocl₊
    ; commute = λ f → assocl⊕l
    }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

M⊕ : Monoidal PiCat
M⊕ = record
  { ⊗ = ⊕-bifunctor
  ; id = ZERO
  ; identityˡ = 0⊕x≡x
  ; identityʳ = x⊕0≡x
  ; assoc = [x⊕y]⊕z≡x⊕[y⊕z]
  ; triangle = triangle⊕l
  ; pentagon = pentagon⊕l
  }

------------------------------------------------------------------------------

-- multiplicative bifunctor and monoidal structure
⊗-bifunctor : Bifunctor PiCat PiCat PiCat
⊗-bifunctor = record
  { F₀ = λ {(u , v) → TIMES u v}
  ; F₁ = λ {(x⟷y , z⟷w) → x⟷y ⊗ z⟷w }
  ; identity = id⟷⊗id⟷⇔
  ; homomorphism = hom⊗◎⇔
  ; F-resp-≡ = λ {(x , y) → resp⊗⇔ x y}
  }

module ×h = MonoidalHelperFunctors PiCat ⊗-bifunctor ONE

1⊗x≡x : NaturalIsomorphism ×h.id⊗x ×h.x
1⊗x≡x = record 
  { F⇒G = record
    { η = λ X → unite⋆l
    ; commute = λ f → uniter⋆⇔l } 
  ; F⇐G = record
    { η = λ X → uniti⋆l
    ; commute = λ f → unitir⋆⇔l } 
  ; iso = λ X → record { isoˡ = linv◎l; isoʳ = rinv◎l }
  }

x⊗1≡x : NaturalIsomorphism ×h.x⊗id ×h.x
x⊗1≡x = record
  { F⇒G = record
    { η = λ X → unite⋆r 
    ; commute = λ f → uniter⋆⇔r
    }
  ; F⇐G = record
    { η = λ X → uniti⋆r
    ; commute = λ f → unitir⋆⇔r 
    }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

[x⊗y]⊗z≡x⊗[y⊗z] : NaturalIsomorphism ×h.[x⊗y]⊗z ×h.x⊗[y⊗z]
[x⊗y]⊗z≡x⊗[y⊗z] = record
  { F⇒G = record
    { η = λ X → assocr⋆
    ; commute = λ f → assocr⊗r
    }
  ; F⇐G = record
    { η = λ X → assocl⋆
    ; commute = λ f → assocl⊗l
    }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

M⊗ : Monoidal PiCat
M⊗ = record
  { ⊗ = ⊗-bifunctor
  ; id = ONE
  ; identityˡ = 1⊗x≡x
  ; identityʳ = x⊗1≡x
  ; assoc = [x⊗y]⊗z≡x⊗[y⊗z]
  ; triangle = triangle⊗l
  ; pentagon = pentagon⊗l
  }

x⊕y≡y⊕x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
x⊕y≡y⊕x = record 
  { F⇒G = record { η = λ X → swap₊ ; commute = λ f → swapr₊⇔ } 
  ; F⇐G = record { η = λ X → swap₊ ; commute = λ f → swapr₊⇔ } 
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l } }

BM⊕ : Braided M⊕
BM⊕ = record
  { braid = x⊕y≡y⊕x
  ; hexagon₁ = hexagonr⊕l
  ; hexagon₂ = hexagonl⊕l
  }

x⊗y≡y⊗x : NaturalIsomorphism ×h.x⊗y ×h.y⊗x
x⊗y≡y⊗x = record 
  { F⇒G = record { η = λ X → swap⋆ ; commute = λ f → swapr⋆⇔ } 
  ; F⇐G = record { η = λ X → swap⋆ ; commute = λ f → swapr⋆⇔ } 
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l } }

BM⊗ : Braided M⊗
BM⊗ = record
  { braid = x⊗y≡y⊗x
  ; hexagon₁ = hexagonr⊗l
  ; hexagon₂ = hexagonl⊗l
  }

SBM⊕ : Symmetric BM⊕
SBM⊕ = record { symmetry = linv◎l }

SBM⊗ : Symmetric BM⊗
SBM⊗ = record { symmetry = rinv◎l }

module r = BimonoidalHelperFunctors BM⊕ BM⊗

x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
x⊗0≡0 = record 
  { F⇒G = record
    { η = λ X → absorbl
    ; commute = λ f → absorbl⇔l
    } 
  ; F⇐G = record
    { η = λ X → factorzr
    ; commute = λ f → factorzr⇔l
    } 
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l } 
  }

0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
0⊗x≡0 = record
  { F⇒G = record { η = λ X → absorbr ; commute = λ f → absorbr⇔l }
  ; F⇐G = record { η = λ X → factorzl ; commute = λ f → factorzl⇔l }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record
  { F⇒G = record { η = λ _ → distl ; commute = λ f → distl⇔l }
  ; F⇐G = record { η = λ _ → factorl ; commute = λ f → factorl⇔l }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record { η = λ X → dist ; commute = λ f → dist⇔l }
  ; F⇐G = record { η = λ X → factor ; commute = λ f → factor⇔l }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

Pi0Rig : RigCategory SBM⊕ SBM⊗
Pi0Rig = record 
  { distribₗ = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
  ; distribᵣ = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z] 
  ; annₗ = 0⊗x≡0 
  ; annᵣ = x⊗0≡0
  ; laplazaI = swap₊distl⇔l
  ; laplazaII = dist-swap⋆⇔l
  ; laplazaIV = assocl₊-dist-dist⇔l
  ; laplazaVI = assocl⋆-distl⇔l
  ; laplazaX = absorbr0-absorbl0⇔
  ; laplazaXI = absorbr⇔distl-absorb-unite
  ; laplazaXIII = unite⋆r0-absorbr1⇔
  ; laplazaXV = absorbl≡swap⋆◎absorbr 
  }
