{-# OPTIONS --without-K #-}

module Pi1Cat where

-- Proving that Pi with one level of interesting 2 path structure is a
-- symmetric rig groupoid
--
-- U is a collection of types
--
-- Between any two types, there could be zero, 1, or many
-- identifications. If there is more than one idenfication, any two
-- idenfications can themselves have no identifications between them
-- (id and not at BOOL ⟷ BOOL) or they can have exactly one
-- identification between them (id and id∘id). 
-- 
-- Definition 3.1.7. A type A is a 1-type if for all x, y : A and p, q
-- : x = y and r, s : p = q, we have r = s.

open import Level using () renaming (zero to lzero)
open import Relation.Binary.Core using (IsEquivalence)

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric

open import PiLevel1
  using (U; _⟷_; id⟷; _◎_;
        _⇔_; assoc◎l; idr◎l; idl◎l; id⇔; 2!; trans⇔; resp◎⇔)

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
  ; ∘-resp-≡ = λ f g → resp◎⇔ g f 
  }

------------------------------------------------------------------------------

