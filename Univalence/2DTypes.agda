{-# OPTIONS --without-K #-}

module 2DTypes where

-- open import Level renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function using (_∘_)

open import PiU
open import PiLevel0
open import PiEquiv
open import PiLevel1
open import Equiv
open import EquivEquiv using (_≋_; module _≋_)

open import Categories.Category
open import Categories.Groupoid

-- should probably make this level-polymorphic
record Typ : Set where
  field
    carr : U
    auto : carr ⟷ carr

open Typ

-- The above 'induces' a groupoid structure, which
-- we need to show in detail.
-- First, a useful container for the info we need:
record Hm (t : Typ) (a b : ⟦ carr t ⟧) : Set where
  constructor hm
  field
    eq : carr t ⟷ carr t
    fwd : proj₁ (c2equiv eq) a ≡ b
    bwd : isqinv.g (proj₂ (c2equiv eq)) b ≡ a
    
-- note how (auto t) is not actually used!
-- also: not sure e₁ and e₂ always used coherently, as types are not enough
--  to decide which one to use...
induceCat : Typ → Category _ _ _
induceCat t = record
  { Obj =  ⟦ carr t ⟧
  ; _⇒_ = Hm t -- λ a b → Σ (carr t ⟷ carr t) (λ e → proj₁ (c2equiv e) a ≡ b)
  ; _≡_ = λ { (hm e₁ _ _) → λ { (hm e₂ _ _) → e₁ ⇔ e₂} }
  ; id = hm id⟷ refl refl
  ; _∘_ = λ { {A} {B} {C} (hm e₁ fwd₁ bwd₁) (hm e₂ fwd₂ bwd₂) →
  
   let pf₁ = (begin (
        proj₁ (c2equiv e₁ ● c2equiv e₂) A
          ≡⟨ β₁ A ⟩
        (proj₁ (c2equiv e₁) ∘ (proj₁ (c2equiv e₂))) A
          ≡⟨ cong (proj₁ (c2equiv e₁)) fwd₂ ⟩
        proj₁ (c2equiv e₁) B
          ≡⟨ fwd₁ ⟩
        C ∎ ))
       -- same as above (in opposite direction), just compressed
       pf₂ = trans (β₂ C)
            (trans (cong (isqinv.g (proj₂ (c2equiv e₂))) bwd₁)
                   bwd₂)
   in
        hm (e₂ ◎ e₁) pf₁ pf₂ }
  ; assoc = assoc◎l
  ; identityˡ = idr◎l
  ; identityʳ = idl◎l
  ; equiv = record { refl = id⇔ ; sym = 2! ; trans = trans⇔ }
  ; ∘-resp-≡ = λ f g → g ⊡ f
  }
  where open Typ
        open ≡-Reasoning

induceG : (t : Typ)  → Groupoid (induceCat t)
induceG t = record
  { _⁻¹ = λ { {A} {B} (hm e fw bw) →
    hm (! e) (trans (f≡ (!≡sym≃ e) B) bw) (trans (g≡ (!≡sym≃ e) A) fw) }
  ; iso = record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }
  where open _≋_

1T : Typ
1T = record { carr = ONE; auto = id⟷ }

BOOL : U
BOOL = PLUS ONE ONE

1T′ : Typ
1T′ = record { carr = BOOL; auto = swap₊ }

-- The question now is, what is an equivalence between
-- Typ A and B ?  Since we want it to map (in some sense, trivially)
-- to the groupoid structure, this means that what we
-- really want are two functors going in each direction,
-- and a proof that these compose to the identity, but not
-- 'one the nose', but rather up to natural isomorphism.

-- Problem: 1T′ is not a fractional type!
-- To get that, you really need 1T with a non-trivial
-- automorphism.  Rather like id⟷ ⊎ id⟷ with
-- the 'right' composition law to make it into ℤ₂.
