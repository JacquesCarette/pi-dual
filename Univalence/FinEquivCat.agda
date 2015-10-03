{-# OPTIONS --without-K #-}

module FinEquivCat where

-- We will define a rig category whose objects are Fin types and whose
-- morphisms are type equivalences; and where the equivalence of
-- morphisms ≋ is extensional

open import Level using () renaming (zero to lzero; suc to lsuc)

open import Data.Empty using ()
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Unit using ()
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product
  using (_,_; proj₁; proj₂;_×_; Σ; uncurry)
  renaming (map to map×)
import Function as F using (_∘_; id)

import Relation.Binary.PropositionalEquality as P
  using (refl; trans; cong)

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

open import Equiv using (id≃; sym≃; _∼_; sym∼; _●_)
open import EquivEquiv
  using (_≋_; eq; id≋; sym≋; trans≋; _◎_; ●-assoc; lid≋; rid≋;
         linv≋; rinv≋; module _≋_)

open import FinEquivTypeEquiv
  using (_fin≃_; module PlusE; module TimesE; module PlusTimesE)
open PlusE using (_+F_; unite+; unite+r; uniti+; uniti+r)
open TimesE using (_*F_)
open import FinEquivEquiv
  using ([id+id]≋id; +●≋●+; _+≋_;
         unite₊-nat; unite₊r-nat; uniti₊-nat;
         id*id≋id)

------------------------------------------------------------------------------
-- Fin and type equivalences are a category
-- note how all of the 'higher structure' (i.e. ≋ equations) are all
-- generic, i.e. they are true of all equivalences, not just _fin≃_.

FinEquivCat : Category lzero lzero lzero
FinEquivCat = record
  { Obj = ℕ
  ; _⇒_ = _fin≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = _●_ 
  ; assoc = λ { {f = f} {g} {h} → ●-assoc {f = f} {g} {h} }
  ; identityˡ = lid≋
  ; identityʳ = rid≋ 
  ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ } 
  ; ∘-resp-≡ = _◎_
  }

FinEquivGroupoid : Groupoid FinEquivCat
FinEquivGroupoid = record 
  { _⁻¹ = sym≃ 
  ; iso = λ { {f = A≃B} → record
    { isoˡ = linv≋ A≃B
    ; isoʳ = rinv≋ A≃B
    } }
  }

-- The additive structure is monoidal

⊎-bifunctor : Bifunctor FinEquivCat FinEquivCat FinEquivCat
⊎-bifunctor = record
  { F₀ = uncurry _+_ 
  ; F₁ = uncurry _+F_
  ; identity = [id+id]≋id
  ; homomorphism = +●≋●+
  ; F-resp-≡ = uncurry _+≋_
  }

module ⊎h = MonoidalHelperFunctors FinEquivCat ⊎-bifunctor 0

0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊎x≡x = record 
  { F⇒G = record
    { η = λ _ → unite+  
    ; commute = λ _ → unite₊-nat }
  ; F⇐G = record
    { η = λ _ → uniti+ 
    ; commute = λ _ →  uniti₊-nat }
  ; iso = λ _ → record
    { isoˡ = linv≋ unite+ 
    ; isoʳ = rinv≋ unite+ 
    }
  }

x⊎0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊎0≡x = record
  { F⇒G = record
    { η = λ _ → unite+r 
    ; commute = λ _ → unite₊r-nat 
    }
  ; F⇐G = record
    { η = λ _ → uniti+r 
    ; commute = λ _ → {!!} 
    }
  ; iso = λ X → record
    { isoˡ = linv≋ unite+r
    ; isoʳ = rinv≋ unite+r
    }
  }

-- The multiplicative structure is monoidal

×-bifunctor : Bifunctor FinEquivCat FinEquivCat FinEquivCat
×-bifunctor = record
  { F₀ = uncurry _*_ 
  ; F₁ = uncurry _*F_
  ; identity = id*id≋id
  ; homomorphism = {!!}
  ; F-resp-≡ = {!!}
  }

------------------------------------------------------------------------------
