{-# OPTIONS --without-K #-}

module FinEquivCat where

-- We will define a rig category whose objects are Fin types and whose
-- morphisms are type equivalences; and where the equivalence of
-- morphisms ≋ is extensional

open import Level using () renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as P
  using (refl; trans; cong)
open import Relation.Binary using (Rel)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_,_; proj₁; proj₂;_×_; Σ) renaming (map to map×)
open import Data.Unit using ()
open import Data.Empty using ()
import Function as F using (_∘_; id)

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

open import FinEquiv using (_fin≃_; module Plus)
open import Equiv using (id≃; sym≃; isequiv; g-left-inv; _∼_; sym∼; _●_)
open import EquivEquiv
  using (_≋_; eq; id≋; sym≋; trans≋; ●-resp-≋; ●-assoc; lid≋; rid≋)
open import Data.Sum.Properties
  using (map⊎idid≡id)

------------------------------------------------------------------------------
-- Fin and type equivalences are a category

FinEquivCat : Category lzero lzero lzero
FinEquivCat = record
  { Obj = ℕ
  ; _⇒_ = _fin≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = _●_ 
  ; assoc = λ { {f = f} {g} {h} → ●-assoc f g h}
  ; identityˡ = lid≋
  ; identityʳ = rid≋ 
  ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ } 
  ; ∘-resp-≡ = ●-resp-≋ 
  }

FinEquivGroupoid : Groupoid FinEquivCat
FinEquivGroupoid = record 
  { _⁻¹ = sym≃ 
  ; iso = λ { {_} {_} {A≃B} →
    let α = isequiv.α (proj₂ A≃B) in
    let β = g-left-inv A≃B in record
    { isoˡ = eq β β
    ; isoʳ = eq α α
    } }
  }

-- The additive structure is monoidal

{-
⊎-bifunctor : Bifunctor FinEquivCat FinEquivCat FinEquivCat
⊎-bifunctor = record
  { F₀ = λ {(m , n) → m + n}
  ; F₁ = λ {( m≃n , o≃p ) → m≃n +F o≃p}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≡ = λ x → eq (λ x₁ → {!!}) {!!}
  }
  where open Plus
-}
------------------------------------------------------------------------------
