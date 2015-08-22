{-# OPTIONS --without-K #-}

module FinEquivCat where

-- We will define a rig category whose objects are Fin types and whose
-- morphisms are type equivalences; and where the equivalence of
-- morphisms ≋ is extensional

open import Level using () renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (Rel)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_,_; proj₁; proj₂;_×_; Σ) renaming (map to map×)
open import Data.Unit
open import Data.Empty
import Function as F

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

open import FinEquiv using (_fin≃_; _●_; module Plus)
open import Equiv using (id≃; sym≃; isequiv; g-left-inv; _∼_; sym∼)
open import EquivEquiv using (_≋_; eq; id≋; sym≋; trans≋; ●-resp-≋)
open import Data.Sum.Properties

------------------------------------------------------------------------------
-- Fin and type equivalences are a category

FinEquivCat : Category lzero lzero lzero
FinEquivCat = record
  { Obj = ℕ
  ; _⇒_ = _fin≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = λ bc ab → ab ● bc 
  ; assoc = eq (λ _ → P.refl) (λ _ → P.refl) 
  ; identityˡ = eq (λ _ → P.refl) (λ _ → P.refl) 
  ; identityʳ = eq (λ _ → P.refl) (λ _ → P.refl) 
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

{--
private
  fwd : ∀ {m n} → Fin m ⊎ Fin n → Fin (m + n)
  fwd {m} {n} = proj₁ (Plus.fwd-iso {m} {n})

⊎-bifunctor : Bifunctor FinEquivCat FinEquivCat FinEquivCat
⊎-bifunctor = record
  { F₀ = λ {(m , n) → m + n}
  ; F₁ = λ {( m≃n , o≃p ) → Plus.cong+-iso m≃n o≃p}
  ; identity = eq pf₁ pf₁
  ; homomorphism = λ { {f = (f₀ , mkqinv g₀ _ _) , (f₁ , mkqinv g₁ _ _)}
                       {    (f₂ , mkqinv g₂ _ _) , (f₃ , mkqinv g₃ _ _)} → eq {!!} {!!} }
  ; F-resp-≡ = λ x → eq (λ x₁ → {!!}) {!!}
  }
  where
    open Plus
    pf₁ : ∀ {m n} → (fwd {m} {n} F.∘ (map⊎ F.id F.id) F.∘ bwd) ∼ F.id
    pf₁ y = P.trans (P.cong fwd (map⊎idid≡id (bwd y))) (fwd∘bwd~id y)
--}

------------------------------------------------------------------------------
