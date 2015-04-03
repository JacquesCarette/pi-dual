{-# OPTIONS --without-K #-}

module FinEquivCat where

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

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided

open import FinEquiv using (_fin≃_; _●_; module Plus)
open import Equiv using (id≃; sym≃; mkqinv; _∼_; sym∼)
open import TypeEquivCat using (_≋_; eq; id≋; sym≋; trans≋; ●-resp-≋)
open import Data.Sum.Properties

------------------------------------------------------------------------------

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
  ; iso = λ { {_} {_} {f , mkqinv g α β} → record
    { isoˡ = eq β β
    ; isoʳ = eq α α
    } }
  }

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

