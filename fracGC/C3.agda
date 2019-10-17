{-# OPTIONS --without-K #-}

module C3 where
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Nullary

infix  70 _×ᵤ_
infix  60 _+ᵤ_
infix  40 _↔_
infixr 50 _◎_

-- Pi
mutual
  data 𝕌 : Set where
    𝟘 : 𝕌
    𝟙 : 𝕌
    _+ᵤ_ : 𝕌 → 𝕌 → 𝕌
    _×ᵤ_ : 𝕌 → 𝕌 → 𝕌
    ●_[_] : (t : 𝕌) → ⟦ t ⟧ → 𝕌
    𝟙/●_[_] : (t : 𝕌) → ⟦ t ⟧ → 𝕌

  ⟦_⟧ : 𝕌 → Set
  ⟦ 𝟘 ⟧ = ⊥
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ ● t [ v ] ⟧ = Σ[ x ∈ ⟦ t ⟧ ] x ≡ v
  ⟦ 𝟙/● t [ v ] ⟧ = ⊤  -- all information is in the type
  
  data _↔_ : 𝕌 → 𝕌 → Set where
    unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ↔ t
    uniti₊l : {t : 𝕌} → t ↔ 𝟘 +ᵤ t
    unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ↔ t
    uniti₊r : {t : 𝕌} → t ↔ t +ᵤ 𝟘
    swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ↔ t₂ +ᵤ t₁
    assocl₊ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ↔ (t₁ +ᵤ t₂) +ᵤ t₃
    assocr₊ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ↔ t₁ +ᵤ (t₂ +ᵤ t₃)
    unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ↔ t
    uniti⋆l : {t : 𝕌} → t ↔ 𝟙 ×ᵤ t
    unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ↔ t
    uniti⋆r : {t : 𝕌} → t ↔ t ×ᵤ 𝟙
    swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ↔ t₂ ×ᵤ t₁
    assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ ×ᵤ t₂) ×ᵤ t₃
    assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ↔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
    absorbr : {t : 𝕌} → 𝟘 ×ᵤ t ↔ 𝟘
    absorbl : {t : 𝕌} → t ×ᵤ 𝟘 ↔ 𝟘
    factorzr : {t : 𝕌} → 𝟘 ↔ t ×ᵤ 𝟘
    factorzl : {t : 𝕌} → 𝟘 ↔ 𝟘 ×ᵤ t
    dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ↔ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
    factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ +ᵤ t₂) ×ᵤ t₃
    distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ↔ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
    factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ↔ t₁ ×ᵤ (t₂ +ᵤ t₃)
    id↔     : {t : 𝕌} → t ↔ t
    _◎_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ↔ t₂) → (t₂ ↔ t₃) → (t₁ ↔ t₃)
    _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ +ᵤ t₂ ↔ t₃ +ᵤ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ ×ᵤ t₂ ↔ t₃ ×ᵤ t₄)
    -- new combinators
    η : {t : 𝕌} {v : ⟦ t ⟧} → 𝟙 ↔ ● t [ v ] ×ᵤ 𝟙/● t [ v ]
    ε : {t : 𝕌} {v : ⟦ t ⟧} → ● t [ v ] ×ᵤ 𝟙/● t [ v ] ↔ 𝟙
    ext : {t : 𝕌} {v : ⟦ t ⟧} → ● t [ v ] ↔ t
    ret : {t : 𝕌} {v : ⟦ t ⟧} → t ↔ ● t [ v ]

𝕌dec : (t : 𝕌) → Decidable (_≡_ {A = ⟦ t ⟧})
𝕌dec 𝟘 ()
𝕌dec 𝟙 tt tt = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ y) with 𝕌dec t₁ x y
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ .x) | yes refl = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ y)  | no ¬p = no (λ p → ¬p (lem p))
  where
  lem : {x y : ⟦ t₁ ⟧} → inj₁ x ≡ inj₁ y → x ≡ y
  lem refl = refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₂ y) = no (λ ())
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₁ y) = no (λ ())
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ y) with 𝕌dec t₂ x y
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ .x) | yes refl = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ y) | no ¬p = no (λ p → ¬p (lem p))
  where
  lem : {x y : ⟦ t₂ ⟧} → inj₂ x ≡ inj₂ y → x ≡ y
  lem refl = refl
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , y₂) with 𝕌dec t₁ x₁ x₂ | 𝕌dec t₂ y₁ y₂
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (.x₁ , .y₁) | yes refl | yes refl = yes refl
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (.x₁ , y₂) | yes refl | no ¬p = no (λ p → ¬p (cong proj₂ p))
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , .y₁) | no ¬p | yes refl = no (λ p → ¬p (cong proj₁ p))
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , y₂) | no ¬p | no ¬p₁ = no (λ p → ¬p (cong proj₁ p))
𝕌dec ● t [ v ] (.v , refl) (.v , refl) = yes refl
𝕌dec 𝟙/● t [ v ] tt tt = yes refl

interp : {t₁ t₂ : 𝕌} → (t₁ ↔ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
interp unite₊l (inj₁ ())
interp unite₊l (inj₂ v) = v
interp uniti₊l v = inj₂ v
interp unite₊r (inj₁ v) = v
interp unite₊r (inj₂ ())
interp uniti₊r v = inj₁ v
interp swap₊ (inj₁ v) = inj₂ v
interp swap₊ (inj₂ v) = inj₁ v
interp assocl₊ (inj₁ v) = inj₁ (inj₁ v)
interp assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
interp assocl₊ (inj₂ (inj₂ v)) = inj₂ v
interp assocr₊ (inj₁ (inj₁ v)) = inj₁ v
interp assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
interp assocr₊ (inj₂ v) = inj₂ (inj₂ v)
interp unite⋆l v = proj₂ v
interp uniti⋆l v = tt , v
interp unite⋆r v = proj₁ v
interp uniti⋆r v = v , tt
interp swap⋆ (v₁ , v₂) = v₂ , v₁
interp assocl⋆ (v₁ , v₂ , v₃) = (v₁ , v₂) , v₃
interp assocr⋆ ((v₁ , v₂) , v₃) = v₁ , v₂ , v₃
interp absorbr (() , v)
interp absorbl (v , ())
interp factorzr ()
interp factorzl ()
interp dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
interp dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
interp factor (inj₁ (v₁ , v₃)) = inj₁ v₁ , v₃
interp factor (inj₂ (v₂ , v₃)) = inj₂ v₂ , v₃
interp distl (v₁ , inj₁ v₂) = inj₁ (v₁ , v₂)
interp distl (v₁ , inj₂ v₃) = inj₂ (v₁ , v₃)
interp factorl (inj₁ (v₁ , v₂)) = v₁ , inj₁ v₂
interp factorl (inj₂ (v₁ , v₃)) = v₁ , inj₂ v₃
interp id↔ v = v
interp (c₁ ◎ c₂) v = interp c₂ (interp c₁ v)
interp (c₁ ⊕ c₂) (inj₁ v) = inj₁ (interp c₁ v)
interp (c₁ ⊕ c₂) (inj₂ v) = inj₂ (interp c₂ v)
interp (c₁ ⊗ c₂) (v₁ , v₂) = interp c₁ v₁ , interp c₂ v₂
interp (η {t} {v}) tt = (v , refl) , tt
interp ε v = tt
interp ext (v , refl) = v
interp (ret {t} {v}) x with 𝕌dec t x v
interp (ret {_} {.x}) x | yes refl = x , refl
interp (ret {_} {v}) x | no ¬p = {!!}  -- stuck
