{-# OPTIONS --without-K #-}

module PiFracDyn where
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Core
open import Relation.Nullary

open import Singleton

infix  70 _×ᵤ_
infix  60 _+ᵤ_
infix  40 _↔_
infixr 50 _⊚_

data ◯ : Set where
  ○ : ◯

-- Pi

mutual
  data 𝕌 : Set where
    𝟘 : 𝕌
    𝟙 : 𝕌
    _+ᵤ_ : 𝕌 → 𝕌 → 𝕌
    _×ᵤ_ : 𝕌 → 𝕌 → 𝕌
    𝟙/_ : (t : 𝕌) → 𝕌
    -- ●_[_] : (t : 𝕌) → ⟦ t ⟧ → 𝕌
    -- 𝟙/●_[_] : (t : 𝕌) → ⟦ t ⟧ → 𝕌

  ⟦_⟧ : 𝕌 → Set
  ⟦ 𝟘 ⟧ = ⊥
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ 𝟙/ t ⟧ = ◯
  --  ⟦ ● t [ v ] ⟧ = ⟦ t ⟧ -- Singleton ⟦ t ⟧ v 
  --  ⟦ 𝟙/● t [ v ] ⟧ = ◯
      -- all information is in the type, so the value is just a token

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
    _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ↔ t₂) → (t₂ ↔ t₃) → (t₁ ↔ t₃)
    _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ +ᵤ t₂ ↔ t₃ +ᵤ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ ×ᵤ t₂ ↔ t₃ ×ᵤ t₄)
    η : {t : 𝕌} {v : ⟦ t ⟧} → 𝟙 ↔ t ×ᵤ (𝟙/ t)
    ε : {t : 𝕌} {v : ⟦ t ⟧} → t ×ᵤ (𝟙/ t) ↔ 𝟙
    --    η : {t : 𝕌} {v : ⟦ t ⟧} → 𝟙 ↔ ● t [ v ] ×ᵤ 𝟙/● t [ v ]
    --    ε : {t : 𝕌} {v : ⟦ t ⟧} → ● t [ v ] ×ᵤ 𝟙/● t [ v ] ↔ 𝟙
    --    ext : {t : 𝕌} {v : ⟦ t ⟧} → ● t [ v ] ↔ t
    --    ret : {t : 𝕌} {v : ⟦ t ⟧} → t ↔ ● t [ v ]

{--
𝕌dec : (t : 𝕌) → Decidable (_≡_ {A = ⟦ t ⟧})
𝕌dec 𝟘 ()
𝕌dec 𝟙 tt tt = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ y) with 𝕌dec t₁ x y
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ .x) | yes refl = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ y)  | no ¬p = no (λ {refl → ¬p refl})
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₂ y) = no (λ ())
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₁ y) = no (λ ())
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ y) with 𝕌dec t₂ x y
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ .x) | yes refl = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ y) | no ¬p = no (λ {refl → ¬p refl})
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , y₂) with 𝕌dec t₁ x₁ x₂ | 𝕌dec t₂ y₁ y₂
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (.x₁ , .y₁) | yes refl | yes refl = yes refl
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (.x₁ , y₂) | yes refl | no ¬p = no (λ p → ¬p (cong proj₂ p))
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , .y₁) | no ¬p | yes refl = no (λ p → ¬p (cong proj₁ p))
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , y₂) | no ¬p | no ¬p₁ = no (λ p → ¬p (cong proj₁ p))
-- 𝕌dec ● t [ v ] (⇑ .v refl) (⇑ .v refl) = yes refl
-- 𝕌dec ● t [ v ] x y = yes pointed-all-paths
𝕌dec ● t [ v ] x y = {!!} -- 
𝕌dec 𝟙/● t [ v ] ○ ○ = yes refl
--}

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
interp (c₁ ⊚ c₂) v = interp c₂ (interp c₁ v)
interp (c₁ ⊕ c₂) (inj₁ v) = inj₁ (interp c₁ v)
interp (c₁ ⊕ c₂) (inj₂ v) = inj₂ (interp c₂ v)
interp (c₁ ⊗ c₂) (v₁ , v₂) = interp c₁ v₁ , interp c₂ v₂
interp (η {t} {v}) tt = v , ○ 
interp (ε {t} {v}) (v' , ○) = tt -- if v ≡ v' then tt else throw Error
-- interp (η {t} {v}) tt = (v , refl) , ○ 
-- interp ext (v , refl) = v
-- interp ext v = v
-- interp (ret {t} {v}) x with 𝕌dec t x v
-- interp (ret {_} {.x}) x | yes refl = x , refl 
-- interp (ret {_} {.x}) x | yes refl = x
-- interp (ret {_} {v}) x | no ¬p = {!!} 
   -- we are expecting v, seeing x which is not v
-- interp (ret {t} {v}) x = x 
  
𝟚 : 𝕌
𝟚 = 𝟙 +ᵤ 𝟙

𝔽 𝕋 : ⟦ 𝟚 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt


--   ─────┬────⊕───  ───────
--        |    |   ⨉
--     ┌──⊕────┴───  ───┐
--     └────────────────┘
id' : 𝟚 ↔ 𝟚
{--
id' = uniti⋆r ⊚ (id↔ ⊗ η {v = 𝔽}) ⊚ assocl⋆ ⊚
      (((id↔ ⊗ ext) ⊚ xorr ⊚ xorl ⊚ swap⋆ ⊚ (id↔ ⊗ ret)) ⊗ id↔) ⊚
      assocr⋆ ⊚ (id↔ ⊗ ε {v = 𝔽}) ⊚ unite⋆r
      where
      xorr xorl : 𝟚 ×ᵤ 𝟚 ↔ 𝟚 ×ᵤ 𝟚
      xorr = dist ⊚ (id↔ ⊕ (id↔ ⊗ swap₊)) ⊚ factor
      xorl = distl ⊚ (id↔ ⊕ (swap₊ ⊗ id↔)) ⊚ factorl
--}
id' = uniti⋆r ⊚ (id↔ ⊗ η {v = 𝔽}) ⊚ assocl⋆ ⊚
      ((xorr ⊚ xorl ⊚ swap⋆) ⊗ id↔) ⊚
      assocr⋆ ⊚ (id↔ ⊗ ε {v = 𝔽}) ⊚ unite⋆r
      where
      xorr xorl : 𝟚 ×ᵤ 𝟚 ↔ 𝟚 ×ᵤ 𝟚
      xorr = dist ⊚ (id↔ ⊕ (id↔ ⊗ swap₊)) ⊚ factor
      xorl = distl ⊚ (id↔ ⊕ (swap₊ ⊗ id↔)) ⊚ factorl

ex1 : interp id' 𝕋 ≡ 𝕋
ex1 = refl

ex2 : interp id' 𝔽 ≡ 𝔽
ex2 = refl


--     ┌──────  ───────┐
--     └──────╲╱───────┘
--            ╱╲
--     ┌─────    ──────┐
--     └───────────────┘
switch : 𝟙 ↔ 𝟙
switch = uniti⋆r ⊚ (η {v = 𝔽} ⊗ η {v = 𝔽}) ⊚ assocl⋆ ⊚
         (((swap⋆ ⊗ id↔) ⊚ assocr⋆ ⊚ (id↔ ⊗ swap⋆) ⊚ assocl⋆ ⊚ (swap⋆ ⊗ id↔)) ⊗ id↔)
         ⊚ assocr⋆ ⊚ (ε {v = 𝔽} ⊗ ε {v = 𝔽}) ⊚ unite⋆r
