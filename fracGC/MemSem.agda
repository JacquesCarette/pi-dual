{-# OPTIONS --without-K --safe #-}

module MemSem where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; inject+; raise)
open import Data.Vec
open import Data.Vec.Properties
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_
infix  80 ∣_∣

data 𝕌 : Set where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌

⟦_⟧ : (A : 𝕌) → Set
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

data _⟷_ : 𝕌 → 𝕌 → Set where
  unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ⟷ t
  uniti₊l : {t : 𝕌} → t ⟷ 𝟘 +ᵤ t
  unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ⟷ t
  uniti₊r : {t : 𝕌} → t ⟷ t +ᵤ 𝟘
  swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ⟷ t₂ +ᵤ t₁
  assocl₊ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ +ᵤ t₂) +ᵤ t₃
  assocr₊ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ⟷ t₁ +ᵤ (t₂ +ᵤ t₃)
  unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ⟷ t
  uniti⋆l : {t : 𝕌} → t ⟷ 𝟙 ×ᵤ t
  unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ⟷ t
  uniti⋆r : {t : 𝕌} → t ⟷ t ×ᵤ 𝟙
  swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ⟷ t₂ ×ᵤ t₁
  assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  absorbr : {t : 𝕌} → 𝟘 ×ᵤ t ⟷ 𝟘
  absorbl : {t : 𝕌} → t ×ᵤ 𝟘 ⟷ 𝟘
  factorzr : {t : 𝕌} → 𝟘 ⟷ t ×ᵤ 𝟘
  factorzl : {t : 𝕌} → 𝟘 ⟷ 𝟘 ×ᵤ t
  dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
  factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤ t₃)
  id⟷     : {t : 𝕌} → t ⟷ t
  _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)

∣_∣ : (A : 𝕌) → ℕ
∣ 𝟘 ∣ = 0
∣ 𝟙 ∣ = 1
∣ A₁ +ᵤ A₂ ∣ = ∣ A₁ ∣ + ∣ A₂ ∣
∣ A₁ ×ᵤ A₂ ∣ = ∣ A₁ ∣ * ∣ A₂ ∣

Enum : (A : 𝕌) → Vec ⟦ A ⟧ ∣ A ∣
Enum 𝟘 = []
Enum 𝟙 = tt ∷ []
Enum (A₁ +ᵤ A₂) = map inj₁ (Enum A₁) ++ map inj₂ (Enum A₂)
Enum (A₁ ×ᵤ A₂) = concat (map (λ a₁ → map (a₁ ,_) (Enum A₂)) (Enum A₁))

Find : {A : 𝕌} (x : ⟦ A ⟧) → Σ[ i ∈ Fin ∣ A ∣ ] (x ≡ lookup (Enum A) i)
Find {𝟘} ()
Find {𝟙} tt = zero , refl
Find {A₁ +ᵤ A₂} (inj₁ x) with Find x
Find {A₁ +ᵤ A₂} (inj₁ .(lookup (Enum A₁) i)) | i , refl = inject+ ∣ A₂ ∣ i
                                                      , sym (trans (lookup-++ˡ (map inj₁ (Enum A₁)) (map inj₂ (Enum A₂)) i)
                                                                   (lookup-map i inj₁ (Enum A₁)))
Find {A₁ +ᵤ A₂} (inj₂ y) with Find y
Find {A₁ +ᵤ A₂} (inj₂ .(lookup (Enum A₂) i)) | i , refl = raise ∣ A₁ ∣ i
                                                      , sym (trans (lookup-++ʳ (map inj₁ (Enum A₁)) (map inj₂ (Enum A₂)) i)
                                                                   (lookup-map i inj₂ (Enum A₂)))
Find {A₁ ×ᵤ A₂} (x , y) with Find x
... | i , p = {!!}

card= : (t₁ t₂ : 𝕌) (C : t₁ ⟷ t₂) → (∣ t₁ ∣ ≡ ∣ t₂ ∣)
card= .(𝟘 +ᵤ t₂) t₂ unite₊l = refl
card= t₁ .(𝟘 +ᵤ t₁) uniti₊l = refl
card= .(t₂ +ᵤ 𝟘) t₂ unite₊r rewrite +-identityʳ ∣ t₂ ∣ = refl
card= t₁ .(t₁ +ᵤ 𝟘) uniti₊r rewrite +-identityʳ ∣ t₁ ∣ = refl
card= (t₁ +ᵤ t₂) _ swap₊ rewrite +-comm ∣ t₁ ∣ ∣ t₂ ∣ = refl
card= (t₁ +ᵤ t₂ +ᵤ t₃) _ assocl₊ rewrite +-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= ((t₁ +ᵤ t₂) +ᵤ t₃) _ assocr₊  rewrite +-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= (𝟙 ×ᵤ t₂) t₂ unite⋆l  rewrite +-identityʳ ∣ t₂ ∣ = refl
card= t₁ (𝟙 ×ᵤ t₁) uniti⋆l  rewrite +-identityʳ ∣ t₁ ∣ = refl
card= (t₂ ×ᵤ 𝟙) t₂ unite⋆r  rewrite *-identityʳ ∣ t₂ ∣ = refl
card= t₁ (t₁ ×ᵤ 𝟙) uniti⋆r  rewrite *-identityʳ ∣ t₁ ∣ = refl
card= (t₁ ×ᵤ t₂) _ swap⋆  rewrite *-comm ∣ t₁ ∣ ∣ t₂ ∣ = refl
card= (t₁ ×ᵤ t₂ ×ᵤ t₃) _ assocl⋆  rewrite *-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= ((t₁ ×ᵤ t₂) ×ᵤ t₃) _ assocr⋆  rewrite *-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= .(𝟘 ×ᵤ _) .𝟘 absorbr  = refl
card= (t ×ᵤ 𝟘) .𝟘 absorbl  rewrite *-zeroʳ ∣ t ∣ = refl
card= .𝟘 (t ×ᵤ 𝟘) factorzr  rewrite *-zeroʳ ∣ t ∣ = refl
card= .𝟘 .(𝟘 ×ᵤ _) factorzl  = refl
card= ((t₁ +ᵤ t₂) ×ᵤ t₃) _ dist  rewrite *-distribʳ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= _ ((t₁ +ᵤ t₂) ×ᵤ t₃) factor  rewrite *-distribʳ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= (t₃ ×ᵤ (t₁ +ᵤ t₂)) _ distl  rewrite *-distribˡ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= _ (t₃ ×ᵤ (t₁ +ᵤ t₂)) factorl  rewrite *-distribˡ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= t₁ .t₁ id⟷  = refl
card= t₁ t₂ (c₁ ⊚ c₂)  rewrite card= _ _ c₁ | card= _ _ c₂ = refl
card= (t₁ +ᵤ t₂) (t₃ +ᵤ t₄) (c₁ ⊕ c₂) rewrite card= _ _ c₁ | card= _ _ c₂ = refl
card= (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄) (c₁ ⊗ c₂) rewrite card= _ _ c₁ | card= _ _ c₂ = refl

data State : ℕ → Set where
  _∥_∥_ : {A B : 𝕌} → A ⟷ B → Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State ∣ A ∣

step :  ∀ {n} → State n → State n
step (unite₊l {t} ∥ va ∥ i) with lookup va i
... | inj₂ y = id⟷ ∥ Enum t ∥ proj₁ (Find {t} y)
step (uniti₊l {t} ∥ va ∥ i) with lookup va i
... | y = id⟷ ∥ Enum (𝟘 +ᵤ t) ∥ proj₁ (Find {𝟘 +ᵤ t} (inj₂ y))
step (unite₊r {t} ∥ va ∥ i) rewrite +-identityʳ ∣ t ∣ with lookup va i
... | inj₁ x = id⟷ ∥ Enum t ∥ proj₁ (Find {t} x)
step (uniti₊r {t} ∥ va ∥ i) rewrite sym (+-identityʳ ∣ t ∣) with lookup va i
... | x = id⟷ ∥ Enum (t +ᵤ 𝟘) ∥ proj₁ (Find {t +ᵤ 𝟘} (inj₁ x))
step (swap₊ {t₁} {t₂} ∥ va ∥ i) rewrite +-comm ∣ t₁ ∣ ∣ t₂ ∣ with lookup va i
... | inj₁ x = id⟷ ∥ Enum (t₂ +ᵤ t₁) ∥ proj₁ (Find {t₂ +ᵤ t₁} (inj₂ x))
... | inj₂ y = id⟷ ∥ Enum (t₂ +ᵤ t₁) ∥ proj₁ (Find {t₂ +ᵤ t₁} (inj₁ y))
step (assocl₊ {t₁} {t₂} {t₃} ∥ va ∥ i) rewrite sym (+-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣)) with lookup va i
... | inj₁ x = id⟷ ∥ Enum ((t₁ +ᵤ t₂) +ᵤ t₃) ∥ proj₁ (Find {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₁ (inj₁ x)))
... | inj₂ (inj₁ y) = id⟷ ∥ Enum ((t₁ +ᵤ t₂) +ᵤ t₃) ∥ proj₁ (Find {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₁ (inj₂ y)))
... | inj₂ (inj₂ z) = id⟷ ∥ Enum ((t₁ +ᵤ t₂) +ᵤ t₃) ∥ proj₁ (Find {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₂ z))
step (assocr₊ {t₁} {t₂} {t₃} ∥ va ∥ i) rewrite +-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = {!!}
step (unite⋆l ∥ va ∥ i) = {!!}
step (uniti⋆l ∥ va ∥ i) = {!!}
step (unite⋆r ∥ va ∥ i) = {!!}
step (uniti⋆r ∥ va ∥ i) = {!!}
step (swap⋆ ∥ va ∥ i) = {!!}
step (assocl⋆ ∥ va ∥ i) = {!!}
step (assocr⋆ ∥ va ∥ i) = {!!}
step (absorbl ∥ va ∥ i) = {!!}
step (dist ∥ va ∥ i) = {!!}
step (factor ∥ va ∥ i) = {!!}
step (distl ∥ va ∥ i) = {!!}
step (factorl ∥ va ∥ i) = {!!}
step (id⟷ ∥ va ∥ i) = {!!}
step ((c₁ ⊚ c₂) ∥ va ∥ i) = {!!}
step ((c₁ ⊕ c₂) ∥ va ∥ i) = {!!}
step ((c₁ ⊗ c₂) ∥ va ∥ i) = {!!}
