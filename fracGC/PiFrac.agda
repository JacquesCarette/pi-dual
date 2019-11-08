{-# OPTIONS --without-K --safe #-}

-- Definition of Pi with fractionals

module PiFrac where

-- From the standard library:
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

-- The basic types we add:
open import Singleton

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_

------------------------------------------------------------------------------
-- Pi with fractionals

-- The following are all mutually dependent:

data 𝕌 : Set                               -- 𝕌niverse of types
⟦_⟧ : (A : 𝕌) → Set                        -- denotation of types
data _⟷_ : 𝕌 → 𝕌 → Set                     -- type equivalences
eval : {A B : 𝕌} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧ -- evaluating an equivalence

data 𝕌 where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌
  ●_[_]   : (A : 𝕌) → ⟦ A ⟧ → 𝕌
  𝟙/●_[_] : (A : 𝕌) → ⟦ A ⟧ → 𝕌

⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ ● A [ v ] ⟧ = Singleton ⟦ A ⟧ v
⟦ 𝟙/● A [ v ] ⟧ = Recip ⟦ A ⟧ v

data _⟷_ where
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
  -- new operations on Singleton
  lift : {t₁ t₂ : 𝕌} → {v₁ : ⟦ t₁ ⟧} →
           (c : t₁ ⟷ t₂) →
           (● t₁ [ v₁ ] ⟷ ● t₂ [ eval c v₁ ])
  tensorl : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            ● t₁ ×ᵤ t₂ [ v₁ , v₂ ] ⟷ ● t₁ [ v₁ ] ×ᵤ ● t₂ [ v₂ ]
  tensorr : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            ● t₁ [ v₁ ] ×ᵤ ● t₂ [ v₂ ] ⟷ ● t₁ ×ᵤ t₂ [ v₁ , v₂ ]
  plusll : {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} →
            ● (t₁ +ᵤ t₂) [ inj₁ v ] ⟷ ● t₁ [ v ]
  pluslr : {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} →
             ● t₁ [ v ] ⟷ ● (t₁ +ᵤ t₂) [ inj₁ v ]
  plusrl : {t₁ t₂ : 𝕌} {v : ⟦ t₂ ⟧} →
            ● (t₁ +ᵤ t₂) [ inj₂ v ] ⟷ ● t₂ [ v ]
  plusrr : {t₁ t₂ : 𝕌} {v : ⟦ t₂ ⟧} →
             ● t₂ [ v ] ⟷ ● (t₁ +ᵤ t₂) [ inj₂ v ]
  fracl : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            𝟙/● t₁ ×ᵤ t₂ [ v₁ , v₂ ] ⟷ 𝟙/● t₁ [ v₁ ] ×ᵤ 𝟙/● t₂ [ v₂ ]
  fracr : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            𝟙/● t₁ [ v₁ ] ×ᵤ 𝟙/● t₂ [ v₂ ] ⟷ 𝟙/● t₁ ×ᵤ t₂ [ v₁ , v₂ ]
  -- fractionals
  η : {t : 𝕌} → (v : ⟦ t ⟧) → 𝟙 ⟷ ● t [ v ] ×ᵤ 𝟙/● t [ v ]
  ε : {t : 𝕌} → (v : ⟦ t ⟧) → ● t [ v ] ×ᵤ 𝟙/● t [ v ] ⟷ 𝟙
  -- prop eq
  == : ∀ {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} {w w' : ⟦ t₂ ⟧} →
       (● t₁ [ v ] ⟷ ● t₂ [ w ]) → (w ≡ w') → (● t₁ [ v ] ⟷ ● t₂ [ w' ])


eval unite₊l (inj₂ v) = v
eval uniti₊l v  = inj₂ v
eval unite₊r (inj₁ v) = v
eval uniti₊r v  = inj₁ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆l (tt , v) = v
eval uniti⋆l v = (tt , v)
eval unite⋆r (v , tt) = v
eval uniti⋆r v = (v , tt)
eval swap⋆ (v₁ , v₂)          = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbl ()
eval absorbr ()
eval factorzl ()
eval factorzr ()
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval distl (v , inj₁ v₁) = inj₁ (v , v₁)
eval distl (v , inj₂ v₂) = inj₂ (v , v₂)
eval factorl (inj₁ (v , v₁)) = (v , inj₁ v₁)
eval factorl (inj₂ (v , v₂)) = (v , inj₂ v₂)
eval id⟷ v = v
eval (c₁ ⊚ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)
eval (lift c) (w , v≡w) = eval c w , cong (eval c) v≡w 
eval tensorl ((w₁ , w₂) , vp≡wp) =
  (w₁ , cong proj₁ vp≡wp) , (w₂ , cong proj₂ vp≡wp)
eval tensorr ((w₁ , p₁) , (w₂ , p₂)) =
  (w₁ , w₂) , cong₂ _,_ p₁ p₂ 
eval (η v) tt = (v , refl) , λ _ → tt 
eval (ε v) (p , f) = f p
eval (plusll {v = .w₁}) (inj₁ w₁ , refl) = w₁ , refl 
eval pluslr (v₁ , refl) = inj₁ v₁ , refl
eval (plusrl {v = .w₂}) (inj₂ w₂ , refl) = w₂ , refl
eval plusrr (v₂ , refl) = inj₂ v₂ , refl
eval (fracl {v₁ = v₁} {v₂ = v₂}) f = (λ _ → f ((v₁ , v₂) , refl)) , (λ _ → f ((v₁ , v₂) , refl))
eval fracr (f₁ , f₂) ((w₁ , w₂) , refl) = let _ = f₁ (w₁ , refl) ; _ = f₂ (w₂ , refl) in tt
eval (== c eq) s₁ = let (w₂ , p) = eval c s₁ in w₂ , trans (sym eq) p 


focus : {t : 𝕌} → (v : ⟦ t ⟧) → Singleton ⟦ t ⟧ v
focus v = (v , refl)

unfocus : {t : 𝕌} {v : ⟦ t ⟧} → Singleton ⟦ t ⟧ v → ⟦ t ⟧
unfocus (v , refl) = v

------------------------------------------------------------------------------
