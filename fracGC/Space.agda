{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Space where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _⊔_ to _ℕ⊔_)
open import Data.Nat.Properties
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣; _+_; _⊔_; -_)
open import Data.Rational
  using (ℚ)
  renaming (1/_ to recip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to R[_])
  using (_≡_; refl; sym; trans; cong; inspect)

open import Pointed
open import PiFrac

------------------------------------------------------------------------------
-- Space denotational semantics

-- for each type, we calculate its memory requirements which are two
-- numbers (m , z). The number m represents the amount of space needed
-- to store values of the type. The number z represents the effect of
-- the value on space when it is interpreted. Ex. a gc process needs m
-- bits to be stored but when run it releases z bits.

-- Number of points in type
card : (t : 𝕌) → ℕ
card 𝟘 = 0
card 𝟙 = 1
card (t₁ +ᵤ t₂) = card t₁ ℕ+ card t₂
card (t₁ ×ᵤ t₂) = card t₁ ℕ* card t₂
card ● t [ v ] = 1
card 𝟙/● t [ v ] = 1

-- If number of points is zero then it is impossible to find a value
-- of the type
0empty : {t : 𝕌} → card t ≡ 0 → (v : ⟦ t ⟧) → ⊥
0empty {𝟘} _ ()
0empty {𝟙} () tt
0empty {t₁ +ᵤ t₂} s (inj₁ v₁)
  with card t₁ | card t₂ | inspect card t₁
0empty {t₁ +ᵤ t₂} refl (inj₁ v₁) | ℕ.zero | ℕ.zero | R[ s₁ ] =
  0empty {t₁} s₁ v₁
0empty {t₁ +ᵤ t₂} s (inj₂ v₂)
  with card t₁ | card t₂ | inspect card t₂
0empty {t₁ +ᵤ t₂} refl (inj₂ v₂) | ℕ.zero | ℕ.zero | R[ s₂ ] =
  0empty {t₂} s₂ v₂
0empty {t₁ ×ᵤ t₂} s (v₁ , v₂)
  with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
0empty {t₁ ×ᵤ t₂} refl (v₁ , v₂) | ℕ.zero | _ | R[ s₁ ] | _ =
  0empty {t₁} s₁ v₁
0empty {t₁ ×ᵤ t₂} s (v₁ , v₂) | ℕ.suc n₁ | ℕ.zero | R[ s₁ ] | R[ s₂ ] =
  0empty {t₂} s₂ v₂
0empty {● t [ v ]} () (⇑ .v refl)
0empty {𝟙/● t [ v ]} () f

-- Space effects 

-- For a pointed type, even though we only have one value, that value
-- could be large and we need just as much space to store it as we
-- would need for any value of the given type. For a fractional type,
-- the effect is to de-allocate the space above.

space : (t : 𝕌) → {¬t≡0 : ¬ card t ≡ 0} → ℤ
space 𝟘 {0ne} = ⊥-elim (0ne refl)
space 𝟙 = + 0 
space (t₁ +ᵤ t₂) {pne} with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (pne refl) 
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] =
  space t₂ {λ t2≡0 → ⊥-elim (pne (trans (sym s₂) t2≡0))}
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] =
  space t₁
    {λ t1≡0 →
      ⊥-elim (pne (trans (sym (trans s₁ (sym (+-identityʳ (suc m))))) t1≡0))}
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] =
  + 1 + (space t₁ {λ t1≡0 → ⊥-elim (1+n≢0 (trans (sym s₁) t1≡0))} ⊔
         space t₂ {λ t2≡0 → ⊥-elim ((1+n≢0 (trans (sym s₂) t2≡0)))})
space (t₁ ×ᵤ t₂) {pne} with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (pne refl) 
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] = ⊥-elim (pne refl) 
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (pne (*-zeroʳ (suc m)))
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] =
  space t₁ {λ t1≡0 → ⊥-elim (1+n≢0 (trans (sym s₁) t1≡0))} +
  space t₂ {λ t2≡0 → ⊥-elim (1+n≢0 (trans (sym s₂) t2≡0))}
space ● t [ v ]   = space t {λ t≡0 → 0empty t≡0 v} 
space 𝟙/● t [ v ] = - space t {λ t≡0 → 0empty t≡0 v}  

-- TODO

-- Every combinator preserves space effects

space= : (t₁ t₂ : 𝕌) (C : t₁ ⟷ t₂) → ¬ (card t₁ ≡ 0) → (card t₁ ≡ card t₂)
space= .(𝟘 +ᵤ t₂) t₂ unite₊l neq = refl
space= t₁ .(𝟘 +ᵤ t₁) uniti₊l neq = refl
space= .(t₂ +ᵤ 𝟘) t₂ unite₊r neq rewrite +-identityʳ (card t₂) = refl
space= t₁ .(t₁ +ᵤ 𝟘) uniti₊r neq rewrite +-identityʳ (card t₁) = refl
space= (t₁ +ᵤ t₂) _ swap₊ neq rewrite +-comm (card t₁) (card t₂) = refl
space= (t₁ +ᵤ t₂ +ᵤ t₃) _ assocl₊ neq rewrite +-assoc (card t₁) (card t₂) (card t₃) = refl
space= ((t₁ +ᵤ t₂) +ᵤ t₃) _ assocr₊ neq rewrite +-assoc (card t₁) (card t₂) (card t₃) = refl
space= (𝟙 ×ᵤ t₂) t₂ unite⋆l neq rewrite +-identityʳ (card t₂) = refl
space= t₁ (𝟙 ×ᵤ t₁) uniti⋆l neq rewrite +-identityʳ (card t₁) = refl
space= (t₂ ×ᵤ 𝟙) t₂ unite⋆r neq rewrite *-identityʳ (card t₂) = refl
space= t₁ (t₁ ×ᵤ 𝟙) uniti⋆r neq rewrite *-identityʳ (card t₁) = refl
space= (t₁ ×ᵤ t₂) _ swap⋆ neq rewrite *-comm (card t₁) (card t₂) = refl
space= (t₁ ×ᵤ t₂ ×ᵤ t₃) _ assocl⋆ neq rewrite *-assoc (card t₁) (card t₂) (card t₃) = refl
space= ((t₁ ×ᵤ t₂) ×ᵤ t₃) _ assocr⋆ neq rewrite *-assoc (card t₁) (card t₂) (card t₃) = refl
space= .(𝟘 ×ᵤ _) .𝟘 absorbr neq = refl
space= (t ×ᵤ 𝟘) .𝟘 absorbl neq rewrite *-zeroʳ (card t) = refl
space= .𝟘 (t ×ᵤ 𝟘) factorzr neq rewrite *-zeroʳ (card t) = refl
space= .𝟘 .(𝟘 ×ᵤ _) factorzl neq = refl
space= ((t₁ +ᵤ t₂) ×ᵤ t₃) _ dist neq rewrite *-distribʳ-+ (card t₃) (card t₁) (card t₂) = refl
space= _ ((t₁ +ᵤ t₂) ×ᵤ t₃) factor neq rewrite *-distribʳ-+ (card t₃) (card t₁) (card t₂) = refl
space= (t₃ ×ᵤ (t₁ +ᵤ t₂)) _ distl neq rewrite *-distribˡ-+ (card t₃) (card t₁) (card t₂) = refl
space= _ (t₃ ×ᵤ (t₁ +ᵤ t₂)) factorl neq rewrite *-distribˡ-+ (card t₃) (card t₁) (card t₂) = refl
space= t₁ .t₁ id⟷ neq = refl
space= t₁ t₂ (c₁ ⊚ c₂) neq rewrite space= _ _ c₁ neq = space= _ _ c₂ (λ {p → neq (trans (space= _ _ c₁ neq) p)})
space= (t₁ +ᵤ t₂) (t₃ +ᵤ t₄) (c₁ ⊕ c₂) neq = {!!}
space= (t₁ ×ᵤ t₂) (t₃ ×ᵤ t₄) (c₁ ⊗ c₂) neq = {!!}
space= .(● _ [ _ ]) .(● _ [ eval c _ ]) (lift c) neq = refl
space= .(● _ ×ᵤ _ [ _ , _ ]) .(● _ [ _ ] ×ᵤ ● _ [ _ ]) tensorl neq = refl
space= .(● _ [ _ ] ×ᵤ ● _ [ _ ]) .(● _ ×ᵤ _ [ _ , _ ]) tensorr neq = refl
space= .(● _ +ᵤ _ [ inj₁ _ ]) .(● _ [ _ ]) plusl neq = refl
space= .(● _ +ᵤ _ [ inj₂ _ ]) .(● _ [ _ ]) plusr neq = refl
space= .𝟙 .(● _ [ v ] ×ᵤ 𝟙/● _ [ v ]) (η v) neq = refl
space= .(● _ [ v ] ×ᵤ 𝟙/● _ [ v ]) .𝟙 (ε v) neq = refl
space= .(● _ [ _ ]) .(● _ [ _ ]) (== c x) neq = refl

-- Groupoid interpretation ???? Groupoid for pointed 1/A is point and
-- (size A) loops on point labeled (= a1), (= a2), (= a3), etc.

------------------------------------------------------------------------------
