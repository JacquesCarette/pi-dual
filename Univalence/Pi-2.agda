module Pi-2 where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Level -2
-- Types are -2 groupoids or equivalently all types are contractible

mutual

  data U : Set where
    ONE   : U
    TIMES : U → U → U
    PATH  : {t : U} → ⟦ t ⟧ → ⟦ t ⟧ → U

  ⟦_⟧ : U → Set
  ⟦ ONE ⟧         = ⊤
  ⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ PATH v₁ v₂ ⟧  = (v₁ ≡ v₂)

-- Proof that all types are contractible. Def. 3.11.1 in the HoTT book

isContr : (t : U) → Σ[ v ∈ ⟦ t ⟧ ] ((v' : ⟦ t ⟧) → (v ≡ v'))
isContr ONE = (tt , λ v → refl)
isContr (TIMES t₁ t₂) with isContr t₁ | isContr t₂ 
... | (v₁ , f₁) | (v₂ , f₂) = ((v₁ , v₂) , f) 
  where f : (vv : ⟦ t₁ ⟧ × ⟦ t₂ ⟧) → (v₁ , v₂) ≡ vv
        f (v₁' , v₂') = cong₂ _,′_ (f₁ v₁') (f₂ v₂') 
isContr (PATH {t} v₁ v₂) with isContr t
isContr (PATH {t} v₁ v₂) | (v' , f') = 
  (trans (sym (f' v₁))  (f' v₂) , 
  λ p → proof-irrelevance (trans (sym (f' v₁))  (f' v₂)) p)

------------------------------------------------------------------------------
