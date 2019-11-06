{-# OPTIONS --without-K --safe #-}

-- Backwards evaluator and the fact that with eval, forms a reversible evaluator

module BackwardsEval where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Singleton
open import PiFrac

bwd : {A B : 𝕌} → (A ⟷ B) → ⟦ B ⟧ → ⟦ A ⟧
bwd-eval : {A B : 𝕌} → (c : A ⟷ B) → (v : ⟦ A ⟧) → bwd c (eval c v) ≡ v

bwd unite₊l v = inj₂ v
bwd uniti₊l (inj₂ v) = v
bwd unite₊r v = inj₁ v
bwd uniti₊r (inj₁ v) = v
bwd swap₊ (inj₁ v) = inj₂ v
bwd swap₊ (inj₂ v) = inj₁ v
bwd assocl₊ (inj₁ (inj₁ v)) = inj₁ v
bwd assocl₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
bwd assocl₊ (inj₂ v) = inj₂ (inj₂ v)
bwd assocr₊ (inj₁ v) = inj₁ (inj₁ v)
bwd assocr₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
bwd assocr₊ (inj₂ (inj₂ v)) = inj₂ v
bwd unite⋆l v = (tt , v)
bwd uniti⋆l (tt , v) = v
bwd unite⋆r v = (v , tt)
bwd uniti⋆r (v , tt) = v
bwd swap⋆ (v₁ , v₂) = (v₂ , v₁)
bwd assocl⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
bwd assocr⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
bwd dist (inj₁ (v₁ , v₂)) = (inj₁ v₁ , v₂)
bwd dist (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
bwd factor (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
bwd factor (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
bwd distl (inj₁ (v₁ , v₂)) = (v₁ , inj₁ v₂)
bwd distl (inj₂ (v₁ , v₃)) = (v₁ , inj₂ v₃)
bwd factorl (v₁ , inj₁ v₂) = inj₁ (v₁ , v₂)
bwd factorl (v₁ , inj₂ v₃) = inj₂ (v₁ , v₃)
bwd id⟷ v = v
bwd (c₁ ⊚ c₂) v = bwd c₁ (bwd c₂ v)
bwd (c₁ ⊕ c₂) (inj₁ v) = inj₁ (bwd c₁ v)
bwd (c₁ ⊕ c₂) (inj₂ v) = inj₂ (bwd c₂ v)
bwd (c₁ ⊗ c₂) (v₁ , v₂) = (bwd c₁ v₁ , bwd c₂ v₂)
bwd (lift {_} {_} {v₁} c) (●₁ , v≡●₁) = (bwd c ●₁) , (trans (sym (bwd-eval c v₁)) (cong (bwd c) v≡●₁))
bwd tensorl ((w₁ , p₁) , (w₂ , p₂)) = (w₁ ,  w₂) , (cong₂ _,_ p₁ p₂)
bwd tensorr ((v₁ , v₂) , p) = (v₁ , cong proj₁ p) , (v₂ , cong proj₂ p)
bwd plusl (w , p) = (inj₁ w) , (cong inj₁ p)
bwd plusr (w , p) = (inj₂ w) , (cong inj₂ p)
bwd (η v) p = tt
bwd (ε v) tt = (v , refl) , λ _ → tt
bwd (== c eq) v = bwd c (subst (Singleton ⟦ _ ⟧) (sym eq) v)
bwd (focus v) (.v , refl) = tt
bwd unfocus v = v , {!!} 

bwd-eval unite₊l (inj₂ v) = refl
bwd-eval uniti₊l v = refl
bwd-eval unite₊r (inj₁ v) = refl
bwd-eval uniti₊r v = refl
bwd-eval swap₊ (inj₁ v) = refl
bwd-eval swap₊ (inj₂ v) = refl
bwd-eval assocl₊ (inj₁ v) = refl
bwd-eval assocl₊ (inj₂ (inj₁ v)) = refl
bwd-eval assocl₊ (inj₂ (inj₂ v)) = refl
bwd-eval assocr₊ (inj₁ (inj₁ v)) = refl
bwd-eval assocr₊ (inj₁ (inj₂ v)) = refl
bwd-eval assocr₊ (inj₂ v) = refl
bwd-eval unite⋆l (tt , v) = refl
bwd-eval uniti⋆l v = refl
bwd-eval unite⋆r (v , tt) = refl
bwd-eval uniti⋆r v = refl
bwd-eval swap⋆ (v₁ , v₂) = refl
bwd-eval assocl⋆ (v₁ , (v₂ , v₃)) = refl
bwd-eval assocr⋆ ((v₁ , v₂) , v₃) = refl
bwd-eval dist (inj₁ v₁ , v₃) = refl
bwd-eval dist (inj₂ v₂ , v₃) = refl
bwd-eval factor (inj₁ (v₁ , v₃)) = refl
bwd-eval factor (inj₂ (v₂ , v₃)) = refl
bwd-eval distl (v₁ , inj₁ v₂) = refl
bwd-eval distl (v₁ , inj₂ v₃) = refl
bwd-eval factorl (inj₁ (v₁ , v₂)) = refl
bwd-eval factorl (inj₂ (v₁ , v₃)) = refl
bwd-eval id⟷ v = refl
bwd-eval (c₁ ⊚ c₂) v = trans (cong (bwd c₁) (bwd-eval c₂ (eval c₁ v))) (bwd-eval c₁ v)
bwd-eval (c₁ ⊕ c₂) (inj₁ v₁) = cong inj₁ (bwd-eval c₁ v₁)
bwd-eval (c₁ ⊕ c₂) (inj₂ v₂) = cong inj₂ (bwd-eval c₂ v₂)
bwd-eval (c₁ ⊗ c₂) (v₁ , v₂) = cong₂ _,_ (bwd-eval c₁ v₁) (bwd-eval c₂ v₂)
bwd-eval (lift c) v = pointed-all-paths
bwd-eval tensorl p = pointed-all-paths
bwd-eval tensorr (p₁ , p₂) = cong₂ _,_ pointed-all-paths pointed-all-paths
bwd-eval plusl p = pointed-all-paths
bwd-eval plusr p = pointed-all-paths
bwd-eval (η v) tt = refl
bwd-eval (ε v) (p , r) = cong₂ _,_ pointed-all-paths refl
bwd-eval (== c eq) p = pointed-all-paths
bwd-eval (focus v) tt = {!!}
bwd-eval unfocus (v , refl) = {!!} 

eval-bwd : {A B : 𝕌} → (c : A ⟷ B) → (v : ⟦ B ⟧) → eval c (bwd c v) ≡ v
eval-bwd unite₊l v = refl
eval-bwd uniti₊l (inj₂ v) = refl
eval-bwd unite₊r v = refl
eval-bwd uniti₊r (inj₁ v) = refl
eval-bwd swap₊ (inj₁ v) = refl
eval-bwd swap₊ (inj₂ v) = refl
eval-bwd assocl₊ (inj₁ (inj₁ v)) = refl
eval-bwd assocl₊ (inj₁ (inj₂ v)) = refl
eval-bwd assocl₊ (inj₂ v) = refl
eval-bwd assocr₊ (inj₁ v) = refl
eval-bwd assocr₊ (inj₂ (inj₁ v)) = refl
eval-bwd assocr₊ (inj₂ (inj₂ v)) = refl
eval-bwd unite⋆l v = refl
eval-bwd uniti⋆l (tt , v) = refl
eval-bwd unite⋆r v = refl
eval-bwd uniti⋆r (v , tt) = refl
eval-bwd swap⋆ (v₂ , v₁) = refl
eval-bwd assocl⋆ ((v₁ , v₂) , v₃) = refl
eval-bwd assocr⋆ (v₁ , (v₂ , v₃)) = refl
eval-bwd dist (inj₁ (v₁ , v₂)) = refl
eval-bwd dist (inj₂ (v₂ , v₃)) = refl
eval-bwd factor (inj₁ v₁ , v₃) = refl
eval-bwd factor (inj₂ v₂ , v₃) = refl
eval-bwd distl (inj₁ (v₁ , v₂)) = refl
eval-bwd distl (inj₂ (v₁ , v₃)) = refl
eval-bwd factorl (v₁ , inj₁ v₂) = refl
eval-bwd factorl (v₁ , inj₂ v₃) = refl
eval-bwd id⟷ v = refl
eval-bwd (c₁ ⊚ c₂) v = trans (cong (eval c₂) (eval-bwd c₁ (bwd c₂ v))) (eval-bwd c₂ v)
eval-bwd (c₁ ⊕ c₂) (inj₁ v) = cong inj₁ (eval-bwd c₁ v)
eval-bwd (c₁ ⊕ c₂) (inj₂ v) = cong inj₂ (eval-bwd c₂ v)
eval-bwd (c₁ ⊗ c₂) (v₃ , v₄) = cong₂ _,_ (eval-bwd c₁ v₃) (eval-bwd c₂ v₄)
eval-bwd (lift c) x = pointed-all-paths
eval-bwd tensorl p = cong₂ _,_ pointed-all-paths pointed-all-paths
eval-bwd tensorr p = pointed-all-paths
eval-bwd plusl p = pointed-all-paths
eval-bwd plusr p = pointed-all-paths
eval-bwd (η v) (p , r) = cong₂ _,_ pointed-all-paths refl
eval-bwd (ε v) tt = refl
eval-bwd (== c eq) p = pointed-all-paths
eval-bwd (focus v) (v , refl) = {!!}
eval-bwd unfocus v = {!!} 
