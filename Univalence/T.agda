module T where

open import Level
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin) 

data Exp : Set where
  ONE   : Exp
  PLUS  : Exp → Exp → Exp

val : Exp → ℕ
val ONE           = 1
val (PLUS e₁ e₂)  = val e₁ + val e₂

data eqExp : Exp → Exp → Set where
  idExp    : {e : Exp} → eqExp e e
  transExp : {e₁ e₂ e₃ : Exp} → (eqExp e₁ e₂) → (eqExp e₂ e₃) → (eqExp e₁ e₃)

val≡ : {e₁ e₂ : Exp} → (eqExp e₁ e₂) → (val e₁ ≡ val e₂)
val≡ idExp = refl
val≡ (transExp α₁ α₂) = trans (val≡ α₁) (val≡ α₂)

subst-trans : {P : ℕ → Set} {p : (n : ℕ) → P n} {e₁ e₂ e₃ : Exp} 
              {α : eqExp e₁ e₂} {β : eqExp e₂ e₃} → 
              subst P (trans (val≡ α) (val≡ β)) (p (val e₁)) ≡
              subst P (val≡ β) (subst P (val≡ α) (p (val e₁)))
subst-trans {P} {p} {e₁} {.e₁} {e₃} {idExp} {β} = refl
subst-trans {P} {p} {e₁} {e₂} {e₃} {transExp {.e₁} {e₄} {.e₂} α' β'} {β} = 
  begin (subst P (trans (val≡ (transExp α' β')) (val≡ β)) (p (val e₁))
           ≡⟨ refl ⟩ 
         subst P (trans (trans (val≡ α') (val≡ β')) (val≡ β)) (p (val e₁))
           ≡⟨ {!!} ⟩ 
         subst P (val≡ β) (subst P (val≡ (transExp α' β')) (p (val e₁))) ∎)
  where open ≡-Reasoning

-- subst-trans {P} {p} {e₁} {e₂} {e₃} {α} {β} = {!!}

pr : {P : ℕ → Set} {p : (n : ℕ) → P n} {e₁ e₂ : Exp} {α : eqExp e₁ e₂} → 
    subst P (val≡ α) (p (val e₁)) ≡ p (val e₂)
pr {P} {p} {e} {.e} {idExp} = refl
pr {P} {p} {e₁} {e₃} {transExp {e₂ = e₂} α β} = 
  begin (subst P (val≡ (transExp α β)) (p (val e₁))
           ≡⟨ refl ⟩
         subst P (trans (val≡ α) (val≡ β)) (p (val e₁))
           ≡⟨ subst-trans {P} {p} {e₁} {e₂} {e₃} {α} {β} ⟩ 
         subst P (val≡ β) (subst P (val≡ α) (p (val e₁)))
           ≡⟨ cong (λ x → subst P (val≡ β) x) (pr {P} {p} {e₁} {e₂} {α}) ⟩ 
         subst P (val≡ β) (p (val e₂))
           ≡⟨ pr {P} {p} {e₂} {e₃} {β} ⟩ 
         p (val e₃) ∎)
  where open ≡-Reasoning

