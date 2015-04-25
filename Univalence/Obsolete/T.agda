{-# OPTIONS --without-K #-}

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

trans-assoc : {A : Set} {x y z w : A} → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → 
  trans (trans p q) r ≡ trans p (trans q r)
trans-assoc refl refl refl = refl 

subst-trans : (P : ℕ → Set) (p : (n : ℕ) → P n) {e₁ e₂ e₃ : Exp} → 
              (α : eqExp e₁ e₂) (β : eqExp e₂ e₃) (v : P (val e₁)) → 
              subst P (trans (val≡ α) (val≡ β)) v ≡
              subst P (val≡ β) (subst P (val≡ α) v)
subst-trans P p idExp β v = refl
subst-trans P p (transExp α₁ α₂) β v = 
  begin (subst P (trans (trans (val≡ α₁) (val≡ α₂)) (val≡ β)) v
         ≡⟨ cong (λ x → subst P x v) 
                 (trans-assoc (val≡ α₁) (val≡ α₂) (val≡ β))  ⟩
         subst P (trans (val≡ α₁) (trans (val≡ α₂) (val≡ β))) v
         ≡⟨ refl ⟩ 
         subst P (trans (val≡ α₁) (val≡ (transExp α₂ β))) v
         ≡⟨  subst-trans P p α₁ (transExp α₂ β) v ⟩ 
         subst P (val≡ (transExp α₂ β)) (subst P (val≡ α₁) v)
         ≡⟨ refl ⟩ 
         subst P (trans (val≡ α₂) (val≡ β)) (subst P (val≡ α₁) v)
         ≡⟨ subst-trans P p α₂ β (subst P (val≡ α₁) v) ⟩ 
         subst P (val≡ β) (subst P (val≡ α₂) (subst P (val≡ α₁) v))
         ≡⟨ cong (λ x → subst P (val≡ β) x) (sym (subst-trans P p α₁ α₂ v)) ⟩ 
         subst P (val≡ β) (subst P (trans (val≡ α₁) (val≡ α₂)) v)
         ≡⟨ refl ⟩ 
         subst P (val≡ β) (subst P (val≡ (transExp α₁ α₂)) v) ∎)
  where open ≡-Reasoning

pr : {P : ℕ → Set} {p : (n : ℕ) → P n} {e₁ e₂ : Exp} {α : eqExp e₁ e₂} → 
    subst P (val≡ α) (p (val e₁)) ≡ p (val e₂)
pr {P} {p} {e} {.e} {idExp} = refl
pr {P} {p} {e₁} {e₃} {transExp {e₂ = e₂} α β} = 
  begin (subst P (val≡ (transExp α β)) (p (val e₁))
           ≡⟨ refl ⟩
         subst P (trans (val≡ α) (val≡ β)) (p (val e₁))
           ≡⟨ subst-trans P p α β (p (val e₁)) ⟩ 
         subst P (val≡ β) (subst P (val≡ α) (p (val e₁)))
           ≡⟨ cong (λ x → subst P (val≡ β) x) (pr {P} {p} {e₁} {e₂} {α}) ⟩ 
         subst P (val≡ β) (p (val e₂))
           ≡⟨ pr {P} {p} {e₂} {e₃} {β} ⟩ 
         p (val e₃) ∎)
  where open ≡-Reasoning
