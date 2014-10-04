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

-- Courtesy of Wolfram Kahl, a dependent cong₂                                  
cong₂D : {a b c : Level} {A : Set a} {B : A → Set b} {C : Set c} 
         (f : (x : A) → B x → C)
       → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
       → (x₁≡x₂ : x₁ ≡ x₂) → y₁ ≡ subst B (sym x₁≡x₂) y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂D f refl refl = refl

congD : {a b : Level} {A : Set a} {B : A → Set b}
         (f : (x : A) → B x) → {x₁ x₂ : A} → (x₁≡x₂ : x₁ ≡ x₂) → 
         f x₁ ≡ subst B (sym x₁≡x₂) (f x₂)
congD f refl = refl

xx : {P : ℕ → Set} {p : (n : ℕ) → P n} {e₁ e₂ : Exp} {α : eqExp e₁ e₂} → 
    p (val e₁) ≡ subst P (sym (val≡ α)) (p (val e₂))
xx {P} {p} {e₁} {e₂} {α} = congD p (val≡ α)


pr : {P : ℕ → Set} {p : (n : ℕ) → P n} {e₁ e₂ : Exp} {α : eqExp e₁ e₂} → 
    subst P (val≡ α) (p (val e₁)) ≡ p (val e₂)
pr {P} {p} {e} {.e} {idExp} = refl
pr {P} {p} {e₁} {e₂} {transExp α₁ α₂} = 
  begin (subst P (val≡ (transExp α₁ α₂)) (p (val e₁))
           ≡⟨ refl ⟩
         subst P (trans (val≡ α₁) (val≡ α₂)) (p (val e₁))
           ≡⟨ {!!} ⟩
         p (val e₂) ∎)
  where open ≡-Reasoning
