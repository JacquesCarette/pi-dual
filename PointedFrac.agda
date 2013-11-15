module PointedFrac where

open import Data.Sum
open import Data.Product

record ∙_ (A : Set) : Set where
  constructor ⇡ 
  field
    focus : A

open ∙_

data _⟷_ : {A B : Set} → ∙ A → ∙ B → Set1 where
  id : {A : Set} → (x : A) → (⇡ x) ⟷ (⇡ x)
  swap₊₁ : {A B : Set} → {x : A} → _⟷_ {A ⊎ B} {B ⊎ A} (⇡ (inj₁ x)) (⇡ (inj₂ x))
  swap₊₂ : {A B : Set} → {y : B} → _⟷_ {A ⊎ B} {B ⊎ A} (⇡ (inj₂ y)) (⇡ (inj₁ y))
  swap× : {A B : Set} → {x : A} → {y : B} ‌→ ⇡ (x , y) ⟷ ⇡ (y , x)
  -- ...and so on

-- shorter arrow for a shorter definition!
data _↔_ : Set → Set → Set1 where
  id : {A : Set} → A ↔ A
  swap₊ : {A B : Set} → (A ⊎ B) ↔ (B ⊎ A)
  swap× : {A B : Set} → (A × B) ↔ (B × A)

-- Theorem, equivalent to stepping: if c : A ↔ B and v : A, then there exists v' : B and c' : (∙ x) ⟷ (∙ y)
eval : {A B : Set} → (A ↔ B) → (v : A) → Σ[ v' ∈ B ] ((⇡ v) ⟷ (⇡ v'))
eval id v = v , id v
eval swap₊ (inj₁ x) = inj₂ x , swap₊₁
eval swap₊ (inj₂ y) = inj₁ y , swap₊₂
eval swap× (x , y) = (y , x) , swap×

-- "forget" the extra structure
↓ : {A B : Set} → {x : A} → {y : B} → (⇡ x) ⟷ (⇡ y) → A ↔ B
↓ {A} {.A} {x} (id .x) = id
↓ swap₊₁ = swap₊
↓ swap₊₂ = swap₊
↓ swap× = swap×

