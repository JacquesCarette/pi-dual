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

-- Theorem, equivalent to stepping: if c : A ↔ B and v : A, then there exists v' : B and c' : (∙ v) ⟷ (∙ v')
eval : {A B : Set} → (A ↔ B) → (v : A) → Σ[ v' ∈ B ] ((⇡ v) ⟷ (⇡ v'))
eval id v = v , id v
eval swap₊ (inj₁ x) = inj₂ x , swap₊₁
eval swap₊ (inj₂ y) = inj₁ y , swap₊₂
eval swap× (x , y) = (y , x) , swap×

-- Theorem, equivalent to backwards stepping: 
-- if c : A ↔ B and v' : B, then there exists v : A and c' : (∙ v) ⟷ (∙ v')
evalB : {A B : Set} → (A ↔ B) → (v' : B) → Σ[ v ∈ A ] ((⇡ v) ⟷ (⇡ v'))
evalB id v = v , id v
evalB swap₊ (inj₁ x) = inj₂ x , swap₊₂
evalB swap₊ (inj₂ y) = inj₁ y , swap₊₁
evalB swap× (x , y) = (y , x) , swap×

-- if c : A ↔ B and v : A, then evalB c (eval c v) ⟷ v
right-inv : {A B : Set} → (c : A ↔ B) → (v : A) → ⇡ (proj₁ (evalB c (proj₁ (eval c v)))) ⟷ ⇡ v
right-inv id v = id v
right-inv swap₊ (inj₁ x) = id (inj₁ x)
right-inv swap₊ (inj₂ y) = id (inj₂ y)
right-inv swap× v = id v

-- left-inv should be just as easy.

-- we should also be able to make a statement about proj₂ associated with back-and-forth

-- and create a function that maps c to its inverse, and 'prove' eval c = evalB @ inverse c

-- "forget" the extra structure
↓ : {A B : Set} → {x : A} → {y : B} → (⇡ x) ⟷ (⇡ y) → A ↔ B
↓ {A} {.A} {x} (id .x) = id
↓ swap₊₁ = swap₊
↓ swap₊₂ = swap₊
↓ swap× = swap×

