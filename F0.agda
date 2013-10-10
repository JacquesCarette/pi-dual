{-# OPTIONS --without-K #-}

module F0 where

import Level as L
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function using (id ; _$_ )

infixr 90 _⊗_
infixr 80 _⊕_
infixr 60 _∘_
infix  30 _⟷_

---------------------------------------------------------------------------
-- Our own version of refl that makes 'a' explicit

data _≡_ {u} {A : Set u} : (a b : A) → Set u where
  refl : (a : A) → (a ≡ a)

-- if we have no occurrences of reciprocals then we can use plain sets; for
-- consistency with the rest of the story we will explicitly add refl paths

-- pi types with no reciprocals

data B : Set where
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

-- discrete groupoids

record 0-type : Set₁ where
  constructor G₀
  field
    ∣_∣ : Set
  paths : {a : ∣_∣} → (a ≡ a)
  paths {a} = refl a

open 0-type public

plus : 0-type → 0-type → 0-type
plus t₁ t₂ = G₀ (∣ t₁ ∣ ⊎ ∣ t₂ ∣)

times : 0-type → 0-type → 0-type
times t₁ t₂ = G₀ (∣ t₁ ∣ × ∣ t₂ ∣)

-- We interpret types as discrete groupoids

⟦_⟧ : B → 0-type
⟦ ONE ⟧ = G₀ ⊤
⟦ PLUS b₁ b₂ ⟧ = plus ⟦ b₁ ⟧ ⟦ b₂ ⟧
⟦ TIMES b₁ b₂ ⟧ = times ⟦ b₁ ⟧ ⟦ b₂ ⟧

-- isos

data _⟷_ : B → B → Set where
  -- + 
  swap₊   : { b₁ b₂ : B } → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
  -- *
  unite⋆  : { b : B } → TIMES ONE b ⟷ b
  uniti⋆  : { b : B } → b ⟷ TIMES ONE b
  swap⋆   : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
  -- * distributes over + 
  dist    : { b₁ b₂ b₃ : B } → 
            TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor  : { b₁ b₂ b₃ : B } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
  -- congruence
  id⟷   : { b : B } → b ⟷ b
  sym    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _∘_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)

-- interpret isos as functors

record 0-functor (A B : 0-type) : Set where
  constructor F₀
  field
    fobj : ∣ A ∣ → ∣ B ∣
  fmor : {a b : ∣ A ∣} → (a ≡ b) → (fobj a ≡ fobj b)
  fmor {a} {.a} (refl .a) = refl (fobj a)

open 0-functor public

swap⊎ : {A B : Set} → A ⊎ B → B ⊎ A
swap⊎ (inj₁ a) = inj₂ a
swap⊎ (inj₂ b) = inj₁ b

assocl⊎ : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
assocl⊎ (inj₁ x) = inj₁ (inj₁ x)
assocl⊎ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
assocl⊎ (inj₂ (inj₂ y)) = inj₂ y

assocr⊎ : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
assocr⊎ (inj₁ (inj₁ x)) = inj₁ x
assocr⊎ (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
assocr⊎ (inj₂ y) = inj₂ (inj₂ y)

unite× : {A : Set} → ⊤ × A → A
unite× (tt , x) = x

uniti× : {A : Set} → A → ⊤ × A
uniti× x = (tt , x)

swap× : {A B : Set} → A × B → B × A
swap× (a , b) = (b , a)

assocl× : {A B C : Set} → A × (B × C) → (A × B) × C
assocl× (x , (y , z)) = (x , y) , z

assocr× : {A B C : Set} → (A × B) × C → A × (B × C)
assocr× ((x , y) , z) = x , (y , z)

dist×⊎ : {A B C : Set} → (A ⊎ B) × C → (A × C) ⊎ (B × C)
dist×⊎ (inj₁ a , c) = inj₁ (a , c)
dist×⊎ (inj₂ b , c) = inj₂ (b , c)

factor⊎× : {A B C : Set} → (A × C) ⊎ (B × C) → (A ⊎ B) × C
factor⊎× (inj₁ (a , c)) = (inj₁ a , c)
factor⊎× (inj₂ (b , c)) = (inj₂ b , c)

ev⊎ : {A B C D : Set} → (A → C) → (B → D) → A ⊎ B → C ⊎ D
ev⊎ f _ (inj₁ a) = inj₁ (f a)
ev⊎ _ g (inj₂ b) = inj₂ (g b)

ev× : {A B C D : Set} → (A → C) → (B → D) → A × B → C × D
ev× f g (a , b) = (f a , g b)

mutual 
       eval : {b₁ b₂ : B} → (b₁ ⟷ b₂) → 0-functor ⟦ b₁ ⟧ ⟦ b₂ ⟧
       eval swap₊ = F₀ swap⊎
       eval assocl₊ = F₀ assocl⊎
       eval assocr₊ = F₀ assocr⊎
       eval unite⋆ = F₀ unite×
       eval uniti⋆ = F₀ uniti×
       eval swap⋆ = F₀ swap×
       eval assocl⋆ = F₀ assocl×
       eval assocr⋆ = F₀ assocr×
       eval dist = F₀ dist×⊎
       eval factor = F₀ factor⊎×
       eval id⟷ = F₀ id
       eval (sym c) = evalB c
       eval (c₁ ∘ c₂) = F₀ (λ x → fobj (eval c₂) (fobj (eval c₁) x))
       eval (c₁ ⊕ c₂) = F₀ (ev⊎ (fobj $ eval c₁) (fobj $ eval c₂))
       eval (c₁ ⊗ c₂) = F₀ (ev× (fobj $ eval c₁) (fobj $ eval c₂))

       evalB : {b₁ b₂ : B} → (b₁ ⟷ b₂) → 0-functor ⟦ b₂ ⟧ ⟦ b₁ ⟧
       evalB swap₊ = F₀ swap⊎
       evalB assocl₊ = F₀ assocr⊎
       evalB assocr₊ = F₀ assocl⊎
       evalB unite⋆ = F₀ uniti×
       evalB uniti⋆ = F₀ unite×
       evalB swap⋆ = F₀ swap×
       evalB assocl⋆ = F₀ assocr×
       evalB assocr⋆ = F₀ assocl×
       evalB dist = F₀ factor⊎×
       evalB factor = F₀ dist×⊎
       evalB id⟷ = F₀ id
       evalB (sym c) = eval c
       evalB (c₁ ∘ c₂) = F₀ (λ x → fobj (evalB c₁) (fobj (evalB c₂) x))
       evalB (c₁ ⊕ c₂) = F₀ (ev⊎ (fobj $ evalB c₁) (fobj $ evalB c₂))
       evalB (c₁ ⊗ c₂) = F₀ (ev× (fobj $ evalB c₁) (fobj $ evalB c₂))

---------------------------------------------------------------------------
