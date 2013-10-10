{-# OPTIONS --without-K #-}

module F0 where

import Level as L
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function using (id)

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

eval : {b₁ b₂ : B} → (b₁ ⟷ b₂) → 0-functor ⟦ b₁ ⟧ ⟦ b₂ ⟧
eval swap₊ = F₀ swap⊎
eval assocl₊ = F₀ assocl⊎ -- : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
eval assocr₊ = F₀ assocr⊎ -- : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
eval unite⋆ = F₀ unite× -- : { b : B } → TIMES ONE b ⟷ b
eval uniti⋆ = F₀ uniti× -- : { b : B } → b ⟷ TIMES ONE b
eval swap⋆ = F₀ swap× --  : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
eval assocl⋆ = F₀ assocl× -- : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
eval assocr⋆ = F₀ assocr× -- : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
eval dist = F₀ dist×⊎ -- : { b₁ b₂ b₃ : B } → TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
eval factor = F₀ {!!} -- : { b₁ b₂ b₃ : B } → PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
eval id⟷ = F₀ id --  : { b : B } → b ⟷ b
eval (sym c) = F₀ {!!} -- : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
eval (c₁ ∘ c₂) = F₀ {!!} -- : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
eval (c₁ ⊕ c₂) = F₀ {!!} -- : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
eval (c₁ ⊗ c₂) = F₀ {!!} -- : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)

---------------------------------------------------------------------------
