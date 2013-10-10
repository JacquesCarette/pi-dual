{-# OPTIONS --without-K #-}

module F1 where

import Level as L
open import Data.Unit
open import Data.Sum
open import Data.Product

{--
infixr 90 _⊗_
infixr 80 _⊕_
infixr 60 _∘_
infix  30 _⟷_
--}

---------------------------------------------------------------------------
-- Our own version of refl that makes 'a' explicit

data _≡_ {u} {A : Set u} : (a b : A) → Set u where
  refl : (a : A) → (a ≡ a)

-- if we have no occurrences of reciprocals then we can use plain sets; for
-- consistency with the rest of the story we will explicitly add refl paths
-- in this file we assume we have exactly one occurrence of reciprocals
-- so 1/b is ok but 1/(1/b) not ok

-- pi types with no reciprocals

data B0 : Set where
  ONE    : B0
  PLUS0  : B0 → B0 → B0
  TIMES0 : B0 → B0 → B0

data B1 : Set where
  LIFT0  : B0 → B1
  PLUS1  : B1 → B1 → B1
  TIMES1 : B1 → B1 → B1
  RECIP1 : B0 → B1

-- discrete groupoids

record 2-type : Set₁ where
  constructor G₂
  field
    ∣_∣ : Set
    1-paths : {a b : ∣_∣} → (a ≡ b)
--    2-paths : {a b : ∣_∣} {p q : 1-paths {a} {b}} → (p ≡ q)

open 2-type public

x : (r : 2-type) → {a b : ∣ r ∣} → (a ≡ b)
x = 1-paths

p : (r : 2-type) → {a b : ∣ r ∣} {q p : x r {a} {b}} → (p ≡ q)
p = ?

{--

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

eval : {b₁ b₂ : B} → (b₁ ⟷ b₂) → 0-functor ⟦ b₁ ⟧ ⟦ b₂ ⟧
eval swap₊ = F₀ swap⊎
eval assocl₊ = ? -- : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
eval assocr₊ = ? -- : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
eval unite⋆ = ? -- : { b : B } → TIMES ONE b ⟷ b
eval uniti⋆ = ? -- : { b : B } → b ⟷ TIMES ONE b
eval swap⋆ = ? --  : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
eval assocl⋆ = ? -- : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
eval assocr⋆ = ? -- : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
eval dist = ? -- : { b₁ b₂ b₃ : B } → TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
eval factor = ? -- : { b₁ b₂ b₃ : B } → PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
eval id⟷ = ? --  : { b : B } → b ⟷ b
eval (sym c) = ? -- : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
eval (c₁ ∘ c₂) = ? -- : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
eval (c₁ ⊕ c₂) = ? -- : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
eval (c₁ ⊗ c₂) = ? -- : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)

---------------------------------------------------------------------------
--}
