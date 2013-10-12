{-# OPTIONS --without-K #-}

module F1a where

open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.List

open import Data.Nat
open import Data.Bool

{--
infixr 90 _⊗_
infixr 80 _⊕_
infixr 60 _∘_
infix  30 _⟷_
--}

---------------------------------------------------------------------------
-- Paths

-- Path relation should be an equivalence 
data IPath (I A : Set) : Set where
  _↝_ : {i : I} (a : A) → (b : A) → IPath I A

Path : Set → Set
Path A = IPath ⊤ A

id↝ : {A : Set} → (a : A) → Path A
id↝ a = a ↝ a

ap : {A B I : Set} → (A → B) → IPath I A → IPath I B
ap f (_↝_ {i} a a') = _↝_ {i = i} (f a) (f a')

iap : {A B I J : Set} → (I → J) → (A → B) → IPath I A → IPath J B
iap g f (_↝_ {i} a a') = _↝_ {i = g i} (f a) (f a')

ipathProd : {A B I J : Set} → IPath I A → IPath J B → IPath (I × J) (A × B)
ipathProd (_↝_ {i = i} a a') (_↝_ {i = j} b b') = _↝_ {i = i , j} (a , b) (a' , b')

_×↝_ : {A B I J : Set} → List (IPath I A) → List (IPath J B) → List (IPath (I × J) (A × B))
pas ×↝ pbs = concatMap (λ pa → map (ipathProd pa) pbs) pas
  
-- pi types with exactly one level of reciprocals

data B0 : Set where
  ONE    : B0
  PLUS0  : B0 → B0 → B0
  TIMES0 : B0 → B0 → B0

data B1 : Set where
  LIFT0  : B0 → B1
  PLUS1  : B1 → B1 → B1
  TIMES1 : B1 → B1 → B1
  RECIP1 : B0 → B1

-- interpretation of B0 as discrete groupoids

record 0-type : Set₁ where
  constructor G₀
  field
    ∣_∣₀ : Set

open 0-type public

plus : 0-type → 0-type → 0-type
plus t₁ t₂ = G₀ (∣ t₁ ∣₀ ⊎ ∣ t₂ ∣₀) 

times : 0-type → 0-type → 0-type
times t₁ t₂ = G₀ (∣ t₁ ∣₀ × ∣ t₂ ∣₀)

⟦_⟧₀ : B0 → 0-type
⟦ ONE ⟧₀ = G₀ ⊤ 
⟦ PLUS0 b₁ b₂ ⟧₀ = plus ⟦ b₁ ⟧₀ ⟦ b₂ ⟧₀
⟦ TIMES0 b₁ b₂ ⟧₀ = times ⟦ b₁ ⟧₀ ⟦ b₂ ⟧₀

elems0 : (b : B0) → List ∣ ⟦ b ⟧₀ ∣₀
elems0 ONE = [ tt ]
elems0 (PLUS0 b b') = map inj₁ (elems0 b) ++ map inj₂ (elems0 b')
elems0 (TIMES0 b b') = 
  concatMap (λ a → map (λ b → (a , b)) (elems0 b')) (elems0 b)

-- interpretation of B1 types as 2-types

record 1-type : Set₁ where
  constructor G₂
  field
    I : Set
    ∣_∣₁ : Set
    1-paths : List (IPath I ∣_∣₁)

open 1-type public

_⊎↝_ : {I J A B : Set} → List (IPath I A) → List (IPath J B) → List (IPath (I ⊎ J) (A ⊎ B))
p₁ ⊎↝ p₂ = map (iap inj₁ inj₁) p₁ ++ map (iap inj₂ inj₂) p₂

⟦_⟧₁ : B1 → 1-type
⟦ LIFT0 b0 ⟧₁ = G₂ ⊤ ∣ ⟦ b0 ⟧₀ ∣₀ (map id↝ (elems0 b0))
⟦ PLUS1 b₁ b₂ ⟧₁ with ⟦ b₁ ⟧₁ | ⟦ b₂ ⟧₁ 
... | G₂ I₁ 0p₁ 1p₁ | G₂ I₂ 0p₂ 1p₂ = G₂ (I₁ ⊎ I₂) (0p₁ ⊎ 0p₂) (1p₁ ⊎↝ 1p₂)
⟦ TIMES1 b₁ b₂ ⟧₁ with ⟦ b₁ ⟧₁ | ⟦ b₂ ⟧₁ 
... | G₂ I₁ 0p₁ 1p₁ | G₂ I₂ 0p₂ 1p₂ = G₂ (I₁ × I₂) (0p₁ × 0p₂) (1p₁ ×↝ 1p₂)
⟦ RECIP1 b0 ⟧₁ = G₂ (∣ ⟦ TIMES0 b0 b0 ⟧₀ ∣₀ ) ⊤ (concatMap (λ a → map (λ b → _↝_ {i = a , b} tt tt) (elems0 b0)) (elems0 b0) )

test10 = ⟦ LIFT0 ONE ⟧₁
test11 = ⟦ LIFT0 (PLUS0 ONE ONE) ⟧₁
test12 = ⟦ RECIP1 (PLUS0 ONE ONE) ⟧₁

-- isos

data _⟷_ : B1 → B1 → Set where
  -- + 
  swap₊   : { b₁ b₂ : B1 } → PLUS1 b₁ b₂ ⟷ PLUS1 b₂ b₁
{-  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
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

record 1-functor (A B : 1-type) : Set where
  constructor F₁
  field
    find : I A → I B
    fobj : ∣ A ∣₁ → ∣ B ∣₁
  fmor : {a b : ∣ A ∣₁} → {i j : I A} → (IPath i a) → (IPath j (fobj a) (fobj b))
  fmor {a} {b} (p) = ?

open 1-functor public

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
