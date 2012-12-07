module VecSN where

open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum 
open import Data.Vec
open import Data.Nat
open import Data.Bool
open import Data.Nat.Properties

------------------------------------------------------------------------------
-- types (dimension of a vector space)

data B : Set where
  ZERO   : B
  ONE    : B
  PLUS   : B → B → B
  TIMES  : B → B → B

-- values (indices for vectors which match the dimension)

data BVAL : B → Set where
  UNIT   : BVAL ONE
  LEFT   : {b₁ b₂ : B} → BVAL b₁ → BVAL (PLUS b₁ b₂)
  RIGHT  : {b₁ b₂ : B} → BVAL b₂ → BVAL (PLUS b₁ b₂)
  PAIR   : {b₁ b₂ : B} → BVAL b₁ → BVAL b₂ → BVAL (TIMES b₁ b₂)

-- isomorphisms between types

data _⟷_ : B → B → Set where
  -- (+,0) commutative monoid
  unite₊  : { b : B } → PLUS ZERO b ⟷ b
  uniti₊  : { b : B } → b ⟷ PLUS ZERO b
  swap₊   : { b₁ b₂ : B } → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
  -- (*,1) commutative monoid
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
  -- closure
  id⟷   : { b : B } → b ⟷ b
  sym    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)

------------------------------------------------------------------------------
-- next layer of types (vectors and duals assuming underlying field is F_3
-- and that we do not allow superpositions)

mutual 

  data Scalar : Set where
    NO   : Scalar
    YES+ : Scalar
    YES- : Scalar
    ip   : {b : B} → V b → V⋆ b → Scalar

  data V : B → Set where
    zero   : {b : B} → V b
    ket    : {b : B} → BVAL b → V b
    s      : {b : B} → Scalar → V b
    dual   : {b : B} → V⋆ b → V b
    neg    : {b : B} → V b → V b
    choose : {b : B} → V b → V b → V b

  data V⋆ : B → Set where
    zero⋆   : {b : B} → V⋆ b
    ket⋆    : {b : B} → BVAL b → V⋆ b
    s⋆      : {b : B} → Scalar → V⋆ b
    dual⋆   : {b : B} → V b → V⋆ b
    neg⋆    : {b : B} → V⋆ b → V⋆ b
    choose⋆ : {b : B} → V⋆ b → V⋆ b → V⋆ b

data Iso : {b₁ b₂ : B} → V b₁ → V b₂ → Set where
  base : {b₁ b₂ : B} {v₁ : BVAL b₁} {v₂ : BVAL b₂} → 
         (b₁ ⟷ b₂) → Iso (ket v₁) (ket v₂)
  -- additive duality
  η₊      : { b : B } → { φ : V b } → Iso (zero {b}) (choose (neg φ) φ)
  ε₊      : { b : B } → { φ : V b } → Iso (choose φ (neg φ)) (zero {b})
  -- multiplicative duality
  refe⋆   : { b : B } → { φ : V b } → Iso (dual (dual⋆ φ)) φ
  refi⋆   : { b : B } → { φ : V b } → Iso φ (dual (dual⋆ φ))
  rile⋆   : { b : B } → { φ : V b } → Iso {b} {b} (s (ip φ (s⋆ (ip φ (dual⋆ φ))))) φ
  rili⋆   : { b : B } → { φ : V b } → Iso {b} {b} φ (s (ip φ (s⋆ (ip φ (dual⋆ φ)))))

------------------------------------------------------------------------------

