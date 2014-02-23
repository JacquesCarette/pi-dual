{-# OPTIONS --without-K #-}
-- Finite types and paths between them
module FT where

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Sum 
open import Data.Product 
-- open import Function

infixl 10 _◎_

------------------------------------------------------------------------------
-- Finite types

data FT : Set where
  ZERO  : FT
  ONE   : FT
  PLUS  : FT → FT → FT
  TIMES : FT → FT → FT

⟦_⟧ : FT → Set
⟦ ZERO ⟧ = ⊥
⟦ ONE ⟧ = ⊤
⟦ PLUS B₁ B₂ ⟧ = ⟦ B₁ ⟧ ⊎ ⟦ B₂ ⟧
⟦ TIMES B₁ B₂ ⟧ = ⟦ B₁ ⟧ × ⟦ B₂ ⟧

------------------------------------------------------------------------------
-- Generalized paths are pi-combinators

data _⇛_ : FT → FT → Set where
  -- additive structure
  unite₊⇛  : { b : FT } → PLUS ZERO b ⇛ b

  uniti₊⇛  : { b : FT } → b ⇛ PLUS ZERO b
  swap₊⇛   : { b₁ b₂ : FT } → PLUS b₁ b₂ ⇛ PLUS b₂ b₁
  assocl₊⇛ : { b₁ b₂ b₃ : FT } → PLUS b₁ (PLUS b₂ b₃) ⇛ PLUS (PLUS b₁ b₂) b₃
  assocr₊⇛ : { b₁ b₂ b₃ : FT } → PLUS (PLUS b₁ b₂) b₃ ⇛ PLUS b₁ (PLUS b₂ b₃)
  -- multiplicative structure
  unite⋆⇛  : { b : FT } → TIMES ONE b ⇛ b
  uniti⋆⇛  : { b : FT } → b ⇛ TIMES ONE b
  swap⋆⇛   : { b₁ b₂ : FT } → TIMES b₁ b₂ ⇛ TIMES b₂ b₁
  assocl⋆⇛ : { b₁ b₂ b₃ : FT } → 
             TIMES b₁ (TIMES b₂ b₃) ⇛ TIMES (TIMES b₁ b₂) b₃
  assocr⋆⇛ : { b₁ b₂ b₃ : FT } → 
             TIMES (TIMES b₁ b₂) b₃ ⇛ TIMES b₁ (TIMES b₂ b₃)
  -- distributivity
  distz⇛   : { b : FT } → TIMES ZERO b ⇛ ZERO
  factorz⇛ : { b : FT } → ZERO ⇛ TIMES ZERO b
  dist⇛    : { b₁ b₂ b₃ : FT } → 
            TIMES (PLUS b₁ b₂) b₃ ⇛ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor⇛  : { b₁ b₂ b₃ : FT } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⇛ TIMES (PLUS b₁ b₂) b₃
  -- congruence
  id⇛    : { b : FT } → b ⇛ b
  sym⇛   : { b₁ b₂ : FT } → (b₁ ⇛ b₂) → (b₂ ⇛ b₁)
  _◎_    : { b₁ b₂ b₃ : FT } → (b₁ ⇛ b₂) → (b₂ ⇛ b₃) → (b₁ ⇛ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : FT } → 
           (b₁ ⇛ b₃) → (b₂ ⇛ b₄) → (PLUS b₁ b₂ ⇛ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : FT } → 
           (b₁ ⇛ b₃) → (b₂ ⇛ b₄) → (TIMES b₁ b₂ ⇛ TIMES b₃ b₄)

------------------------------------------------------------------------------

{--

Not used

BOOL-FT : Set
BOOL-FT = ⟦ PLUS ONE ONE ⟧

true-FT : BOOL-FT
true-FT = inj₁ tt

false-FT : BOOL-FT
false-FT = inj₂ tt

witness : (B : FT) → Maybe ⟦ B ⟧
witness ZERO = nothing
witness ONE = just tt
witness (PLUS B₁ B₂) with witness B₁ | witness B₂ 
... | nothing | nothing = nothing
... | nothing | just b  = just (inj₂ b)
... | just b  | _ = just (inj₁ b) 
witness (TIMES B₁ B₂) with witness B₁ | witness B₂ 
... | nothing | _ = nothing
... | just b  | nothing = nothing
... | just b₁ | just b₂ = just (b₁ , b₂)

elems : (B : FT) → List ⟦ B ⟧
elems ZERO          = []
elems ONE           = [ tt ]
elems (PLUS B₁ B₂)  = map inj₁ (elems B₁) ++ map inj₂ (elems B₂) 
elems (TIMES B₁ B₂) = concatMap 
                        (λ e₁ → map (λ e₂ → (e₁ , e₂)) (elems B₂)) 
                        (elems B₁)
      
expandF : {B₁ B₂ : FT} → (⟦ B₁ ⟧ → ⟦ B₂ ⟧) → List (⟦ B₁ ⟧ × ⟦ B₂ ⟧)
expandF {B₁} {B₂} f = map (λ e → (e , f e)) (elems B₁)

test0 : List ((⊤ × BOOL-FT) × BOOL-FT)
test0 = expandF (unite⋆ {BOOL-FT})


--}
