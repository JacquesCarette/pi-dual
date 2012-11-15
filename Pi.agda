{-# OPTIONS --no-termination-check #-}

module Pi where

open import Data.Nat hiding (_⊔_; suc; _+_; _*_)
open import Data.Vec 
open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality hiding (sym)
open import Relation.Binary.Core
open import Algebra
import Algebra.FunctionProperties as FunctionProperties
open import Algebra.FunctionProperties.Core 
open import Algebra.Structures

infixr 30 _⟷_
infixr 30 _⟺_
infixr 20 _⊙_
infixr 20 _◎_

------------------------------------------------------------------------------
-- First we define a universe of our value types

data B : Set where
  ZERO  : B
  ONE   : B
  PLUS  : B → B → B
  TIMES : B → B → B

⟦_⟧ : B → Set
⟦ ZERO ⟧         = ⊥
⟦ ONE ⟧          = ⊤
⟦ PLUS b1 b2 ⟧   = ⟦ b1 ⟧ ⊎ ⟦ b2 ⟧
⟦ TIMES b1 b2 ⟧  = ⟦ b1 ⟧ × ⟦ b2 ⟧

------------------------------------------------------------------------------
-- Now we define another universe for our equivalences. First the codes for
-- equivalences.

data _⟷_ : B → B → Set where

  unite₊  : { b : B } → PLUS ZERO b ⟷ b
  uniti₊  : { b : B } → b ⟷ PLUS ZERO b
  swap₊   : { b₁ b₂ : B } → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)

  unite⋆  : { b : B } → TIMES ONE b ⟷ b
  uniti⋆  : { b : B } → b ⟷ TIMES ONE b
  swap⋆   : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)

  dist    : { b₁ b₂ b₃ : B } → 
            TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor  : { b₁ b₂ b₃ : B } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃

  id⟷   : { b : B } → b ⟷ b
  sym    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)

--

dist' : {b₁ b₂ b₃ : B} → TIMES b₁ (PLUS b₂ b₃) ⟷ PLUS (TIMES b₁ b₂) (TIMES b₁ b₃)
dist' = swap⋆ ◎ dist ◎ (swap⋆ ⊕ swap⋆) 

midtofront : {a b c : B} → TIMES a (TIMES b c) ⟷ TIMES b (TIMES a c)
midtofront = assocl⋆ ◎ (swap⋆ ⊗ id⟷) ◎ assocr⋆

------------------------------------------------------------------------------
-- Evaluation

adjoint : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
adjoint unite₊    = uniti₊
adjoint uniti₊    = unite₊
adjoint swap₊     = swap₊
adjoint assocl₊   = assocr₊
adjoint assocr₊   = assocl₊
adjoint unite⋆    = uniti⋆
adjoint uniti⋆    = unite⋆
adjoint swap⋆     = swap⋆
adjoint assocl⋆   = assocr⋆
adjoint assocr⋆   = assocl⋆
adjoint dist      = factor
adjoint factor    = dist
adjoint id⟷      = id⟷
adjoint (sym c)   = c
adjoint (c₁ ◎ c₂) = adjoint c₂ ◎ adjoint c₁
adjoint (c₁ ⊕ c₂) = adjoint c₁ ⊕ adjoint c₂
adjoint (c₁ ⊗ c₂) = adjoint c₁ ⊗ adjoint c₂

eval  :{ b₁ b₂ : B } → (b₁ ⟷ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
eval unite₊ (inj₁ ())
eval unite₊ (inj₂ v) = v
eval uniti₊ v = inj₂ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆ (tt , v) = v
eval uniti⋆ v = (tt , v)
eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval id⟷ v = v
eval (sym c) v = eval (adjoint c) v
eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

------------------------------------------------------------------------------
-- NOW WE DEFINE THE SEMANTIC NOTION OF EQUIVALENCE

record _⟺_ (b₁ b₂ : B) : Set where 
  constructor equiv
  field
    f₁₂ : ⟦ b₁ ⟧ → ⟦ b₂ ⟧
    f₂₁ : ⟦ b₂ ⟧ → ⟦ b₁ ⟧
    p₁  : ∀ { x : ⟦ b₁ ⟧ } → f₂₁ (f₁₂ x) ≡ x
    p₂  : ∀ { x : ⟦ b₂ ⟧ } → f₁₂ (f₂₁ x) ≡ x

open _⟺_ public

lem-⟺-inv : ∀{A B C : Set }(g₁₂ : A → B )(g₂₁ : B → A)
  (g₂₃ : B → C)(g₃₂ : C → B) →
     (∀ {x : B } → g₁₂ (g₂₁ x) ≡ x) → ({y : C } → g₂₃ (g₃₂ y) ≡ y ) →
     (∀ {z} → g₂₃ (g₁₂ (g₂₁ (g₃₂ z))) ≡ z)
lem-⟺-inv g₁₂ g₂₁ g₂₃ g₃₂ p₁ p₂ {z = z} = trans p p₂ 
  where w = g₁₂ (g₂₁ (g₃₂ z))
        p = cong g₂₃ {w} p₁
 
_⊙_ : {b₁ b₂ b₃ : B} → b₁ ⟺ b₂ → b₂ ⟺ b₃ → b₁ ⟺ b₃
r ⊙ s = equiv (λ x → f₁₂ s ( f₁₂ r x)) (λ x → f₂₁ r ( f₂₁ s x))
              (lem-⟺-inv (f₂₁ s) (f₁₂ s) (f₂₁ r) (f₁₂ r) (p₁ s) (p₁ r)) 
              (lem-⟺-inv (f₁₂ r) (f₂₁ r) (f₁₂ s) (f₂₁ s) (p₂ r) (p₂ s)) 

-- THESE ARE NEEDED MULTIPLE TIMES, FACTOR OUT

zeroe : {A : Set} → ⊥ ⊎ A → A
zeroe (inj₁ ())
zeroe (inj₂ V) = V

zeroi : {A : Set} → A → ⊥ ⊎ A
zeroi v = inj₂ v

zeroeip : { A : Set } { x : ⊥ ⊎ A } → zeroi (zeroe x) ≡ x
zeroeip { x = inj₁ () }
zeroeip { x = inj₂ v } = refl

sw : {A₁ A₂ : Set} → A₁ ⊎ A₂ → A₂ ⊎ A₁
sw (inj₁ v) = inj₂ v
sw (inj₂ v) = inj₁ v

swp : { A₁ A₂ : Set } → { x : A₁ ⊎ A₂ } → sw (sw x) ≡ x
swp { x = inj₁ v } = refl
swp { x = inj₂ v } = refl

-- And finally we map each code to an actual equivalence

iso : { b₁ b₂ : B } → b₁ ⟷ b₂ → b₁ ⟺ b₂
iso id⟷ = equiv id id refl refl
iso (f ◎ g) = (iso f) ⊙ (iso g)
iso unite₊ = equiv zeroe zeroi zeroeip refl 
iso swap₊ = equiv sw sw swp swp
iso _ = {!!} 
 
-- 

⟷IsEquivalence : IsEquivalence _⟺_ 
⟷IsEquivalence = record {
    refl = ? ;
    sym = ? ;
    trans = ? 
  } 

+IsSemigroup : IsSemigroup _⟺_  PLUS
+IsSemigroup = record {
    isEquivalence = ⟷IsEquivalence ;
    assoc = ? ;
    ∙-cong = ? 
  }


------------------------------------------------------------------------------
