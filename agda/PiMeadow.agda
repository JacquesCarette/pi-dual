module PiMeadow where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (sym)

infixr 20 _◎_

data <_> {A : Set} : A → Set where
  singleton : (x : A) -> < x > 

mutual

  data B : Set₁ where
    ZERO  : B 
    ONE   : B
    PLUS  : B → B → B
    TIMES : B → B → B
    SING  : (b : B) → ⟦ b ⟧ → B
    RECIP : (b : B) → ⟦ b ⟧ → B
    DPAIR : (b : B) → (⟦ b ⟧ → B) → B

  ⟦_⟧ : B → Set
  ⟦ ZERO ⟧         = ⊥
  ⟦ ONE ⟧          = ⊤
  ⟦ PLUS b₁ b₂ ⟧   = ⟦ b₁ ⟧ ⊎ ⟦ b₂ ⟧
  ⟦ TIMES b₁ b₂ ⟧  = ⟦ b₁ ⟧ × ⟦ b₂ ⟧
  ⟦ SING b v ⟧  = <_> {⟦ b ⟧} v
  ⟦ RECIP b v ⟧      = <_> {⟦ b ⟧} v → ⊤
  ⟦ DPAIR b c ⟧ = Σ ⟦ b ⟧ (λ v → ⟦ c v ⟧)

-- Useful abbrev
leftIdemp : (b : B) → ⟦ b ⟧ → B
leftIdemp b v = TIMES (SING b v) (RECIP b v)
 
data _⟷_ : B → B → Set₁ where
  unite₊ : {b : B} → PLUS ZERO b ⟷ b
  uniti₊ : {b : B} → b ⟷ PLUS ZERO b
  swap₊ : {b₁ b₂ : B} → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
  unite⋆  : { b : B } → TIMES ONE b ⟷ b
  uniti⋆  : { b : B } → b ⟷ TIMES ONE b
  swap⋆ : {b₁ b₂ : B} → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
  id⟷ : {b : B } → b ⟷ b
  sym    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
--  _◑_    : { b₁ b₂ b₃ b₄ b₅: B } → (DPAIR b₁ c ⟷ b₂) →
--           (b₂ ⟷ DPAIR b₃ d) → (c : B  
--           (DPAIR b₁ c) ⟷ DPAIR (b₃ d)) 
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)
  η : {b : B} → b ⟷ DPAIR b (λ v → leftIdemp b v)
  ε : {b : B} → (DPAIR b (λ v → leftIdemp b v)) ⟷ b 

{-
_◑_ : { b₁ b₂ b₃ : B } {c : ⟦ b₁ ⟧ → B} {d : ⟦ b₃ ⟧ → B} → 
          (DPAIR b₁ c ⟷ b₂) → (b₂ ⟷ DPAIR b₃ d) → 
          (DPAIR b₁ c ⟷ DPAIR b₃ d) 
f ◑ g = {!!}
-}

mutual
  eval : {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
  eval unite₊ (inj₁ ())
  eval unite₊ (inj₂ v) = v
  eval uniti₊ v = inj₂ v
  eval swap₊ (inj₁ x) = inj₂ x
  eval swap₊ (inj₂ y) = inj₁ y
  eval assocl₊ (inj₁ x) = inj₁ (inj₁ x)
  eval assocl₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  eval assocl₊ (inj₂ (inj₂ x)) = inj₂ x
  eval assocr₊ (inj₁ (inj₁ x)) = inj₁ x
  eval assocr₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  eval assocr₊ (inj₂ y) = inj₂ (inj₂ y)
  eval unite⋆ (tt , x) = x
  eval uniti⋆ v = ( tt , v)
  eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
  eval assocl⋆ (x , (y , z)) = ((x , y), z)
  eval assocr⋆ ((x , y), z) = (x , (y , z))
  eval id⟷ v = v
  eval (sym c) v = evalB c v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (inj₁ x) = inj₁ (eval c₁ x)
  eval (c₁ ⊕ c₂) (inj₂ y) = inj₂ (eval c₂ y)
  eval (c₁ ⊗ c₂) (x , y) = (eval c₁ x , eval c₂ y)
  eval (η {b}) v = v , ((singleton v) , (λ x → tt))
  eval (ε {b}) (w , c) = w

  evalB :  {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → ⟦ b₂ ⟧ → ⟦ b₁ ⟧
  evalB uniti₊ (inj₁ ())
  evalB uniti₊ (inj₂ v) = v
  evalB unite₊ v = inj₂ v
  evalB swap₊ (inj₁ x) = inj₂ x
  evalB swap₊ (inj₂ y) = inj₁ y
  evalB assocr₊ (inj₁ x) = inj₁ (inj₁ x)
  evalB assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalB assocr₊ (inj₂ (inj₂ x)) = inj₂ x
  evalB assocl₊ (inj₁ (inj₁ x)) = inj₁ x
  evalB assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalB assocl₊ (inj₂ y) = inj₂ (inj₂ y)
  evalB uniti⋆ (tt , x) = x
  evalB unite⋆ v = ( tt , v)
  evalB swap⋆ (v₁ , v₂) = (v₂ , v₁)
  evalB assocr⋆ (x , (y , z)) = ((x , y), z)
  evalB assocl⋆ ((x , y), z) = (x , (y , z))
  evalB id⟷ v = v
  evalB (sym c) v = eval c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (inj₁ x) = inj₁ (evalB c₁ x)
  evalB (c₁ ⊕ c₂) (inj₂ y) = inj₂ (evalB c₂ y)
  evalB (c₁ ⊗ c₂) (x , y) = (evalB c₁ x , evalB c₂ y)
  evalB (η {b}) (w , c) = w
  evalB (ε {b}) v = v , ((singleton v) , (λ x → tt))

-- they are properly inverse of each other
-- easy direction
η∘ε : {b : B} (v : ⟦ b ⟧) → eval {b} (η ◎ ε) v ≡ v
η∘ε _ = refl

-- hard direction.
ε∘η : {b : B} (v : ⟦ b ⟧) → { w : Σ < v > (λ _ → < v > → ⊤) } 
      → (eval {DPAIR b (leftIdemp b) } {_} (ε ◎ η) (v , w)) ≡ (v , w)
ε∘η {b} v {(singleton .v , r )} = cong f {v , v , (singleton v)} refl
    where f : Σ ⟦ b ⟧ (λ x → Σ ⟦ b ⟧ (λ y → < v >)) → 
                Σ ⟦ b ⟧ (λ z → Σ < z > (λ x → < z > → ⊤ ))
          f (_ , (_ , j)) = (v , j , r)

-- Now need to write some actual programs...