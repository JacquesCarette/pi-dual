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
  NEG   : B → B
  TIMES : B → B → B
  RECIP : B → B

⟦_⟧ : B → Set
⟦ ZERO ⟧         = ⊥
⟦ ONE ⟧          = ⊤
⟦ PLUS b1 b2 ⟧   = ⟦ b1 ⟧ ⊎ ⟦ b2 ⟧
⟦ NEG b ⟧        = {!!} 
⟦ TIMES b1 b2 ⟧  = ⟦ b1 ⟧ × ⟦ b2 ⟧
⟦ RECIP b ⟧      = {!!} 


-- Define module over a ring (the types bot, top, disjoint union, and product
-- do form a ring as shown in the type-iso library) 

module MR(C : CommutativeRing Level.zero Level.zero) where

  open Data.Nat using (ℕ; zero; suc; _*_)
  open Data.Vec using ([]; _∷_; map; _++_)

  R-module : Set → ℕ → Set
  R-module c dim = Vec c dim 

  zeroV : ∀ {b : Set} → R-module b 0
  zeroV = []

  tensorV : {b₁ b₂ : Set } {m₁ m₂ : ℕ} → 
            R-module b₁ m₁ → R-module b₂ m₂ → 
            R-module (b₁ × b₂) (m₁ * m₂)
  tensorV [] _ = []
  tensorV (x ∷ xs) ys = (map (λ y → (x , y)) ys) ++ (tensorV xs ys)

open MR

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
  η₊      : { b : B } → ZERO ⟷ PLUS (NEG b) b
  ε₊      : { b : B } → PLUS b (NEG b) ⟷ ZERO
  refe⋆   : { b : B } → RECIP (RECIP b) ⟷ b
  refi⋆   : { b : B } → b ⟷ RECIP (RECIP b) 
  rile⋆   : { b : B } → TIMES b (TIMES b (RECIP b)) ⟷ b
  rili⋆   : { b : B } → b ⟷ TIMES b (TIMES b (RECIP b)) 
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

--

neg : {b₁ b₂ : B} → (b₁ ⟷ b₂) → (NEG b₁ ⟷ NEG b₂) 
neg {b₁} {b₂} c =              -- -b1
  uniti₊ ◎                     -- 0 + (-b1)
  (η₊ {b₂} ⊕ id⟷) ◎           -- (-b2 + b2) + (-b1)
  ((id⟷ ⊕ sym c) ⊕ id⟷) ◎    -- (-b2 + b1) + (-b1)
  assocr₊ ◎                    -- (-b2) + (b1 + (-b1))
  (id⟷ ⊕ ε₊) ◎                -- (-b2) + 0
  swap₊ ◎                      -- 0 + (-b2)
  unite₊                       -- -b2

--

mul0 : {b : B} → TIMES ZERO b ⟷ ZERO
mul0 =                    -- 0*b
  uniti₊ ◎                  --  0 + 0*b
  (η₊ ⊕ id⟷) ◎        -- (-(0*b) + 0*b) + 0*b
  assocr₊ ◎              -- -(0*b) + (0*b + 0*b)
  (id⟷ ⊕ factor) ◎  -- -(0*b) + (0+0)*b
  (id⟷ ⊕ (unite₊ ⊗ id⟷)) ◎  -- -(0*b) + 0*b
  swap₊ ◎  ε₊ -- 0

inv0 : TIMES ZERO (RECIP ZERO) ⟷ ZERO
inv0 = mul0 

--

recip : {b₁ b₂ : B} → (b₁ ⟷ b₂) → (RECIP b₁ ⟷ RECIP b₂) 
recip {b₁} {b₂} c =          -- 1/a
  rili⋆ {RECIP b₁} ◎         -- 1/a * (1/a * 1/1/a)
  (id⟷ ⊗ (id⟷ ⊗ refe⋆)) ◎   -- 1/a * (1/a * a)
  assocl⋆ ◎                  -- (1/a * 1/a) * a
  (id⟷ ⊗ reciplem c) ◎     -- (1/a * 1/a) * (a * ((a * 1/b) * (b * 1/b)))
  assocl⋆ ◎                  -- (((1/a * 1/a) * a) * ((a * 1/b) * (b * 1/b)))
  ((id⟷ ⊗ refi⋆ ) ⊗ id⟷) ◎   -- (((1/a *1/a) * 1/(1/a)) * ((a * 1/b) * (b * 1/b))
  ((assocr⋆ ◎ rile⋆ ) ⊗ (id⟷ ⊗ ((sym c) ⊗ id⟷))) ◎ -- 1/a * ((a * 1/b) * (a * 1/b))
  (id⟷ ⊗ (assocr⋆ ◎ (id⟷ ⊗ midtofront))) ◎ -- 1/a * (a * (a * (1/b * 1/b)))
  (assocl⋆ ◎ assocl⋆) ◎                      -- ((1/a * a) * a) * (1/b * 1/b)
  (((swap⋆ ⊗ id⟷) ◎ swap⋆) ⊗ id⟷) ◎         -- ((a * (a * 1/a)) * (1/b * 1/b))
  (rile⋆ ⊗ id⟷ ) ◎                           -- a * (1/b * 1/b)
  ((c ◎ refi⋆ ) ⊗ id⟷) ◎ swap⋆ ◎             -- (1/b * 1/b) * 1/(1/b)
  assocr⋆ ◎ rile⋆                             -- 1/b
  where 
    reciplem : {b₁ b₂ : B} → (b₁ ⟷ b₂) → (b₁ ⟷ (TIMES b₁ (TIMES (TIMES b₁ (RECIP b₂)) (TIMES b₂ (RECIP b₂)))))
    reciplem {b₁} {b₂} c =  c ◎                       -- b
      rili⋆ ◎                                -- b * (b * 1/b)
      (rili⋆ ⊗ id⟷) ◎                        -- (b * (b * 1/b)) * (b * 1/b)
      (((sym c) ⊗ ((sym c) ⊗ id⟷)) ⊗ id⟷) ◎ -- ((a * (a * 1/b)) * (b * 1/b))  
      assocr⋆                                -- a * ((a * 1/b) * (b * 1/b))


--

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
adjoint η₊        = swap₊ ◎ ε₊
adjoint ε₊        = η₊ ◎ swap₊
adjoint refe⋆     = refi⋆
adjoint refi⋆     = refe⋆
adjoint rile⋆     = rili⋆
adjoint rili⋆     = rile⋆
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
eval η₊ ()
eval ε₊ (inj₁ x) = {!!}
eval ε₊ (inj₂ y) = {!!}
eval refe⋆ v = {!!}
eval refi⋆ v = {!!}
eval rile⋆ v = {!!}
eval rili⋆ v = {!!}
eval id⟷ v = v
eval (sym c) v = eval (adjoint c) v
eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

------------------------------------------------------------------------------
-- Define the alternative semantics based on small-step semantics

------------------------------------------------------------------------------
-- Connect with Algebra

⟷IsEquivalence : IsEquivalence _⟷_
⟷IsEquivalence = record {
    refl = id⟷ ;
    sym = sym  ;
    trans = _◎_ 
  } 

+IsSemigroup : IsSemigroup _⟷_ PLUS
+IsSemigroup = record {
    isEquivalence = ⟷IsEquivalence ;
    assoc = λ x y z → assocr₊ {x} {y} {z} ;
    ∙-cong = _⊕_
  }

+0IsMonoid : IsMonoid _⟷_ PLUS ZERO
+0IsMonoid = record {
    isSemigroup = +IsSemigroup ;
    identity = ((λ x → unite₊ {x}) , 
                (λ x → swap₊ ◎ unite₊ {x}))
  }

+0IsCommutativeMonoid : IsCommutativeMonoid _⟷_ PLUS ZERO
+0IsCommutativeMonoid = record {
    isSemigroup = +IsSemigroup ;
    identityˡ = λ x → unite₊ {x} ;
    comm = λ x y → swap₊ {x} {y} 
  }

+0CommutativeMonoid : CommutativeMonoid _ _
+0CommutativeMonoid = record {
  Carrier = B ;
  _≈_ = _⟷_ ; 
  _∙_ = PLUS ;
  ε = ZERO ;
  isCommutativeMonoid = +0IsCommutativeMonoid  
  }

-- 

⋆IsSemigroup : IsSemigroup _⟷_ TIMES
⋆IsSemigroup = record {
    isEquivalence = ⟷IsEquivalence ;
    assoc = λ x y z → assocr⋆ {x} {y} {z} ;
    ∙-cong = _⊗_
  }

⋆1IsMonoid : IsMonoid _⟷_ TIMES ONE
⋆1IsMonoid = record {
    isSemigroup = ⋆IsSemigroup ;
    identity = ((λ x → unite⋆ {x}) , 
                (λ x → swap⋆ ◎ unite⋆ {x}))
  }  

⋆1IsCommutativeMonoid : IsCommutativeMonoid _⟷_ TIMES ONE
⋆1IsCommutativeMonoid = record {
    isSemigroup = ⋆IsSemigroup ;
    identityˡ = λ x → unite⋆ {x} ;
    comm = λ x y → swap⋆ {x} {y} 
  }  

⋆1CommutativeMonoid : CommutativeMonoid _ _ 
⋆1CommutativeMonoid = record {
  Carrier = B ;
  _≈_ = _⟷_ ; 
  _∙_ = TIMES ;
  ε = ONE ;
  isCommutativeMonoid = ⋆1IsCommutativeMonoid
  }

record IsCommutativeSemiringWithoutAnnihilatingZero
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (0# 1# : A) 
       : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    *-isCommutativeMonoid : IsCommutativeMonoid ≈ * 1#
    distrib               : * DistributesOver +

B-isCommutativeSemiringWithoutAnnihilatingZero
    : IsCommutativeSemiringWithoutAnnihilatingZero _⟷_ PLUS TIMES ZERO ONE
B-isCommutativeSemiringWithoutAnnihilatingZero = record {
    +-isCommutativeMonoid = +0IsCommutativeMonoid ;
    *-isCommutativeMonoid = ⋆1IsCommutativeMonoid ;
    distrib = ( (λ x y z → dist' {x} {y} {z}) ,
                (λ x y z → dist {y} {z} {x} ))
    }

-- 

+0-IsGroup : IsGroup _⟷_ PLUS ZERO NEG
+0-IsGroup = record {
  isMonoid = +0IsMonoid ; 
  inverse = ( (λ x → swap₊ ◎ ε₊ {x}) , 
              (λ x → ε₊ {x}) );
  ⁻¹-cong = neg
  }

+0-IsAbelianGroup : IsAbelianGroup _⟷_ PLUS ZERO NEG
+0-IsAbelianGroup = record {
    isGroup = +0-IsGroup ; 
    comm = λ x y → swap₊ {x} {y} 
  }

B-IsRing : IsRing _⟷_ PLUS TIMES NEG ZERO ONE
B-IsRing = record {
    +-isAbelianGroup = +0-IsAbelianGroup ; 
    *-isMonoid = ⋆1IsMonoid ;
    distrib = ( (λ x y z → dist' {x} {y} {z}) ,
                (λ x y z → dist {y} {z} {x} ))
  }

B-IsCommutativeRing : IsCommutativeRing _⟷_ PLUS TIMES NEG ZERO ONE
B-IsCommutativeRing = record {
    isRing = B-IsRing ;
    *-comm = λ x y → swap⋆ {x} {y} 
  }

-- 

B-CommutativeRing : CommutativeRing _ _
B-CommutativeRing = record {
    Carrier = B ;
    _≈_ = _⟷_ ; 
    _+_ = PLUS ;
    _*_ = TIMES ;
    -_ = NEG ;
    0# = ZERO ;
    1# = ONE ;
    isCommutativeRing = B-IsCommutativeRing
  } 

-- 

record IsMeadow
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (- r : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +*-isCommutativeRing : IsCommutativeRing ≈ + * - 0# 1#
    *-refl-l : ∀ x → ≈ (r (r x)) x
    *-refl-r : ∀ x → ≈ x (r (r x))
    *-ril-l : ∀ x → ≈ (* x (* x (r x))) x
    *-ril-r : ∀ x → ≈ x (* x (* x (r x)))
    r-cong : ∀ x y → ≈ x y → ≈ (r x) (r y)

record Meadow c ℓ : Set (suc (c ⊔ ℓ)) where
  field 
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    _+_ : Op₂ Carrier
    _*_ : Op₂ Carrier
    -_ : Op₁ Carrier
    r  : Op₁ Carrier
    0# : Carrier
    1# : Carrier
    isMeadow : IsMeadow _≈_ _+_ _*_ -_ r 0# 1#

B-/IsMeadow : IsMeadow _⟷_ PLUS TIMES NEG RECIP ZERO ONE
B-/IsMeadow = record {
    +*-isCommutativeRing = B-IsCommutativeRing ;
    *-refl-l = λ x → refe⋆ {x} ;
    *-refl-r = λ x → sym (refe⋆ {x}) ;
    *-ril-l = λ x → sym (rili⋆ {x}) ;
    *-ril-r = λ x → rili⋆ {x} ;
    r-cong = λ x y → recip {x} {y} 
  }

B-/Meadow : Meadow _ _
B-/Meadow = record {
    Carrier = B ;
    _≈_ = _⟷_ ;
    _+_ = PLUS ;
    _*_ = TIMES ; 
    -_ = NEG ;
    r  = RECIP ;
    0# = ZERO ;
    1# = ONE ;
    isMeadow = B-/IsMeadow
  }

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
 
------------------------------------------------------------------------------
-- Examples

BOOL : B
BOOL = PLUS ONE ONE

BOOL² : B
BOOL² = TIMES BOOL BOOL

BOOL³ : B
BOOL³ = TIMES BOOL BOOL² 

unitπ : ⟦ ONE ⟧
unitπ = tt

trueπ : ⟦ BOOL ⟧
trueπ = inj₁ tt

falseπ : ⟦ BOOL ⟧
falseπ = inj₂ tt

e0 : ⟦ BOOL² ⟧
e0 = (falseπ , falseπ)

e1 : ⟦ BOOL² ⟧
e1 = (falseπ , trueπ)

e2 : ⟦ BOOL² ⟧
e2 = (trueπ , falseπ)

e3 : ⟦ BOOL² ⟧
e3 = (trueπ , trueπ)

notπ : BOOL ⟷ BOOL
notπ = swap₊

ifc : { b : B } → (b ⟷ b) → (TIMES BOOL b ⟷ TIMES BOOL b)
ifc c = dist ◎ ((id⟷ ⊗ c) ⊕ id⟷) ◎ factor

cnot : BOOL² ⟷ BOOL²
cnot = ifc notπ

toffoli : BOOL³ ⟷ BOOL³
toffoli = ifc cnot

test1 : ⟦ BOOL³ ⟧
test1 = eval toffoli (trueπ , (trueπ , trueπ))

------------------------------------------------------------------------------
