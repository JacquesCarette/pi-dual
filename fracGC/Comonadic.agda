{-# OPTIONS --without-K #-}

module Comonadic where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Rational
  using (ℚ; _/_; _+_; _*_; _≢0)
  renaming (1/_ to recip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product -- using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Core using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; module ≡-Reasoning)
open import Category.Comonad

infix  30 _⟷_
infixr 50 _◎_

------------------------------------------------------------------------------
-- Pi with fractionals comonad

record Pointed (A : Set) (v : A) : Set where
  constructor ⇑
  field
    ● : A
    v≡● : v ≡ ● 

open Pointed

Recip : (A : Set) → (v : A) → Set
Recip A v = (w : A) → (v ≡ w) → ⊤

--

data U : Set 
⟦_⟧ : (A : U) → Set
data _⟷_ : U → U → Set 
eval : {A B : U} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧

data U where
  ZERO    : U
  ONE     : U
  PLUS    : U → U → U
  TIMES   : U → U → U
  POINTED : (A : U) → {v : ⟦ A ⟧} → U
  RECIP   : (A : U) → {v : ⟦ A ⟧} → U

⟦ ZERO ⟧ = ⊥ 
⟦ ONE ⟧ = ⊤
⟦ PLUS t₁ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ POINTED A {v} ⟧ = Pointed ⟦ A ⟧ v
⟦ RECIP A {v} ⟧ = Recip ⟦ A ⟧ v

data _⟷_ where
  unite₊l : {t : U} → PLUS ZERO t ⟷ t
  uniti₊l : {t : U} → t ⟷ PLUS ZERO t
  unite₊r : {t : U} → PLUS t ZERO ⟷ t
  uniti₊r : {t : U} → t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆l  : {t : U} → t ⟷ TIMES ONE t
  unite⋆r : {t : U} → TIMES t ONE ⟷ t
  uniti⋆r : {t : U} → t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → 
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : {t₁ t₂ t₃ : U} → 
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : {t₁ t₂ t₃ : U } →
            TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : {t₁ t₂ t₃ : U } →
            PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)
  -- comonad
  -- not informnation preserving; not reversible
  extract : {t : U} → {v : ⟦ t ⟧} → POINTED t {v} ⟷ t
  extend : {t₁ t₂ : U} → {v₁ : ⟦ t₁ ⟧} → 
           (c : POINTED t₁ {v₁} ⟷ t₂) →
           (POINTED t₁ {v₁} ⟷ POINTED t₂ {eval c (⇑ v₁ refl)})
  tensorl : {t₁ t₂ : U} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
           POINTED (TIMES t₁ t₂) {(v₁ , v₂)} ⟷
           TIMES (POINTED t₁ {v₁}) (POINTED t₂ {v₂})
  tensorr : {t₁ t₂ : U} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
           TIMES (POINTED t₁ {v₁}) (POINTED t₂ {v₂}) ⟷
           POINTED (TIMES t₁ t₂) {(v₁ , v₂)} 
           
  -- fractionals
  η : {t : U} → (v : ⟦ t ⟧) → ONE ⟷ TIMES (POINTED t {v}) (RECIP t {v})
  ε : {t : U} → (v : ⟦ t ⟧) → TIMES (POINTED t {v}) (RECIP t {v}) ⟷ ONE

eval unite₊l (inj₂ v) = v 
eval uniti₊l v  = inj₂ v 
eval unite₊r (inj₁ v) = v
eval uniti₊r v  = inj₁ v 
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v) 
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆l (tt , v) = v
eval uniti⋆l v = (tt , v)
eval unite⋆r (v , tt) = v
eval uniti⋆r v = (v , tt)
eval swap⋆ (v₁ , v₂)          = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbl () 
eval absorbr () 
eval factorzl () 
eval factorzr () 
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval distl (v , inj₁ v₁) = inj₁ (v , v₁)
eval distl (v , inj₂ v₂) = inj₂ (v , v₂) 
eval factorl (inj₁ (v , v₁)) = (v , inj₁ v₁)
eval factorl (inj₂ (v , v₂)) = (v , inj₂ v₂) 
eval id⟷ v = v
eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)
eval extract p = ● p
eval (extend {v₁ = v₁} c) p with ● p | v≡● p
eval (extend {v₁ = .v₂} c) p | v₂ | refl = ⇑ (eval c (⇑ v₂ refl)) refl
eval tensorl p with ● p | v≡● p
... | (v₁ , v₂) | refl = ⇑ v₁ refl , ⇑ v₂ refl 
eval tensorr (p₁ , p₂) with ● p₁ | v≡● p₁ | ● p₂ | v≡● p₂
... | v₁ | refl | v₂ | refl = ⇑ (v₁ , v₂) refl 
eval (η v) tt = ⇑ v refl , λ w v≡w → tt
eval (ε v) (p , f) = f (● p) (v≡● p)

------------------------------------------------------------------------------
-- Set up for examples

infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : U) {t₂ : U} {t₃ : U} →
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U) → {t : U} → (t ⟷ t)
_□ t = id⟷

TWO BOOL : U
TWO = PLUS ONE ONE
BOOL  = PLUS ONE ONE

BOOL² : U
BOOL² = TIMES BOOL BOOL

𝟚 : Set
𝟚 = ⟦ TWO ⟧

#f #t : 𝟚
#f = inj₁ tt
#t = inj₂ tt

lift : {t₁ t₂ : U} {v₁ : ⟦ t₁ ⟧} → 
       (c : t₁ ⟷ t₂) → (POINTED t₁ {v₁} ⟷ POINTED t₂ {eval c v₁})
lift c = extend (extract ◎ c) 

------------------------------------------------------------------------------
-- Examples

zigzag : ∀ b → POINTED TWO {b} ⟷ POINTED TWO {b}
zigzag b =
  lift uniti⋆l ◎                       -- POINTED (ONE * TWO)
  tensorl ◎                            -- POINTED ONE * POINTED TWO
  ((extract ◎ η b) ⊗ id⟷) ◎          -- (POINTED TWO * RECIP TWO) * POINTED TWO
  assocr⋆ ◎                            -- POINTED TWO * (RECIP TWO * POINTED TWO)
  (id⟷ ⊗ swap⋆) ◎                    -- POINTED TWO * (POINTED TWO * RECIP TWO)
  (id⟷ ⊗ ε b) ◎                      -- POINTED TWO * ONE
  unite⋆r 

test1 = eval (zigzag #f) (⇑ #f refl)      -- (⇑ #f refl)
-- test2 = eval (zigzag #f) (⇑ #t refl)   -- typechecks if given proof #f=#t
-- test3 = eval (zigzag #t) (⇑ #f refl)   -- typechecks if given proof #f=#t
test4 = eval (zigzag #t) (⇑ #t refl)      -- (⇑ #t refl) 

-- Conventional PI examples

NOT : BOOL ⟷ BOOL
NOT = swap₊

NEG1 NEG2 NEG3 NEG4 NEG5 : BOOL ⟷ BOOL
NEG1 = swap₊
NEG2 = id⟷ ◎ NOT
NEG3 = NOT ◎ NOT ◎ NOT
NEG4 = NOT ◎ id⟷
NEG5 = uniti⋆l ◎ swap⋆ ◎ (NOT ⊗ id⟷) ◎ swap⋆ ◎ unite⋆l
NEG6 = uniti⋆r ◎ (NOT ⊗ id⟷) ◎ unite⋆r -- same as above, but shorter

CNOT : BOOL² ⟷ BOOL²
CNOT = TIMES BOOL BOOL
         ⟷⟨ id⟷ ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ dist ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT) ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ factor ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ id⟷ ⟩
       TIMES BOOL BOOL □
  where x = ONE; y = ONE

TOFFOLI : TIMES BOOL BOOL² ⟷ TIMES BOOL BOOL²
TOFFOLI = TIMES BOOL BOOL²
            ⟷⟨ id⟷ ⟩
          TIMES (PLUS x y) BOOL²
            ⟷⟨ dist ⟩
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ factor ⟩
          TIMES (PLUS x y) BOOL²
            ⟷⟨ id⟷ ⟩
         TIMES BOOL BOOL² □
  where x = ONE; y = ONE

PERES : TIMES (TIMES BOOL BOOL) BOOL ⟷ TIMES (TIMES BOOL BOOL) BOOL
PERES = (id⟷ ⊗ NOT) ◎ assocr⋆ ◎ (id⟷ ⊗ swap⋆) ◎
        TOFFOLI ◎
        (id⟷ ⊗ (NOT ⊗ id⟷)) ◎
        TOFFOLI ◎
        (id⟷ ⊗ swap⋆) ◎ (id⟷ ⊗ (NOT ⊗ id⟷)) ◎
        TOFFOLI ◎
        (id⟷ ⊗ (NOT ⊗ id⟷)) ◎ assocl⋆

SWAP12 SWAP23 SWAP13 ROTL ROTR :
  PLUS ONE (PLUS ONE ONE) ⟷ PLUS ONE (PLUS ONE ONE)
SWAP12 = assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊
SWAP23 = id⟷ ⊕ swap₊
SWAP13 = SWAP23 ◎ SWAP12 ◎ SWAP23
ROTR   = SWAP12 ◎ SWAP23
ROTL   = SWAP13 ◎ SWAP23

t3 : ∀ {b₁ b₂} → 
     POINTED (TIMES BOOL BOOL²) {(#f , (b₁ , b₂))} ⟷
     POINTED (TIMES BOOL BOOL²) {(#f , (b₁ , b₂))}
t3 = lift  TOFFOLI

{--
The following do not typecheck. Good

t4 : POINTED (TIMES BOOL BOOL²) {(#t , (#f , #f))} ⟷
     POINTED (TIMES BOOL BOOL²) {(#t , (#f , #t))}
t4 = lift TOFFOLI

t5 : ∀ {b₁ b₂} → 
     POINTED (TIMES BOOL BOOL²) {(b₁ , (#f , b₂))} ⟷
     POINTED (TIMES BOOL BOOL²) {(b₁ , (#f , b₂))}
t5 = lift  TOFFOLI
--}

t6 : ∀ {b} →
     POINTED (TIMES BOOL BOOL²) {(#t , (#t , b))} ⟷
     POINTED (TIMES BOOL BOOL²) {(#t , (#t , eval NOT b))}
t6 = lift TOFFOLI

-- Ancilla examples from literature

-- Fig. 2 in Ricercar

CONTROLLED : {A : U} → (A ⟷ A) → (TIMES BOOL A ⟷ TIMES BOOL A)
CONTROLLED c = dist ◎ (id⟷ ⊕ (id⟷ ⊗ c)) ◎ factor

fig2a : TIMES BOOL (TIMES BOOL (TIMES BOOL BOOL)) ⟷ 
        TIMES BOOL (TIMES BOOL (TIMES BOOL BOOL))
fig2a = CONTROLLED (CONTROLLED (CONTROLLED NOT))

fig2b : ∀ {v w} →
        POINTED (TIMES BOOL (TIMES BOOL (TIMES BOOL BOOL))) {v} ⟷ 
        POINTED (TIMES BOOL (TIMES BOOL (TIMES BOOL BOOL))) {w}
fig2b = lift uniti⋆r ◎
        tensorl ◎ (tensorl ⊗ id⟷) ◎ ((id⟷ ⊗ tensorl) ⊗ id⟷) ◎ 
        {!!}

------------------------------------------------------------------------------

{--
zigzag : ∀ b → POINTED TWO {b} ⟷ POINTED TWO {b}
zigzag b =
  lift uniti⋆l ◎                       -- POINTED (ONE * TWO)
  tensorl ◎                            -- POINTED ONE * POINTED TWO
  ((extract ◎ η b) ⊗ id⟷) ◎          -- (POINTED TWO * RECIP TWO) * POINTED TWO
  assocr⋆ ◎                            -- POINTED TWO * (RECIP TWO * POINTED TWO)
  (id⟷ ⊗ swap⋆) ◎                    -- POINTED TWO * (POINTED TWO * RECIP TWO)
  (id⟷ ⊗ ε b) ◎                      -- POINTED TWO * ONE
  unite⋆r 
--}
