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
  using (_≡_; refl; cong₂; module ≡-Reasoning)
open import Category.Comonad

-- infix  30 _⟷_
-- infixr 50 _◎_

------------------------------------------------------------------------------
-- Pi with fractionals comonad

record Pointed (A : Set) : Set where
  constructor ⇑
  field
    ● : A

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
⟦ POINTED A ⟧ = Pointed ⟦ A ⟧ 
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
  extract : {t : U} {v : ⟦ t ⟧} → POINTED t {v} ⟷ t
  extend : {t₁ t₂ : U} {v₁ : ⟦ t₁ ⟧} → 
           (c : POINTED t₁ {v₁} ⟷ t₂) →
           (POINTED t₁ {v₁} ⟷ POINTED t₂ {eval c (⇑ v₁)})
  -- fractionals
  η : {t : U} {v : ⟦ t ⟧} → ONE ⟷ TIMES (POINTED t {v}) (RECIP t {v})
  ε : {t : U} {v : ⟦ t ⟧} → TIMES (POINTED t {v}) (RECIP t {v}) ⟷ ONE


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
eval (extend c) p = ⇑ (eval c (⇑ (● p)))
eval (η {t} {v}) tt = ⇑ v , λ w v≡w → tt
eval (ε {t} {v}) (p , f) = f v refl 

{--

------------------------------------------------------------------------------
-- Pointed types comonad


pcomonad : RawComonad Pointed
pcomonad = record {
  extract = ●; 
  extend = λ f P → ⇑ (f P) 
  }

open RawComonad pcomonad

eval● : {A B : U} → (A ⟷ B) → Pointed ⟦ A ⟧ → Pointed ⟦ B ⟧
eval● c v = extend (λ p → eval c (extract p)) v

-- Write in comonadic style now

data _⬌_ : {A B : U} → Pointed ⟦ A ⟧ → Pointed ⟦ B ⟧ → Set where
  lift : {A B : U} {v : ⟦ A ⟧} → 
         (c : A ⟷ B) → ⇑ v ⬌ eval● c (⇑ v)

-- Examples

infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : U) {t₂ : U} {t₃ : U} →
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U) → {t : U} → (t ⟷ t)
_□ t = id⟷

BOOL : U
BOOL  = PLUS ONE ONE

FALSE TRUE : ⟦ BOOL ⟧
FALSE = inj₁ tt
TRUE = inj₂ tt

POINTED : {A : U} → ⟦ A ⟧ → Pointed ⟦ A ⟧
POINTED v = record { ● = v } 

BOOL² : U
BOOL² = TIMES BOOL BOOL

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

--

t1 : Pointed ⟦ BOOL ⟧ 
t1 = eval● NOT (POINTED FALSE)

t2 : Pointed ⟦ TIMES BOOL BOOL² ⟧ 
t2 = eval● TOFFOLI (POINTED (TRUE , (TRUE , FALSE)))

t3 : ⇑ (TRUE , (TRUE , FALSE)) ⬌ ⇑ (TRUE , (TRUE , TRUE))
t3 = lift TOFFOLI

--Incorrect so doesn't type check
--t4 : ⇑ (TRUE , (FALSE , FALSE)) ⬌ ⇑ (TRUE , (FALSE , TRUE))
--t4 = lift TOFFOLI

t5 : ∀ {b₁ b₂} → ⇑ (FALSE , (b₁ , b₂)) ⬌ ⇑ (FALSE , (b₁ , b₂))
t5 = lift TOFFOLI

--t6 : ∀ {b₁ b₂} → ⇑ (b₁ , (FALSE , b₂)) ⬌ ⇑ (b₁ , (FALSE , b₂))
--t6 = lift TOFFOLI

t7 : ∀ {b} → ⇑ (TRUE , (TRUE , b)) ⬌ ⇑ (TRUE , (TRUE , eval NOT b))
t7 = lift TOFFOLI

{--

------------------------------------------------------------------------------
-- Fractionals

infixr 20 _◡_
infix 30 _⬌_
infixl 40 _⊞₁_ _⊞₂_
infixl 50 _⊠_ 

data U/ : Set where
  ret  : {A : U} → Pointed ⟦ A ⟧ → U/
  1/ : U/ → U/
  _⊞₁_  : U/ → U/ → U/
  _⊞₂_  : U/ → U/ → U/
  _⊠_  : U/ → U/ → U/

⟦_⟧/ : U/ → Σ[ A ∈ Set ] A
⟦ ret {A} r ⟧/ = ⟦ A ⟧ , ● r
⟦ 1/ P ⟧/ with ⟦ P ⟧/
... | S , v = (Σ[ x ∈ S ] x ≡ v → ⊤), λ { (w , w≡v) → tt}
⟦ P₁ ⊞₁ P₂ ⟧/ with ⟦ P₁ ⟧/ | ⟦ P₂ ⟧/
... | (S₁ , v₁) | (S₂ , v₂) = (S₁ ⊎ S₂) , inj₁ v₁
⟦ P₁ ⊞₂ P₂ ⟧/ with ⟦ P₁ ⟧/ | ⟦ P₂ ⟧/
... | (S₁ , v₁) | (S₂ , v₂) = (S₁ ⊎ S₂) , inj₂ v₂
⟦ P₁ ⊠ P₂ ⟧/ with ⟦ P₁ ⟧/ | ⟦ P₂ ⟧/
... | (S₁ , v₁) | (S₂ , v₂) = (S₁ × S₂) , (v₁ , v₂)

data _⬌_ : U/ → U/ → Set where
  lift : {A B : U} {a : ⟦ A ⟧} {b : ⟦ B ⟧} →
         (A ⟷ B) → (ret (⇑ a) ⬌ ret (⇑ b))
  split : {A B : U} {a : ⟦ A ⟧} {b : ⟦ B ⟧} →
         ret (⇑ (a , b)) ⬌ ret (⇑ a) ⊠ ret (⇑ b)
  unsplit : {A B : U} {a : ⟦ A ⟧} {b : ⟦ B ⟧} →
         ret (⇑ a) ⊠ ret (⇑ b) ⬌ ret (⇑ (a , b)) 
  swap⋆/   : {T₁ T₂ : U/} → T₁ ⊠ T₂ ⬌ T₂ ⊠ T₁
  assocr⋆/ : {T₁ T₂ T₃ : U/} → (T₁ ⊠ T₂) ⊠ T₃ ⬌ T₁ ⊠ (T₂ ⊠ T₃)
  _◡_ : {PA₁ PA₂ PA₃ : U/} →
        (PA₁ ⬌ PA₂) → (PA₂ ⬌ PA₃) → (PA₁ ⬌ PA₃)
  _➕₁_ : {T₁ T₂ T₃ T₄ : U/} → (T₁ ⬌ T₃) → (T₂ ⬌ T₄) → (T₁ ⊞₁ T₂ ⬌ T₃ ⊞₁ T₄)
  _➕₂_ : {T₁ T₂ T₃ T₄ : U/} → (T₁ ⬌ T₃) → (T₂ ⬌ T₄) → (T₁ ⊞₂ T₂ ⬌ T₃ ⊞₂ T₄)
  _✖_ : {T₁ T₂ T₃ T₄ : U/} → (T₁ ⬌ T₃) → (T₂ ⬌ T₄) → (T₁ ⊠ T₂ ⬌ T₃ ⊠ T₄)
  η : {PA : U/} → ret (⇑ tt) ⬌ PA ⊠ 1/ PA
  ε : {PA : U/} → PA ⊠ 1/ PA ⬌ ret (⇑ tt)

zigzag : {A : U} {v : ⟦ A ⟧} → ret (⇑ v) ⬌ ret (⇑ v)
zigzag {v = v} =
  (lift {b = (tt , v)} uniti⋆l) ◡
  split ◡
  (η ✖ lift {b = v} id⟷ ) ◡
  assocr⋆/ ◡
  (lift {b = v} id⟷ ✖ swap⋆/) ◡
  (lift {b = v} id⟷ ✖ ε) ◡
  unsplit ◡
  lift unite⋆r

------------------------------------------------------------------------------

{--
-- Use space denotation: the denotation of a fractional type is a base
-- type and a number representing the heap size.
⟦_⟧/ : U/ → Set × (Σ[ p ∈  ℚ ] (∣ ℚ.numerator p ∣ ≢0))
⟦ ret {A} _ ⟧/ = ⟦ A ⟧ , ∣ A ∣U , {!!}
⟦ 1/ P ⟧/ with ⟦ P ⟧/
... | (S , n , notz) = S , recip n {notz}, {!!} 
⟦ P₁ ⊞ P₂ ⟧/ with ⟦ P₁ ⟧/ | ⟦ P₂ ⟧/
... | (S₁ , n₁ , notz1) | (S₂ , n₂ , notz2) = (S₁ ⊎ S₂) , (n₁ + n₂) , {!!} 
⟦ P₁ ⊠ P₂ ⟧/ with ⟦ P₁ ⟧/ | ⟦ P₂ ⟧/
... | (S₁ , n₁ , notz1) | (S₂ , n₂ , notz2) = (S₁ × S₂) , (n₁ * n₂) , {!!} 
--}

------------------------------------------------------------------------------
--}
--}
