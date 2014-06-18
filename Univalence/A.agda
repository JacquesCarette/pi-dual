{-# OPTIONS --without-K #-}

module A where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

infix  4  _≡_   -- propositional equality
infixr 10 _◎_
infixr 30 _⟷_

------------------------------------------------------------------------------
-- Our own version of refl that makes 'a' explicit

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

sym : ∀ {ℓ} {A : Set ℓ} {a b : A} → (a ≡ b) → (b ≡ a)
sym {a = a} {b = .a} (refl .a) = refl a

{--

Just confirming that the following does not typecheck!

proof-irrelevance : {A : Set} {x y : A} (p q : x ≡ y) →  p ≡ q
proof-irrelevance (refl x) (refl .x) = refl (refl x)

--}

------------------------------------------------------------------------------
{--
Types are higher groupoids:
- 0 is empty
- 1 has one element and one path refl
- sum type is disjoint union; paths are component wise
- product type is cartesian product; paths are pairs of paths
--}

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

-- Points 

⟦_⟧ : U → Set
⟦ ZERO ⟧       = ⊥
⟦ ONE ⟧        = ⊤
⟦ PLUS t t' ⟧  = ⟦ t ⟧ ⊎ ⟦ t' ⟧
⟦ TIMES t t' ⟧ = ⟦ t ⟧ × ⟦ t' ⟧

BOOL : U
BOOL = PLUS ONE ONE

BOOL² : U
BOOL² = TIMES BOOL BOOL

TRUE : ⟦ BOOL ⟧
TRUE = inj₁ tt

FALSE : ⟦ BOOL ⟧
FALSE = inj₂ tt

------------------------------------------------------------------------------
-- Paths connect points in t₁ and t₂ if there is an isomorphism between the
-- types t₁ and t₂. The family ⟷ plays the role of identity types in HoTT

data _⟷_ : U → U → Set where
  unite₊  : {t : U} → PLUS ZERO t ⟷ t
  uniti₊  : {t : U} → t ⟷ PLUS ZERO t
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆  : {t : U} → t ⟷ TIMES ONE t
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  distz   : {t : U} → TIMES ZERO t ⟷ ZERO
  factorz : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → 
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) 
  factor  : {t₁ t₂ t₃ : U} → 
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  id⟷    : {t : U} → t ⟷ t
  sym⟷   : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

cond : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → 
       ((TIMES BOOL t₁) ⟷ (TIMES BOOL t₂))
cond f g = dist ◎ ((id⟷ ⊗ f) ⊕ (id⟷ ⊗ g)) ◎ factor 

controlled : {t : U} → (t ⟷ t) → ((TIMES BOOL t) ⟷ (TIMES BOOL t))
controlled f = cond f id⟷

cnot : BOOL² ⟷ BOOL²
cnot = controlled swap₊

-- Paths: each combinator defines a space of paths between its end points

mutual

  Paths : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧ → Set
  Paths unite₊ (inj₁ ()) 
  Paths unite₊ (inj₂ v) v' = (v ≡ v')
  Paths uniti₊ v (inj₁ ())
  Paths uniti₊ v (inj₂ v') = (v ≡ v')
  Paths swap₊ (inj₁ v) (inj₁ v') = ⊥
  Paths swap₊ (inj₁ v) (inj₂ v') = (v ≡ v')
  Paths swap₊ (inj₂ v) (inj₁ v') = (v ≡ v')
  Paths swap₊ (inj₂ v) (inj₂ v') = ⊥
  Paths assocl₊ (inj₁ v) (inj₁ (inj₁ v')) = (v ≡ v')
  Paths assocl₊ (inj₁ v) (inj₁ (inj₂ v')) = ⊥
  Paths assocl₊ (inj₁ v) (inj₂ v') = ⊥
  Paths assocl₊ (inj₂ (inj₁ v)) (inj₁ (inj₁ v')) = ⊥
  Paths assocl₊ (inj₂ (inj₁ v)) (inj₁ (inj₂ v')) = (v ≡ v')
  Paths assocl₊ (inj₂ (inj₁ v)) (inj₂ v') = ⊥
  Paths assocl₊ (inj₂ (inj₂ v)) (inj₁ v') = ⊥
  Paths assocl₊ (inj₂ (inj₂ v)) (inj₂ v') = (v ≡ v')
  Paths assocr₊ (inj₁ (inj₁ v)) (inj₁ v') = (v ≡ v')
  Paths assocr₊ (inj₁ (inj₁ v)) (inj₂ v') = ⊥
  Paths assocr₊ (inj₁ (inj₂ v)) (inj₁ v') = ⊥
  Paths assocr₊ (inj₁ (inj₂ v)) (inj₂ (inj₁ v')) = (v ≡ v')
  Paths assocr₊ (inj₁ (inj₂ v)) (inj₂ (inj₂ v')) = ⊥
  Paths assocr₊ (inj₂ v) (inj₁ v') = ⊥
  Paths assocr₊ (inj₂ v) (inj₂ (inj₁ v')) = ⊥
  Paths assocr₊ (inj₂ v) (inj₂ (inj₂ v')) = (v ≡ v')
  Paths unite⋆ (tt , v) v' = (v ≡ v')
  Paths uniti⋆ v (tt , v') = (v ≡ v')
  Paths swap⋆ (v₁ , v₂) (v₂' , v₁') = (v₁ ≡ v₁') × (v₂ ≡ v₂')
  Paths assocl⋆ (v₁ , (v₂ , v₃)) ((v₁' , v₂') , v₃') = 
    (v₁ ≡ v₁') × (v₂ ≡ v₂') × (v₃ ≡ v₃')
  Paths assocr⋆ ((v₁ , v₂) , v₃) (v₁' , (v₂' , v₃')) = 
    (v₁ ≡ v₁') × (v₂ ≡ v₂') × (v₃ ≡ v₃')
  Paths distz (() , v)
  Paths factorz ()
  Paths dist (inj₁ v₁ , v₃) (inj₁ (v₁' , v₃')) = (v₁ ≡ v₁') × (v₃ ≡ v₃')
  Paths dist (inj₁ v₁ , v₃) (inj₂ (v₂' , v₃')) = ⊥
  Paths dist (inj₂ v₂ , v₃) (inj₁ (v₁' , v₃')) = ⊥
  Paths dist (inj₂ v₂ , v₃) (inj₂ (v₂' , v₃')) = (v₂ ≡ v₂') × (v₃ ≡ v₃')
  Paths factor (inj₁ (v₁ , v₃)) (inj₁ v₁' , v₃') = 
    (v₁ ≡ v₁') × (v₃ ≡ v₃')
  Paths factor (inj₁ (v₁ , v₃)) (inj₂ v₂' , v₃') = ⊥
  Paths factor (inj₂ (v₂ , v₃)) (inj₁ v₁' , v₃') = ⊥
  Paths factor (inj₂ (v₂ , v₃)) (inj₂ v₂' , v₃') = 
    (v₂ ≡ v₂') × (v₃ ≡ v₃')
  Paths {t} id⟷ v v' = (v ≡ v')
  Paths (sym⟷ c) v v' = PathsB c v v'
  Paths (_◎_ {t₁} {t₂} {t₃} c₁ c₂) v v' = 
    Σ[ u ∈ ⟦ t₂ ⟧ ] (Paths c₁ v u × Paths c₂ u v')
  Paths (c₁ ⊕ c₂) (inj₁ v) (inj₁ v') = Paths c₁ v v'
  Paths (c₁ ⊕ c₂) (inj₁ v) (inj₂ v') = ⊥
  Paths (c₁ ⊕ c₂) (inj₂ v) (inj₁ v') = ⊥
  Paths (c₁ ⊕ c₂) (inj₂ v) (inj₂ v') = Paths c₂ v v'
  Paths (c₁ ⊗ c₂) (v₁ , v₂) (v₁' , v₂') = 
    Paths c₁ v₁ v₁' × Paths c₂ v₂ v₂'

  PathsB : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧ → Set
  PathsB unite₊ v (inj₁ ())
  PathsB unite₊ v (inj₂ v') = (v ≡ v')
  PathsB uniti₊ (inj₁ ()) 
  PathsB uniti₊ (inj₂ v) v' = (v ≡ v')
  PathsB swap₊ (inj₁ v) (inj₁ v') = ⊥
  PathsB swap₊ (inj₁ v) (inj₂ v') = (v ≡ v')
  PathsB swap₊ (inj₂ v) (inj₁ v') = (v ≡ v')
  PathsB swap₊ (inj₂ v) (inj₂ v') = ⊥
  PathsB assocl₊ (inj₁ (inj₁ v)) (inj₁ v') = (v ≡ v')
  PathsB assocl₊ (inj₁ (inj₁ v)) (inj₂ v') = ⊥
  PathsB assocl₊ (inj₁ (inj₂ v)) (inj₁ v') = ⊥
  PathsB assocl₊ (inj₁ (inj₂ v)) (inj₂ (inj₁ v')) = (v ≡ v')
  PathsB assocl₊ (inj₁ (inj₂ v)) (inj₂ (inj₂ v')) = ⊥
  PathsB assocl₊ (inj₂ v) (inj₁ v') = ⊥
  PathsB assocl₊ (inj₂ v) (inj₂ (inj₁ v')) = ⊥
  PathsB assocl₊ (inj₂ v) (inj₂ (inj₂ v')) = (v ≡ v')
  PathsB assocr₊ (inj₁ v) (inj₁ (inj₁ v')) = (v ≡ v')
  PathsB assocr₊ (inj₁ v) (inj₁ (inj₂ v')) = ⊥
  PathsB assocr₊ (inj₁ v) (inj₂ v') = ⊥
  PathsB assocr₊ (inj₂ (inj₁ v)) (inj₁ (inj₁ v')) = ⊥
  PathsB assocr₊ (inj₂ (inj₁ v)) (inj₁ (inj₂ v')) = (v ≡ v')
  PathsB assocr₊ (inj₂ (inj₁ v)) (inj₂ v') = ⊥
  PathsB assocr₊ (inj₂ (inj₂ v)) (inj₁ v') = ⊥
  PathsB assocr₊ (inj₂ (inj₂ v)) (inj₂ v') = (v ≡ v')
  PathsB unite⋆ v (tt , v') = (v ≡ v')
  PathsB uniti⋆ (tt , v) v' = (v ≡ v')
  PathsB swap⋆ (v₁ , v₂) (v₂' , v₁') = (v₁ ≡ v₁') × (v₂ ≡ v₂')
  PathsB assocl⋆ ((v₁ , v₂) , v₃) (v₁' , (v₂' , v₃')) = 
    (v₁ ≡ v₁') × (v₂ ≡ v₂') × (v₃ ≡ v₃')
  PathsB assocr⋆ (v₁ , (v₂ , v₃)) ((v₁' , v₂') , v₃') = 
    (v₁ ≡ v₁') × (v₂ ≡ v₂') × (v₃ ≡ v₃')
  PathsB distz ()
  PathsB factorz (() , v)
  PathsB dist (inj₁ (v₁ , v₃)) (inj₁ v₁' , v₃') = 
    (v₁ ≡ v₁') × (v₃ ≡ v₃')
  PathsB dist (inj₁ (v₁ , v₃)) (inj₂ v₂' , v₃') = ⊥
  PathsB dist (inj₂ (v₂ , v₃)) (inj₁ v₁' , v₃') = ⊥
  PathsB dist (inj₂ (v₂ , v₃)) (inj₂ v₂' , v₃') = 
    (v₂ ≡ v₂') × (v₃ ≡ v₃')
  PathsB factor (inj₁ v₁ , v₃) (inj₁ (v₁' , v₃')) = 
    (v₁ ≡ v₁') × (v₃ ≡ v₃')
  PathsB factor (inj₁ v₁ , v₃) (inj₂ (v₂' , v₃')) = ⊥
  PathsB factor (inj₂ v₂ , v₃) (inj₁ (v₁' , v₃')) = ⊥
  PathsB factor (inj₂ v₂ , v₃) (inj₂ (v₂' , v₃')) = 
    (v₂ ≡ v₂') × (v₃ ≡ v₃')
  PathsB {t} id⟷ v v' = (v ≡ v')
  PathsB (sym⟷ c) v v' = Paths c v v'
  PathsB (_◎_ {t₁} {t₂} {t₃} c₁ c₂) v v' = 
    Σ[ u ∈ ⟦ t₂ ⟧ ] (PathsB c₂ v u × PathsB c₁ u v')
  PathsB (c₁ ⊕ c₂) (inj₁ v) (inj₁ v') = PathsB c₁ v v'
  PathsB (c₁ ⊕ c₂) (inj₁ v) (inj₂ v') = ⊥
  PathsB (c₁ ⊕ c₂) (inj₂ v) (inj₁ v') = ⊥
  PathsB (c₁ ⊕ c₂) (inj₂ v) (inj₂ v') = PathsB c₂ v v'
  PathsB (c₁ ⊗ c₂) (v₁ , v₂) (v₁' , v₂') = 
    PathsB c₁ v₁ v₁' × PathsB c₂ v₂ v₂'

-- Given a combinator c : t₁ ⟷ t₂ and values v₁ : ⟦ t₁ ⟧ and v₂ : ⟦ t₂ ⟧,
-- Paths c v₁ v₂ gives us the space of paths that could connect v₁ and v₂
-- Examples:

pathIdtt : Paths id⟷ tt tt
pathIdtt = refl tt

-- three different ways of relating F to F:

pathIdFF : Paths id⟷ FALSE FALSE
pathIdFF = refl FALSE

pathNotNotFF : Paths (swap₊ ◎ swap₊) FALSE FALSE
pathNotNotFF = TRUE , refl tt , refl tt

pathPlusFF : Paths (id⟷ ⊕ id⟷) FALSE FALSE
pathPlusFF = refl tt

-- are there 2-paths between the above 3 paths???

-- space of paths is empty; cannot produce any path; can 
-- use pattern matching to confirm that the space is empty
pathIdFT : Paths id⟷ FALSE TRUE → ⊤
pathIdFT ()

-- three different ways of relating (F,F) to (F,F)

pathIdFFFF : Paths id⟷ (FALSE , FALSE) (FALSE , FALSE) 
pathIdFFFF = refl (FALSE , FALSE) 

pathTimesFFFF : Paths (id⟷ ⊗ id⟷) (FALSE , FALSE) (FALSE , FALSE) 
pathTimesFFFF = (refl FALSE , refl FALSE) 

pathTimesPlusFFFF : Paths 
                      ((id⟷ ⊕ id⟷) ⊗ (id⟷ ⊕ id⟷)) 
                      (FALSE , FALSE) (FALSE , FALSE) 
pathTimesPlusFFFF = (refl tt , refl tt)

pathSwap₊FT : Paths swap₊ FALSE TRUE
pathSwap₊FT = refl tt

pathSwap₊TF : Paths swap₊ TRUE FALSE
pathSwap₊TF = refl tt

-- no path
pathSwap₊FF : Paths swap₊ FALSE FALSE → ⊤
pathSwap₊FF ()

pathCnotTF : Paths cnot (TRUE , FALSE) (TRUE , TRUE)
pathCnotTF = inj₁ (tt , FALSE) , -- first intermediate value
             -- path using dist from (T,F) to (inj₁ (tt , F)) 
             (refl tt , refl FALSE) , 
             -- path from (inj₁ (tt , F)) to (T,T)
             (inj₁ (tt , TRUE) , -- next intermediate value
             (refl tt , refl tt) , 
             (refl tt , refl TRUE))

-- here is a completely different path between (T,F) and (T,T)
pathIdNotTF : Paths (id⟷ ⊗ swap₊) (TRUE , FALSE) (TRUE , TRUE)
pathIdNotTF = refl TRUE , refl tt

-- is there a 2-path between the two paths above? 

pathUnite₊ : {t : U} {v v' : ⟦ t ⟧} → (v ≡ v') → Paths unite₊ (inj₂ v) v'
pathUnite₊ p = p

-- Higher groupoid structure

-- For every path between v₁ and v₂ there is a path between v₂ and v₁

pathInv : {t₁ t₂ : U} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} {c : t₁ ⟷ t₂} → 
          Paths c v₁ v₂ → Paths (sym⟷ c) v₂ v₁
pathInv {v₁ = inj₁ ()} {v₂ = v} {unite₊}
pathInv {v₁ = inj₂ v} {v₂ = v'} {unite₊} p = sym p
pathInv {v₁ = v} {v₂ = inj₁ ()} {uniti₊} 
pathInv {v₁ = v} {v₂ = inj₂ v'} {uniti₊} p = sym p 
pathInv {v₁ = inj₁ v} {v₂ = inj₁ v'} {swap₊} ()
pathInv {v₁ = inj₁ v} {v₂ = inj₂ v'} {swap₊} p = sym p
pathInv {v₁ = inj₂ v} {v₂ = inj₁ v'} {swap₊} p = sym p
pathInv {v₁ = inj₂ v} {v₂ = inj₂ v'} {swap₊} ()
pathInv {v₁ = inj₁ v} {v₂ = inj₁ (inj₁ v')} {assocl₊} p = sym p
pathInv {v₁ = inj₁ v} {v₂ = inj₁ (inj₂ v')} {assocl₊} ()
pathInv {v₁ = inj₁ v} {v₂ = inj₂ v'} {assocl₊} ()
pathInv {v₁ = inj₂ (inj₁ v)} {v₂ = inj₁ (inj₁ v')} {assocl₊} ()
pathInv {v₁ = inj₂ (inj₁ v)} {v₂ = inj₁ (inj₂ v')} {assocl₊} p = sym p
pathInv {v₁ = inj₂ (inj₁ v)} {v₂ = inj₂ v'} {assocl₊} ()
pathInv {v₁ = inj₂ (inj₂ v)} {v₂ = inj₁ v'} {assocl₊} ()
pathInv {v₁ = inj₂ (inj₂ v)} {v₂ = inj₂ v'} {assocl₊} p = sym p
pathInv {v₁ = inj₁ (inj₁ v)} {v₂ = inj₁ v'} {assocr₊} p = sym p
pathInv {v₁ = inj₁ (inj₁ v)} {v₂ = inj₂ v'} {assocr₊} ()
pathInv {v₁ = inj₁ (inj₂ v)} {v₂ = inj₁ v'} {assocr₊} ()
pathInv {v₁ = inj₁ (inj₂ v)} {v₂ = inj₂ (inj₁ v')} {assocr₊} p = sym p
pathInv {v₁ = inj₁ (inj₂ v)} {v₂ = inj₂ (inj₂ v')} {assocr₊} ()
pathInv {v₁ = inj₂ v} {v₂ = inj₁ v'} {assocr₊} ()
pathInv {v₁ = inj₂ v} {v₂ = inj₂ (inj₁ v')} {assocr₊} ()
pathInv {v₁ = inj₂ v} {v₂ = inj₂ (inj₂ v')} {assocr₊} p = sym p
pathInv {v₁ = (tt , v)} {v₂ = v'} {unite⋆} p = sym p
pathInv {v₁ = v} {v₂ = (tt , v')} {uniti⋆} p = sym p
pathInv {v₁ = (u , v)} {v₂ = (v' , u')} {swap⋆} (p₁ , p₂) = (sym p₂ , sym p₁)
pathInv {v₁ = (u , (v , w))} {v₂ = ((u' , v') , w')} {assocl⋆} (p₁ , p₂ , p₃) = 
  (sym p₁ , sym p₂ , sym p₃)
pathInv {v₁ = ((u , v) , w)} {v₂ = (u' , (v' , w'))} {assocr⋆} (p₁ , p₂ , p₃) = 
  (sym p₁ , sym p₂ , sym p₃)
pathInv {v₁ = _} {v₂ = ()} {distz}
pathInv {v₁ = ()} {v₂ = _} {factorz} 
pathInv {v₁ = (inj₁ v₁ , v₃)} {v₂ = inj₁ (v₁' , v₃')} {dist} (p₁ , p₂) = 
  (sym p₁ , sym p₂)
pathInv {v₁ = (inj₁ v₁ , v₃)} {v₂ = inj₂ (v₂' , v₃')} {dist} ()
pathInv {v₁ = (inj₂ v₂ , v₃)} {v₂ = inj₁ (v₁' , v₃')} {dist} ()
pathInv {v₁ = (inj₂ v₂ , v₃)} {v₂ = inj₂ (v₂' , v₃')} {dist} (p₁ , p₂) = 
  (sym p₁ , sym p₂)
pathInv {v₁ = inj₁ (v₁ , v₃)} {v₂ = (inj₁ v₁' , v₃')} {factor} (p₁ , p₂) = 
  (sym p₁ , sym p₂)
pathInv {v₁ = inj₁ (v₁ , v₃)} {v₂ = (inj₂ v₂' , v₃')} {factor} ()
pathInv {v₁ = inj₂ (v₂ , v₃)} {v₂ = (inj₁ v₁' , v₃')} {factor} ()
pathInv {v₁ = inj₂ (v₂ , v₃)} {v₂ = (inj₂ v₂' , v₃')} {factor} (p₁ , p₂) = 
  (sym p₁ , sym p₂)
pathInv {v₁ = v} {v₂ = v'} {id⟷} p = sym p
pathInv {v₁ = v} {v₂ = v'} {sym⟷ c} p = {!!} 
pathInv {v₁ = v} {v₂ = v'} {c₁ ◎ c₂} (u , (p₁ , p₂)) = 
  (u , (pathInv {c = c₂} p₂  , pathInv {c = c₁} p₁))
pathInv {v₁ = inj₁ v} {v₂ = inj₁ v'} {c₁ ⊕ c₂} p = pathInv {c = c₁} p
pathInv {v₁ = inj₁ v} {v₂ = inj₂ v'} {c₁ ⊕ c₂} ()
pathInv {v₁ = inj₂ v} {v₂ = inj₁ v'} {c₁ ⊕ c₂} ()
pathInv {v₁ = inj₂ v} {v₂ = inj₂ v'} {c₁ ⊕ c₂} p = pathInv {c = c₂} p 
pathInv {v₁ = (u , v)} {v₂ = (u' , v')} {c₁ ⊗ c₂} (p₁ , p₂) = 
  (pathInv {c = c₁} p₁ , pathInv {c = c₂} p₂)

{--
-- If we have a path between v₁ and v₁' and a combinator that connects v₁ to
-- v₂, then the combinator also connects v₁' to some v₂' such that there is
-- path between v₂ and v₂'

pathFunctor : {t₁ t₂ : U} {v₁ v₁' : ⟦ t₁ ⟧} {v₂ v₂' : ⟦ t₂ ⟧} {c : t₁ ⟷ t₂} →
  (v₁ ≡ v₁') → Paths c v₁ v₂ → (v₂ ≡ v₂') → Paths c v₁' v₂'
pathFunctor = {!!} 

All kind of structure to investigate in the HoTT book. Let's push forward
with cubical types though...
--}
  
------------------------------------------------------------------------------
-- N dimensional version

data C : ℕ → Set where
  ZD   : U → C 0
  Node : {n : ℕ} → C n → C n → C (suc n) 

⟦_⟧N : {n : ℕ} → C n → Set
⟦ ZD t ⟧N = ⟦ t ⟧ 
⟦ Node c₁ c₂ ⟧N = ⟦ c₁ ⟧N ⊎ ⟦ c₂ ⟧N

liftN : (n : ℕ) → (t : U) → C n
liftN 0 t = ZD t
liftN (suc n) t = Node (liftN n t) (liftN n ZERO)

zeroN : (n : ℕ) → C n
zeroN n = liftN n ZERO

oneN : (n : ℕ) → C n
oneN n = liftN n ONE

plus : {n : ℕ} → C n → C n → C n
plus (ZD t₁) (ZD t₂) = ZD (PLUS t₁ t₂)
plus (Node c₁ c₂) (Node c₁' c₂') = Node (plus c₁ c₁') (plus c₂ c₂')

times : {m n : ℕ} → C m → C n → C (m + n)
times (ZD t₁) (ZD t₂) = ZD (TIMES t₁ t₂)
times (ZD t) (Node c₁ c₂) = Node (times (ZD t) c₁) (times (ZD t) c₂)
times (Node c₁ c₂) c = Node (times c₁ c) (times c₂ c) 

-- N-dimensional paths connect points in c₁ and c₂ if there is an isomorphism
-- between the types c₁ and c₂. 
  
data _⟺_ : {n : ℕ} → C n → C n → Set where
  baseC : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ((ZD t₁) ⟺ (ZD t₂))
  nodeC : {n : ℕ} {c₁ : C n} {c₂ : C n} {c₃ : C n} {c₄ : C n} → 
          (c₁ ⟺ c₂) → (c₃ ⟺ c₄) → ((Node c₁ c₃) ⟺ (Node c₂ c₄))
  zerolC : {n : ℕ} {c : C n} → ((Node c c) ⟺ (zeroN (suc n)))
  zerorC : {n : ℕ} {c : C n} → ((zeroN (suc n)) ⟺ (Node c c))

NPaths : {n : ℕ} {c₁ c₂ : C n} → (c₁ ⟺ c₂) → ⟦ c₁ ⟧N → ⟦ c₂ ⟧N → Set
NPaths (baseC c) v₁ v₂ = Paths c v₁ v₂
NPaths (nodeC α₁ α₂) (inj₁ v₁) (inj₁ v₂) = NPaths α₁ v₁ v₂
NPaths (nodeC α₁ α₂) (inj₁ v₁) (inj₂ v₂) = ⊥ 
NPaths (nodeC α₁ α₂) (inj₂ v₁) (inj₁ v₂) = ⊥ 
NPaths (nodeC α₁ α₂) (inj₂ v₁) (inj₂ v₂) = NPaths α₂ v₁ v₂
NPaths zerolC v₁ v₂ = {!!}
NPaths zerorC v₁ v₂ = {!!}
