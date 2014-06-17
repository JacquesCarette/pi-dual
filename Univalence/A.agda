{-# OPTIONS --without-K #-}

module A where

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
-- Paths connecting points in t₁ and t₂ if there is an isomorphism between
-- them

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

-- IsoPaths: each combinator defines a space of paths between its end points

mutual

  IsoPaths : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧ → Set
  IsoPaths unite₊ (inj₁ ()) 
  IsoPaths unite₊ (inj₂ v) v' = (v ≡ v')
  IsoPaths uniti₊ v (inj₁ ())
  IsoPaths uniti₊ v (inj₂ v') = (v ≡ v')
  IsoPaths swap₊ (inj₁ v) (inj₁ v') = ⊥
  IsoPaths swap₊ (inj₁ v) (inj₂ v') = (v ≡ v')
  IsoPaths swap₊ (inj₂ v) (inj₁ v') = (v ≡ v')
  IsoPaths swap₊ (inj₂ v) (inj₂ v') = ⊥
  IsoPaths assocl₊ (inj₁ v) (inj₁ (inj₁ v')) = (v ≡ v')
  IsoPaths assocl₊ (inj₁ v) (inj₁ (inj₂ v')) = ⊥
  IsoPaths assocl₊ (inj₁ v) (inj₂ v') = ⊥
  IsoPaths assocl₊ (inj₂ (inj₁ v)) (inj₁ (inj₁ v')) = ⊥
  IsoPaths assocl₊ (inj₂ (inj₁ v)) (inj₁ (inj₂ v')) = (v ≡ v')
  IsoPaths assocl₊ (inj₂ (inj₁ v)) (inj₂ v') = ⊥
  IsoPaths assocl₊ (inj₂ (inj₂ v)) (inj₁ v') = ⊥
  IsoPaths assocl₊ (inj₂ (inj₂ v)) (inj₂ v') = (v ≡ v')
  IsoPaths assocr₊ (inj₁ (inj₁ v)) (inj₁ v') = (v ≡ v')
  IsoPaths assocr₊ (inj₁ (inj₁ v)) (inj₂ v') = ⊥
  IsoPaths assocr₊ (inj₁ (inj₂ v)) (inj₁ v') = ⊥
  IsoPaths assocr₊ (inj₁ (inj₂ v)) (inj₂ (inj₁ v')) = (v ≡ v')
  IsoPaths assocr₊ (inj₁ (inj₂ v)) (inj₂ (inj₂ v')) = ⊥
  IsoPaths assocr₊ (inj₂ v) (inj₁ v') = ⊥
  IsoPaths assocr₊ (inj₂ v) (inj₂ (inj₁ v')) = ⊥
  IsoPaths assocr₊ (inj₂ v) (inj₂ (inj₂ v')) = (v ≡ v')
  IsoPaths unite⋆ (tt , v) v' = (v ≡ v')
  IsoPaths uniti⋆ v (tt , v') = (v ≡ v')
  IsoPaths swap⋆ (v₁ , v₂) (v₂' , v₁') = (v₁ ≡ v₁') × (v₂ ≡ v₂')
  IsoPaths assocl⋆ (v₁ , (v₂ , v₃)) ((v₁' , v₂') , v₃') = 
    (v₁ ≡ v₁') × (v₂ ≡ v₂') × (v₃ ≡ v₃')
  IsoPaths assocr⋆ ((v₁ , v₂) , v₃) (v₁' , (v₂' , v₃')) = 
    (v₁ ≡ v₁') × (v₂ ≡ v₂') × (v₃ ≡ v₃')
  IsoPaths distz (() , v)
  IsoPaths factorz ()
  IsoPaths dist (inj₁ v₁ , v₃) (inj₁ (v₁' , v₃')) = (v₁ ≡ v₁') × (v₃ ≡ v₃')
  IsoPaths dist (inj₁ v₁ , v₃) (inj₂ (v₂' , v₃')) = ⊥
  IsoPaths dist (inj₂ v₂ , v₃) (inj₁ (v₁' , v₃')) = ⊥
  IsoPaths dist (inj₂ v₂ , v₃) (inj₂ (v₂' , v₃')) = (v₂ ≡ v₂') × (v₃ ≡ v₃')
  IsoPaths factor (inj₁ (v₁ , v₃)) (inj₁ v₁' , v₃') = 
    (v₁ ≡ v₁') × (v₃ ≡ v₃')
  IsoPaths factor (inj₁ (v₁ , v₃)) (inj₂ v₂' , v₃') = ⊥
  IsoPaths factor (inj₂ (v₂ , v₃)) (inj₁ v₁' , v₃') = ⊥
  IsoPaths factor (inj₂ (v₂ , v₃)) (inj₂ v₂' , v₃') = 
    (v₂ ≡ v₂') × (v₃ ≡ v₃')
  IsoPaths {t} id⟷ v v' = (v ≡ v')
  IsoPaths (sym⟷ c) v = IsoPathsB c v
  IsoPaths (_◎_ {t₁} {t₂} {t₃} c₁ c₂) v v' = 
    Σ[ u ∈ ⟦ t₂ ⟧ ] (IsoPaths c₁ v u × IsoPaths c₂ u v')
  IsoPaths (c₁ ⊕ c₂) (inj₁ v) (inj₁ v') = IsoPaths c₁ v v'
  IsoPaths (c₁ ⊕ c₂) (inj₁ v) (inj₂ v') = ⊥
  IsoPaths (c₁ ⊕ c₂) (inj₂ v) (inj₁ v') = ⊥
  IsoPaths (c₁ ⊕ c₂) (inj₂ v) (inj₂ v') = IsoPaths c₂ v v'
  IsoPaths (c₁ ⊗ c₂) (v₁ , v₂) (v₁' , v₂') = 
    IsoPaths c₁ v₁ v₁' × IsoPaths c₂ v₂ v₂'

  IsoPathsB : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧ → Set
  IsoPathsB unite₊ v (inj₁ ())
  IsoPathsB unite₊ v (inj₂ v') = (v ≡ v')
  IsoPathsB uniti₊ (inj₁ ()) 
  IsoPathsB uniti₊ (inj₂ v) v' = (v ≡ v')
  IsoPathsB swap₊ (inj₁ v) (inj₁ v') = ⊥
  IsoPathsB swap₊ (inj₁ v) (inj₂ v') = (v ≡ v')
  IsoPathsB swap₊ (inj₂ v) (inj₁ v') = (v ≡ v')
  IsoPathsB swap₊ (inj₂ v) (inj₂ v') = ⊥
  IsoPathsB assocl₊ (inj₁ (inj₁ v)) (inj₁ v') = (v ≡ v')
  IsoPathsB assocl₊ (inj₁ (inj₁ v)) (inj₂ v') = ⊥
  IsoPathsB assocl₊ (inj₁ (inj₂ v)) (inj₁ v') = ⊥
  IsoPathsB assocl₊ (inj₁ (inj₂ v)) (inj₂ (inj₁ v')) = (v ≡ v')
  IsoPathsB assocl₊ (inj₁ (inj₂ v)) (inj₂ (inj₂ v')) = ⊥
  IsoPathsB assocl₊ (inj₂ v) (inj₁ v') = ⊥
  IsoPathsB assocl₊ (inj₂ v) (inj₂ (inj₁ v')) = ⊥
  IsoPathsB assocl₊ (inj₂ v) (inj₂ (inj₂ v')) = (v ≡ v')
  IsoPathsB assocr₊ (inj₁ v) (inj₁ (inj₁ v')) = (v ≡ v')
  IsoPathsB assocr₊ (inj₁ v) (inj₁ (inj₂ v')) = ⊥
  IsoPathsB assocr₊ (inj₁ v) (inj₂ v') = ⊥
  IsoPathsB assocr₊ (inj₂ (inj₁ v)) (inj₁ (inj₁ v')) = ⊥
  IsoPathsB assocr₊ (inj₂ (inj₁ v)) (inj₁ (inj₂ v')) = (v ≡ v')
  IsoPathsB assocr₊ (inj₂ (inj₁ v)) (inj₂ v') = ⊥
  IsoPathsB assocr₊ (inj₂ (inj₂ v)) (inj₁ v') = ⊥
  IsoPathsB assocr₊ (inj₂ (inj₂ v)) (inj₂ v') = (v ≡ v')
  IsoPathsB unite⋆ v (tt , v') = (v ≡ v')
  IsoPathsB uniti⋆ (tt , v) v' = (v ≡ v')
  IsoPathsB swap⋆ (v₁ , v₂) (v₂' , v₁') = (v₁ ≡ v₁') × (v₂ ≡ v₂')
  IsoPathsB assocl⋆ ((v₁ , v₂) , v₃) (v₁' , (v₂' , v₃')) = 
    (v₁ ≡ v₁') × (v₂ ≡ v₂') × (v₃ ≡ v₃')
  IsoPathsB assocr⋆ (v₁ , (v₂ , v₃)) ((v₁' , v₂') , v₃') = 
    (v₁ ≡ v₁') × (v₂ ≡ v₂') × (v₃ ≡ v₃')
  IsoPathsB distz ()
  IsoPathsB factorz (() , v)
  IsoPathsB dist (inj₁ (v₁ , v₃)) (inj₁ v₁' , v₃') = 
    (v₁ ≡ v₁') × (v₃ ≡ v₃')
  IsoPathsB dist (inj₁ (v₁ , v₃)) (inj₂ v₂' , v₃') = ⊥
  IsoPathsB dist (inj₂ (v₂ , v₃)) (inj₁ v₁' , v₃') = ⊥
  IsoPathsB dist (inj₂ (v₂ , v₃)) (inj₂ v₂' , v₃') = 
    (v₂ ≡ v₂') × (v₃ ≡ v₃')
  IsoPathsB factor (inj₁ v₁ , v₃) (inj₁ (v₁' , v₃')) = 
    (v₁ ≡ v₁') × (v₃ ≡ v₃')
  IsoPathsB factor (inj₁ v₁ , v₃) (inj₂ (v₂' , v₃')) = ⊥
  IsoPathsB factor (inj₂ v₂ , v₃) (inj₁ (v₁' , v₃')) = ⊥
  IsoPathsB factor (inj₂ v₂ , v₃) (inj₂ (v₂' , v₃')) = 
    (v₂ ≡ v₂') × (v₃ ≡ v₃')
  IsoPathsB {t} id⟷ v v' = (v ≡ v')
  IsoPathsB (sym⟷ c) v = IsoPaths c v
  IsoPathsB (_◎_ {t₁} {t₂} {t₃} c₁ c₂) v v' = 
    Σ[ u ∈ ⟦ t₂ ⟧ ] (IsoPathsB c₂ v u × IsoPathsB c₁ u v')
  IsoPathsB (c₁ ⊕ c₂) (inj₁ v) (inj₁ v') = IsoPathsB c₁ v v'
  IsoPathsB (c₁ ⊕ c₂) (inj₁ v) (inj₂ v') = ⊥
  IsoPathsB (c₁ ⊕ c₂) (inj₂ v) (inj₁ v') = ⊥
  IsoPathsB (c₁ ⊕ c₂) (inj₂ v) (inj₂ v') = IsoPathsB c₂ v v'
  IsoPathsB (c₁ ⊗ c₂) (v₁ , v₂) (v₁' , v₂') = 
    IsoPathsB c₁ v₁ v₁' × IsoPathsB c₂ v₂ v₂'

-- Given a combinator c : t₁ ⟷ t₂ and values v₁ : ⟦ t₁ ⟧ and v₂ : ⟦ t₂ ⟧,
-- IsoPaths c v₁ v₂ gives us the space of paths that could connect v₁ and v₂
-- Examples:

pathIdtt : IsoPaths id⟷ tt tt
pathIdtt = refl tt

-- three different ways of relating F to F:

pathIdFF : IsoPaths id⟷ FALSE FALSE
pathIdFF = refl FALSE

pathNotNotFF : IsoPaths (swap₊ ◎ swap₊) FALSE FALSE
pathNotNotFF = TRUE , refl tt , refl tt

pathPlusFF : IsoPaths (id⟷ ⊕ id⟷) FALSE FALSE
pathPlusFF = refl tt

-- are there 2-paths between the above 3 paths???

-- space of paths is empty; cannot produce any path; can 
-- use pattern matching to confirm that the space is empty
pathIdFT : IsoPaths id⟷ FALSE TRUE → ⊤
pathIdFT ()

pathIdFFFF : IsoPaths id⟷ (FALSE , FALSE) (FALSE , FALSE) 
pathIdFFFF = refl (FALSE , FALSE) 

pathTimesFFFF : IsoPaths (id⟷ ⊗ id⟷) (FALSE , FALSE) (FALSE , FALSE) 
pathTimesFFFF = (refl FALSE , refl FALSE) 

pathTimesPlusFFFF : IsoPaths 
                      ((id⟷ ⊕ id⟷) ⊗ (id⟷ ⊕ id⟷)) 
                      (FALSE , FALSE) (FALSE , FALSE) 
pathTimesPlusFFFF = (refl tt , refl tt)

pathSwap₊FT : IsoPaths swap₊ FALSE TRUE
pathSwap₊FT = refl tt

pathSwap₊TF : IsoPaths swap₊ TRUE FALSE
pathSwap₊TF = refl tt

-- no path
pathSwap₊FF : IsoPaths swap₊ FALSE FALSE → ⊤
pathSwap₊FF ()

pathCnotTF : IsoPaths cnot (TRUE , FALSE) (TRUE , TRUE)
pathCnotTF = inj₁ (tt , FALSE) , -- first intermediate value
             -- path using dist from (T,F) to (inj₁ (tt , F)) 
             (refl tt , refl FALSE) , 
             -- path from (inj₁ (tt , F)) to (T,T)
             (inj₁ (tt , TRUE) , -- next intermediate value
             (refl tt , refl tt) , 
             (refl tt , refl TRUE))

-- here is a completely different path between (T,F) and (T,T)
pathIdNotTF : IsoPaths (id⟷ ⊗ swap₊) (TRUE , FALSE) (TRUE , TRUE)
pathIdNotTF = refl TRUE , refl tt

-- is there a 2-path between the two paths above? 

pathUnite₊ : {t : U} {v v' : ⟦ t ⟧} → (v ≡ v') → IsoPaths unite₊ (inj₂ v) v'
pathUnite₊ p = p

-- If we have a path between v₁ and v₁' and a combinator that connects v₁ to
-- v₂, then the combinator also connects v₁' to some v₂' such that there is
-- path between v₂ and v₂'

pathFunctor : {t₁ t₂ : U} {v₁ v₁' : ⟦ t₁ ⟧} {v₂ v₂' : ⟦ t₂ ⟧} {c : t₁ ⟷ t₂} →
  (v₁ ≡ v₁') → IsoPaths c v₁ v₂ → (v₂ ≡ v₂') → IsoPaths c v₁' v₂'
pathFunctor = {!!} 

  

