{-# OPTIONS --without-K #-}

module A2 where

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

------------------------------------------------------------------------------
{--
Types are higher groupoids:
- 0 is empty
- 1 has one element and one path refl
- sum type is disjoint union; paths are component wise
- product type is cartesian product; paths are pairs of paths
--}

mutual 

  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
    ID    : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧ → U

  ⟦_⟧ : U → Set
  ⟦ ZERO ⟧        = ⊥
  ⟦ ONE ⟧         = ⊤
  ⟦ PLUS t t' ⟧   = ⟦ t ⟧ ⊎ ⟦ t' ⟧
  ⟦ TIMES t t' ⟧  = ⟦ t ⟧ × ⟦ t' ⟧
  ⟦ ID {t₁} {t₂} c v₁ v₂ ⟧ = Paths {t₁} {t₂} c v₁ v₂

-- 2Paths = Paths {ID {t₁} {t₂} c v₁ v₂} {ID {t₁} {t₂} c v₁ v₂} ???

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
-- isos involving id types:
    -- prodId says (ID_a x ID_b) = ID_(a x b) etc.
    -- also need to add unitId, sumId, ... sections 2.6 - 2.12
    prodId : {t₁ t₂ t₁' t₂' : U} 
             {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} {v₁' : ⟦ t₁' ⟧} {v₂' : ⟦ t₂' ⟧} 
             {c : t₁ ⟷ t₂} {c' : t₁' ⟷ t₂'} → 
             (TIMES (ID {t₁} {t₂} c v₁ v₂) (ID {t₁'} {t₂'} c' v₁' v₂')) ⟷ 
             (ID {TIMES t₁ t₁'} {TIMES t₂ t₂'} (c ⊗ c') (v₁ , v₁') (v₂ , v₂'))
    -- groupoid structure ???

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
  Paths prodId (p , q) r = ((p , q) ≡ r)

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
  PathsB prodId (p , q) r = ((p , q) ≡ r)

------------------------------------------------------------------------------
