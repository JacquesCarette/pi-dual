{-# OPTIONS --without-K #-}

module A3 where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

------------------------------------------------------------------------------
-- Level 0 

module Pi0 where

  infixr 10 _◎_
  infixr 30 _⟷_

  -- types
  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
  
  -- values
  ⟦_⟧ : U → Set
  ⟦ ZERO ⟧        = ⊥
  ⟦ ONE ⟧         = ⊤
  ⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

  -- Examples

  BOOL : U
  BOOL = PLUS ONE ONE

  BOOL² : U
  BOOL² = TIMES BOOL BOOL

  TRUE : ⟦ BOOL ⟧
  TRUE = inj₁ tt

  FALSE : ⟦ BOOL ⟧
  FALSE = inj₂ tt

  -- combinators 
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

  -- Examples

  COND : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → 
         ((TIMES BOOL t₁) ⟷ (TIMES BOOL t₂))
  COND f g = dist ◎ ((id⟷ ⊗ f) ⊕ (id⟷ ⊗ g)) ◎ factor 

  CONTROLLED : {t : U} → (t ⟷ t) → ((TIMES BOOL t) ⟷ (TIMES BOOL t))
  CONTROLLED f = COND f id⟷
  
  CNOT : BOOL² ⟷ BOOL²
  CNOT = CONTROLLED swap₊

------------------------------------------------------------------------------
-- Level 1 includes level 0 equivalences...

module Pi1 where
  -- types
  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
    EQUIV : {t₁ t₂ : Pi0.U} → (t₁ Pi0.⟷ t₂) → Pi0.⟦ t₁ ⟧ → Pi0.⟦ t₂ ⟧ → U

  -- Path types and values

  data Unite₊ {t : Pi0.U} : Pi0.⟦ Pi0.PLUS Pi0.ZERO t ⟧ → Pi0.⟦ t ⟧ → Set where
    pathUnite₊ : (v : Pi0.⟦ t ⟧) → Unite₊ (inj₂ v) v

  data Uniti₊ {t : Pi0.U} : Pi0.⟦ t ⟧ → Pi0.⟦ Pi0.PLUS Pi0.ZERO t ⟧ → Set where
    pathUniti₊ : (v : Pi0.⟦ t ⟧) → Uniti₊ v (inj₂ v)

  data Swap₊ {t₁ t₂ : Pi0.U} : 
    Pi0.⟦ Pi0.PLUS t₁ t₂ ⟧ → Pi0.⟦ Pi0.PLUS t₂ t₁ ⟧ → Set where
    path1Swap₊ : (v₁ : Pi0.⟦ t₁ ⟧) → Swap₊ (inj₁ v₁) (inj₂ v₁)
    path2Swap₊ : (v₂ : Pi0.⟦ t₂ ⟧) → Swap₊ (inj₂ v₂) (inj₁ v₂)

  data Assocl₊ {t₁ t₂ t₃ : Pi0.U} : 
    Pi0.⟦ Pi0.PLUS t₁ (Pi0.PLUS t₂ t₃) ⟧ → 
    Pi0.⟦ Pi0.PLUS (Pi0.PLUS t₁ t₂) t₃ ⟧ → Set where
    path1Assocl₊ : (v₁ : Pi0.⟦ t₁ ⟧) → Assocl₊ (inj₁ v₁) (inj₁ (inj₁ v₁))
    path2Assocl₊ : (v₂ : Pi0.⟦ t₂ ⟧) → Assocl₊ (inj₂ (inj₁ v₂)) (inj₁ (inj₂ v₂))
    path3Assocl₊ : (v₃ : Pi0.⟦ t₃ ⟧) → Assocl₊ (inj₂ (inj₂ v₃)) (inj₂ v₃)

  data Assocr₊ {t₁ t₂ t₃ : Pi0.U} : 
    Pi0.⟦ Pi0.PLUS (Pi0.PLUS t₁ t₂) t₃ ⟧ → 
    Pi0.⟦ Pi0.PLUS t₁ (Pi0.PLUS t₂ t₃) ⟧ → Set where
    path1Assocr₊ : (v₁ : Pi0.⟦ t₁ ⟧) → Assocr₊ (inj₁ (inj₁ v₁)) (inj₁ v₁)
    path2Assocr₊ : (v₂ : Pi0.⟦ t₂ ⟧) → 
      Assocr₊ (inj₁ (inj₂ v₂)) (inj₂ (inj₁ v₂)) 
    path3Assocr₊ : (v₃ : Pi0.⟦ t₃ ⟧) → Assocr₊ (inj₂ v₃) (inj₂ (inj₂ v₃))

  data Unite⋆ {t : Pi0.U} : Pi0.⟦ Pi0.TIMES Pi0.ONE t ⟧ → Pi0.⟦ t ⟧ → Set where
    pathUnite⋆ : (v : Pi0.⟦ t ⟧) → Unite⋆ (tt , v) v

  data Uniti⋆ {t : Pi0.U} : Pi0.⟦ t ⟧ → Pi0.⟦ Pi0.TIMES Pi0.ONE t ⟧ → Set where
    pathUniti⋆ : (v : Pi0.⟦ t ⟧) → Uniti⋆ v (tt , v)

  data Swap⋆ {t₁ t₂ : Pi0.U} : 
    Pi0.⟦ Pi0.TIMES t₁ t₂ ⟧ → Pi0.⟦ Pi0.TIMES t₂ t₁ ⟧ → Set where
    pathSwap⋆ : 
      (v₁ : Pi0.⟦ t₁ ⟧) → (v₂ : Pi0.⟦ t₂ ⟧) → Swap⋆ (v₁ , v₂) (v₂ , v₁)

  data Assocl⋆ {t₁ t₂ t₃ : Pi0.U} : 
    Pi0.⟦ Pi0.TIMES t₁ (Pi0.TIMES t₂ t₃) ⟧ →
    Pi0.⟦ Pi0.TIMES (Pi0.TIMES t₁ t₂) t₃ ⟧ → Set where
    pathAssocl⋆ : 
      (v₁ : Pi0.⟦ t₁ ⟧) → (v₂ : Pi0.⟦ t₂ ⟧) → (v₃ : Pi0.⟦ t₃ ⟧) → 
      Assocl⋆ (v₁ , (v₂ , v₃)) ((v₁ , v₂) , v₃)

  data Assocr⋆ {t₁ t₂ t₃ : Pi0.U} : 
    Pi0.⟦ Pi0.TIMES (Pi0.TIMES t₁ t₂) t₃ ⟧ → 
    Pi0.⟦ Pi0.TIMES t₁ (Pi0.TIMES t₂ t₃) ⟧ → Set where
    pathAssocr⋆ : 
      (v₁ : Pi0.⟦ t₁ ⟧) → (v₂ : Pi0.⟦ t₂ ⟧) → (v₃ : Pi0.⟦ t₃ ⟧) → 
      Assocr⋆ ((v₁ , v₂) , v₃) (v₁ , (v₂ , v₃))

  data Dist {t₁ t₂ t₃ : Pi0.U} : 
    Pi0.⟦ Pi0.TIMES (Pi0.PLUS t₁ t₂) t₃ ⟧ → 
    Pi0.⟦ Pi0.PLUS (Pi0.TIMES t₁ t₃) (Pi0.TIMES t₂ t₃) ⟧ → Set where
    path1Dist : 
      (v₁ : Pi0.⟦ t₁ ⟧) → (v₃ : Pi0.⟦ t₃ ⟧) → 
      Dist (inj₁ v₁ , v₃) (inj₁ (v₁ , v₃))
    path2Dist : 
      (v₂ : Pi0.⟦ t₂ ⟧) → (v₃ : Pi0.⟦ t₃ ⟧) → 
      Dist (inj₂ v₂ , v₃) (inj₂ (v₂ , v₃))
        
  data Factor {t₁ t₂ t₃ : Pi0.U} : 
    Pi0.⟦ Pi0.PLUS (Pi0.TIMES t₁ t₃) (Pi0.TIMES t₂ t₃) ⟧ → 
    Pi0.⟦ Pi0.TIMES (Pi0.PLUS t₁ t₂) t₃ ⟧ → Set where
    path1Factor : 
      (v₁ : Pi0.⟦ t₁ ⟧) → (v₃ : Pi0.⟦ t₃ ⟧) → 
      Factor (inj₁ (v₁ , v₃)) (inj₁ v₁ , v₃)
    path2Factor : 
      (v₂ : Pi0.⟦ t₂ ⟧) → (v₃ : Pi0.⟦ t₃ ⟧) → 
      Factor (inj₂ (v₂ , v₃)) (inj₂ v₂ , v₃)
        
  data Id⟷ {t : Pi0.U} : Pi0.⟦ t ⟧ → Pi0.⟦ t ⟧ → Set where
    pathId⟷ : (v : Pi0.⟦ t ⟧) → Id⟷ v v

  -- General values
  mutual
    ⟦_⟧ : U → Set
    ⟦ ZERO ⟧          = ⊥
    ⟦ ONE ⟧           = ⊤
    ⟦ PLUS t₁ t₂ ⟧    = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
    ⟦ TIMES t₁ t₂ ⟧   = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
    ⟦ EQUIV c v₁ v₂ ⟧ = Paths c v₁ v₂

    Paths : {t₁ t₂ : Pi0.U} → (t₁ Pi0.⟷ t₂) → Pi0.⟦ t₁ ⟧ → Pi0.⟦ t₂ ⟧ → Set
    Paths Pi0.unite₊ (inj₁ ()) _
    Paths Pi0.unite₊ (inj₂ v) v' = Unite₊ (inj₂ v) v'
    Paths Pi0.uniti₊ v (inj₁ ())
    Paths Pi0.uniti₊ v (inj₂ v') = Uniti₊ v (inj₂ v')
    Paths Pi0.swap₊ v v' = Swap₊ v v'
    Paths Pi0.assocl₊ v v' = Assocl₊ v v'
    Paths Pi0.assocr₊ v v' = Assocr₊ v v'
    Paths Pi0.unite⋆ v v' = Unite⋆ v v'
    Paths Pi0.uniti⋆ v v' = Uniti⋆ v v'
    Paths Pi0.swap⋆ v v' = Swap⋆ v v'
    Paths Pi0.assocl⋆ v v' = Assocl⋆ v v'
    Paths Pi0.assocr⋆ v v' = Assocr⋆ v v'
    Paths Pi0.distz v ()
    Paths Pi0.factorz () v'
    Paths Pi0.dist v v' = Dist v v'
    Paths Pi0.factor v v' = Factor v v'
    Paths Pi0.id⟷ v v' = Id⟷ v v'
    Paths (Pi0.sym⟷ c) v v' = Paths c v' v
    Paths (Pi0._◎_ {t₂ = t₂} c₁ c₂) v₁ v₃ = 
      Σ[ v₂ ∈ Pi0.⟦ t₂ ⟧ ] (Paths c₁ v₁ v₂ × Paths c₂ v₂ v₃)
    Paths (c₁ Pi0.⊕ c₂) (inj₁ v₁) (inj₁ v₁') = Paths c₁ v₁ v₁'
    Paths (c₁ Pi0.⊕ c₂) (inj₁ v₁) (inj₂ v₂') = ⊥
    Paths (c₁ Pi0.⊕ c₂) (inj₂ v₂) (inj₁ v₁') = ⊥
    Paths (c₁ Pi0.⊕ c₂) (inj₂ v₂) (inj₂ v₂') = Paths c₂ v₂ v₂'
    Paths (c₁ Pi0.⊗ c₂) (v₁ , v₂) (v₁' , v₂') = 
      Paths c₁ v₁ v₁' × Paths c₂ v₂ v₂'

  -- Examples
  -- A few paths between FALSE and FALSE

  p₁ : ⟦ EQUIV Pi0.id⟷ Pi0.FALSE Pi0.FALSE ⟧
  p₁ = pathId⟷ Pi0.FALSE 

  p₂ : ⟦ EQUIV (Pi0.id⟷ Pi0.◎ Pi0.id⟷) Pi0.FALSE Pi0.FALSE ⟧
  p₂ = (Pi0.FALSE , (p₁ , p₁))

  p₃ : ⟦ EQUIV (Pi0.swap₊ Pi0.◎ Pi0.swap₊) Pi0.FALSE Pi0.FALSE ⟧
  p₃ = (Pi0.TRUE , (path2Swap₊ tt , path1Swap₊ tt))

  p₄ : ⟦ EQUIV (Pi0.id⟷ Pi0.⊕ Pi0.id⟷) Pi0.FALSE Pi0.FALSE ⟧
  p₄ = pathId⟷ tt

  -- A few paths between (TRUE,TRUE) and (TRUE,TRUE)

  p₅ : ⟦ EQUIV Pi0.id⟷ (Pi0.TRUE , Pi0.TRUE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₅ = pathId⟷ (Pi0.TRUE , Pi0.TRUE)

  p₆ : ⟦ EQUIV (Pi0.id⟷ Pi0.⊗ Pi0.id⟷) 
        (Pi0.TRUE , Pi0.TRUE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₆ = (pathId⟷ Pi0.TRUE , pathId⟷ Pi0.TRUE)

  -- A few paths between (TRUE,FALSE) and (TRUE,TRUE)

  p₇ : ⟦ EQUIV (Pi0.id⟷ Pi0.⊗ Pi0.swap₊) 
        (Pi0.TRUE , Pi0.FALSE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₇ = (pathId⟷ Pi0.TRUE , path2Swap₊ tt)

  p₈ : ⟦ EQUIV Pi0.CNOT (Pi0.TRUE , Pi0.FALSE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₈ = ((inj₁ (tt , Pi0.FALSE)) , 
        (path1Dist tt Pi0.FALSE ,
        ((inj₁ (tt , Pi0.TRUE)) , 
        ((pathId⟷ tt , path2Swap₊ tt) , 
         path1Factor tt Pi0.TRUE))))

  -- combinators 
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
    lidl    : {t₁ t₂ : Pi0.U} 
              {c : t₁ Pi0.⟷ t₂} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} → 
              EQUIV (Pi0.id⟷ Pi0.◎ c) v₁ v₂ ⟷ EQUIV c v₁ v₂
    lidr    : {t₁ t₂ : Pi0.U} 
              {c : t₁ Pi0.⟷ t₂} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} → 
              EQUIV c v₁ v₂ ⟷ EQUIV (Pi0.id⟷ Pi0.◎ c) v₁ v₂

  -- Examples
  -- id;swap₊ is equivalent to swap₊
  e₁ : EQUIV (Pi0.id⟷ Pi0.◎ Pi0.swap₊) Pi0.FALSE Pi0.TRUE ⟷ 
       EQUIV Pi0.swap₊ Pi0.FALSE Pi0.TRUE
  e₁ = lidl

------------------------------------------------------------------------------
-- Level 2 explicitly...

module Pi2 where
  -- types
  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
    EQUIV : {t₁ t₂ : Pi1.U} → (t₁ Pi1.⟷ t₂) → Pi1.⟦ t₁ ⟧ → Pi1.⟦ t₂ ⟧ → U

  data Unite₊ {t : Pi1.U} : Pi1.⟦ Pi1.PLUS Pi1.ZERO t ⟧ → Pi1.⟦ t ⟧ → Set where
    pathUnite₊ : (v₁ : Pi1.⟦ Pi1.PLUS Pi1.ZERO t ⟧) → (v₂ : Pi1.⟦ t ⟧) → Unite₊ v₁ v₂

  data Id⟷ {t : Pi1.U} : Pi1.⟦ t ⟧ → Pi1.⟦ t ⟧ → Set where
    pathId⟷ : (v₁ : Pi1.⟦ t ⟧) → (v₂ : Pi1.⟦ t ⟧) → Id⟷ v₁ v₂

  -- values
  mutual 

    ⟦_⟧ : U → Set
    ⟦ ZERO ⟧          = ⊥
    ⟦ ONE ⟧           = ⊤
    ⟦ PLUS t₁ t₂ ⟧    = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
    ⟦ TIMES t₁ t₂ ⟧   = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
    ⟦ EQUIV c v₁ v₂ ⟧ = f c v₁ v₂

    f : {t₁ t₂ : Pi1.U} → (t₁ Pi1.⟷ t₂) → Pi1.⟦ t₁ ⟧ → Pi1.⟦ t₂ ⟧ → Set
    f (Pi1.id⟷ {t}) v v' = Id⟷ {t} v v' 
    f (Pi1._◎_ {t₂ = t₂} c₁ c₂) v₁ v₃ = 
      Σ[ v₂ ∈ Pi1.⟦ t₂ ⟧ ] (f c₁ v₁ v₂ × f c₂ v₂ v₃)
    f (Pi1.lidl {v₁ = v₁}) (.v₁ , (Pi1.pathId⟷ .v₁ , q)) q' = ⊥ -- todo
    f c v₁ v₂ = ⊥ -- to do 

  -- combinators 
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
    id⟷     : {t : U} → t ⟷ t
    sym⟷    : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)
    lid     : {t₁ t₂ : Pi1.U} {v₁ : Pi1.⟦ t₁ ⟧} {v₂ : Pi1.⟦ t₂ ⟧} 
              {c : t₁ Pi1.⟷ t₂} → 
              EQUIV (Pi1.id⟷ Pi1.◎ c) v₁ v₂ ⟷ EQUIV c v₁ v₂

------------------------------------------------------------------------------

