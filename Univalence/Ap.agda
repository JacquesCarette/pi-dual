module Ap where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Groupoid

------------------------------------------------------------------------------
-- Level 0: 
-- types are collections of points
-- equivalences are commutative semiring combinators between points

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

  -- pointed types

  record U• : Set where
    constructor •[_,_]
    field
      ∣_∣ : U
      • : ⟦ ∣_∣ ⟧

  open U•

  -- Examples

  BOOL : U
  BOOL = PLUS ONE ONE

  BOOL² : U
  BOOL² = TIMES BOOL BOOL

  TRUE : ⟦ BOOL ⟧
  TRUE = inj₁ tt

  FALSE : ⟦ BOOL ⟧
  FALSE = inj₂ tt

  BOOL•F : U•
  BOOL•F = •[ BOOL , FALSE ]

  BOOL•T : U•
  BOOL•T = •[ BOOL , TRUE ]

  -- combinators between pointed types

  data _⟷_ : U• → U• → Set where
    unite₊  : {t : U•} → •[ PLUS ZERO ∣ t ∣ , inj₂ (• t) ] ⟷ t
    uniti₊  : {t : U•} → t ⟷ •[ PLUS ZERO ∣ t ∣ , inj₂ (• t) ]
    swap1₊  : {t₁ t₂ : U•} → •[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₁ (• t₁) ] ⟷ 
                             •[ PLUS ∣ t₂ ∣ ∣ t₁ ∣ , inj₂ (• t₁) ]
    swap2₊  : {t₁ t₂ : U•} → •[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₂ (• t₂) ] ⟷ 
                             •[ PLUS ∣ t₂ ∣ ∣ t₁ ∣ , inj₁ (• t₂) ]
    assocl1₊ : {t₁ t₂ t₃ : U•} → 
               •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₁ (• t₁) ] ⟷ 
               •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₁ (inj₁ (• t₁)) ]
    assocl2₊ : {t₁ t₂ t₃ : U•} → 
               •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₂ (inj₁ (• t₂)) ] ⟷ 
               •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₁ (inj₂ (• t₂)) ]
    assocl3₊ : {t₁ t₂ t₃ : U•} → 
               •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₂ (inj₂ (• t₃)) ] ⟷ 
               •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₂ (• t₃) ]
    assocr1₊ : {t₁ t₂ t₃ : U•} → 
               •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₁ (inj₁ (• t₁)) ] ⟷ 
               •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₁ (• t₁) ] 
    assocr2₊ : {t₁ t₂ t₃ : U•} → 
               •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₁ (inj₂ (• t₂)) ] ⟷ 
               •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₂ (inj₁ (• t₂)) ] 
    assocr3₊ : {t₁ t₂ t₃ : U•} → 
               •[ PLUS (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , inj₂ (• t₃) ] ⟷ 
               •[ PLUS ∣ t₁ ∣ (PLUS ∣ t₂ ∣ ∣ t₃ ∣) , inj₂ (inj₂ (• t₃)) ]
    unite⋆  : {t : U•} → •[ TIMES ONE ∣ t ∣ , (tt , • t) ] ⟷ t               
    uniti⋆  : {t : U•} → t ⟷ •[ TIMES ONE ∣ t ∣ , (tt , • t) ] 
    swap⋆   : {t₁ t₂ : U•} → •[ TIMES ∣ t₁ ∣ ∣ t₂ ∣ , (• t₁ , • t₂) ] ⟷ 
                             •[ TIMES ∣ t₂ ∣ ∣ t₁ ∣ , (• t₂ , • t₁) ]
    assocl⋆ : {t₁ t₂ t₃ : U•} → 
              •[ TIMES ∣ t₁ ∣ (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , (• t₁ , (• t₂ , • t₃)) ] ⟷ 
              •[ TIMES (TIMES ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , ((• t₁ , • t₂) , • t₃) ]
    assocr⋆ : {t₁ t₂ t₃ : U•} → 
              •[ TIMES (TIMES ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , ((• t₁ , • t₂) , • t₃) ] ⟷ 
              •[ TIMES ∣ t₁ ∣ (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , (• t₁ , (• t₂ , • t₃)) ]
    -- distz   EMPTY
    -- factorz EMPTY
    dist1   : {t₁ t₂ t₃ : U•} → 
              •[ TIMES (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , (inj₁ (• t₁) , • t₃) ] ⟷ 
              •[ PLUS (TIMES ∣ t₁ ∣ ∣ t₃ ∣) (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , 
                 inj₁ (• t₁ , • t₃) ]
    dist2   : {t₁ t₂ t₃ : U•} → 
              •[ TIMES (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , (inj₂ (• t₂) , • t₃) ] ⟷ 
              •[ PLUS (TIMES ∣ t₁ ∣ ∣ t₃ ∣) (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , 
                 inj₂ (• t₂ , • t₃) ]
    factor1   : {t₁ t₂ t₃ : U•} → 
              •[ PLUS (TIMES ∣ t₁ ∣ ∣ t₃ ∣) (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , 
                 inj₁ (• t₁ , • t₃) ] ⟷ 
              •[ TIMES (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , (inj₁ (• t₁) , • t₃) ]
    factor2   : {t₁ t₂ t₃ : U•} → 
              •[ PLUS (TIMES ∣ t₁ ∣ ∣ t₃ ∣) (TIMES ∣ t₂ ∣ ∣ t₃ ∣) , 
                 inj₂ (• t₂ , • t₃) ] ⟷ 
              •[ TIMES (PLUS ∣ t₁ ∣ ∣ t₂ ∣) ∣ t₃ ∣ , (inj₂ (• t₂) , • t₃) ]
    id⟷    : {t : U•} → t ⟷ t
    sym⟷   : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_    : {t₁ t₂ t₃ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕1_   : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
             (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₁ (• t₁) ] ⟷ 
              •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₁ (• t₃) ])
    _⊕2_   : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
             (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₂ (• t₂) ] ⟷ 
              •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₂ (• t₄) ])
    _⊗_     : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
            (•[ TIMES ∣ t₁ ∣ ∣ t₂ ∣ , (• t₁ , • t₂ ) ] ⟷ 
             •[ TIMES ∣ t₃ ∣ ∣ t₄ ∣ , (• t₃ , • t₄ ) ])

  -- Examples

  NOT•T : •[ BOOL , TRUE ] ⟷ •[ BOOL , FALSE ]
  NOT•T = swap1₊

  NOT•F : •[ BOOL , FALSE ] ⟷ •[ BOOL , TRUE ]
  NOT•F = swap2₊

  CNOT•Fx : {b : ⟦ BOOL ⟧} → 
            •[ BOOL² , (FALSE , b) ] ⟷ •[ BOOL² , (FALSE , b) ]
  CNOT•Fx = dist2 ◎ ((id⟷ ⊗ NOT•F) ⊕2 id⟷) ◎ factor2

  CNOT•TF : •[ BOOL² , (TRUE , FALSE) ] ⟷ •[ BOOL² , (TRUE , TRUE) ]
  CNOT•TF = dist1 ◎ 
            ((id⟷ ⊗ NOT•F) ⊕1 (id⟷ {•[ TIMES ONE BOOL , (tt , FALSE) ]})) ◎ 
            factor1

  CNOT•TT : •[ BOOL² , (TRUE , TRUE) ] ⟷ •[ BOOL² , (TRUE , FALSE) ]
  CNOT•TT = dist1 ◎ 
            ((id⟷ ⊗ NOT•T) ⊕1 (id⟷ {•[ TIMES ONE BOOL , (tt , TRUE) ]})) ◎ 
            factor1

------------------------------------------------------------------------------
-- Level 1 
-- types are collections of paths (where paths are the commutative semiring
-- equivalences between points)
-- equivalences are between paths are groupoid combinators
-- we will then also add commutative semiring combinators on top

module Pi1 where

--  infixr 10 _◎_
--  infixr 30 _⟷_

  -- types

  data U : Set where
    EQUIV : {t₁ t₂ : Pi0.U•} → (t₁ Pi0.⟷ t₂) → U

  -- values

  data Path⊤ : Set where
    pathtt : Path⊤

  data Path⊎ (A B : Set) : Set where
    pathLeft  : A → Path⊎ A B
    pathRight : B → Path⊎ A B

  data Path× (A B : Set) : Set where
    pathPair : A → B → Path× A B

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

  data PathRev (A : Set) : Set where
    pathRev : A → PathRev A

  record PathTrans (A : Set) (B C : A → Set) : Set where
    constructor pathTrans
    field
      anchor : A
      pre    : B anchor
      post   : C anchor

  mutual
    ⟦_⟧ : U → Set
    ⟦ EQUIV c ⟧ = Paths c -- space of paths corresponding to c

    Paths : {t₁ t₂ : Pi0.U•} → (t₁ Pi0.⟷ t₂) → Set
    Paths {Pi0.•[ .(Pi0.PLUS Pi0.ZERO ∣_∣) , .(inj₂ •) ]} {Pi0.•[ ∣_∣ , • ]} Pi0.unite₊ = Unite₊ (inj₂ •) •
    Paths {Pi0.•[ ∣_∣ , • ]} {Pi0.•[ .(Pi0.PLUS Pi0.ZERO ∣_∣) , .(inj₂ •) ]} Pi0.uniti₊ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.swap1₊ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.swap2₊ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.assocl1₊ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.assocl2₊ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.assocl3₊ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.assocr1₊ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.assocr2₊ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.assocr3₊ = {!!}
    Paths {Pi0.•[ .(Pi0.TIMES Pi0.ONE ∣_∣) , .(tt , •) ]} {Pi0.•[ ∣_∣ , • ]} Pi0.unite⋆ = {!!}
    Paths {Pi0.•[ ∣_∣ , • ]} {Pi0.•[ .(Pi0.TIMES Pi0.ONE ∣_∣) , .(tt , •) ]} Pi0.uniti⋆ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.swap⋆ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.assocl⋆ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.assocr⋆ = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.dist1 = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.dist2 = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.factor1 = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} Pi0.factor2 = {!!}
    Paths {Pi0.•[ ∣_∣ , • ]} {Pi0.•[ .∣_∣ , .• ]} Pi0.id⟷ = {!!}
    Paths {Pi0.•[ ∣_∣ , • ]} {Pi0.•[ ∣_∣₁ , •₁ ]} (Pi0.sym⟷ c) = {!!}
    Paths {Pi0.•[ ∣_∣ , • ]} {Pi0.•[ ∣_∣₁ , •₁ ]} (c Pi0.◎ c₁) = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} (c Pi0.⊕1 c₁) = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} (c Pi0.⊕2 c₁) = {!!}
    Paths {Pi0.•[ ._ , ._ ]} {Pi0.•[ ._ , ._ ]} (c Pi0.⊗ c₁) = {!!} 
{--
    Paths Pi0.unite₊ (inj₁ ()) v 
    Paths Pi0.unite₊ (inj₂ v') v = Unite₊ v (inj₂ v')
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
    Paths (Pi0.sym⟷ c) v v' = PathRev (Paths c v' v)
    Paths (Pi0._◎_ {t₂ = t₂} c₁ c₂) v₁ v₃ = 
      PathTrans Pi0.⟦ t₂ ⟧ (λ v₂ → Paths c₁ v₁ v₂) (λ v₂ → Paths c₂ v₂ v₃)
    Paths (c₁ Pi0.⊕ c₂) (inj₁ v₁) (inj₁ v₁') = Path⊎ (Paths c₁ v₁ v₁') ⊥
    Paths (c₁ Pi0.⊕ c₂) (inj₁ v₁) (inj₂ v₂') = ⊥
    Paths (c₁ Pi0.⊕ c₂) (inj₂ v₂) (inj₁ v₁') = ⊥
    Paths (c₁ Pi0.⊕ c₂) (inj₂ v₂) (inj₂ v₂') = Path⊎ ⊥ (Paths c₂ v₂ v₂')
    Paths (c₁ Pi0.⊗ c₂) (v₁ , v₂) (v₁' , v₂') = 
      Path× (Paths c₁ v₁ v₁') (Paths c₂ v₂ v₂')

  -- Examples
  -- A few paths between FALSE and FALSE

  p₁ : ⟦ EQUIV Pi0.id⟷ Pi0.FALSE Pi0.FALSE ⟧
  p₁ = pathId⟷ Pi0.FALSE 

  p₂ : ⟦ EQUIV (Pi0.id⟷ Pi0.◎ Pi0.id⟷) Pi0.FALSE Pi0.FALSE ⟧
  p₂ = pathTrans Pi0.FALSE p₁ p₁

  p₃ : ⟦ EQUIV (Pi0.swap₊ Pi0.◎ Pi0.swap₊) Pi0.FALSE Pi0.FALSE ⟧
  p₃ = pathTrans Pi0.TRUE (path2Swap₊ tt) (path1Swap₊ tt)

  p₄ : ⟦ EQUIV (Pi0.id⟷ Pi0.⊕ Pi0.id⟷) Pi0.FALSE Pi0.FALSE ⟧
  p₄ = pathRight (pathId⟷ tt)

  -- A few paths between (TRUE,TRUE) and (TRUE,TRUE)

  p₅ : ⟦ EQUIV Pi0.id⟷ (Pi0.TRUE , Pi0.TRUE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₅ = pathId⟷ (Pi0.TRUE , Pi0.TRUE)

  p₆ : ⟦ EQUIV (Pi0.id⟷ Pi0.⊗ Pi0.id⟷) 
        (Pi0.TRUE , Pi0.TRUE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₆ = pathPair (pathId⟷ Pi0.TRUE) (pathId⟷ Pi0.TRUE)

  -- A few paths between (TRUE,FALSE) and (TRUE,TRUE)

  p₇ : ⟦ EQUIV (Pi0.id⟷ Pi0.⊗ Pi0.swap₊) 
        (Pi0.TRUE , Pi0.FALSE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₇ = pathPair (pathId⟷ Pi0.TRUE) (path2Swap₊ tt)

  p₇' : ⟦ EQUIV (Pi0.swap₊ Pi0.⊗ Pi0.id⟷)
        (Pi0.FALSE , Pi0.TRUE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₇' = pathPair (path2Swap₊ tt) (pathId⟷ Pi0.TRUE) 

  p₈ : ⟦ EQUIV Pi0.CNOT (Pi0.TRUE , Pi0.FALSE) (Pi0.TRUE , Pi0.TRUE) ⟧
  p₈ = pathTrans (inj₁ (tt , Pi0.FALSE))
         (path1Dist tt Pi0.FALSE)
         (pathTrans (inj₁ (tt , Pi0.TRUE))
            (pathLeft (pathPair (pathId⟷ tt) (path2Swap₊ tt)))
            (path1Factor tt Pi0.TRUE))

  -- groupoid combinators to reason about id, rev, and trans
  data _⟷_ : U → U → Set where
    id⟷    : {t₁ t₂ : Pi0.U} {c : t₁ Pi0.⟷ t₂} {v₀ : Pi0.⟦ t₁ ⟧} {v₁ : Pi0.⟦ t₂ ⟧} → EQUIV c v₀ v₁ ⟷ EQUIV c v₀ v₁
    sym⟷  : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    lidl    : {t₁ t₂ : Pi0.U} 
              {c : t₁ Pi0.⟷ t₂} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} → 
              EQUIV (Pi0.id⟷ Pi0.◎ c) v₁ v₂ ⟷ EQUIV c v₁ v₂
    lidr    : {t₁ t₂ : Pi0.U} 
              {c : t₁ Pi0.⟷ t₂} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} → 
              EQUIV c v₁ v₂ ⟷ EQUIV (Pi0.id⟷ Pi0.◎ c) v₁ v₂
    ridl    : {t₁ t₂ : Pi0.U} 
              {c : t₁ Pi0.⟷ t₂} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} → 
              EQUIV (c Pi0.◎ Pi0.id⟷) v₁ v₂ ⟷ EQUIV c v₁ v₂
    ridr    : {t₁ t₂ : Pi0.U} 
              {c : t₁ Pi0.⟷ t₂} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} → 
              EQUIV c v₁ v₂ ⟷ EQUIV (c Pi0.◎ Pi0.id⟷) v₁ v₂
    invll   : {t₁ t₂ : Pi0.U} {c : t₁ Pi0.⟷ t₂} {v₀ v₂ : Pi0.⟦ t₂ ⟧}  → 
              EQUIV (Pi0.sym⟷ c Pi0.◎ c) v₀ v₂ ⟷ EQUIV Pi0.id⟷ v₀ v₂
    invlr   : {t₁ t₂ : Pi0.U} {c : t₁ Pi0.⟷ t₂} {v₀ v₂ : Pi0.⟦ t₂ ⟧}  → 
              EQUIV Pi0.id⟷ v₀ v₂ ⟷ EQUIV (Pi0.sym⟷ c Pi0.◎ c) v₀ v₂ 
    invrl   : {t₁ t₂ : Pi0.U} {c : t₁ Pi0.⟷ t₂} {v₀ v₁ : Pi0.⟦ t₁ ⟧}  → 
              EQUIV (c Pi0.◎ Pi0.sym⟷ c) v₀ v₁ ⟷ EQUIV Pi0.id⟷ v₀ v₁
    invrr   : {t₁ t₂ : Pi0.U} {c : t₁ Pi0.⟷ t₂} {v₀ v₁ : Pi0.⟦ t₁ ⟧}  → 
              EQUIV Pi0.id⟷ v₀ v₁ ⟷ EQUIV (c Pi0.◎ Pi0.sym⟷ c) v₀ v₁
    invinvl : {t₁ t₂ : Pi0.U} 
              {c : t₁ Pi0.⟷ t₂} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} → 
              EQUIV (Pi0.sym⟷ (Pi0.sym⟷ c)) v₁ v₂ ⟷ EQUIV c v₁ v₂
    invinvr : {t₁ t₂ : Pi0.U} 
              {c : t₁ Pi0.⟷ t₂} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} → 
              EQUIV c v₁ v₂ ⟷ EQUIV (Pi0.sym⟷ (Pi0.sym⟷ c)) v₁ v₂ 
    tassocl : {t₁ t₂ t₃ t₄ : Pi0.U} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} {c₃ : t₃ Pi0.⟷ t₄}
              {v₁ : Pi0.⟦ t₁ ⟧} {v₄ : Pi0.⟦ t₄ ⟧} → 
              EQUIV (c₁ Pi0.◎ (c₂ Pi0.◎ c₃)) v₁ v₄ ⟷ 
              EQUIV ((c₁ Pi0.◎ c₂) Pi0.◎ c₃) v₁ v₄
    tassocr : {t₁ t₂ t₃ t₄ : Pi0.U} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} {c₃ : t₃ Pi0.⟷ t₄}
              {v₁ : Pi0.⟦ t₁ ⟧} {v₄ : Pi0.⟦ t₄ ⟧} → 
              EQUIV ((c₁ Pi0.◎ c₂) Pi0.◎ c₃) v₁ v₄ ⟷ 
              EQUIV (c₁ Pi0.◎ (c₂ Pi0.◎ c₃)) v₁ v₄ 
    -- this is closely related to Eckmann-Hilton
    resp◎   : {t₁ t₂ t₃ : Pi0.U} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} 
              {c₃ : t₁ Pi0.⟷ t₂} {c₄ : t₂ Pi0.⟷ t₃} 
              {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} {v₃ : Pi0.⟦ t₃ ⟧} → 
              (EQUIV c₁ v₁ v₂ ⟷ EQUIV c₃ v₁ v₂) → 
              (EQUIV c₂ v₂ v₃ ⟷ EQUIV c₄ v₂ v₃) → 
               EQUIV (c₁ Pi0.◎ c₂) v₁ v₃ ⟷ EQUIV (c₃ Pi0.◎ c₄) v₁ v₃

  -- Examples
  -- id;swap₊ is equivalent to swap₊
  e₁ : EQUIV (Pi0.id⟷ Pi0.◎ Pi0.swap₊) Pi0.FALSE Pi0.TRUE ⟷ 
       EQUIV Pi0.swap₊ Pi0.FALSE Pi0.TRUE
  e₁ = lidl

  -- swap₊;id;swap₊ is equivalent to id
  e₂ : EQUIV (Pi0.swap₊ Pi0.◎ (Pi0.id⟷ Pi0.◎ Pi0.swap₊)) Pi0.FALSE Pi0.FALSE ⟷ 
       EQUIV Pi0.id⟷ Pi0.FALSE Pi0.FALSE 
  e₂ = {!!}


  arr : {t₁ t₂ : Pi0.U} {c : t₁ Pi0.⟷ t₂} → Pi0.⟦ t₁ ⟧ → Pi0.⟦ t₂ ⟧ → Set
  arr {t₁} {t₂} {c} v₁ v₂ = ⟦ EQUIV c v₁ v₂ ⟧
 
  -- we have a 1Groupoid structure
  G : 1Groupoid
  G = record
        { set = Pi0.U
        ; _↝_ = Pi0._⟷_
        ; _≈_ = λ c₀ c₁ → ∀ {v₀ v₁} → EQUIV c₀ v₀ v₁ ⟷ EQUIV c₁ v₀ v₁
        ; id = Pi0.id⟷
        ; _∘_ = λ c₀ c₁ → c₁ Pi0.◎ c₀
        ; _⁻¹ = Pi0.sym⟷
        ; lneutr = λ α → ridl {c = α}
        ; rneutr = λ α → lidl { c = α}
        ; assoc = λ α β δ {v₁} {v₄} → tassocl 
        ; equiv = record { refl = λ {c} {v₀} {v₁} → id⟷
                                   ; sym = λ c → sym⟷ c 
                                   ; trans = λ c₀ c₁ → c₀ ◎ c₁ }
        ; linv = λ α → invrl {c = α}
        ; rinv = λ α → invll {c = α}
        ; ∘-resp-≈ = λ {x} {y} {z} {f} {h} {g} {i} f⟷h g⟷i {v₀} {v₁} → 
                     resp◎ {x} {y} {z} {g} {f} {i} {h} {v₀} {{!val f⟷h!}} {v₁} 
                       g⟷i f⟷h 
        }

------------------------------------------------------------------------------


--}
