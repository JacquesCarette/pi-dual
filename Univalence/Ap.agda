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
-- so we use pointed types to express them

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

  Space : (t• : U•) → Set
  Space •[ t , v ] = ⟦ t ⟧

  point : (t• : U•) → Space t• 
  point •[ t , v ] = v

  -- examples

  ONE• : U•
  ONE• = •[ ONE , tt ]

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

  -- equivalences between pointed types

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

  -- examples

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

  --  proof that we have a groupoid structure ???

------------------------------------------------------------------------------
-- Level 1 
-- types are collections of paths, where these paths are the level 0 
-- commutative semiring equivalences between points
-- equivalences are groupoid combinators in addition to another layer
-- of commutative semiring combinators 

module Pi1 where

  infixr 10 _◎_
  infixr 30 _⟷_

  -- types

  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
    PATH  : {t₁ t₂ : Pi0.U•} → (t₁ Pi0.⟷ t₂) → U

  -- values

  data Path {t₁ t₂ : Pi0.U•} : (Pi0.Space t₁) → (Pi0.Space t₂) → Set where
    path : (c : t₁ Pi0.⟷ t₂) → Path (Pi0.point t₁) (Pi0.point t₂)

  ⟦_⟧ : U → Set
  ⟦ ZERO ⟧             = ⊥
  ⟦ ONE ⟧              = ⊤
  ⟦ PLUS t₁ t₂ ⟧       = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ TIMES t₁ t₂ ⟧      = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ PATH {t₁} {t₂} c ⟧ = Path {t₁} {t₂} (Pi0.point t₁) (Pi0.point t₂) 

  -- pointed types

  record U• : Set where
    constructor •[_,_]
    field
      ∣_∣ : U
      • : ⟦ ∣_∣ ⟧

  open U•

  Space : (t• : U•) → Set
  Space •[ t , p ] = ⟦ t ⟧

  point : (t• : U•) → Space t• 
  point •[ t , p ] = p

  _∘_ : {t₁ t₂ t₃ : Pi0.U•} → 
        Path (Pi0.point t₁) (Pi0.point t₂) → 
        Path (Pi0.point t₂) (Pi0.point t₃) →
        Path (Pi0.point t₁) (Pi0.point t₃)
  path c₁ ∘ path c₂ = path (c₁ Pi0.◎ c₂)

  PathSpace : {t₁ t₂ : Pi0.U•} → (c : t₁ Pi0.⟷ t₂) → U•
  PathSpace c = •[ PATH c , path c ]

  -- examples
  -- several paths between T and F; some of these will be equivalent
  
  p₁ p₂ p₃ p₄ : Path Pi0.TRUE Pi0.FALSE
  p₁ = path Pi0.swap1₊ 
  p₂ = path (Pi0.swap1₊ Pi0.◎ Pi0.id⟷)
  p₃ = path (Pi0.swap1₊ Pi0.◎ Pi0.swap2₊ Pi0.◎ Pi0.swap1₊)
  p₄ = path (Pi0.uniti⋆ Pi0.◎ 
             Pi0.swap⋆ Pi0.◎ 
             (Pi0.swap1₊ Pi0.⊗ Pi0.id⟷) Pi0.◎ 
             Pi0.swap⋆ Pi0.◎ 
             Pi0.unite⋆)

  -- groupoid combinators to reason about id, sym, and trans
  -- commutative semiring combinators for 0, 1, +, *

  data _⟷_ : U• → U• → Set where

    -- common combinators

    id⟷    : {t : U•} → t ⟷ t
    sym⟷   : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_     : {t₁ t₂ t₃ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)

    -- groupoid combinators

    lidl    : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace (Pi0.id⟷ Pi0.◎ c) ⟷ PathSpace c
    lidr    : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace c ⟷ PathSpace (Pi0.id⟷ Pi0.◎ c)
    ridl    : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace (c Pi0.◎ Pi0.id⟷) ⟷ PathSpace c
    ridr    : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace c ⟷ PathSpace (c Pi0.◎ Pi0.id⟷)
    invll   : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace (Pi0.sym⟷ c Pi0.◎ c) ⟷ PathSpace {t₂} {t₂} Pi0.id⟷ 
    invlr   : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace {t₂} {t₂} Pi0.id⟷ ⟷ PathSpace (Pi0.sym⟷ c Pi0.◎ c)
    invrl   : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace (c Pi0.◎ Pi0.sym⟷ c) ⟷ PathSpace {t₁} {t₁} Pi0.id⟷
    invrr   : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace {t₁} {t₁} Pi0.id⟷ ⟷ PathSpace (c Pi0.◎ Pi0.sym⟷ c)
    invinvl : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace (Pi0.sym⟷ (Pi0.sym⟷ c)) ⟷ PathSpace c
    invinvr : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PathSpace c ⟷ PathSpace (Pi0.sym⟷ (Pi0.sym⟷ c))
    tassocl : {t₁ t₂ t₃ t₄ : Pi0.U•} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} {c₃ : t₃ Pi0.⟷ t₄} → 
              PathSpace (c₁ Pi0.◎ (c₂ Pi0.◎ c₃)) ⟷ 
              PathSpace ((c₁ Pi0.◎ c₂) Pi0.◎ c₃)
    tassocr : {t₁ t₂ t₃ t₄ : Pi0.U•} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} {c₃ : t₃ Pi0.⟷ t₄} → 
              PathSpace ((c₁ Pi0.◎ c₂) Pi0.◎ c₃) ⟷ 
              PathSpace (c₁ Pi0.◎ (c₂ Pi0.◎ c₃))
    -- resp◎ is closely related to Eckmann-Hilton
    resp◎   : {t₁ t₂ t₃ : Pi0.U•} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} 
              {c₃ : t₁ Pi0.⟷ t₂} {c₄ : t₂ Pi0.⟷ t₃} → 
              (PathSpace c₁ ⟷ PathSpace c₃) → 
              (PathSpace c₂ ⟷ PathSpace c₄) → 
              PathSpace (c₁ Pi0.◎ c₂) ⟷ PathSpace (c₃ Pi0.◎ c₄)

    -- commutative semiring combinators

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
    _⊕1_   : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
             (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₁ (• t₁) ] ⟷ 
              •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₁ (• t₃) ])
    _⊕2_   : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
             (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₂ (• t₂) ] ⟷ 
              •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₂ (• t₄) ])
    _⊗_     : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
            (•[ TIMES ∣ t₁ ∣ ∣ t₂ ∣ , (• t₁ , • t₂ ) ] ⟷ 
             •[ TIMES ∣ t₃ ∣ ∣ t₄ ∣ , (• t₃ , • t₄ ) ])

  -- proof that we have a 1Groupoid structure

  G : 1Groupoid
  G = record
        { set = Pi0.U•
        ; _↝_ = Pi0._⟷_
        ; _≈_ = λ c₀ c₁ → PathSpace c₀ ⟷ PathSpace c₁
        ; id = Pi0.id⟷
        ; _∘_ = λ c₀ c₁ → c₁ Pi0.◎ c₀
        ; _⁻¹ = Pi0.sym⟷
        ; lneutr = λ _ → ridl
        ; rneutr = λ _ → lidl
        ; assoc = λ _ _ _ → tassocl
        ; equiv = record { refl = id⟷ 
                                ; sym = λ c → sym⟷ c 
                                ; trans = λ c₀ c₁ → c₀ ◎ c₁ }
        ; linv = λ _ → invrl 
        ; rinv = λ _ → invll 
        ; ∘-resp-≈ = λ f⟷h g⟷i → resp◎ g⟷i f⟷h 
        }

------------------------------------------------------------------------------
-- Level 2 
-- types are collections of 2paths, where these 2paths are the level 1
-- groupoid and commutative semiring equivalences between 1paths
-- equivalences are groupoid combinators in addition to another layer
-- of commutative semiring combinators 

module Pi2 where

--  infixr 10 _◎_
--  infixr 30 _⟷_

  -- types

  data U : Set where
    ZERO   : U
    ONE    : U
    PLUS   : U → U → U
    TIMES  : U → U → U
    2PATH  : {t₁ t₂ : Pi1.U•} → (t₁ Pi1.⟷ t₂) → U

  -- values

  data 2Path {t₁ t₂ : Pi1.U•} : Pi1.Space t₁ → Pi1.Space t₂ → Set where
    2path : (c : t₁ Pi1.⟷ t₂) → 2Path (Pi1.point t₁) (Pi1.point t₂)

  ⟦_⟧ : U → Set
  ⟦ ZERO ⟧             = ⊥
  ⟦ ONE ⟧              = ⊤
  ⟦ PLUS t₁ t₂ ⟧       = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ TIMES t₁ t₂ ⟧      = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ 2PATH {t₁} {t₂} c ⟧ = 2Path {t₁} {t₂} (Pi1.point t₁) (Pi1.point t₂) 

  -- pointed types

  record U• : Set where
    constructor •[_,_]
    field
      ∣_∣ : U
      • : ⟦ ∣_∣ ⟧

  open U•

  Space : (t• : U•) → Set
  Space •[ t , p ] = ⟦ t ⟧

  point : (t• : U•) → Space t• 
  point •[ t , p ] = p

  _∘_ : {t₁ t₂ t₃ : Pi1.U•} → 
        2Path (Pi1.point t₁) (Pi1.point t₂) → 
        2Path (Pi1.point t₂) (Pi1.point t₃) →
        2Path (Pi1.point t₁) (Pi1.point t₃)
  2path c₁ ∘ 2path c₂ = 2path (c₁ Pi1.◎ c₂)

  2PathSpace : {t₁ t₂ : Pi1.U•} → (c : t₁ Pi1.⟷ t₂) → U•
  2PathSpace c = •[ 2PATH c , 2path c ]

  -- examples

  -- groupoid combinators to reason about id, sym, and trans
  -- commutative semiring combinators for 0, 1, +, *

  data _⟷_ : U• → U• → Set where

    -- common combinators

    id⟷    : {t : U•} → t ⟷ t
    sym⟷   : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_     : {t₁ t₂ t₃ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)

    -- groupoid combinators

    lidl    : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace (Pi1.id⟷ Pi1.◎ c) ⟷ 2PathSpace c
    lidr    : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace c ⟷ 2PathSpace (Pi1.id⟷ Pi1.◎ c)
    ridl    : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace (c Pi1.◎ Pi1.id⟷) ⟷ 2PathSpace c
    ridr    : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace c ⟷ 2PathSpace (c Pi1.◎ Pi1.id⟷)
    invll   : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace (Pi1.sym⟷ c Pi1.◎ c) ⟷ 2PathSpace {t₂} {t₂} Pi1.id⟷ 
    invlr   : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace {t₂} {t₂} Pi1.id⟷ ⟷ 2PathSpace (Pi1.sym⟷ c Pi1.◎ c)
    invrl   : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace (c Pi1.◎ Pi1.sym⟷ c) ⟷ 2PathSpace {t₁} {t₁} Pi1.id⟷
    invrr   : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace {t₁} {t₁} Pi1.id⟷ ⟷ 2PathSpace (c Pi1.◎ Pi1.sym⟷ c)
    invinvl : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace (Pi1.sym⟷ (Pi1.sym⟷ c)) ⟷ 2PathSpace c
    invinvr : {t₁ t₂ : Pi1.U•} {c : t₁ Pi1.⟷ t₂} → 
              2PathSpace c ⟷ 2PathSpace (Pi1.sym⟷ (Pi1.sym⟷ c))
    tassocl : {t₁ t₂ t₃ t₄ : Pi1.U•} 
              {c₁ : t₁ Pi1.⟷ t₂} {c₂ : t₂ Pi1.⟷ t₃} {c₃ : t₃ Pi1.⟷ t₄} → 
              2PathSpace (c₁ Pi1.◎ (c₂ Pi1.◎ c₃)) ⟷ 
              2PathSpace ((c₁ Pi1.◎ c₂) Pi1.◎ c₃)
    tassocr : {t₁ t₂ t₃ t₄ : Pi1.U•} 
              {c₁ : t₁ Pi1.⟷ t₂} {c₂ : t₂ Pi1.⟷ t₃} {c₃ : t₃ Pi1.⟷ t₄} → 
              2PathSpace ((c₁ Pi1.◎ c₂) Pi1.◎ c₃) ⟷ 
              2PathSpace (c₁ Pi1.◎ (c₂ Pi1.◎ c₃))
    -- resp◎ is closely related to Eckmann-Hilton
    resp◎   : {t₁ t₂ t₃ : Pi1.U•} 
              {c₁ : t₁ Pi1.⟷ t₂} {c₂ : t₂ Pi1.⟷ t₃} 
              {c₃ : t₁ Pi1.⟷ t₂} {c₄ : t₂ Pi1.⟷ t₃} → 
              (2PathSpace c₁ ⟷ 2PathSpace c₃) → 
              (2PathSpace c₂ ⟷ 2PathSpace c₄) → 
              2PathSpace (c₁ Pi1.◎ c₂) ⟷ 2PathSpace (c₃ Pi1.◎ c₄)

    -- commutative semiring combinators

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
    _⊕1_   : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
             (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₁ (• t₁) ] ⟷ 
              •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₁ (• t₃) ])
    _⊕2_   : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
             (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₂ (• t₂) ] ⟷ 
              •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₂ (• t₄) ])
    _⊗_     : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
            (•[ TIMES ∣ t₁ ∣ ∣ t₂ ∣ , (• t₁ , • t₂ ) ] ⟷ 
             •[ TIMES ∣ t₃ ∣ ∣ t₄ ∣ , (• t₃ , • t₄ ) ])

  -- proof that we have a 1Groupoid structure

  G : 1Groupoid
  G = record
        { set = Pi1.U•
        ; _↝_ = Pi1._⟷_
        ; _≈_ = λ c₀ c₁ → 2PathSpace c₀ ⟷ 2PathSpace c₁
        ; id = Pi1.id⟷
        ; _∘_ = λ c₀ c₁ → c₁ Pi1.◎ c₀
        ; _⁻¹ = Pi1.sym⟷
        ; lneutr = λ _ → ridl
        ; rneutr = λ _ → lidl
        ; assoc = λ _ _ _ → tassocl
        ; equiv = record { refl = id⟷ 
                                ; sym = λ c → sym⟷ c 
                                ; trans = λ c₀ c₁ → c₀ ◎ c₁ }
        ; linv = λ _ → invrl 
        ; rinv = λ _ → invll 
        ; ∘-resp-≈ = λ f⟷h g⟷i → resp◎ g⟷i f⟷h 
        }

  -- examples

------------------------------------------------------------------------------

