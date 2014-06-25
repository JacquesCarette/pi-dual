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

  Space : (t• : U•) → Set
  Space •[ t , v ] = ⟦ t ⟧

  point : (t• : U•) → Space t• 
  point •[ t , v ] = v

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
-- we then add commutative semiring combinators on top

module Pi1 where

  infixr 10 _◎_
  infixr 30 _⟷_

  -- types

  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
    PATH : {t₁ t₂ : Pi0.U•} → (t₁ Pi0.⟷ t₂) → U

  -- values

{--
  data Path {t₁ t₂ : Pi0.U•} : 
    (t₁ Pi0.⟷ t₂) → (Pi0.Space t₁) → (Pi0.Space t₂) → Set where
    path : (c : t₁ Pi0.⟷ t₂) → Path c (Pi0.point t₁) (Pi0.point t₂)
--}

  data Path {t₁ t₂ : Pi0.U•} : (Pi0.Space t₁) → (Pi0.Space t₂) → Set where
    path : (c : t₁ Pi0.⟷ t₂) → Path (Pi0.point t₁) (Pi0.point t₂)

  ⟦_⟧ : U → Set
  ⟦ ZERO ⟧          = ⊥
  ⟦ ONE ⟧           = ⊤
  ⟦ PLUS t₁ t₂ ⟧    = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ TIMES t₁ t₂ ⟧   = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ PATH {t₁} {t₂} c ⟧ = Path {t₁} {t₂} (Pi0.point t₁) (Pi0.point t₂) 

  -- examples
  -- several paths
  
  p₁ : Path Pi0.TRUE Pi0.FALSE
  p₁ = path Pi0.swap1₊ 

  p₂ : Path Pi0.TRUE Pi0.FALSE
  p₂ = path (Pi0.swap1₊ Pi0.◎ Pi0.id⟷)
  
  -- groupoid combinators to reason about id, rev, and trans

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
    _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)
    id⟷    : {t : U} → t ⟷ t
    sym⟷   : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    lidl    : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH (Pi0.id⟷ Pi0.◎ c) ⟷ PATH c 
    lidr    : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH c ⟷ PATH (Pi0.id⟷ Pi0.◎ c) 
    ridl    : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH (c Pi0.◎ Pi0.id⟷) ⟷ PATH c
    ridr    : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH c ⟷ PATH (c Pi0.◎ Pi0.id⟷) 
    invll   : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH (Pi0.sym⟷ c Pi0.◎ c) ⟷ PATH {t₂} {t₂} Pi0.id⟷ 
    invlr   : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH {t₂} {t₂} Pi0.id⟷ ⟷ PATH (Pi0.sym⟷ c Pi0.◎ c) 
    invrl   : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH (c Pi0.◎ Pi0.sym⟷ c) ⟷ PATH {t₁} {t₁} Pi0.id⟷ 
    invrr   : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH {t₁} {t₁} Pi0.id⟷ ⟷ PATH (c Pi0.◎ Pi0.sym⟷ c) 
    invinvl : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} →
              PATH (Pi0.sym⟷ (Pi0.sym⟷ c)) ⟷ PATH c
    invinvr : {t₁ t₂ : Pi0.U•} {c : t₁ Pi0.⟷ t₂} → 
              PATH c ⟷ PATH (Pi0.sym⟷ (Pi0.sym⟷ c))
    tassocl : {t₁ t₂ t₃ t₄ : Pi0.U•} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} {c₃ : t₃ Pi0.⟷ t₄} → 
              PATH (c₁ Pi0.◎ (c₂ Pi0.◎ c₃)) ⟷ PATH ((c₁ Pi0.◎ c₂) Pi0.◎ c₃) 
    tassocr : {t₁ t₂ t₃ t₄ : Pi0.U•} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} {c₃ : t₃ Pi0.⟷ t₄} → 
              PATH ((c₁ Pi0.◎ c₂) Pi0.◎ c₃) ⟷ PATH (c₁ Pi0.◎ (c₂ Pi0.◎ c₃))
    -- resp◎ is closely related to Eckmann-Hilton
    resp◎   : {t₁ t₂ t₃ : Pi0.U•} 
              {c₁ : t₁ Pi0.⟷ t₂} {c₂ : t₂ Pi0.⟷ t₃} 
              {c₃ : t₁ Pi0.⟷ t₂} {c₄ : t₂ Pi0.⟷ t₃} → 
              (PATH c₁ ⟷ PATH c₃) → (PATH c₂ ⟷ PATH c₄) → 
              PATH (c₁ Pi0.◎ c₂) ⟷ PATH (c₃ Pi0.◎ c₄) 

  -- we have a 1Groupoid structure

  G : 1Groupoid
  G = record
        { set = Pi0.U•
        ; _↝_ = Pi0._⟷_
        ; _≈_ = λ c₀ c₁ → PATH c₀ ⟷ PATH c₁
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

