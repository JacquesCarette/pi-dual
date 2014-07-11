module Pi1 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Groupoid

infix  2  _□       
infixr 2  _⟷⟨_⟩_   
infix  2  _▤       
infixr 2  _⇔⟨_⟩_   
infixr 10 _◎_
infixr 30 _⟷_

------------------------------------------------------------------------------
-- Level 0: 
-- Types at this level are just plain sets with no interesting path structure. 
-- The path structure is defined at levels 1 and beyond. 

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

⟦_⟧ : U → Set
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

-- Programs
-- We use pointed types; programs map a pointed type to another
-- In other words, each program takes one particular value to another; if we
-- want to work on another value, we generally use another program. 
-- 
-- Should we way to collect these fibers into a collection somehow...

record U• : Set where
  constructor •[_,_]
  field
    ∣_∣ : U
    • : ⟦ ∣_∣ ⟧

open U•

-- examples of plain types, values, and pointed types

ZERO• : {absurd : ⟦ ZERO ⟧} →  U•
ZERO• {absurd} = •[ ZERO , absurd ]

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

-- The actual programs are the commutative semiring isomorphisms between
-- pointed types.

data _⟷_ : U• → U• → Set where
  unite₊  : ∀ {t v} → •[ PLUS ZERO t , inj₂ v ] ⟷ •[ t , v ]
  uniti₊  : ∀ {t v} → •[ t , v ] ⟷ •[ PLUS ZERO t , inj₂ v ]
  swap1₊  : ∀ {t₁ t₂ v₁} → 
            •[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₂ t₁ , inj₂ v₁ ]
  swap2₊  : ∀ {t₁ t₂ v₂} → 
            •[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₂ t₁ , inj₁ v₂ ]
  assocl1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ]
  assocl2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ]
  assocl3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ]
  assocr1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] 
  assocr2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] 
  assocr3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
  unite⋆  : ∀ {t v} → •[ TIMES ONE t , (tt , v) ] ⟷ •[ t , v ]
  uniti⋆  : ∀ {t v} → •[ t , v ] ⟷ •[ TIMES ONE t , (tt , v) ] 
  swap⋆   : ∀ {t₁ t₂ v₁ v₂} → 
              •[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₂ t₁ , (v₂ , v₁) ]
  assocl⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ] ⟷ 
            •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ]
  assocr⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ] ⟷ 
            •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ]
  distz : ∀ {t v absurd} → 
            •[ TIMES ZERO t , (absurd , v) ] ⟷ •[ ZERO , absurd ]
  factorz : ∀ {t v absurd} → 
            •[ ZERO , absurd ] ⟷ •[ TIMES ZERO t , (absurd , v) ]
  dist1   : ∀ {t₁ t₂ t₃ v₁ v₃} → 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ⟷ 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ]
  dist2   : ∀ {t₁ t₂ t₃ v₂ v₃} → 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ⟷ 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ]
  factor1   : ∀ {t₁ t₂ t₃ v₁ v₃} → 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ⟷ 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ]
  factor2   : ∀ {t₁ t₂ t₃ v₂ v₃} → 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ⟷ 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ]
  id⟷    : ∀ {t v} → •[ t , v ] ⟷ •[ t , v ]
  _◎_    : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
           (•[ t₂ , v₂ ] ⟷ •[ t₃ , v₃ ]) → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ])
  ⊕1   : ∀ {t₁ t₂ t₃ t₄ v₁ v₃} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → 
           (•[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₃ t₄ , inj₁ v₃ ])
  ⊕2   : ∀ {t₁ t₂ t₃ t₄ v₂ v₄} → 
           (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₃ t₄ , inj₂ v₄ ])
  _⊗_     : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
          (•[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₃ t₄ , (v₃ , v₄) ])

! : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊ = uniti₊
! uniti₊ = unite₊
! swap1₊ = swap2₊
! swap2₊ = swap1₊
! assocl1₊ = assocr1₊
! assocl2₊ = assocr2₊
! assocl3₊ = assocr3₊
! assocr1₊ = assocl1₊
! assocr2₊ = assocl2₊
! assocr3₊ = assocl3₊
! unite⋆ = uniti⋆
! uniti⋆ = unite⋆
! swap⋆ = swap⋆
! assocl⋆ = assocr⋆
! assocr⋆ = assocl⋆
! distz = factorz
! factorz = distz
! dist1 = factor1 
! dist2 = factor2 
! factor1 = dist1 
! factor2 = dist2 
! id⟷ = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁ 
! (⊕1 c₁) = ⊕1 (! c₁)
! (⊕2 c₂) = ⊕2 (! c₂)
! (c₁ ⊗ c₂) = ! c₁ ⊗ ! c₂ 

-- example programs using nicer syntax that shows intermediate values
-- instead of point-free combinators

_⟷⟨_⟩_ : (t₁ : U•) {t₂ : U•} {t₃ : U•} → 
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃) 
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U•) → {t : U•} → (t ⟷ t)
_□ t = id⟷

-- 

NOT•T : •[ BOOL , TRUE ] ⟷ •[ BOOL , FALSE ]
NOT•T = swap1₊

NOT•F : •[ BOOL , FALSE ] ⟷ •[ BOOL , TRUE ]
NOT•F = swap2₊

CNOT•Fx : {b : ⟦ BOOL ⟧} → 
          •[ BOOL² , (FALSE , b) ] ⟷ •[ BOOL² , (FALSE , b) ]
CNOT•Fx = dist2 ◎ (⊕2 id⟷) ◎ factor2

CNOT•TF : •[ BOOL² , (TRUE , FALSE) ] ⟷ •[ BOOL² , (TRUE , TRUE) ]
CNOT•TF = dist1 ◎ 
          (⊕1 (id⟷ ⊗ NOT•F)) ◎
          factor1

{--
point free style 

CNOT•TT : •[ BOOL² , (TRUE , TRUE) ] ⟷ •[ BOOL² , (TRUE , FALSE) ]
CNOT•TT = dist1 ◎ 
          ((id⟷ ⊗ NOT•T) ⊕1 (id⟷ {TIMES ONE BOOL} {(tt , TRUE)})) ◎ 
          factor1
--}

CNOT•TT : •[ BOOL² , (TRUE , TRUE) ] ⟷ •[ BOOL² , (TRUE , FALSE) ]
CNOT•TT = •[ BOOL² , (TRUE , TRUE) ]
             ⟷⟨ dist1 ⟩ 
           •[ PLUS (TIMES ONE BOOL) (TIMES ONE BOOL) , inj₁ (tt , TRUE) ]
             ⟷⟨ ⊕1 (id⟷ ⊗ NOT•T)⟩ 
           •[ PLUS (TIMES ONE BOOL) (TIMES ONE BOOL) , inj₁ (tt , FALSE) ]
             ⟷⟨ factor1 ⟩
           •[ BOOL² , (TRUE , FALSE) ] □

CNOT•TT' : ∀ {t v} → 
  •[ TIMES (PLUS t ONE) BOOL , (inj₁ v , TRUE) ] ⟷ 
  •[ TIMES (PLUS t ONE) BOOL , (inj₁ v , FALSE) ]
CNOT•TT' {t} {v} = 
  •[ TIMES (PLUS t ONE) BOOL , (inj₁ v , TRUE) ]
    ⟷⟨ dist1 ⟩ 
  •[ PLUS (TIMES t BOOL) (TIMES ONE BOOL) , inj₁ (v , TRUE) ]
    ⟷⟨ ⊕1 (id⟷ ⊗ NOT•T)⟩ 
  •[ PLUS (TIMES t BOOL) (TIMES ONE BOOL) , inj₁ (v , FALSE) ]
    ⟷⟨ factor1 ⟩
  •[ TIMES (PLUS t ONE) BOOL , (inj₁ v , FALSE) ] □

-- The universe of types is a groupoid. The objects of this groupoid are the
-- pointed types; the morphisms are the programs; and the equivalence of
-- programs is the degenerate observational equivalence that equates every
-- two programs that are extensionally equivalent.

_obs≅_ : {t₁ t₂ : U•} → (c₁ c₂ : t₁ ⟷ t₂) → Set
c₁ obs≅ c₂ = ⊤ 

UG : 1Groupoid
UG = record
       { set = U•
       ; _↝_ = _⟷_
       ; _≈_ = _obs≅_
       ; id = id⟷
       ; _∘_ = λ y⟷z x⟷y → x⟷y ◎ y⟷z 
       ; _⁻¹ = !
       ; lneutr = λ _ → tt 
       ; rneutr = λ _ → tt 
       ; assoc = λ _ _ _ → tt
       ; equiv = record { refl = tt 
                        ; sym = λ _ → tt 
                        ; trans = λ _ _ → tt 
                        } 
       ; linv = λ _ → tt 
       ; rinv = λ _ → tt 
       ; ∘-resp-≈ = λ _ _ → tt
       }

------------------------------------------------------------------------------
-- Level 1: 
-- Types are sets of paths. The paths are defined at level 0.  At level 1,
-- there is no interesting 2path structure. From the perspective of level 0,
-- we have points with non-trivial paths between them, i.e., we have a
-- groupoid. The paths cross type boundaries, i.e., we have heterogeneous
-- equality

-- types

data 1U : Set where
  1ZERO  : 1U              -- empty set of paths
  1ONE   : 1U              -- a trivial path
  1PLUS  : 1U → 1U → 1U      -- disjoint union of paths
  1TIMES : 1U → 1U → 1U      -- pairs of paths
  PATH  : (t₁ t₂ : U•) → 1U -- level 0 paths between values

-- values

data Path (t₁ t₂ : U•) : Set where
  path : (c : t₁ ⟷ t₂) → Path t₁ t₂

1⟦_⟧ : 1U → Set
1⟦ 1ZERO ⟧             = ⊥
1⟦ 1ONE ⟧              = ⊤
1⟦ 1PLUS t₁ t₂ ⟧       = 1⟦ t₁ ⟧ ⊎ 1⟦ t₂ ⟧
1⟦ 1TIMES t₁ t₂ ⟧      = 1⟦ t₁ ⟧ × 1⟦ t₂ ⟧
1⟦ PATH t₁ t₂ ⟧ = Path t₁ t₂

-- examples

T⟷F : Set
T⟷F = Path BOOL•T BOOL•F

F⟷T : Set
F⟷T = Path BOOL•F BOOL•T

p₁ p₂ p₃ p₄ p₅ : T⟷F
p₁ = path NOT•T
p₂ = path (id⟷ ◎ NOT•T)
p₃ = path (NOT•T ◎ NOT•F ◎ NOT•T)
p₄ = path (NOT•T ◎ id⟷)
p₅ = path (uniti⋆ ◎ swap⋆ ◎ (NOT•T ⊗ id⟷) ◎ swap⋆ ◎ unite⋆)
   
p₆ : (T⟷F × T⟷F) ⊎ F⟷T
p₆ = inj₁ (p₁ , p₂)

-- Programs map paths to paths. We also use pointed types.

record 1U• : Set where
  constructor 1•[_,_]
  field
    1∣_∣ : 1U
    1• : 1⟦ 1∣_∣ ⟧

open 1U•

data _⇔_ : 1U• → 1U• → Set where
  unite₊  : ∀ {t v} → 1•[ 1PLUS 1ZERO t , inj₂ v ] ⇔ 1•[ t , v ]
  uniti₊  : ∀ {t v} → 1•[ t , v ] ⇔ 1•[ 1PLUS 1ZERO t , inj₂ v ]
  swap1₊  : ∀ {t₁ t₂ v₁} → 
            1•[ 1PLUS t₁ t₂ , inj₁ v₁ ] ⇔ 1•[ 1PLUS t₂ t₁ , inj₂ v₁ ]
  swap2₊  : ∀ {t₁ t₂ v₂} → 
            1•[ 1PLUS t₁ t₂ , inj₂ v₂ ] ⇔ 1•[ 1PLUS t₂ t₁ , inj₁ v₂ ]
  assocl1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₁ v₁ ] ⇔ 
             1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ]
  assocl2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] ⇔ 
             1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ]
  assocl3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] ⇔ 
             1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₂ v₃ ]
  assocr1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ] ⇔ 
             1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₁ v₁ ] 
  assocr2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ] ⇔ 
             1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] 
  assocr3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             1•[ 1PLUS (1PLUS t₁ t₂) t₃ , inj₂ v₃ ] ⇔ 
             1•[ 1PLUS t₁ (1PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
  unite⋆  : ∀ {t v} → 1•[ 1TIMES 1ONE t , (tt , v) ] ⇔ 1•[ t , v ]
  uniti⋆  : ∀ {t v} → 1•[ t , v ] ⇔ 1•[ 1TIMES 1ONE t , (tt , v) ] 
  swap⋆   : ∀ {t₁ t₂ v₁ v₂} → 
              1•[ 1TIMES t₁ t₂ , (v₁ , v₂) ] ⇔ 1•[ 1TIMES t₂ t₁ , (v₂ , v₁) ]
  assocl⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            1•[ 1TIMES t₁ (1TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ] ⇔ 
            1•[ 1TIMES (1TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ]
  assocr⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            1•[ 1TIMES (1TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ] ⇔ 
            1•[ 1TIMES t₁ (1TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ]
  distz : ∀ {t v absurd} → 
            1•[ 1TIMES 1ZERO t , (absurd , v) ] ⇔ 1•[ 1ZERO , absurd ]
  factorz : ∀ {t v absurd} → 
            1•[ 1ZERO , absurd ] ⇔ 1•[ 1TIMES 1ZERO t , (absurd , v) ]
  dist1   : ∀ {t₁ t₂ t₃ v₁ v₃} → 
            1•[ 1TIMES (1PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ⇔ 
            1•[ 1PLUS (1TIMES t₁ t₃) (1TIMES t₂ t₃) , inj₁ (v₁ , v₃) ]
  dist2   : ∀ {t₁ t₂ t₃ v₂ v₃} → 
            1•[ 1TIMES (1PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ⇔ 
            1•[ 1PLUS (1TIMES t₁ t₃) (1TIMES t₂ t₃) , inj₂ (v₂ , v₃) ]
  factor1   : ∀ {t₁ t₂ t₃ v₁ v₃} → 
            1•[ 1PLUS (1TIMES t₁ t₃) (1TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ⇔ 
            1•[ 1TIMES (1PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ]
  factor2   : ∀ {t₁ t₂ t₃ v₂ v₃} → 
            1•[ 1PLUS (1TIMES t₁ t₃) (1TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ⇔ 
            1•[ 1TIMES (1PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ]
  id⇔    : ∀ {t v} → 1•[ t , v ] ⇔ 1•[ t , v ]
  _◎_    : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → (1•[ t₁ , v₁ ] ⇔ 1•[ t₂ , v₂ ]) → 
           (1•[ t₂ , v₂ ] ⇔ 1•[ t₃ , v₃ ]) → 
           (1•[ t₁ , v₁ ] ⇔ 1•[ t₃ , v₃ ])
  ⊕1   : ∀ {t₁ t₂ t₃ t₄ v₁ v₃} → 
           (1•[ t₁ , v₁ ] ⇔ 1•[ t₃ , v₃ ]) → 
           (1•[ 1PLUS t₁ t₂ , inj₁ v₁ ] ⇔ 1•[ 1PLUS t₃ t₄ , inj₁ v₃ ])
  ⊕2   : ∀ {t₁ t₂ t₃ t₄ v₂ v₄} → 
           (1•[ t₂ , v₂ ] ⇔ 1•[ t₄ , v₄ ]) → 
           (1•[ 1PLUS t₁ t₂ , inj₂ v₂ ] ⇔ 1•[ 1PLUS t₃ t₄ , inj₂ v₄ ])
  _⊗_     : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (1•[ t₁ , v₁ ] ⇔ 1•[ t₃ , v₃ ]) → (1•[ t₂ , v₂ ] ⇔ 1•[ t₄ , v₄ ]) → 
          (1•[ 1TIMES t₁ t₂ , (v₁ , v₂) ] ⇔ 1•[ 1TIMES t₃ t₄ , (v₃ , v₄) ])
  lidl : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂} → 
        1•[ PATH t₁ t₂ , path (id⟷ ◎ c) ] ⇔ 1•[ PATH t₁ t₂ , path c ]
  lidr : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂} → 
        1•[ PATH t₁ t₂ , path c ] ⇔ 1•[ PATH t₁ t₂ , path (id⟷ ◎ c) ] 
  ridl : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂} → 
        1•[ PATH t₁ t₂ , path (c ◎ id⟷) ] ⇔ 1•[ PATH t₁ t₂ , path c ]
  ridr : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂} → 
        1•[ PATH t₁ t₂ , path c ] ⇔ 1•[ PATH t₁ t₂ , path (c ◎ id⟷) ] 
  assocl : ∀ {t₁ t₂ t₃ t₄}  → 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
          1•[ PATH t₁ t₄ , path (c₁ ◎ (c₂ ◎ c₃)) ] ⇔ 
          1•[ PATH t₁ t₄ , path ((c₁ ◎ c₂) ◎ c₃) ]
  assocr : ∀ {t₁ t₂ t₃ t₄}  → 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
          1•[ PATH t₁ t₄ , path ((c₁ ◎ c₂) ◎ c₃) ] ⇔ 
          1•[ PATH t₁ t₄ , path (c₁ ◎ (c₂ ◎ c₃)) ] 
  unite₊l : ∀ {t v} → 
          1•[ PATH (•[ PLUS ZERO t , inj₂ v ]) (•[ PLUS ZERO t , inj₂ v ]) , 
          path (unite₊ ◎ uniti₊) ] ⇔ 
          1•[ PATH (•[ PLUS ZERO t , inj₂ v ]) (•[ PLUS ZERO t , inj₂ v ]) , 
          path id⟷ ] 
  unite₊r : ∀ {t v} → 
          1•[ PATH (•[ PLUS ZERO t , inj₂ v ]) (•[ PLUS ZERO t , inj₂ v ]) , 
          path id⟷ ] ⇔ 
          1•[ PATH (•[ PLUS ZERO t , inj₂ v ]) (•[ PLUS ZERO t , inj₂ v ]) , 
          path (unite₊ ◎ uniti₊) ] 
  uniti₊l : ∀ {t v} → 
          1•[ PATH (•[ t , v ]) (•[ t , v ]) , path (uniti₊ ◎ unite₊) ] ⇔ 
          1•[ PATH (•[ t , v ]) (•[ t , v ]) , path id⟷ ] 
  uniti₊r : ∀ {t v} → 
          1•[ PATH (•[ t , v ]) (•[ t , v ]) , path id⟷ ] ⇔ 
          1•[ PATH (•[ t , v ]) (•[ t , v ]) , path (uniti₊ ◎ unite₊) ] 
  swap1₊l : ∀ {t₁ t₂ v₁} → 
          1•[ PATH •[ PLUS t₁ t₂ , inj₁ v₁ ] •[ PLUS t₁ t₂ , inj₁ v₁ ] ,
          path (swap1₊ ◎ ! swap1₊) ] ⇔
          1•[ PATH •[ PLUS t₁ t₂ , inj₁ v₁ ] •[ PLUS t₁ t₂ , inj₁ v₁ ] , 
          path id⟷ ]
  swap1₊r : ∀ {t₁ t₂ v₁} → 
          1•[ PATH •[ PLUS t₁ t₂ , inj₁ v₁ ] •[ PLUS t₁ t₂ , inj₁ v₁ ] , 
          path id⟷ ] ⇔
          1•[ PATH •[ PLUS t₁ t₂ , inj₁ v₁ ] •[ PLUS t₁ t₂ , inj₁ v₁ ] ,
          path (swap1₊ ◎ ! swap1₊) ] 
  swap2₊l : ∀ {t₁ t₂ v₂} → 
          1•[ PATH •[ PLUS t₁ t₂ , inj₂ v₂ ] •[ PLUS t₁ t₂ , inj₂ v₂ ] , 
          path (swap2₊ ◎ ! swap2₊) ] ⇔
          1•[ PATH •[ PLUS t₁ t₂ , inj₂ v₂ ] •[ PLUS t₁ t₂ , inj₂ v₂ ] , 
          path id⟷ ]
  swap2₊r : ∀ {t₁ t₂ v₂} → 
          1•[ PATH •[ PLUS t₁ t₂ , inj₂ v₂ ] •[ PLUS t₁ t₂ , inj₂ v₂ ] , 
          path id⟷ ] ⇔
          1•[ PATH •[ PLUS t₁ t₂ , inj₂ v₂ ] •[ PLUS t₁ t₂ , inj₂ v₂ ] , 
          path (swap2₊ ◎ ! swap2₊) ] 
  assocl1₊l : ∀ {t₁ t₂ t₃ v₁} → 
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] , 
          path (assocl1₊ ◎ ! assocl1₊) ] ⇔
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] , 
          path id⟷ ]
  assocl1₊r : ∀ {t₁ t₂ t₃ v₁} → 
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] , 
          path id⟷ ] ⇔
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] , 
          path (assocl1₊ ◎ ! assocl1₊) ] 
  assocl2₊l : ∀ {t₁ t₂ t₃ v₂} → 
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] , 
          path (assocl2₊ ◎ ! assocl2₊) ] ⇔
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] , 
          path id⟷ ]
  assocl2₊r : ∀ {t₁ t₂ t₃ v₂} → 
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] , 
          path id⟷ ] ⇔
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] , 
          path (assocl2₊ ◎ ! assocl2₊) ] 
  assocl3₊l : ∀ {t₁ t₂ t₃ v₃} → 
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] , 
          path (assocl3₊ ◎ ! assocl3₊) ] ⇔
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] , 
          path id⟷ ]
  assocl3₊r : ∀ {t₁ t₂ t₃ v₃} → 
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] , 
          path id⟷ ] ⇔
          1•[ PATH •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
                   •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] , 
          path (assocl3₊ ◎ ! assocl3₊) ] 
  resp◎   : ∀ {t₁ t₂ t₃} →
           {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} → 
           (1•[ PATH t₁ t₂ , path c₁ ] ⇔ 1•[ PATH t₁ t₂ , path c₃ ]) → 
           (1•[ PATH t₂ t₃ , path c₂ ] ⇔ 1•[ PATH t₂ t₃ , path c₄ ]) → 
           1•[ PATH t₁ t₃ , path (c₁ ◎ c₂) ] ⇔ 1•[ PATH t₁ t₃ , path (c₃ ◎ c₄) ]

1! : {t₁ t₂ : 1U•} → (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
1! unite₊ = uniti₊
1! uniti₊ = unite₊
1! swap1₊ = swap2₊
1! swap2₊ = swap1₊
1! assocl1₊ = assocr1₊
1! assocl2₊ = assocr2₊
1! assocl3₊ = assocr3₊
1! assocr1₊ = assocl1₊
1! assocr2₊ = assocl2₊
1! assocr3₊ = assocl3₊
1! unite⋆ = uniti⋆
1! uniti⋆ = unite⋆
1! swap⋆ = swap⋆
1! assocl⋆ = assocr⋆
1! assocr⋆ = assocl⋆
1! distz = factorz
1! factorz = distz
1! dist1 = factor1 
1! dist2 = factor2 
1! factor1 = dist1 
1! factor2 = dist2 
1! id⇔ = id⇔
1! (c₁ ◎ c₂) = 1! c₂ ◎ 1! c₁ 
1! (⊕1 c₁) = ⊕1 (1! c₁)
1! (⊕2 c₂) = ⊕2 (1! c₂)
1! (c₁ ⊗ c₂) = 1! c₁ ⊗ 1! c₂ 
1! (resp◎ c₁ c₂) = resp◎ (1! c₁) (1! c₂)
1! ridl = ridr
1! ridr = ridl
1! lidl = lidr
1! lidr = lidl
1! assocl = assocr
1! assocr = assocl
1! unite₊l = unite₊r
1! unite₊r = unite₊l
1! uniti₊l = uniti₊r
1! uniti₊r = uniti₊l
1! swap1₊l = swap1₊r
1! swap1₊r = swap1₊l
1! swap2₊l = swap2₊r
1! swap2₊r = swap2₊l
1! assocl1₊l = assocl1₊r
1! assocl1₊r = assocl1₊l
1! assocl2₊l = assocl2₊r
1! assocl2₊r = assocl2₊l
1! assocl3₊l = assocl3₊r
1! assocl3₊r = assocl3₊l

1!≡ : {t₁ t₂ : 1U•} → (c : t₁ ⇔ t₂) → 1! (1! c) ≡ c
1!≡ unite₊ = refl
1!≡ uniti₊ = refl
1!≡ swap1₊ = refl
1!≡ swap2₊ = refl
1!≡ assocl1₊ = refl
1!≡ assocl2₊ = refl
1!≡ assocl3₊ = refl
1!≡ assocr1₊ = refl
1!≡ assocr2₊ = refl
1!≡ assocr3₊ = refl
1!≡ unite⋆ = refl
1!≡ uniti⋆ = refl
1!≡ swap⋆ = refl
1!≡ assocl⋆ = refl
1!≡ assocr⋆ = refl
1!≡ distz = refl
1!≡ factorz = refl
1!≡ dist1 = refl
1!≡ dist2 = refl
1!≡ factor1 = refl
1!≡ factor2 = refl
1!≡ id⇔ = refl
1!≡ (c₁ ◎ c₂) = cong₂ (λ c₁ c₂ → c₁ ◎ c₂) (1!≡ c₁) (1!≡ c₂)
1!≡ (⊕1 c₁) = cong (λ c₁ → ⊕1 c₁) (1!≡ c₁)
1!≡ (⊕2 c₂) = cong (λ c₂ → ⊕2 c₂) (1!≡ c₂)
1!≡ (c₁ ⊗ c₂) = cong₂ (λ c₁ c₂ → c₁ ⊗ c₂) (1!≡ c₁) (1!≡ c₂)
1!≡ lidl = refl
1!≡ lidr = refl
1!≡ ridl = refl
1!≡ ridr = refl
1!≡ (resp◎ c₁ c₂) = cong₂ (λ c₁ c₂ → resp◎ c₁ c₂) (1!≡ c₁) (1!≡ c₂)
1!≡ assocl = refl
1!≡ assocr = refl
1!≡ unite₊l = refl
1!≡ unite₊r = refl
1!≡ uniti₊l = refl
1!≡ uniti₊r = refl
1!≡ swap1₊l = refl 
1!≡ swap1₊r = refl 
1!≡ swap2₊l = refl 
1!≡ swap2₊r = refl 
1!≡ assocl1₊l = refl
1!≡ assocl1₊r = refl
1!≡ assocl2₊l = refl
1!≡ assocl2₊r = refl
1!≡ assocl3₊l = refl
1!≡ assocl3₊r = refl

-- better syntax for writing 2paths

_⇔⟨_⟩_ : {t₁ t₂ : U•} (c₁ : t₁ ⟷ t₂) {c₂ : t₁ ⟷ t₂} {c₃ : t₁ ⟷ t₂} → 
         (1•[ PATH t₁ t₂ , path c₁ ] ⇔ 1•[ PATH t₁ t₂ , path c₂ ]) → 
         (1•[ PATH t₁ t₂ , path c₂ ] ⇔ 1•[ PATH t₁ t₂ , path c₃ ]) → 
         (1•[ PATH t₁ t₂ , path c₁ ] ⇔ 1•[ PATH t₁ t₂ , path c₃ ])
_ ⇔⟨ α ⟩ β = α ◎ β

_▤ : {t₁ t₂ : U•} → (c : t₁ ⟷ t₂) → 
     1•[ PATH t₁ t₂ , path c ] ⇔ 1•[ PATH t₁ t₂ , path c ]
_▤ c = id⇔

α₁ : 1•[ PATH BOOL•T BOOL•F , p₁ ] ⇔ 1•[ PATH BOOL•T BOOL•F , p₁ ]
α₁ = id⇔

α₂ : 1•[ PATH BOOL•T BOOL•F , p₁ ] ⇔ 1•[ PATH BOOL•T BOOL•F , p₂ ]
α₂ = lidr


-- level 0 is a groupoid with a non-trivial path equivalence the various inv*
-- rules are not justified by the groupoid proof; they are justified by the
-- need for computational rules. So it is important to have not just a
-- groupoid structure but a groupoid structure that we can compute with. So
-- if we say that we want p ◎ p⁻¹ to be id, we must have computational rules
-- that allow us to derive this for any path p, and similarly for all the
-- other groupoid rules. (cf. The canonicity for 2D type theory by Licata and
-- Harper)

linv : {t₁ t₂ : U•} → (c : t₁ ⟷ t₂) → 
       1•[ PATH t₁ t₁ , path (c ◎ ! c) ] ⇔ 1•[ PATH t₁ t₁ , path id⟷ ]
linv unite₊ = unite₊l
linv uniti₊ = uniti₊l
linv swap1₊ = swap1₊l
linv swap2₊ = swap2₊l
linv assocl1₊ = assocl1₊l
linv assocl2₊ = assocl2₊l
linv assocl3₊ = assocl3₊l
linv _ = {!!} 
{--
linv assocr1₊ = {!!}
linv assocr2₊ = {!!}
linv assocr3₊ = {!!}
linv unite⋆ = {!!}
linv uniti⋆ = {!!}
linv swap⋆ = {!!}
linv assocl⋆ = {!!}
linv assocr⋆ = {!!}
linv distz = {!!}
linv factorz = {!!}
linv dist1 = {!!}
linv dist2 = {!!}
linv factor1 = {!!}
linv factor2 = {!!}
linv id⟷ = {!!}
linv (c ◎ c₁) = {!!}
linv (c ⊕1 c₁) = {!!}
linv (c ⊕2 c₁) = {!!}
linv (c ⊗ c₁) = {!!} 
--}

rinv : {t₁ t₂ : U•} → (c : t₁ ⟷ t₂) → 
       1•[ PATH t₂ t₂ , path (! c ◎ c) ] ⇔ 1•[ PATH t₂ t₂ , path id⟷ ]
rinv unite₊ = uniti₊l 
rinv uniti₊ = unite₊l
rinv swap1₊ = swap2₊l
rinv swap2₊ = swap1₊l
{--
rinv assocl1₊ = {!!}
rinv assocl2₊ = {!!}
rinv assocl3₊ = {!!}
--}
rinv assocr1₊ = assocl1₊l
rinv assocr2₊ = assocl2₊l
rinv assocr3₊ = assocl3₊l
rinv _ = {!!} 
{--
rinv unite⋆ = {!!}
rinv uniti⋆ = {!!}
rinv swap⋆ = {!!}
rinv assocl⋆ = {!!}
rinv assocr⋆ = {!!}
rinv distz = {!!}
rinv factorz = {!!}
rinv dist1 = {!!}
rinv dist2 = {!!}
rinv factor1 = {!!}
rinv factor2 = {!!}
rinv id⟷ = {!!}
rinv (c ◎ c₁) = {!!}
rinv (c ⊕1 c₁) = {!!}
rinv (c ⊕2 c₁) = {!!}
rinv (c ⊗ c₁) = {!!} 
--}

G : 1Groupoid
G = record
        { set = U•
        ; _↝_ = _⟷_
        ; _≈_ = λ {t₁} {t₂} c₀ c₁ → 
                1•[ PATH t₁ t₂ , path c₀ ] ⇔ 1•[ PATH t₁ t₂ , path c₁ ]
        ; id = id⟷
        ; _∘_ = λ c₀ c₁ → c₁ ◎ c₀
        ; _⁻¹ = ! 
        ; lneutr = λ _ → ridl 
        ; rneutr = λ _ → lidl 
        ; assoc = λ _ _ _ → assocl
        ; equiv = record { refl = id⇔
                                ; sym = λ c → 1! c 
                                ; trans = λ c₀ c₁ → c₀ ◎ c₁ }
        ; linv = λ {t₁} {t₂} c → linv c
        ; rinv = λ {t₁} {t₂} c → rinv c
        ; ∘-resp-≈ = λ f⟷h g⟷i → resp◎ g⟷i f⟷h 
        }

------------------------------------------------------------------------------
-- Int construction

-- Types are of the form t - t'

record Uℤ : Set where
  constructor _-_
  field
    pos  : U
    neg  : U

open Uℤ

ZEROℤ ONEℤ : Uℤ
ZEROℤ = ZERO - ZERO
ONEℤ  = ONE  - ZERO

PLUSℤ : Uℤ → Uℤ → Uℤ
PLUSℤ (pos₁ - neg₁) (pos₂ - neg₂) = PLUS pos₁ pos₂ - PLUS neg₁ neg₂
      
TIMESℤ : Uℤ → Uℤ → Uℤ
TIMESℤ (pos₁ - neg₁) (pos₂ - neg₂) = 
  PLUS (TIMES pos₁ pos₂) (TIMES neg₁ neg₂) - 
  PLUS (TIMES pos₁ neg₂) (TIMES neg₁ pos₂)
  
FLIPℤ : Uℤ → Uℤ
FLIPℤ (pos - neg) = neg - pos

LOLLIℤ : Uℤ → Uℤ → Uℤ
LOLLIℤ (pos₁ - neg₁) (pos₂ - neg₂) = PLUS neg₁ pos₂ - PLUS pos₁ neg₂
       
-- Pointed types 

data Uℤ• : Set where
  pos• : (t : Uℤ) → ⟦ pos t ⟧ → Uℤ•
  neg• : (t : Uℤ) → ⟦ neg t ⟧ → Uℤ•

PLUS1ℤ• : Uℤ• → Uℤ → Uℤ•
PLUS1ℤ• (pos• t₁ v₁) t₂ = pos• (PLUSℤ t₁ t₂) (inj₁ v₁)
PLUS1ℤ• (neg• t₁ v₁) t₂ = neg• (PLUSℤ t₁ t₂) (inj₁ v₁)

PLUS2ℤ• : Uℤ → Uℤ• → Uℤ•
PLUS2ℤ• t₁ (pos• t₂ v₂) = pos• (PLUSℤ t₁ t₂) (inj₂ v₂)
PLUS2ℤ• t₁ (neg• t₂ v₂) = neg• (PLUSℤ t₁ t₂) (inj₂ v₂)

-- Combinators on pointed types

data _⇄_ : Uℤ• → Uℤ• → Set where
  Fwd : ∀ {P₁ N₁ P₂ N₂ p₁ p₂} → 
        •[ PLUS P₁ N₂ , inj₁ p₁ ] ⟷ •[ PLUS N₁ P₂ , inj₂ p₂ ] → 
        (pos• (P₁ - N₁) p₁ ) ⇄ (pos• (P₂ - N₂) p₂)
  Bck : ∀ {P₁ N₁ P₂ N₂ n₁ n₂} → 
        •[ PLUS P₁ N₂ , inj₂ n₂ ] ⟷ •[ PLUS N₁ P₂ , inj₁ n₁ ] → 
        (neg• (P₁ - N₁) n₁ ) ⇄ (neg• (P₂ - N₂) n₂)

id⇄ : ∀ {t} → t ⇄ t
id⇄ {pos• t p} = Fwd swap1₊
id⇄ {neg• t n} = Bck swap2₊

unite₊⇄ : {t : Uℤ•} → PLUS2ℤ• ZEROℤ t ⇄ t
unite₊⇄ {pos• t v} = 
  Fwd (•[ PLUS (PLUS ZERO (pos t)) (neg t) , inj₁ (inj₂ v) ]
         ⟷⟨ assocr2₊ ⟩
       •[ PLUS ZERO (PLUS (pos t) (neg t)) , inj₂ (inj₁ v) ]
         ⟷⟨ unite₊ ◎ swap1₊ ⟩
       •[ PLUS (neg t) (pos t) , inj₂ v ]
         ⟷⟨ uniti₊ ⟩
       •[ PLUS ZERO (PLUS (neg t) (pos t)) , inj₂ (inj₂ v) ]
         ⟷⟨ assocl3₊ ⟩
       •[ PLUS (PLUS ZERO (neg t)) (pos t) , inj₂ v ] □)
unite₊⇄ {neg• t v} = 
  Bck (•[ PLUS (PLUS ZERO (pos t)) (neg t) , inj₂ v ] 
         ⟷⟨ assocr3₊ ⟩
       •[ PLUS ZERO (PLUS (pos t) (neg t)) , inj₂ (inj₂ v) ]  
         ⟷⟨ unite₊ ◎ swap2₊ ◎ uniti₊ ⟩
       •[ PLUS ZERO (PLUS (neg t) (pos t)) , inj₂ (inj₁ v) ]  
         ⟷⟨ assocl2₊ ⟩
       •[ PLUS (PLUS ZERO (neg t)) (pos t) , inj₁ (inj₂ v) ] □)

uniti₊⇄ : {t : Uℤ•} → t ⇄ PLUS2ℤ• ZEROℤ t
uniti₊⇄ {pos• t v} =  
  Fwd (•[ PLUS (pos t) (PLUS ZERO (neg t)) , inj₁ v ] 
        ⟷⟨ assocl1₊ ⟩
       •[ PLUS (PLUS (pos t) ZERO) (neg t) , inj₁ (inj₁ v) ] 
        ⟷⟨ swap1₊ ⟩
       •[ PLUS (neg t) (PLUS (pos t) ZERO) , inj₂ (inj₁ v) ] 
        ⟷⟨ ⊕2 swap1₊ ⟩
       •[ PLUS (neg t) (PLUS ZERO (pos t)) , inj₂ (inj₂ v) ] □)
uniti₊⇄ {neg• t v} =  
  Bck (•[ PLUS (pos t) (PLUS ZERO (neg t)) , inj₂ (inj₂ v) ] 
        ⟷⟨ ⊕2 swap2₊ ⟩
       •[ PLUS (pos t) (PLUS (neg t) ZERO) , inj₂ (inj₁ v) ] 
        ⟷⟨ swap2₊ ⟩
       •[ PLUS (PLUS (neg t) ZERO) (pos t) , inj₁ (inj₁ v) ] 
        ⟷⟨ assocr1₊ ⟩
       •[ PLUS (neg t) (PLUS ZERO (pos t)) , inj₁ v ] □)

swap1₊⇄ : {t₁ : Uℤ•} {t₂ : Uℤ} → PLUS1ℤ• t₁ t₂ ⇄ PLUS2ℤ• t₂ t₁
swap1₊⇄ {pos• t₁ v₁} {t₂} = 
  Fwd (•[ PLUS (PLUS (pos t₁) (pos t₂)) (PLUS (neg t₂) (neg t₁)) ,
          inj₁ (inj₁ v₁) ]
        ⟷⟨ {!!} ⟩
       •[ PLUS (PLUS (neg t₁) (neg t₂)) (PLUS (pos t₂) (pos t₁)) ,
          inj₂ (inj₂ v₁) ] □)
swap1₊⇄ {neg• t₁ v₁} {t₂} = 
  Bck (•[ PLUS (PLUS (pos t₁) (pos t₂)) (PLUS (neg t₂) (neg t₁)) ,
          inj₂ (inj₂ v₁) ]
        ⟷⟨ {!!} ⟩
       •[ PLUS (PLUS (neg t₁) (neg t₂)) (PLUS (pos t₂) (pos t₁)) ,
          inj₁ (inj₁ v₁) ] □)

swap2₊⇄ : {t₁ : Uℤ} {t₂ : Uℤ•} → PLUS2ℤ• t₁ t₂ ⇄ PLUS1ℤ• t₂ t₁
swap2₊⇄ {t₁} {pos• t₂ v₂} = 
  Fwd (•[ PLUS (PLUS (pos t₁) (pos t₂)) (PLUS (neg t₂) (neg t₁)) ,
          inj₁ (inj₂ v₂) ]
        ⟷⟨ {!!} ⟩
       •[ PLUS (PLUS (neg t₁) (neg t₂)) (PLUS (pos t₂) (pos t₁)) ,
          inj₂ (inj₁ v₂) ] □)
swap2₊⇄ {t₁} {neg• t₂ v₂} = 
  Bck (•[ PLUS (PLUS (pos t₁) (pos t₂)) (PLUS (neg t₂) (neg t₁)) ,
          inj₂ (inj₁ v₂) ] 
        ⟷⟨ {!!} ⟩
       •[ PLUS (PLUS (neg t₁) (neg t₂)) (PLUS (pos t₂) (pos t₁)) ,
          inj₁ (inj₂ v₂) ] □)

assocl1₊⇄ : {t₁ : Uℤ•} {t₂ t₃ : Uℤ} → 
            PLUS1ℤ• t₁ (PLUSℤ t₂ t₃) ⇄ PLUS1ℤ• (PLUS1ℤ• t₁ t₂) t₃
assocl1₊⇄ {pos• t₁ v₁} {t₂} {t₃} = 
  Fwd (•[ PLUS (PLUS (pos t₁) (pos (PLUSℤ t₂ t₃)))
               (PLUS (neg (PLUSℤ t₁ t₂)) (neg t₃)) , 
          inj₁ (inj₁ v₁) ]
        ⟷⟨ {!!} ⟩
       •[ PLUS (PLUS (neg t₁) (neg (PLUSℤ t₂ t₃)))
               (PLUS (pos (PLUSℤ t₁ t₂)) (pos t₃)) , 
          inj₂ (inj₁ (inj₁ v₁)) ] □)
assocl1₊⇄ {neg• t₁ v₁} {t₂} {t₃} = 
  Bck (•[ PLUS (PLUS (pos t₁) (pos (PLUSℤ t₂ t₃)))
               (PLUS (neg (PLUSℤ t₁ t₂)) (neg t₃)) , 
          inj₂ (inj₁ (inj₁ v₁)) ] 
        ⟷⟨ {!!} ⟩
       •[ PLUS (PLUS (neg t₁) (neg (PLUSℤ t₂ t₃)))
               (PLUS (pos (PLUSℤ t₁ t₂)) (pos t₃)) , 
          inj₁ (inj₁ v₁) ] □)


------------------------------------------------------------------------------

{--

  assocl2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ]
  assocl3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ]
  assocr1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] 
  assocr2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] 
  assocr3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
  unite⋆  : ∀ {t v} → •[ TIMES ONE t , (tt , v) ] ⟷ •[ t , v ]
  uniti⋆  : ∀ {t v} → •[ t , v ] ⟷ •[ TIMES ONE t , (tt , v) ] 
  swap⋆   : ∀ {t₁ t₂ v₁ v₂} → 
              •[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₂ t₁ , (v₂ , v₁) ]
  assocl⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ] ⟷ 
            •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ]
  assocr⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ] ⟷ 
            •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ]
  distz : ∀ {t v absurd} → 
            •[ TIMES ZERO t , (absurd , v) ] ⟷ •[ ZERO , absurd ]
  factorz : ∀ {t v absurd} → 
            •[ ZERO , absurd ] ⟷ •[ TIMES ZERO t , (absurd , v) ]
  dist1   : ∀ {t₁ t₂ t₃ v₁ v₃} → 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ⟷ 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ]
  dist2   : ∀ {t₁ t₂ t₃ v₂ v₃} → 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ⟷ 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ]
  factor1   : ∀ {t₁ t₂ t₃ v₁ v₃} → 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ⟷ 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ]
  factor2   : ∀ {t₁ t₂ t₃ v₂ v₃} → 
            •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ⟷ 
            •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ]
  id⟷    : ∀ {t v} → •[ t , v ] ⟷ •[ t , v ]
  _◎_    : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
           (•[ t₂ , v₂ ] ⟷ •[ t₃ , v₃ ]) → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ])
  _⊕1_   : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₃ t₄ , inj₁ v₃ ])
  _⊕2_   : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₃ t₄ , inj₂ v₄ ])
  _⊗_     : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
          (•[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₃ t₄ , (v₃ , v₄) ])
trace
eta
epsilon

--}
