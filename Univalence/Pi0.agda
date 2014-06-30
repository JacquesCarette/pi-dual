module Pi0 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Groupoid

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
-- want to work on another value, we generally use another program

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

-- examples of plain types, values, and pointed types

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
  distz : {t : U•} {absurd : ⟦ ZERO ⟧} → 
          •[ TIMES ZERO ∣ t ∣ , (absurd , • t) ] ⟷ •[ ZERO , absurd ]
  factorz : {t : U•} {absurd : ⟦ ZERO ⟧} → 
          •[ ZERO , absurd ] ⟷ •[ TIMES ZERO ∣ t ∣ , (absurd , • t) ] 
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

-- example programs

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

-- The evaluation of a program is not done in order to figure out the output
-- value. Both the input and output values are encoded in the type of the
-- program; what the evaluation does is follow the path to constructively
-- reach the ouput value from the input value. Even though programs of the
-- same pointed types are, by definition, observationally equivalent, they
-- may follow different paths. At this point, we simply declare that all such
-- programs are "the same." At the next level, we will weaken this "path
-- irrelevant" equivalence and reason about which paths can be equated to
-- other paths via 2paths etc.

-- Even though individual types are sets, the universe of types is a
-- groupoid. The objects of this groupoid are the pointed types; the
-- morphisms are the programs; and the equivalence of programs is the
-- degenerate observational equivalence that equates every two programs that
-- are extensionally equivalent.

_obs≅_ : {t₁ t₂ : U•} → (c₁ c₂ : t₁ ⟷ t₂) → Set
c₁ obs≅ c₂ = ⊤ 

UG : 1Groupoid
UG = record
       { set = U•
       ; _↝_ = _⟷_
       ; _≈_ = _obs≅_
       ; id = id⟷
       ; _∘_ = λ y⟷z x⟷y → x⟷y ◎ y⟷z 
       ; _⁻¹ = sym⟷
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
-- Simplifiy various compositions

simplifySym : {t₁ t₂ : U•} → (c₁ : t₁ ⟷ t₂) → (t₂ ⟷ t₁)
simplifySym unite₊ = uniti₊
simplifySym uniti₊ = unite₊
simplifySym swap1₊ = {!!}
simplifySym swap2₊ = {!!}
simplifySym assocl1₊ = {!!}
simplifySym assocl2₊ = {!!}
simplifySym assocl3₊ = {!!}
simplifySym assocr1₊ = {!!}
simplifySym assocr2₊ = {!!}
simplifySym assocr3₊ = {!!}
simplifySym unite⋆ = {!!}
simplifySym uniti⋆ = {!!}
simplifySym swap⋆ = {!!}
simplifySym assocl⋆ = {!!}
simplifySym assocr⋆ = {!!}
simplifySym distz = {!!}
simplifySym factorz = {!!}
simplifySym dist1 = {!!}
simplifySym dist2 = {!!}
simplifySym factor1 = {!!}
simplifySym factor2 = {!!}
simplifySym id⟷ = id⟷
simplifySym (sym⟷ c) = c
simplifySym (c₁ ◎ c₂) = simplifySym c₂ ◎ simplifySym c₁ 
simplifySym (c₁ ⊕1 c₂) = simplifySym c₁ ⊕1 simplifySym c₂ 
simplifySym (c₁ ⊕2 c₂) = simplifySym c₁ ⊕2 simplifySym c₂ 
simplifySym (c₁ ⊗ c₂) = simplifySym c₁ ⊗ simplifySym c₂ 

simplify◎ : {t₁ t₂ t₃ : U•} → (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
simplify◎ id⟷ c₂ = c₂
simplify◎ (c₁ ◎ c₂) c₃ = simplify◎ c₁ (c₂ ◎ c₃)
--
simplify◎ unite₊ unite₊ = {!!}
simplify◎ unite₊ uniti₊ = {!!}
simplify◎ unite₊ swap1₊ = {!!}
simplify◎ unite₊ swap2₊ = {!!}
simplify◎ unite₊ assocl1₊ = {!!}
simplify◎ unite₊ assocl2₊ = {!!}
simplify◎ unite₊ assocl3₊ = {!!}
simplify◎ unite₊ assocr1₊ = {!!}
simplify◎ unite₊ assocr2₊ = {!!}
simplify◎ unite₊ assocr3₊ = {!!}
simplify◎ unite₊ unite⋆ = {!!}
simplify◎ unite₊ uniti⋆ = {!!}
simplify◎ unite₊ swap⋆ = {!!}
simplify◎ unite₊ assocl⋆ = {!!}
simplify◎ unite₊ assocr⋆ = {!!}
simplify◎ unite₊ distz = {!!}
simplify◎ unite₊ factorz = {!!}
simplify◎ unite₊ dist1 = {!!}
simplify◎ unite₊ dist2 = {!!}
simplify◎ unite₊ factor1 = {!!}
simplify◎ unite₊ factor2 = {!!}
simplify◎ unite₊ id⟷ = {!!}
simplify◎ unite₊ (sym⟷ c₂) = {!!}
simplify◎ unite₊ (c₂ ◎ c₃) = {!!}
simplify◎ unite₊ (c₂ ⊕1 c₃) = {!!}
simplify◎ unite₊ (c₂ ⊕2 c₃) = {!!}
simplify◎ unite₊ (c₂ ⊗ c₃) = {!!}
--
simplify◎ uniti₊ c₂ = {!!}
simplify◎ swap1₊ c₂ = {!!}
simplify◎ swap2₊ c₂ = {!!}
simplify◎ assocl1₊ c₂ = {!!}
simplify◎ assocl2₊ c₂ = {!!}
simplify◎ assocl3₊ c₂ = {!!}
simplify◎ assocr1₊ c₂ = {!!}
simplify◎ assocr2₊ c₂ = {!!}
simplify◎ assocr3₊ c₂ = {!!}
simplify◎ unite⋆ c₂ = {!!}
simplify◎ uniti⋆ c₂ = {!!}
simplify◎ swap⋆ c₂ = {!!}
simplify◎ assocl⋆ c₂ = {!!}
simplify◎ assocr⋆ c₂ = {!!}
simplify◎ distz c₂ = {!!}
simplify◎ factorz c₂ = {!!}
simplify◎ dist1 c₂ = {!!}
simplify◎ dist2 c₂ = {!!}
simplify◎ factor1 c₂ = {!!}
simplify◎ factor2 c₂ = {!!}
simplify◎ (sym⟷ c₁) c₂ = {!!}
simplify◎ (c₁ ⊕1 c₂) c₃ = {!!}
simplify◎ (c₁ ⊕2 c₂) c₃ = {!!}
simplify◎ (c₁ ⊗ c₂) c₃ = {!!} 

simplify⊗ : {t₁ t₂ t₃ : U•} → (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
simplify⊗ = {!!} 



------------------------------------------------------------------------------

