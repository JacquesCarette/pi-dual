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
  unite₊  : ∀ {t v} → •[ PLUS ZERO t , inj₂ v ] ⟷ •[ t , v ]
  uniti₊  : ∀ {t v} → •[ t , v ] ⟷ •[ PLUS ZERO t , inj₂ v ]
  swap1₊  : ∀ {t₁ t₂ v₁} → •[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₂ t₁ , inj₂ v₁ ]
  swap2₊  : ∀ {t₁ t₂ v₂} → •[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₂ t₁ , inj₁ v₂ ]
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
  id⟷    : ∀ {t : U•} → t ⟷ t
  sym⟷   : ∀ {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
  _◎_    : ∀ {t₁ t₂ t₃ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕1_   : ∀ {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
           (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₁ (• t₁) ] ⟷ 
            •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₁ (• t₃) ])
  _⊕2_   : ∀ {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
           (•[ PLUS ∣ t₁ ∣ ∣ t₂ ∣ , inj₂ (• t₂) ] ⟷ 
            •[ PLUS ∣ t₃ ∣ ∣ t₄ ∣ , inj₂ (• t₄) ])
  _⊗_     : ∀ {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
          (•[ TIMES ∣ t₁ ∣ ∣ t₂ ∣ , (• t₁ , • t₂) ] ⟷ 
           •[ TIMES ∣ t₃ ∣ ∣ t₄ ∣ , (• t₃ , • t₄) ])

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
simplifySym swap1₊ = swap2₊
simplifySym swap2₊ = swap1₊
simplifySym assocl1₊ = assocr1₊
simplifySym assocl2₊ = assocr2₊
simplifySym assocl3₊ = assocr3₊
simplifySym assocr1₊ = assocl1₊
simplifySym assocr2₊ = assocl2₊
simplifySym assocr3₊ = assocl3₊
simplifySym unite⋆ = uniti⋆
simplifySym uniti⋆ = unite⋆
simplifySym swap⋆ = swap⋆
simplifySym assocl⋆ = assocr⋆
simplifySym assocr⋆ = assocl⋆
simplifySym distz = factorz
simplifySym factorz = distz
simplifySym dist1 = factor1 
simplifySym dist2 = factor2 
simplifySym factor1 = dist1 
simplifySym factor2 = dist2 
simplifySym id⟷ = id⟷
simplifySym (sym⟷ c) = c
simplifySym (c₁ ◎ c₂) = simplifySym c₂ ◎ simplifySym c₁ 
simplifySym (c₁ ⊕1 c₂) = simplifySym c₁ ⊕1 simplifySym c₂ 
simplifySym (c₁ ⊕2 c₂) = simplifySym c₁ ⊕2 simplifySym c₂ 
simplifySym (c₁ ⊗ c₂) = simplifySym c₁ ⊗ simplifySym c₂ 

simplify◎ : {t₁ t₂ t₃ : U•} → (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
simplify◎ id⟷ c₂ = c₂
simplify◎ (c₁ ◎ c₂) c₃ = simplify◎ c₁ (c₂ ◎ c₃)
simplify◎ c₁ c₂ = c₁ ◎ c₂

{--
simplify◎ unite₊ c₂ = {!!} 
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
--}

--simplify⊗ : {t₁ t₂ t₃ : U•} → (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
--simplify⊗ c₁ c₂ = {!!} 

------------------------------------------------------------------------------

