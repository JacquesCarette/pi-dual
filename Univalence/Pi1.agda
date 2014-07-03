module Pi1 where

-- for examples of 2 paths look at proofs of 
-- path assoc; triangle and pentagon rules

-- the idea I guess is that instead of having the usual evaluator where
-- values flow, we want an evaluator that rewrites the circuit to primitive
-- isos; for that we need some normal form for permutations and a proof that
-- we can rewrite any circuit to this normal form

-- plan after that: add trace; this make obs equiv much more interesting and
-- allows a limited form of h.o. functions via the int construction and then
-- do the ring completion to get more complete notion of h.o. functions

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Groupoid

infix  2  _∎       -- equational reasoning for paths
infixr 2  _≡⟨_⟩_   -- equational reasoning for paths
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
  id⟷    : ∀ {t v} → •[ t , v ] ⟷ •[ t , v ]
  sym⟷   : ∀ {t₁ t₂ v₁ v₂} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
           (•[ t₂ , v₂ ] ⟷ •[ t₁ , v₁ ])
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
          ((id⟷ ⊗ NOT•F) ⊕1 (id⟷ {TIMES ONE BOOL} {(tt , TRUE)})) ◎
          factor1

CNOT•TT : •[ BOOL² , (TRUE , TRUE) ] ⟷ •[ BOOL² , (TRUE , FALSE) ]
CNOT•TT = dist1 ◎ 
          ((id⟷ ⊗ NOT•T) ⊕1 (id⟷ {TIMES ONE BOOL} {(tt , TRUE)})) ◎ 
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

simplifyl◎ : {t₁ t₂ t₃ : U•} → (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
simplifyl◎ id⟷ c = c 
simplifyl◎ unite₊ uniti₊ = id⟷
simplifyl◎ uniti₊ unite₊ = id⟷ 
simplifyl◎ swap1₊ swap2₊ = id⟷ 
simplifyl◎ swap2₊ swap1₊ = id⟷ 
simplifyl◎ assocl1₊ assocr1₊ = id⟷ 
simplifyl◎ assocl2₊ assocr2₊ = id⟷ 
simplifyl◎ assocl3₊ assocr3₊ = id⟷ 
simplifyl◎ assocr1₊ assocl1₊ = id⟷ 
simplifyl◎ assocr2₊ assocl2₊ = id⟷ 
simplifyl◎ assocr3₊ assocl3₊ = id⟷ 
simplifyl◎ unite⋆ uniti⋆ = id⟷ 
simplifyl◎ uniti⋆ unite⋆ = id⟷ 
simplifyl◎ swap⋆ swap⋆ = id⟷ 
simplifyl◎ assocl⋆ assocr⋆ = id⟷ 
simplifyl◎ assocr⋆ assocl⋆ = id⟷ 
simplifyl◎ factorz distz = id⟷ 
simplifyl◎ dist1 factor1 = id⟷ 
simplifyl◎ dist2 factor2 = id⟷ 
simplifyl◎ factor1 dist1 = id⟷ 
simplifyl◎ factor2 dist2 = id⟷ 
simplifyl◎ (c₁ ◎ c₂) c₃ = c₁ ◎ (c₂ ◎ c₃) 
simplifyl◎ (c₁ ⊕1 c₂) swap1₊ = swap1₊ ◎ (c₂ ⊕2 c₁)
simplifyl◎ (c₁ ⊕2 c₂) swap2₊ = swap2₊ ◎ (c₂ ⊕1 c₁)
simplifyl◎ (_⊗_ {ONE} c₁ c₂) unite⋆ = unite⋆ ◎ c₂
simplifyl◎ (c₁ ⊗ c₂) swap⋆ = swap⋆ ◎ (c₂ ⊗ c₁)
simplifyl◎ (c₁ ⊗ c₂) (c₃ ⊗ c₄) = (c₁ ◎ c₃) ⊗ (c₂ ◎ c₄) 
simplifyl◎ c₁ c₂ = c₁ ◎ c₂

simplifyr◎ : {t₁ t₂ t₃ : U•} → (c₁ : t₁ ⟷ t₂) → (c₂ : t₂ ⟷ t₃) → (t₁ ⟷ t₃)
simplifyr◎ c id⟷ = c
simplifyr◎ unite₊ uniti₊ = id⟷
simplifyr◎ uniti₊ unite₊ = id⟷ 
simplifyr◎ swap1₊ swap2₊ = id⟷ 
simplifyr◎ swap2₊ swap1₊ = id⟷ 
simplifyr◎ assocl1₊ assocr1₊ = id⟷ 
simplifyr◎ assocl2₊ assocr2₊ = id⟷ 
simplifyr◎ assocl3₊ assocr3₊ = id⟷ 
simplifyr◎ assocr1₊ assocl1₊ = id⟷ 
simplifyr◎ assocr2₊ assocl2₊ = id⟷ 
simplifyr◎ assocr3₊ assocl3₊ = id⟷ 
simplifyr◎ unite⋆ uniti⋆ = id⟷ 
simplifyr◎ uniti⋆ unite⋆ = id⟷ 
simplifyr◎ swap⋆ swap⋆ = id⟷ 
simplifyr◎ assocl⋆ assocr⋆ = id⟷ 
simplifyr◎ assocr⋆ assocl⋆ = id⟷ 
simplifyr◎ factorz distz = id⟷ 
simplifyr◎ dist1 factor1 = id⟷ 
simplifyr◎ dist2 factor2 = id⟷ 
simplifyr◎ factor1 dist1 = id⟷ 
simplifyr◎ factor2 dist2 = id⟷ 
simplifyr◎ (c₁ ◎ c₂) c₃ = c₁ ◎ (c₂ ◎ c₃) 
simplifyr◎ (c₁ ⊕1 c₂) swap1₊ = swap1₊ ◎ (c₂ ⊕2 c₁)
simplifyr◎ (c₁ ⊕2 c₂) swap2₊ = swap2₊ ◎ (c₂ ⊕1 c₁)
simplifyr◎ (_⊗_ {ONE} {ONE} c₁ c₂) unite⋆ = unite⋆ ◎ c₂
simplifyr◎ (c₁ ⊗ c₂) swap⋆ = swap⋆ ◎ (c₂ ⊗ c₁)
simplifyr◎ (c₁ ⊗ c₂) (c₃ ⊗ c₄) = (c₁ ◎ c₃) ⊗ (c₂ ◎ c₄) 
simplifyr◎ c₁ c₂ = c₁ ◎ c₂


------------------------------------------------------------------------------
-- Level 1: 
-- Types are sets of paths. The paths are defined at the previous level
-- (level 0). At level 1, there is no interesting 2path structure. From
-- the perspective of level 0, we have points with non-trivial paths between
-- them, i.e., we have a groupoid. The paths cross type boundaries, i.e., we
-- have heterogeneous equality

-- types

data 2U : Set where
  2ZERO  : 2U              -- empty set of paths
  2ONE   : 2U              -- a trivial path
  2PLUS  : 2U → 2U → 2U      -- disjoint union of paths
  2TIMES : 2U → 2U → 2U      -- pairs of paths
  PATH  : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → 2U -- level 0 paths between values

-- values

data Path (t₁ t₂ : U•) : Set where
  path : (c : t₁ ⟷ t₂) → Path t₁ t₂

2⟦_⟧ : 2U → Set
2⟦ 2ZERO ⟧             = ⊥
2⟦ 2ONE ⟧              = ⊤
2⟦ 2PLUS t₁ t₂ ⟧       = 2⟦ t₁ ⟧ ⊎ 2⟦ t₂ ⟧
2⟦ 2TIMES t₁ t₂ ⟧      = 2⟦ t₁ ⟧ × 2⟦ t₂ ⟧
2⟦ PATH {t₁} {t₂} c ⟧ = Path t₁ t₂

-- examples

T⇔F : Set
T⇔F = Path BOOL•T BOOL•F

F⇔T : Set
F⇔T = Path BOOL•F BOOL•T

-- all the following are paths from T to F; we will show below that they
-- are equivalent using 2paths

p₁ p₂ p₃ p₄ p₅ : T⇔F
p₁ = path NOT•T
p₂ = path (id⟷ ◎ NOT•T)
p₃ = path (NOT•T ◎ NOT•F ◎ NOT•T)
p₄ = path (NOT•T ◎ id⟷)
p₅ = path (uniti⋆ ◎ swap⋆ ◎ (NOT•T ⊗ id⟷) ◎ swap⋆ ◎ unite⋆)
   
p₆ : (T⇔F × T⇔F) ⊎ F⇔T
p₆ = inj₁ (p₁ , p₂)

-- Programs map paths to paths. We also use pointed types.

record 2U• : Set where
  constructor 2•[_,_]
  field
    2∣_∣ : 2U
    2• : 2⟦ 2∣_∣ ⟧

open 2U•

2Space : (t• : 2U•) → Set
2Space 2•[ t , p ] = 2⟦ t ⟧

2point : (t• : 2U•) → 2Space t• 
2point 2•[ t , p ] = p

2Path• : {t₁ t₂ : U•} → (c : t₁ ⟷ t₂) → 2U•
2Path• c = 2•[ PATH c , path c ]

data _⇔_ : 2U• → 2U• → Set where

  -- common combinators

  id⟷    : {t : 2U•} → t ⇔ t
  sym⟷   : {t₁ t₂ : 2U•} → (t₁ ⇔ t₂) → (t₂ ⇔ t₁)
  _◎_     : {t₁ t₂ t₃ : 2U•} → (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)

  -- groupoid combinators defined by induction on P.⟷ in Pi0.agda

  simplifyl◎l : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} 
             {c₁ : •[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]} 
             {c₂ : •[ t₂ , v₂ ] ⟷ •[ t₃ , v₃ ]} → 
    2Path• (c₁ ◎ c₂) ⇔ 2Path• (simplifyl◎ c₁ c₂)

  simplifyl◎r : {t₁ t₂ t₃ : U•} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} → 
    2Path• (simplifyl◎ c₁ c₂) ⇔ 2Path• (c₁ ◎ c₂)

  simplifyr◎l : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} 
             {c₁ : •[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]} 
             {c₂ : •[ t₂ , v₂ ] ⟷ •[ t₃ , v₃ ]} → 
    2Path• (c₁ ◎ c₂) ⇔ 2Path• (simplifyr◎ c₁ c₂)

  simplifyr◎r : {t₁ t₂ t₃ : U•} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} → 
    2Path• (simplifyr◎ c₁ c₂) ⇔ 2Path• (c₁ ◎ c₂)

  simplifySyml : {t₁ t₂ : U•} {c : t₁ ⟷ t₂} → 
    2Path• (sym⟷ c) ⇔ 2Path• (simplifySym c)

  simplifySymr : {t₁ t₂ : U•} {c : t₁ ⟷ t₂} → 
    2Path• (simplifySym c) ⇔ 2Path• (sym⟷ c)

  invll   : ∀ {t₁ t₂ v₁ v₂} → {c : •[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]} → 
            2Path• (sym⟷ c ◎ c) ⇔ 2Path• (id⟷ {t₂} {v₂})
  invlr   : ∀ {t₁ t₂ v₁ v₂} → {c : •[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]} → 
            2Path• (id⟷ {t₂} {v₂}) ⇔ 2Path• (sym⟷ c ◎ c)
  invrl   : ∀ {t₁ t₂ v₁ v₂} → {c : •[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]} → 
            2Path• (c ◎ sym⟷ c) ⇔ 2Path• (id⟷ {t₁} {v₁})
  invrr   : ∀ {t₁ t₂ v₁ v₂} → {c : •[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]} → 
            2Path• (id⟷ {t₁} {v₁}) ⇔ 2Path• (c ◎ sym⟷ c)

  -- resp◎ is closely related to Eckmann-Hilton
  resp◎   : {t₁ t₂ t₃ : U•} 
            {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} 
            {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} → 
            (2Path• c₁ ⇔ 2Path• c₃) → 
            (2Path• c₂ ⇔ 2Path• c₄) → 
            2Path• (c₁ ◎ c₂) ⇔ 2Path• (c₃ ◎ c₄)

  -- commutative semiring combinators

  unite₊  : {t : 2U•} → 2•[ 2PLUS 2ZERO 2∣ t ∣ , inj₂ (2• t) ] ⇔ t
  uniti₊  : {t : 2U•} → t ⇔ 2•[ 2PLUS 2ZERO 2∣ t ∣ , inj₂ (2• t) ]
  swap1₊  : {t₁ t₂ : 2U•} → 2•[ 2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣ , inj₁ (2• t₁) ] ⇔ 
                           2•[ 2PLUS 2∣ t₂ ∣ 2∣ t₁ ∣ , inj₂ (2• t₁) ]
  swap2₊  : {t₁ t₂ : 2U•} → 2•[ 2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣ , inj₂ (2• t₂) ] ⇔ 
                           2•[ 2PLUS 2∣ t₂ ∣ 2∣ t₁ ∣ , inj₁ (2• t₂) ]
  assocl1₊ : {t₁ t₂ t₃ : 2U•} → 
             2•[ 2PLUS 2∣ t₁ ∣ (2PLUS 2∣ t₂ ∣ 2∣ t₃ ∣) , inj₁ (2• t₁) ] ⇔ 
             2•[ 2PLUS (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , inj₁ (inj₁ (2• t₁)) ]
  assocl2₊ : {t₁ t₂ t₃ : 2U•} → 
             2•[ 2PLUS 2∣ t₁ ∣ (2PLUS 2∣ t₂ ∣ 2∣ t₃ ∣) , inj₂ (inj₁ (2• t₂)) ] ⇔ 
             2•[ 2PLUS (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , inj₁ (inj₂ (2• t₂)) ]
  assocl3₊ : {t₁ t₂ t₃ : 2U•} → 
             2•[ 2PLUS 2∣ t₁ ∣ (2PLUS 2∣ t₂ ∣ 2∣ t₃ ∣) , inj₂ (inj₂ (2• t₃)) ] ⇔ 
             2•[ 2PLUS (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , inj₂ (2• t₃) ]
  assocr1₊ : {t₁ t₂ t₃ : 2U•} → 
             2•[ 2PLUS (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , inj₁ (inj₁ (2• t₁)) ] ⇔ 
             2•[ 2PLUS 2∣ t₁ ∣ (2PLUS 2∣ t₂ ∣ 2∣ t₃ ∣) , inj₁ (2• t₁) ] 
  assocr2₊ : {t₁ t₂ t₃ : 2U•} → 
             2•[ 2PLUS (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , inj₁ (inj₂ (2• t₂)) ] ⇔ 
             2•[ 2PLUS 2∣ t₁ ∣ (2PLUS 2∣ t₂ ∣ 2∣ t₃ ∣) , inj₂ (inj₁ (2• t₂)) ] 
  assocr3₊ : {t₁ t₂ t₃ : 2U•} → 
             2•[ 2PLUS (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , inj₂ (2• t₃) ] ⇔ 
             2•[ 2PLUS 2∣ t₁ ∣ (2PLUS 2∣ t₂ ∣ 2∣ t₃ ∣) , inj₂ (inj₂ (2• t₃)) ]
  unite⋆  : {t : 2U•} → 2•[ 2TIMES 2ONE 2∣ t ∣ , (tt , 2• t) ] ⇔ t               
  uniti⋆  : {t : 2U•} → t ⇔ 2•[ 2TIMES 2ONE 2∣ t ∣ , (tt , 2• t) ] 
  swap⋆   : {t₁ t₂ : 2U•} → 2•[ 2TIMES 2∣ t₁ ∣ 2∣ t₂ ∣ , (2• t₁ , 2• t₂) ] ⇔ 
                           2•[ 2TIMES 2∣ t₂ ∣ 2∣ t₁ ∣ , (2• t₂ , 2• t₁) ]
  assocl⋆ : {t₁ t₂ t₃ : 2U•} → 
           2•[ 2TIMES 2∣ t₁ ∣ (2TIMES 2∣ t₂ ∣ 2∣ t₃ ∣) , (2• t₁ , (2• t₂ , 2• t₃)) ] ⇔ 
           2•[ 2TIMES (2TIMES 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , ((2• t₁ , 2• t₂) , 2• t₃) ]
  assocr⋆ : {t₁ t₂ t₃ : 2U•} → 
           2•[ 2TIMES (2TIMES 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , ((2• t₁ , 2• t₂) , 2• t₃) ] ⇔ 
           2•[ 2TIMES 2∣ t₁ ∣ (2TIMES 2∣ t₂ ∣ 2∣ t₃ ∣) , (2• t₁ , (2• t₂ , 2• t₃)) ]
  distz : {t : 2U•} {absurd : 2⟦ 2ZERO ⟧} → 
          2•[ 2TIMES 2ZERO 2∣ t ∣ , (absurd , 2• t) ] ⇔ 2•[ 2ZERO , absurd ]
  factorz : {t : 2U•} {absurd : 2⟦ 2ZERO ⟧} → 
            2•[ 2ZERO , absurd ] ⇔ 2•[ 2TIMES 2ZERO 2∣ t ∣ , (absurd , 2• t) ] 
  dist1   : {t₁ t₂ t₃ : 2U•} → 
            2•[ 2TIMES (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , (inj₁ (2• t₁) , 2• t₃) ] ⇔ 
            2•[ 2PLUS (2TIMES 2∣ t₁ ∣ 2∣ t₃ ∣) (2TIMES 2∣ t₂ ∣ 2∣ t₃ ∣) , 
               inj₁ (2• t₁ , 2• t₃) ]
  dist2   : {t₁ t₂ t₃ : 2U•} → 
            2•[ 2TIMES (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , (inj₂ (2• t₂) , 2• t₃) ] ⇔ 
            2•[ 2PLUS (2TIMES 2∣ t₁ ∣ 2∣ t₃ ∣) (2TIMES 2∣ t₂ ∣ 2∣ t₃ ∣) , 
               inj₂ (2• t₂ , 2• t₃) ]
  factor1   : {t₁ t₂ t₃ : 2U•} → 
            2•[ 2PLUS (2TIMES 2∣ t₁ ∣ 2∣ t₃ ∣) (2TIMES 2∣ t₂ ∣ 2∣ t₃ ∣) , 
               inj₁ (2• t₁ , 2• t₃) ] ⇔ 
            2•[ 2TIMES (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , (inj₁ (2• t₁) , 2• t₃) ]
  factor2   : {t₁ t₂ t₃ : 2U•} → 
            2•[ 2PLUS (2TIMES 2∣ t₁ ∣ 2∣ t₃ ∣) (2TIMES 2∣ t₂ ∣ 2∣ t₃ ∣) , 
               inj₂ (2• t₂ , 2• t₃) ] ⇔ 
            2•[ 2TIMES (2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣) 2∣ t₃ ∣ , (inj₂ (2• t₂) , 2• t₃) ]
  _⊕1_   : {t₁ t₂ t₃ t₄ : 2U•} → (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → 
           (2•[ 2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣ , inj₁ (2• t₁) ] ⇔ 
            2•[ 2PLUS 2∣ t₃ ∣ 2∣ t₄ ∣ , inj₁ (2• t₃) ])
  _⊕2_   : {t₁ t₂ t₃ t₄ : 2U•} → (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → 
           (2•[ 2PLUS 2∣ t₁ ∣ 2∣ t₂ ∣ , inj₂ (2• t₂) ] ⇔ 
            2•[ 2PLUS 2∣ t₃ ∣ 2∣ t₄ ∣ , inj₂ (2• t₄) ])
  _⊗_     : {t₁ t₂ t₃ t₄ : 2U•} → (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → 
            (2•[ 2TIMES 2∣ t₁ ∣ 2∣ t₂ ∣ , (2• t₁ , 2• t₂ ) ] ⇔ 
             2•[ 2TIMES 2∣ t₃ ∣ 2∣ t₄ ∣ , (2• t₃ , 2• t₄ ) ])

-- sane syntax

_≡⟨_⟩_ : {t₁ t₂ : U•} (c₁ : t₁ ⟷ t₂) {c₂ : t₁ ⟷ t₂} {c₃ : t₁ ⟷ t₂} → 
         (2•[ PATH c₁ , path c₁ ] ⇔ 2•[ PATH c₂ , path c₂ ]) → 
         (2•[ PATH c₂ , path c₂ ] ⇔ 2•[ PATH c₃ , path c₃ ]) → 
         (2•[ PATH c₁ , path c₁ ] ⇔ 2•[ PATH c₃ , path c₃ ])
_ ≡⟨ α ⟩ β = α ◎ β

_∎ : {t₁ t₂ : U•} → (c : t₁ ⟷ t₂) → 
     2•[ PATH c , path c ] ⇔ 2•[ PATH c , path c ]
_∎ c = id⟷ 

-- example programs

α₁ : 2Path• NOT•T ⇔ 2Path• (id⟷ ◎ NOT•T)
α₁ = simplifyl◎r

α₂ α₃ : 2•[ 2TIMES (PATH NOT•T) (PATH (NOT•T ◎ id⟷)) , (p₁ , p₄) ] ⇔
        2•[ 2TIMES (PATH NOT•T) (PATH NOT•T) , (p₁ , p₁) ] 
α₂ = id⟷ ⊗ simplifyr◎l
α₃ = swap⋆ ◎ (simplifyr◎l ⊗ id⟷) 

-- let's try to prove that p₁ = p₂ = p₃ = p₄ = p₅

-- p₁ ~> p₂
α₄ : 2•[ PATH NOT•T , p₁ ] ⇔ 2•[ PATH (id⟷ ◎ NOT•T) , p₂ ]
α₄ = simplifyl◎r

-- p₂ ~> p₃
α₅ : 2•[ PATH (id⟷ ◎ NOT•T) , p₂ ] ⇔
     2•[ PATH (NOT•T ◎ NOT•F ◎ NOT•T) , p₃ ]
α₅ = id⟷ ◎ NOT•T
       ≡⟨ simplifyl◎l ⟩ 
     NOT•T
       ≡⟨ simplifyr◎r ⟩ 
     NOT•T ◎ id⟷ 
       ≡⟨ resp◎ id⟷ simplifyl◎r ⟩ 
     NOT•T ◎ NOT•F ◎ NOT•T ∎

-- p₃ ~> p₄
α₆ : 2•[ PATH (NOT•T ◎ NOT•F ◎ NOT•T) , p₃ ] ⇔
     2•[ PATH (NOT•T ◎ id⟷) , p₄ ]
α₆ = resp◎ id⟷ simplifyl◎l

-- p₅ ~> p₁

α₈ : 2•[ PATH (uniti⋆ ◎ swap⋆ ◎ 
             (NOT•T ⊗ id⟷) ◎ swap⋆ ◎ unite⋆) , 
        p₅ ] ⇔
     2•[ PATH NOT•T , p₁ ] 
α₈ = uniti⋆ ◎ swap⋆ ◎ (NOT•T ⊗ id⟷) ◎ swap⋆ ◎ unite⋆
       ≡⟨ resp◎ id⟷ (resp◎ id⟷ simplifyl◎r) ⟩
     uniti⋆ ◎ (swap⋆ ◎ ((NOT•T ⊗ id⟷) ◎ (swap⋆ ◎ unite⋆)))
       ≡⟨ resp◎ id⟷ (resp◎ id⟷ simplifyl◎r) ⟩ 
     uniti⋆ ◎ (swap⋆ ◎ (((NOT•T ⊗ id⟷) ◎ swap⋆) ◎ unite⋆))
       ≡⟨ resp◎ id⟷ (resp◎ id⟷ (resp◎ simplifyl◎l id⟷ )) ⟩
     uniti⋆ ◎ (swap⋆ ◎ ((swap⋆ ◎ (id⟷ ⊗ NOT•T)) ◎ unite⋆))
       ≡⟨ resp◎ id⟷ (resp◎ id⟷ simplifyl◎l) ⟩
     uniti⋆ ◎ (swap⋆ ◎ (swap⋆ ◎ ((id⟷ ⊗ NOT•T) ◎ unite⋆)))
       ≡⟨ resp◎ id⟷ simplifyl◎r ⟩
     uniti⋆ ◎ ((swap⋆ ◎ swap⋆) ◎ ((id⟷ ⊗ NOT•T) ◎ unite⋆))
       ≡⟨ resp◎ id⟷ (resp◎ simplifyl◎l id⟷) ⟩
     uniti⋆ ◎ (id⟷ ◎ ((id⟷ ⊗ NOT•T) ◎ unite⋆))
       ≡⟨ resp◎ id⟷ simplifyl◎l ⟩
     uniti⋆ ◎ ((id⟷ ⊗ NOT•T) ◎ unite⋆)
       ≡⟨ resp◎ id⟷ simplifyl◎l  ⟩
     uniti⋆ ◎ (unite⋆ ◎ NOT•T)
       ≡⟨ simplifyl◎r ⟩
     (uniti⋆ ◎ unite⋆) ◎ NOT•T
       ≡⟨ resp◎ simplifyl◎l id⟷ ⟩
     id⟷ ◎ NOT•T
       ≡⟨ simplifyl◎l ⟩
     NOT•T ∎

-- p₄ ~> p₅

α₇ : 2•[ PATH (NOT•T ◎ id⟷) , p₄ ] ⇔
     2•[ PATH (uniti⋆ ◎ swap⋆ ◎ 
             (NOT•T ⊗ id⟷) ◎ swap⋆ ◎ unite⋆) , 
        p₅ ]
α₇ = simplifyr◎l ◎ (sym⟷ α₈)

-- level 0 is a groupoid with a non-trivial path equivalence the various inv*
-- rules are not justified by the groupoid proof; they are justified by the
-- need for computational rules. So it is important to have not just a
-- groupoid structure but a groupoid structure that we can compute with. So
-- if we say that we want p ◎ p⁻¹ to be id, we must have computational rules
-- that allow us to derive this for any path p, and similarly for all the
-- other groupoid rules. (cf. The canonicity for 2D type theory by Licata and
-- Harper)

G : 1Groupoid
G = record
        { set = U•
        ; _↝_ = _⟷_
        ; _≈_ = λ c₀ c₁ → 2Path• c₀ ⇔ 2Path• c₁
        ; id = id⟷
        ; _∘_ = λ c₀ c₁ → c₁ ◎ c₀
        ; _⁻¹ = sym⟷
        ; lneutr = λ {t₁} {t₂} c → simplifyr◎l 
           {∣ t₁ ∣} {∣ t₂ ∣} {∣ t₂ ∣} 
           {• t₁} {• t₂} {• t₂} {c} {id⟷} 
        ; rneutr = λ {t₁} {t₂} c → simplifyl◎l 
           {∣ t₁ ∣} {∣ t₁ ∣} {∣ t₂ ∣} 
           {• t₁} {• t₁} {• t₂} {id⟷} {c}
        ; assoc = λ _ _ _ → simplifyl◎r
        ; equiv = record { refl = id⟷ 
                                ; sym = λ c → sym⟷ c 
                                ; trans = λ c₀ c₁ → c₀ ◎ c₁ }
        ; linv = λ {t₁} {t₂} c → 
                   invrl {∣ t₁ ∣} {∣ t₂ ∣} {• t₁} {• t₂}
        ; rinv = λ {t₁} {t₂} c → 
                   invll {∣ t₁ ∣} {∣ t₂ ∣} {• t₁} {• t₂}
        ; ∘-resp-≈ = λ f⟷h g⟷i → resp◎ g⟷i f⟷h 
        }

------------------------------------------------------------------------------

