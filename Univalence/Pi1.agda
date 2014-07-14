module Pi1 where

open import Data.List
open import Data.Nat
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
infix 30 _⟷_

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
-- We use pointed types; programs are "fibers" from functions that map a
-- pointed type to another. In other words, each program takes one particular
-- value to another; if we want to work on another value, we generally use
-- another program.
-- 
-- We can recover a regular function by collecting all the fibers that
-- compose to the identity permutation.

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
  swap⋆   : ∀ {t₁ t₂ v₁ v₂} → •[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ 
                              •[ TIMES t₂ t₁ , (v₂ , v₁) ]
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
  _◎_ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
           (•[ t₂ , v₂ ] ⟷ •[ t₃ , v₃ ]) → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) 
  ⊕1   : ∀ {t₁ t₂ t₃ t₄ v₁ v₃} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → 
           (•[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₃ t₄ , inj₁ v₃ ])
  ⊕2   : ∀ {t₁ t₂ t₃ t₄ v₂ v₄} → 
           (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₃ t₄ , inj₂ v₄ ])
  _⊗_     : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → 
           (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₃ t₄ , (v₃ , v₄) ])

-- Nicer syntax that shows intermediate values instead of point-free
-- combinators

_⟷⟨_⟩_ : (t₁ : U•) {t₂ : U•} {t₃ : U•} → 
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃) 
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U•) → {t : U•} → (t ⟷ t)
_□ t = id⟷

-- trace
-- first every combinator (t + t1) <-> (t + t2) can be decomposed into 
-- four relations (or injective partial functions):
-- r11 : t1 -> t2
-- r12 : t1 -> t
-- r21 : t -> t2
-- r22 : t -> t
-- c = r11 ∪ (r12 ◎ r22⋆ ◎ r21)

eval : ∀ {t₁ t₂ v₁ v₂} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → List U•
eval {t₁ = ZERO} {v₁ = ()} _ 
eval {t₂ = ZERO} {v₂ = ()} _ 
eval {t} {PLUS .ZERO .t} {v} {inj₂ .v} uniti₊ = 
  •[ t , v ] ∷ •[ PLUS ZERO t , inj₂ v ] ∷ []
eval {PLUS .ZERO .t} {t} {inj₂ .v} {v} unite₊ = 
  •[ PLUS ZERO t , inj₂ v ] ∷ •[ t , v ] ∷ []
eval {PLUS t₁ t₂} {PLUS .t₂ .t₁} {inj₁ v₁} {inj₂ .v₁} swap1₊ = 
  •[ PLUS t₁ t₂ , inj₁ v₁ ] ∷ •[ PLUS t₂ t₁ , inj₂ v₁ ] ∷ []
eval {PLUS t₁ t₂} {PLUS .t₂ .t₁} {inj₂ v₂} {inj₁ .v₂} swap2₊ = 
  •[ PLUS t₁ t₂ , inj₂ v₂ ] ∷ •[ PLUS t₂ t₁ , inj₁ v₂ ] ∷ []
eval {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} 
     {inj₁ v₁} {inj₁ (inj₁ .v₁)} assocl1₊ =
  •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] ∷ 
  •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ] ∷ [] 
eval {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} 
     {inj₂ (inj₁ v₂)} {inj₁ (inj₂ .v₂)} assocl2₊ =
  •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] ∷ 
  •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ] ∷ [] 
eval {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} 
     {inj₂ (inj₂ v₃)} {inj₂ .v₃} assocl3₊ =
  •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] ∷ 
  •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ] ∷ [] 
eval {PLUS (PLUS .t₁ .t₂) .t₃} {PLUS t₁ (PLUS t₂ t₃)}
     {inj₁ (inj₁ .v₁)} {inj₁ v₁} assocr1₊ =
  •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ] ∷ 
  •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] ∷ [] 
eval {PLUS (PLUS .t₁ .t₂) .t₃} {PLUS t₁ (PLUS t₂ t₃)}
     {inj₁ (inj₂ .v₂)} {inj₂ (inj₁ v₂)} assocr2₊ =
  •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ] ∷ 
  •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] ∷ [] 
eval {PLUS (PLUS .t₁ .t₂) .t₃} {PLUS t₁ (PLUS t₂ t₃)}
     {inj₂ .v₃} {inj₂ (inj₂ v₃)} assocr3₊ =
  •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ] ∷ 
  •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] ∷ [] 
eval {t} {TIMES .ONE .t} {v} {(tt , .v)} uniti⋆ =
  •[ t , v ] ∷ •[ TIMES ONE t , (tt , v) ] ∷ [] 
eval {TIMES .ONE .t} {t} {(tt , .v)} {v} unite⋆ =
  •[ TIMES ONE t , (tt , v) ] ∷ •[ t , v ] ∷ [] 
eval {TIMES t₁ t₂} {TIMES .t₂ .t₁} {(v₁ , v₂)} {(.v₂ , .v₁)} swap⋆ = 
  •[ TIMES t₁ t₂ , (v₁ , v₂) ] ∷ •[ TIMES t₂ t₁ , (v₂ , v₁) ] ∷ []
eval {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} 
     {(v₁ , (v₂ , v₃))} {((.v₁ , .v₂) , .v₃)} assocl⋆ = 
  •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ] ∷ 
  •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ] ∷ []
eval {TIMES (TIMES .t₁ .t₂) .t₃} {TIMES t₁ (TIMES t₂ t₃)}
     {((.v₁ , .v₂) , .v₃)} {(v₁ , (v₂ , v₃))} assocr⋆ = 
  •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ] ∷
  •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ] ∷ []
eval {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)}
     {(inj₁ v₁ , v₃)} {inj₁ (.v₁ , .v₃)} dist1 = 
  •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ∷
  •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ∷ []
eval {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)}
     {(inj₂ v₂ , v₃)} {inj₂ (.v₂ , .v₃)} dist2 = 
  •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ∷
  •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ∷ []
eval {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} {TIMES (PLUS t₁ t₂) t₃}
     {inj₁ (.v₁ , .v₃)} {(inj₁ v₁ , v₃)} factor1 = 
  •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ∷ 
  •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ∷ []
eval {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} {TIMES (PLUS t₁ t₂) t₃}
     {inj₂ (.v₂ , .v₃)} {(inj₂ v₂ , v₃)} factor2 = 
  •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ∷ 
  •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ∷ []
eval {t} {.t} {v} {.v} id⟷ = •[ t , v ] ∷ •[ t , v ] ∷ []
eval {t₁} {t₃} {v₁} {v₃} (_◎_ {t₂ = t₂} {v₂ = v₂} c₁ c₂) = 
  eval {t₁} {t₂} {v₁} {v₂} c₁ ++ eval {t₂} {t₃} {v₂} {v₃} c₂
eval {PLUS t₁ t₂} {PLUS t₃ t₄} {inj₁ v₁} {inj₁ v₃} (⊕1 c) = 
  eval {t₁} {t₃} {v₁} {v₃} c -- tag
eval {PLUS t₁ t₂} {PLUS t₃ t₄} {inj₂ v₂} {inj₂ v₄} (⊕2 c) =
  eval {t₂} {t₄} {v₂} {v₄} c -- tag
eval {TIMES t₁ t₂} {TIMES t₃ t₄} {(v₁ , v₂)} {(v₃ , v₄)} (c₁ ⊗ c₂) = 
  (eval {t₁} {t₃} {v₁} {v₃} c₁) ++ (eval {t₂} {t₄} {v₂} {v₄} c₂)
  -- zip
       
test = eval (•[ BOOL² , (TRUE , TRUE) ]
               ⟷⟨ dist1 ⟩ 
             •[ PLUS (TIMES ONE BOOL) (TIMES ONE BOOL) , inj₁ (tt , TRUE) ]
               ⟷⟨ ⊕1 (id⟷ ⊗ swap1₊)⟩ 
             •[ PLUS (TIMES ONE BOOL) (TIMES ONE BOOL) , inj₁ (tt , FALSE) ]
               ⟷⟨ factor1 ⟩
             •[ BOOL² , (TRUE , FALSE) ] □)


-- The above are "fibers". We collect the fibers into functions. A function
-- is a collection of chains, one that starts at each value in the domain

Fun : (t₁ t₂ : U) → Set
Fun t₁ t₂ = (v₁ : ⟦ t₁ ⟧) → Σ[ v₂ ∈ ⟦ t₂ ⟧ ] (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ])

NOT : Fun BOOL BOOL
NOT (inj₁ tt) = (FALSE , swap1₊)
NOT (inj₂ tt) = (TRUE  , swap2₊)

CNOT : Fun BOOL² BOOL²
CNOT (inj₂ tt , b) = 
  ((FALSE , b) , dist2 ◎ (⊕2 id⟷) ◎ factor2)
CNOT (inj₁ tt , inj₂ tt) = 
  ((TRUE , TRUE) , dist1 ◎ (⊕1 (id⟷ ⊗ swap2₊)) ◎ factor1)
CNOT (inj₁ tt , inj₁ tt) = 
  ((TRUE , FALSE) , 
   (•[ BOOL² , (TRUE , TRUE) ]
      ⟷⟨ dist1 ⟩ 
    •[ PLUS (TIMES ONE BOOL) (TIMES ONE BOOL) , inj₁ (tt , TRUE) ]
      ⟷⟨ ⊕1 (id⟷ ⊗ swap1₊)⟩ 
    •[ PLUS (TIMES ONE BOOL) (TIMES ONE BOOL) , inj₁ (tt , FALSE) ]
      ⟷⟨ factor1 ⟩
    •[ BOOL² , (TRUE , FALSE) ] □))

-- The universe of types is a groupoid. The objects of this groupoid are the
-- pointed types; the morphisms are the programs; and the equivalence of
-- programs is the degenerate observational equivalence that equates every
-- two programs that are extensionally equivalent.

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
p₁ = path swap1₊
p₂ = path (id⟷ ◎ swap1₊)
p₃ = path (swap1₊ ◎ swap2₊ ◎ swap1₊)
p₄ = path (swap1₊ ◎ id⟷)
p₅ = path (uniti⋆ ◎ swap⋆ ◎ (swap1₊ ⊗ id⟷) ◎ swap⋆ ◎ unite⋆)
   
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
  linv◎l : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂ } → 
          1•[ PATH t₁ t₁ , path (c ◎ ! c)] ⇔
          1•[ PATH t₁ t₁ , path id⟷ ]
  linv◎r : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂ } → 
          1•[ PATH t₁ t₁ , path id⟷ ] ⇔
          1•[ PATH t₁ t₁ , path (c ◎ ! c) ]
  rinv◎l : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂ } → 
          1•[ PATH t₂ t₂ , path (! c ◎ c)] ⇔
          1•[ PATH t₂ t₂ , path id⟷ ]
  rinv◎r : ∀ {t₁ t₂} → {c : t₁ ⟷ t₂ } → 
          1•[ PATH t₂ t₂ , path id⟷ ] ⇔
          1•[ PATH t₂ t₂ , path (! c ◎ c) ]
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
1! linv◎l = linv◎r
1! linv◎r = linv◎l
1! rinv◎l = rinv◎r
1! rinv◎r = rinv◎l

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
1!≡ linv◎l = refl
1!≡ linv◎r = refl
1!≡ rinv◎l = refl
1!≡ rinv◎r = refl

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
        ; linv = λ {t₁} {t₂} c → linv◎l
        ; rinv = λ {t₁} {t₂} c → rinv◎l
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

ZEROℤ+• : {t : U} {v : ⟦ t ⟧} → Uℤ• 
ZEROℤ+• {t} {v} = pos• (t - t) v 

ZEROℤ-• : {t : U} {v : ⟦ t ⟧} → Uℤ• 
ZEROℤ-• {t} {v} = neg• (t - t) v 

PLUS1ℤ• : Uℤ• → Uℤ → Uℤ•
PLUS1ℤ• (pos• t₁ v₁) t₂ = pos• (PLUSℤ t₁ t₂) (inj₁ v₁)
PLUS1ℤ• (neg• t₁ v₁) t₂ = neg• (PLUSℤ t₁ t₂) (inj₁ v₁)

PLUS2ℤ• : Uℤ → Uℤ• → Uℤ•
PLUS2ℤ• t₁ (pos• t₂ v₂) = pos• (PLUSℤ t₁ t₂) (inj₂ v₂)
PLUS2ℤ• t₁ (neg• t₂ v₂) = neg• (PLUSℤ t₁ t₂) (inj₂ v₂)

-- Combinators on pointed types

data _⇄_ : Uℤ• → Uℤ• → Set where
  Fwd : ∀ {t₁ t₂ t₃ t₄ v₁ v₃} → 
        •[ PLUS t₁ t₄ , inj₁ v₁ ] ⟷ •[ PLUS t₂ t₃ , inj₂ v₃ ] → 
        pos• (t₁ - t₂) v₁ ⇄ pos• (t₃ - t₄) v₃
  Bck : ∀ {t₁ t₂ t₃ t₄ v₂ v₄} → 
        •[ PLUS t₁ t₄ , inj₂ v₄ ] ⟷ •[ PLUS t₂ t₃ , inj₁ v₂ ] → 
        neg• (t₁ - t₂) v₂ ⇄ neg• (t₃ - t₄) v₄
  B2F : ∀ {t v} → neg• (t - t) v ⇄ pos• (t - t) v
  F2B : ∀ {t v} → pos• (t - t) v ⇄ neg• (t - t) v

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
--}

id⇄ : {t : Uℤ•} → t ⇄ t
id⇄ {pos• t p} = Fwd swap1₊
id⇄ {neg• t n} = Bck swap2₊

_◎⇄_ : {t₁ t₂ t₃ : Uℤ•} → (t₁ ⇄ t₂) → (t₂ ⇄ t₃) → (t₁ ⇄ t₃) 
_◎⇄_ {pos• t₁ v₁} {pos• t₂ v₂} {pos• t₃ v₃} (Fwd c₁) (Fwd c₂) = 
  Fwd (•[ PLUS (pos t₁) (neg t₃) , inj₁ v₁ ] 
        ⟷⟨ {!!} ⟩
       •[ PLUS (neg t₁) (pos t₃) , inj₂ v₃ ] □)
-- c₁ : •[ PLUS (pos t₁) (neg t₂) , inj₁ v₁ ] ⟷
--      •[ PLUS (neg t₁) (pos t₂) , inj₂ v₂ ]
-- c₂ : •[ PLUS (pos t₂) (neg t₃) , inj₁ v₂ ] ⟷
--      •[ PLUS (neg t₂) (pos t₃) , inj₂ v₃ ]
_◎⇄_ {pos• (t₁ - t₂) v₁} {pos• (t₃ - .t₃) v₃} {neg• (.t₃ - .t₃) .v₃} 
     (Fwd c) F2B = {!!}
-- ?7 : pos• (t₁ - t₂) v₁ ⇄ neg• (t₃ - t₃) v₃
Bck c₁ ◎⇄ Bck c₂ = Bck {!!}
Bck c ◎⇄ B2F     = {!!}
B2F ◎⇄ Fwd c     = {!!}
B2F ◎⇄ F2B       = id⇄ 
F2B ◎⇄ Bck c     = {!!}
F2B ◎⇄ B2F       = id⇄ 

{--
  _⊕1_   : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₃ t₄ , inj₁ v₃ ])
  _⊕2_   : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
           (•[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₃ t₄ , inj₂ v₄ ])
  _⊗_     : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
           (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
          (•[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₃ t₄ , (v₃ , v₄) ])
--}

-- trace

η : ∀ {t v} → ZEROℤ+• {t} {v} ⇄ ZEROℤ-• {t} {v}
η = F2B 

ε : ∀ {t v} → ZEROℤ-• {t} {v} ⇄ ZEROℤ+• {t} {v}
ε = B2F

------------------------------------------------------------------------------

