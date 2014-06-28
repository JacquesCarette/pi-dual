module Pi1 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Groupoid
import Pi0 as P

infixr 10 _◎_
infixr 30 _⟷_

------------------------------------------------------------------------------
-- Level 1: 
-- Types are sets of paths. The paths are defined at the previous level
-- (level 0). At level 1, there is no interesting 2path structure. From
-- the perspective of level 0, we have points with non-trivial paths between
-- them, i.e., we have a groupoid. The paths cross type boundaries, i.e., we
-- have heterogeneous equality

-- types

data U : Set where
  ZERO  : U              -- empty set of paths
  ONE   : U              -- a trivial path
  PLUS  : U → U → U      -- disjoint union of paths
  TIMES : U → U → U      -- pairs of paths
  PATH  : {t₁ t₂ : P.U•} → (t₁ P.⟷ t₂) → U -- level 0 paths between values

-- values

data Path {t₁ t₂ : P.U•} : P.Space t₁ → P.Space t₂ → Set where
  path : (c : t₁ P.⟷ t₂) → Path (P.point t₁) (P.point t₂)

⟦_⟧ : U → Set
⟦ ZERO ⟧             = ⊥
⟦ ONE ⟧              = ⊤
⟦ PLUS t₁ t₂ ⟧       = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧      = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ PATH {t₁} {t₂} c ⟧ = Path {t₁} {t₂} (P.point t₁) (P.point t₂) 

-- examples

T⇔F : Set
T⇔F = Path {P.BOOL•T} {P.BOOL•F} P.TRUE P.FALSE

F⇔T : Set
F⇔T = Path {P.BOOL•F} {P.BOOL•T} P.FALSE P.TRUE

p₁ p₂ p₃ p₄ p₅ : T⇔F
p₁ = path P.NOT•T
p₂ = path (P.id⟷ P.◎ P.NOT•T)
p₃ = path (P.NOT•T P.◎ P.NOT•F P.◎ P.NOT•T)
p₄ = path (P.NOT•T P.◎ P.id⟷)
p₅ = path (P.uniti⋆ P.◎ P.swap⋆ P.◎ (P.NOT•T P.⊗ P.id⟷) P.◎ P.swap⋆ P.◎ P.unite⋆)
   
p₆ : (T⇔F × T⇔F) ⊎ F⇔T
p₆ = inj₁ (p₁ , p₂)

-- Programs map paths to paths. We also use pointed types.

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

PathSpace : {t₁ t₂ : P.U•} → (c : t₁ P.⟷ t₂) → U•
PathSpace c = •[ PATH c , path c ]

data _⟷_ : U• → U• → Set where

  -- common combinators

  id⟷    : {t : U•} → t ⟷ t
  sym⟷   : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
  _◎_     : {t₁ t₂ t₃ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)

  -- groupoid combinators

  lidl    : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace (P.id⟷ P.◎ c) ⟷ PathSpace c
  lidr    : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace c ⟷ PathSpace (P.id⟷ P.◎ c)
  ridl    : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace (c P.◎ P.id⟷) ⟷ PathSpace c
  ridr    : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace c ⟷ PathSpace (c P.◎ P.id⟷)
  invll   : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace (P.sym⟷ c P.◎ c) ⟷ PathSpace {t₂} {t₂} P.id⟷ 
  invlr   : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace {t₂} {t₂} P.id⟷ ⟷ PathSpace (P.sym⟷ c P.◎ c)
  invrl   : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace (c P.◎ P.sym⟷ c) ⟷ PathSpace {t₁} {t₁} P.id⟷
  invrr   : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace {t₁} {t₁} P.id⟷ ⟷ PathSpace (c P.◎ P.sym⟷ c)
  invinvl : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace (P.sym⟷ (P.sym⟷ c)) ⟷ PathSpace c
  invinvr : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            PathSpace c ⟷ PathSpace (P.sym⟷ (P.sym⟷ c))
  tassocl : {t₁ t₂ t₃ t₄ : P.U•} 
            {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} {c₃ : t₃ P.⟷ t₄} → 
            PathSpace (c₁ P.◎ (c₂ P.◎ c₃)) ⟷ 
            PathSpace ((c₁ P.◎ c₂) P.◎ c₃)
  tassocr : {t₁ t₂ t₃ t₄ : P.U•} 
            {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} {c₃ : t₃ P.⟷ t₄} → 
            PathSpace ((c₁ P.◎ c₂) P.◎ c₃) ⟷ 
            PathSpace (c₁ P.◎ (c₂ P.◎ c₃))
  -- resp◎ is closely related to Eckmann-Hilton
  resp◎   : {t₁ t₂ t₃ : P.U•} 
            {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} 
            {c₃ : t₁ P.⟷ t₂} {c₄ : t₂ P.⟷ t₃} → 
            (PathSpace c₁ ⟷ PathSpace c₃) → 
            (PathSpace c₂ ⟷ PathSpace c₄) → 
            PathSpace (c₁ P.◎ c₂) ⟷ PathSpace (c₃ P.◎ c₄)

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

α₁ : PathSpace P.NOT•T ⟷ PathSpace (P.id⟷ P.◎ P.NOT•T)
α₁ = lidr 

α₂ α₃ : •[ TIMES (PATH P.NOT•T) (PATH (P.NOT•T P.◎ P.id⟷)) , (p₁ , p₄) ] ⟷ 
        •[ TIMES (PATH P.NOT•T) (PATH P.NOT•T) , (p₁ , p₁) ] 
α₂ = id⟷ ⊗ ridl 
α₃ = swap⋆ ◎ (ridl ⊗ id⟷) 

-- level 0 is a groupoid with a non-trivial path equivalence

G : 1Groupoid
G = record
        { set = P.U•
        ; _↝_ = P._⟷_
        ; _≈_ = λ c₀ c₁ → PathSpace c₀ ⟷ PathSpace c₁
        ; id = P.id⟷
        ; _∘_ = λ c₀ c₁ → c₁ P.◎ c₀
        ; _⁻¹ = P.sym⟷
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

