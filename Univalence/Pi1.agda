module Pi1 where

-- plan after that: add trace; this make obs equiv much more interesting and
-- allows a limited form of h.o. functions via the int construction and then
-- do the ring completion to get more complete notion of h.o. functions

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

data Path (t₁ t₂ : P.U•) : Set where
  path : (c : t₁ P.⟷ t₂) → Path t₁ t₂

⟦_⟧ : U → Set
⟦ ZERO ⟧             = ⊥
⟦ ONE ⟧              = ⊤
⟦ PLUS t₁ t₂ ⟧       = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧      = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ PATH {t₁} {t₂} c ⟧ = Path t₁ t₂

-- examples

T⇔F : Set
T⇔F = Path P.BOOL•T P.BOOL•F

F⇔T : Set
F⇔T = Path P.BOOL•F P.BOOL•T

-- all the following are paths from T to F

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

Path• : {t₁ t₂ : P.U•} → (c : t₁ P.⟷ t₂) → U•
Path• c = •[ PATH c , path c ]

data _⟷_ : U• → U• → Set where

  -- common combinators

  id⟷    : {t : U•} → t ⟷ t
  sym⟷   : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
  _◎_     : {t₁ t₂ t₃ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)

  -- groupoid combinators

  lidl    : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            Path• (P.id⟷ P.◎ c) ⟷ Path• c
  lidr    : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            Path• c ⟷ Path• (P.id⟷ P.◎ c)
  ridl    : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            Path• (c P.◎ P.id⟷) ⟷ Path• c
  ridr    : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            Path• c ⟷ Path• (c P.◎ P.id⟷)
  invll   : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            Path• (P.sym⟷ c P.◎ c) ⟷ Path• (P.id⟷ {t₂})
  invlr   : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            Path• (P.id⟷ {t₂}) ⟷ Path• (P.sym⟷ c P.◎ c)
  invrl   : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            Path• (c P.◎ P.sym⟷ c) ⟷ Path• (P.id⟷ {t₁})
  invrr   : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
            Path• (P.id⟷ {t₁}) ⟷ Path• (c P.◎ P.sym⟷ c)
  invunite₊l : {t : P.U•} → 
            Path• (P.sym⟷ (P.unite₊ {t})) ⟷ Path• (P.uniti₊ {t})
  invunite₊r : {t : P.U•} → 
            Path• (P.uniti₊ {t}) ⟷ Path• (P.sym⟷ (P.unite₊ {t}))
  invuniti₊l : {t : P.U•} → 
            Path• (P.sym⟷ (P.uniti₊ {t})) ⟷ Path• (P.unite₊ {t})
  invuniti₊r : {t : P.U•} → 
            Path• (P.unite₊ {t}) ⟷ Path• (P.sym⟷ (P.uniti₊ {t}))
  invswap1₊l : {t₁ t₂ : P.U•} → 
            Path• (P.sym⟷ (P.swap1₊ {t₁} {t₂})) ⟷ 
            Path• (P.swap2₊ {t₂} {t₁})
  invswap1₊r : {t₁ t₂ : P.U•} → 
            Path• (P.swap2₊ {t₂} {t₁}) ⟷ 
            Path• (P.sym⟷ (P.swap1₊ {t₁} {t₂})) 
  invswap2₊l : {t₁ t₂ : P.U•} → 
            Path• (P.sym⟷ (P.swap2₊ {t₂} {t₁})) ⟷ 
            Path• (P.swap1₊ {t₁} {t₂})
  invswap2₊r : {t₁ t₂ : P.U•} → 
            Path• (P.swap1₊ {t₁} {t₂}) ⟷ 
            Path• (P.sym⟷ (P.swap2₊ {t₂} {t₁})) 
  invassocl1₊l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.assocl1₊ {t₁} {t₂} {t₃})) ⟷
            Path• (P.assocr1₊ {t₁} {t₂} {t₃})
  invassocl1₊r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.assocr1₊ {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.assocl1₊ {t₁} {t₂} {t₃})) 
  invassocl2₊l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.assocl2₊ {t₁} {t₂} {t₃})) ⟷
            Path• (P.assocr2₊ {t₁} {t₂} {t₃})
  invassocl2₊r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.assocr2₊ {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.assocl2₊ {t₁} {t₂} {t₃})) 
  invassocl3₊l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.assocl3₊ {t₁} {t₂} {t₃})) ⟷
            Path• (P.assocr3₊ {t₁} {t₂} {t₃})
  invassocl3₊r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.assocr3₊ {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.assocl3₊ {t₁} {t₂} {t₃})) 
  invassocr1₊l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.assocr1₊ {t₁} {t₂} {t₃})) ⟷
            Path• (P.assocl1₊ {t₁} {t₂} {t₃})
  invassocr1₊r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.assocl1₊ {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.assocr1₊ {t₁} {t₂} {t₃})) 
  invassocr2₊l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.assocr2₊ {t₁} {t₂} {t₃})) ⟷
            Path• (P.assocl2₊ {t₁} {t₂} {t₃})
  invassocr2₊r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.assocl2₊ {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.assocr2₊ {t₁} {t₂} {t₃})) 
  invassocr3₊l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.assocr3₊ {t₁} {t₂} {t₃})) ⟷
            Path• (P.assocl3₊ {t₁} {t₂} {t₃})
  invassocr3₊r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.assocl3₊ {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.assocr3₊ {t₁} {t₂} {t₃})) 
  invunite⋆l : {t : P.U•} → 
            Path• (P.sym⟷ (P.unite⋆ {t})) ⟷ Path• (P.uniti⋆ {t})
  invunite⋆r : {t : P.U•} → 
            Path• (P.uniti⋆ {t}) ⟷ Path• (P.sym⟷ (P.unite⋆ {t}))
  invuniti⋆l : {t : P.U•} → 
            Path• (P.sym⟷ (P.uniti⋆ {t})) ⟷ Path• (P.unite⋆ {t})
  invuniti⋆r : {t : P.U•} → 
            Path• (P.unite⋆ {t}) ⟷ Path• (P.sym⟷ (P.uniti⋆ {t}))
  invswap⋆ : {t₁ t₂ : P.U•} → 
            Path• (P.sym⟷ (P.swap⋆ {t₁} {t₂})) ⟷ Path• (P.swap⋆ {t₂} {t₁})
  invassocl⋆l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.assocl⋆ {t₁} {t₂} {t₃})) ⟷ 
            Path• (P.assocr⋆ {t₁} {t₂} {t₃})
  invassocl⋆r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.assocr⋆ {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.assocl⋆ {t₁} {t₂} {t₃})) 
  invassocr⋆l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.assocr⋆ {t₁} {t₂} {t₃})) ⟷ 
            Path• (P.assocl⋆ {t₁} {t₂} {t₃})
  invassocr⋆r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.assocl⋆ {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.assocr⋆ {t₁} {t₂} {t₃})) 
  invdistzl : {t : P.U•} {absurd : P.⟦ P.ZERO ⟧} → 
            Path• (P.sym⟷ (P.distz {t} {absurd})) ⟷ 
            Path• (P.factorz {t} {absurd})
  invdistzr : {t : P.U•} {absurd : P.⟦ P.ZERO ⟧} → 
            Path• (P.factorz {t} {absurd}) ⟷ 
            Path• (P.sym⟷ (P.distz {t} {absurd})) 
  invfactorzl : {t : P.U•} {absurd : P.⟦ P.ZERO ⟧} → 
            Path• (P.sym⟷ (P.factorz {t} {absurd})) ⟷ 
            Path• (P.distz {t} {absurd})
  invfactorzr : {t : P.U•} {absurd : P.⟦ P.ZERO ⟧} → 
            Path• (P.distz {t} {absurd}) ⟷ 
            Path• (P.sym⟷ (P.factorz {t} {absurd})) 
  invdist1l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.dist1 {t₁} {t₂} {t₃})) ⟷ 
            Path• (P.factor1 {t₁} {t₂} {t₃})
  invdist1r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.factor1 {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.dist1 {t₁} {t₂} {t₃})) 
  invdist2l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.dist2 {t₁} {t₂} {t₃})) ⟷ 
            Path• (P.factor2 {t₁} {t₂} {t₃})
  invdist2r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.factor2 {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.dist2 {t₁} {t₂} {t₃})) 
  invfactor1l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.factor1 {t₁} {t₂} {t₃})) ⟷ 
            Path• (P.dist1 {t₁} {t₂} {t₃})
  invfactor1r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.dist1 {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.factor1 {t₁} {t₂} {t₃})) 
  invfactor2l : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.sym⟷ (P.factor2 {t₁} {t₂} {t₃})) ⟷ 
            Path• (P.dist2 {t₁} {t₂} {t₃})
  invfactor2r : {t₁ t₂ t₃ : P.U•} → 
            Path• (P.dist2 {t₁} {t₂} {t₃}) ⟷ 
            Path• (P.sym⟷ (P.factor2 {t₁} {t₂} {t₃})) 
  invid : {t : P.U•} → 
            Path• (P.sym⟷ (P.id⟷ {t})) ⟷ Path• (P.id⟷ {t})
  invsyml : {t₁ t₂ : P.U•} → (c : t₁ P.⟷ t₂) → 
            Path• (P.sym⟷ (P.sym⟷ c)) ⟷  Path• c
  invsymr : {t₁ t₂ : P.U•} → (c : t₁ P.⟷ t₂) → 
            Path• c ⟷ Path• (P.sym⟷ (P.sym⟷ c)) 
  inv◎l : {t₁ t₂ t₃ : P.U•} → (c₁ : t₁ P.⟷ t₂) (c₂ : t₂ P.⟷ t₃) → 
            Path• (P.sym⟷ (c₁ P.◎ c₂)) ⟷ 
            Path• (P.sym⟷ c₂ P.◎ P.sym⟷ c₁)
  inv◎r : {t₁ t₂ t₃ : P.U•} → (c₁ : t₁ P.⟷ t₂) (c₂ : t₂ P.⟷ t₃) → 
            Path• (P.sym⟷ c₂ P.◎ P.sym⟷ c₁) ⟷ 
            Path• (P.sym⟷ (c₁ P.◎ c₂)) 
  inv⊕1l : {t₁ t₂ t₃ t₄ : P.U•} → (c₁ : t₁ P.⟷ t₃) → (c₂ : t₂ P.⟷ t₄) → 
            Path• (P.sym⟷ (c₁ P.⊕1 c₂)) ⟷ 
            Path• (P.sym⟷ c₁ P.⊕1 P.sym⟷ c₂)
  inv⊕1r : {t₁ t₂ t₃ t₄ : P.U•} → (c₁ : t₁ P.⟷ t₃) → (c₂ : t₂ P.⟷ t₄) → 
            Path• (P.sym⟷ c₁ P.⊕1 P.sym⟷ c₂) ⟷ 
            Path• (P.sym⟷ (c₁ P.⊕1 c₂)) 
  inv⊕2l : {t₁ t₂ t₃ t₄ : P.U•} → (c₁ : t₁ P.⟷ t₃) → (c₂ : t₂ P.⟷ t₄) → 
            Path• (P.sym⟷ (c₁ P.⊕2 c₂)) ⟷ 
            Path• (P.sym⟷ c₁ P.⊕2 P.sym⟷ c₂)
  inv⊕2r : {t₁ t₂ t₃ t₄ : P.U•} → (c₁ : t₁ P.⟷ t₃) → (c₂ : t₂ P.⟷ t₄) → 
            Path• (P.sym⟷ c₁ P.⊕2 P.sym⟷ c₂) ⟷ 
            Path• (P.sym⟷ (c₁ P.⊕2 c₂)) 
  inv⊗l : {t₁ t₂ t₃ t₄ : P.U•} → (c₁ : t₁ P.⟷ t₃) → (c₂ : t₂ P.⟷ t₄) → 
            Path• (P.sym⟷ (c₁ P.⊗ c₂)) ⟷ 
            Path• (P.sym⟷ c₁ P.⊗ P.sym⟷ c₂)
  inv⊗r : {t₁ t₂ t₃ t₄ : P.U•} → (c₁ : t₁ P.⟷ t₃) → (c₂ : t₂ P.⟷ t₄) → 
            Path• (P.sym⟷ c₁ P.⊗ P.sym⟷ c₂) ⟷ 
            Path• (P.sym⟷ (c₁ P.⊗ c₂)) 
  tassocl : {t₁ t₂ t₃ t₄ : P.U•} 
            {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} {c₃ : t₃ P.⟷ t₄} → 
            Path• (c₁ P.◎ (c₂ P.◎ c₃)) ⟷ 
            Path• ((c₁ P.◎ c₂) P.◎ c₃)
  tassocr : {t₁ t₂ t₃ t₄ : P.U•} 
            {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} {c₃ : t₃ P.⟷ t₄} → 
            Path• ((c₁ P.◎ c₂) P.◎ c₃) ⟷ 
            Path• (c₁ P.◎ (c₂ P.◎ c₃))
  -- resp◎ is closely related to Eckmann-Hilton
  resp◎   : {t₁ t₂ t₃ : P.U•} 
            {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} 
            {c₃ : t₁ P.⟷ t₂} {c₄ : t₂ P.⟷ t₃} → 
            (Path• c₁ ⟷ Path• c₃) → 
            (Path• c₂ ⟷ Path• c₄) → 
            Path• (c₁ P.◎ c₂) ⟷ Path• (c₃ P.◎ c₄)

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

α₁ : Path• P.NOT•T ⟷ Path• (P.id⟷ P.◎ P.NOT•T)
α₁ = lidr 

α₂ α₃ : •[ TIMES (PATH P.NOT•T) (PATH (P.NOT•T P.◎ P.id⟷)) , (p₁ , p₄) ] ⟷ 
        •[ TIMES (PATH P.NOT•T) (PATH P.NOT•T) , (p₁ , p₁) ] 
α₂ = id⟷ ⊗ ridl 
α₃ = swap⋆ ◎ (ridl ⊗ id⟷) 

-- let's try to prove that p₁ = p₂ = p₃ = p₄ = p₅

-- p₁ ~> p₂
α₄ : •[ PATH P.NOT•T , p₁ ] ⟷ •[ PATH (P.id⟷ P.◎ P.NOT•T) , p₂ ]
α₄ = lidr

-- p₂ ~> p₃
α₅ : •[ PATH (P.id⟷ P.◎ P.NOT•T) , p₂ ] ⟷ 
     •[ PATH (P.NOT•T P.◎ P.NOT•F P.◎ P.NOT•T) , p₃ ]
α₅ = lidl ◎ ridr ◎ (resp◎ id⟷ (invrr {c = P.NOT•F} ◎ resp◎ id⟷ invswap2₊l))

-- p₃ ~> p₄
α₆ : •[ PATH (P.NOT•T P.◎ P.NOT•F P.◎ P.NOT•T) , p₃ ] ⟷ 
     •[ PATH (P.NOT•T P.◎ P.id⟷) , p₄ ]
α₆ = resp◎ id⟷ ((resp◎ invswap1₊r id⟷) ◎ invll)

-- probably not possible to show that any of these is equal to p₅

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
        { set = P.U•
        ; _↝_ = P._⟷_
        ; _≈_ = λ c₀ c₁ → Path• c₀ ⟷ Path• c₁
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

