module Pi-2 where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Groupoid

infixr 10 _◎_
infixr 30 _⟷_

------------------------------------------------------------------------------
-- Level -2
-- Types are -2 groupoids or equivalently all types are contractible

-- Types and values are defined mutually without reference to programs
-- Types always include PATHs in addition to the usual types.

mutual

  data U : Set where
    ONE   : U
    TIMES : U → U → U
    PATH  : {t : U} → ⟦ t ⟧ → ⟦ t ⟧ → U

  ⟦_⟧ : U → Set
  ⟦ ONE ⟧         = ⊤
  ⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ PATH v₁ v₂ ⟧  = (v₁ ≡ v₂)

-- Proof that all types are contractible. Def. 3.11.1 in the HoTT book

isContr : (t : U) → Σ[ v ∈ ⟦ t ⟧ ] ((v' : ⟦ t ⟧) → (v ≡ v'))
isContr ONE = (tt , λ v → refl)
isContr (TIMES t₁ t₂) with isContr t₁ | isContr t₂ 
... | (v₁ , f₁) | (v₂ , f₂) = ((v₁ , v₂) , f) 
  where f : (vv : ⟦ t₁ ⟧ × ⟦ t₂ ⟧) → (v₁ , v₂) ≡ vv
        f (v₁' , v₂') = cong₂ _,′_ (f₁ v₁') (f₂ v₂') 
isContr (PATH {t} v₁ v₂) with isContr t
isContr (PATH {t} v₁ v₂) | (v' , f') = (p , λ q → proof-irrelevance p q)
  where p = trans (sym (f' v₁))  (f' v₂) 

-- Proof that every type is a groupoid; this does not depend on the
-- definition of programs

isGroupoid : U → 1Groupoid
isGroupoid ONE              = discrete ⊤ 
isGroupoid (TIMES t₁ t₂)    = isGroupoid t₁ ×G isGroupoid t₂
isGroupoid (PATH {t} v₁ v₂) = discrete (v₁ ≡ v₂)

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

data _⟷_ : U• → U• → Set where
  id⟷    : {t : U•} → t ⟷ t
  sym⟷   : {t₁ t₂ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
  _◎_     : {t₁ t₂ t₃ : U•} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
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
  _⊗_     : {t₁ t₂ t₃ t₄ : U•} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → 
            (•[ TIMES ∣ t₁ ∣ ∣ t₂ ∣ , (• t₁ , • t₂ ) ] ⟷ 
             •[ TIMES ∣ t₃ ∣ ∣ t₄ ∣ , (• t₃ , • t₄ ) ])

-- Proof that the universe is itself a groupoid; this DOES depend on the
-- definition of programs; the morphisms between types ARE the programs; all
-- programs between the same types are forced to be the same using a
-- degenerate observational equivalence relation.

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
       ; lneutr = λ _ →  tt 
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

-- Examples

ONE• ONE×ONE• : U•
ONE•     = •[ ONE , tt ]
ONE×ONE• = •[ TIMES ONE ONE , (tt , tt) ] 

PathSpace : {t : U•} → ⟦ ∣ t ∣ ⟧ → U•
PathSpace v = •[ PATH v v , refl ]

c₁ c₂ c₃ : ONE• ⟷ ONE•
c₁ = id⟷
c₂ = uniti⋆ ◎ swap⋆ ◎ unite⋆ 
c₃ = uniti⋆ ◎ uniti⋆ ◎ assocl⋆ ◎ (swap⋆ ⊗ (sym⟷ id⟷)) ◎ 
     assocr⋆ ◎ unite⋆ ◎ unite⋆

-- The evaluation of a program like c₁, c₂, c₃ above is not done in order to
-- figure out the output value. Both the input and output values are encoded
-- in the type of the program; what the evaluation does is follow the path to
-- constructively reach the ouput value from the input value. Even though the
-- programs are observationally equivalent, the follow different paths. The
-- next level will allow us to reason about which of these paths are
-- connected by 2paths etc.

c₄ : ONE×ONE• ⟷ ONE•
c₄ = unite⋆

c₅ : PathSpace tt ⟷ PathSpace tt
c₅ = id⟷ 

c₁≅c₂ : c₁ obs≅ c₂
c₁≅c₂ = tt

-- the following does not typecheck
-- c₁≅c₄ : c₁ obs≅ c₄
-- it is not possible to equate programs that go between different types/values.

------------------------------------------------------------------------------

