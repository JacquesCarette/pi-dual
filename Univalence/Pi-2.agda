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

-- Proof that we have a groupoid; this does not depend on the definition of
-- programs

G : 1Groupoid
G = record
      { set = U
      ; _↝_ = _≡_
      ; _≈_ = _≡_ 
      ; id = refl 
      ; _∘_ = λ y≡z x≡y → trans x≡y y≡z 
      ; _⁻¹ = sym 
      ; lneutr = λ x≡y → proof-irrelevance (trans x≡y refl) x≡y
      ; rneutr = λ _ → refl 
      ; assoc = λ y≡z x≡y w≡x → 
          proof-irrelevance 
            (trans w≡x (trans x≡y y≡z)) 
            (trans (trans w≡x x≡y) y≡z) 
      ; equiv = isEquivalence
      ; linv = λ x≡y → proof-irrelevance (trans x≡y (sym x≡y)) refl 
      ; rinv = λ x≡y → proof-irrelevance (trans (sym x≡y) x≡y) refl 
      ; ∘-resp-≈ = λ f≡h g≡i → cong₂ trans g≡i f≡h 
      }

-- Programs
-- We use pointed types; programs map a pointed type to another
-- Programs should respect paths; if there is a path from v₁ to v₂ and
-- program c maps v₁ to v₁' then it maps v₂ to v₂' and there is a path from
-- v₂ to v₂'

record U• : Set where
  constructor •[_,_]
  field
    ∣_∣ : U
    • : ⟦ ∣_∣ ⟧

open U•

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


-- Examples

-- Some types

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

c₄ : ONE×ONE• ⟷ ONE•
c₄ = unite⋆

c₅ : PathSpace tt ⟷ PathSpace tt
c₅ = id⟷ 

------------------------------------------------------------------------------

