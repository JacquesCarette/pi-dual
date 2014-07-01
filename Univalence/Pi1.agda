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

-- all the following are paths from T to F; we will show below that they
-- are equivalent using 2paths

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

  -- groupoid combinators defined by induction on P.⟷ in Pi0.agda

  simplifyl◎l : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} 
             {c₁ : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} 
             {c₂ : P.U•.•[ t₂ , v₂ ] P.⟷ P.U•.•[ t₃ , v₃ ]} → 
    Path• (c₁ P.◎ c₂) ⟷ Path• (P.simplifyl◎ c₁ c₂)

  simplifyl◎r : {t₁ t₂ t₃ : P.U•} {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} → 
    Path• (P.simplifyl◎ c₁ c₂) ⟷ Path• (c₁ P.◎ c₂)

  simplifyr◎l : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} 
             {c₁ : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} 
             {c₂ : P.U•.•[ t₂ , v₂ ] P.⟷ P.U•.•[ t₃ , v₃ ]} → 
    Path• (c₁ P.◎ c₂) ⟷ Path• (P.simplifyr◎ c₁ c₂)

  simplifyr◎r : {t₁ t₂ t₃ : P.U•} {c₁ : t₁ P.⟷ t₂} {c₂ : t₂ P.⟷ t₃} → 
    Path• (P.simplifyr◎ c₁ c₂) ⟷ Path• (c₁ P.◎ c₂)

  simplifySyml : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
    Path• (P.sym⟷ c) ⟷ Path• (P.simplifySym c)

  simplifySymr : {t₁ t₂ : P.U•} {c : t₁ P.⟷ t₂} → 
    Path• (P.simplifySym c) ⟷ Path• (P.sym⟷ c)

  invll   : ∀ {t₁ t₂ v₁ v₂} → {c : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} → 
            Path• (P.sym⟷ c P.◎ c) ⟷ Path• (P.id⟷ {t₂} {v₂})
  invlr   : ∀ {t₁ t₂ v₁ v₂} → {c : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} → 
            Path• (P.id⟷ {t₂} {v₂}) ⟷ Path• (P.sym⟷ c P.◎ c)
  invrl   : ∀ {t₁ t₂ v₁ v₂} → {c : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} → 
            Path• (c P.◎ P.sym⟷ c) ⟷ Path• (P.id⟷ {t₁} {v₁})
  invrr   : ∀ {t₁ t₂ v₁ v₂} → {c : P.U•.•[ t₁ , v₁ ] P.⟷ P.U•.•[ t₂ , v₂ ]} → 
            Path• (P.id⟷ {t₁} {v₁}) ⟷ Path• (c P.◎ P.sym⟷ c)
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

{--
α₁ : Path• P.NOT•T ⟷ Path• (P.id⟷ P.◎ P.NOT•T)
α₁ = simplify◎r

α₂ α₃ : •[ TIMES (PATH P.NOT•T) (PATH (P.NOT•T P.◎ P.id⟷)) , (p₁ , p₄) ] ⟷ 
        •[ TIMES (PATH P.NOT•T) (PATH P.NOT•T) , (p₁ , p₁) ] 
α₂ = id⟷ ⊗ simplify◎l
α₃ = swap⋆ ◎ (simplify◎l ⊗ id⟷) 

-- let's try to prove that p₁ = p₂ = p₃ = p₄ = p₅

-- p₁ ~> p₂
α₄ : •[ PATH P.NOT•T , p₁ ] ⟷ •[ PATH (P.id⟷ P.◎ P.NOT•T) , p₂ ]
α₄ = simplify◎r

-- p₂ ~> p₃
α₅ : •[ PATH (P.id⟷ P.◎ P.NOT•T) , p₂ ] ⟷ 
     •[ PATH (P.NOT•T P.◎ P.NOT•F P.◎ P.NOT•T) , p₃ ]
α₅ = simplify◎l ◎ simplify◎r ◎ (resp◎ id⟷ (invrr {c = P.NOT•F} ◎ resp◎ id⟷ simplifySyml))
--}
-- p₃ ~> p₄
α₆ : •[ PATH (P.NOT•T P.◎ P.NOT•F P.◎ P.NOT•T) , p₃ ] ⟷ 
     •[ PATH (P.NOT•T P.◎ P.id⟷) , p₄ ]
α₆ = resp◎ id⟷ ((resp◎ simplifySymr id⟷) ◎ invll)

-- p₅ ~> p₁

{--
α₈ : •[ PATH (P.uniti⋆ P.◎ P.swap⋆ P.◎ 
             (P.NOT•T P.⊗ P.id⟷) P.◎ P.swap⋆ P.◎ P.unite⋆) , 
        p₅ ] ⟷ 
     •[ PATH P.NOT•T , p₁ ] 
α₈ = resp◎ id⟷ (resp◎ id⟷ tassocl) ◎ 
     resp◎ id⟷ (resp◎ id⟷ (resp◎ simplify◎l id⟷)) ◎ 
     resp◎ id⟷ (resp◎ id⟷ tassocr) ◎
     resp◎ id⟷ tassocl ◎
     resp◎ id⟷ (resp◎ (resp◎ simplifySymr id⟷) id⟷) ◎
     resp◎ id⟷ (resp◎ invll id⟷) ◎
     resp◎ id⟷ simplify◎l ◎
     resp◎ id⟷ simplify◎l ◎
     resp◎ simplifySyml id⟷ ◎
     tassocl ◎ 
     resp◎ invll id⟷ ◎
     simplify◎l 

-- p₄ ~> p₅

α₇ : •[ PATH (P.NOT•T P.◎ P.id⟷) , p₄ ] ⟷ 
     •[ PATH (P.uniti⋆ P.◎ P.swap⋆ P.◎ 
             (P.NOT•T P.⊗ P.id⟷) P.◎ P.swap⋆ P.◎ P.unite⋆) , 
        p₅ ]
α₇ = simplify◎l ◎ (sym⟷ α₈)
--}

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
        ; lneutr = λ {t₁} {t₂} c → simplifyr◎l 
           {P.U•.∣ t₁ ∣} {P.U•.∣ t₂ ∣} {P.U•.∣ t₂ ∣} 
           {P.U•.• t₁} {P.U•.• t₂} {P.U•.• t₂} {c} {P.id⟷} 
        ; rneutr = λ {t₁} {t₂} c → simplifyl◎l 
           {P.U•.∣ t₁ ∣} {P.U•.∣ t₁ ∣} {P.U•.∣ t₂ ∣} 
           {P.U•.• t₁} {P.U•.• t₁} {P.U•.• t₂} {P.id⟷} {c}
        ; assoc = λ _ _ _ → tassocl
        ; equiv = record { refl = id⟷ 
                                ; sym = λ c → sym⟷ c 
                                ; trans = λ c₀ c₁ → c₀ ◎ c₁ }
        ; linv = λ {t₁} {t₂} c → 
                   invrl {P.U•.∣ t₁ ∣} {P.U•.∣ t₂ ∣} {P.U•.• t₁} {P.U•.• t₂}
        ; rinv = λ {t₁} {t₂} c → 
                   invll {P.U•.∣ t₁ ∣} {P.U•.∣ t₂ ∣} {P.U•.• t₁} {P.U•.• t₂}
        ; ∘-resp-≈ = λ f⟷h g⟷i → resp◎ g⟷i f⟷h 
        }

------------------------------------------------------------------------------

