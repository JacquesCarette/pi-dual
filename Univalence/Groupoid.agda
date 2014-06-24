{-# OPTIONS --without-K #-}

-- Inspired by Thorsten Altenkirch's definition of Groupoids 
-- see his OmegaCats repo on github.  And copumpkin's definition of
-- Category (see his categories repo, also on github).

module Groupoid where

open import Agda.Prim
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Function using (flip)
open import Relation.Binary

-- Useful
Rel0 : Set → Set₁
Rel0 A = Rel A lzero
 
-- 1-groupoids are those where the various laws hold up to ≈.
record 1Groupoid : Set₁ where
  infixr 9 _∘_
  infixr 5 _↝_
  infix  4 _≈_
  field
    set : Set₀
    _↝_ : set → set → Set
    _≈_ : ∀ {A B} → A ↝ B → A ↝ B → Set
    id : ∀ {x} → x ↝ x
    _∘_ : ∀ {x y z} → y ↝ z → x ↝ y → x ↝ z
    _⁻¹ : ∀ {x y} → x ↝ y → y ↝ x
    lneutr : ∀ {x y}(α : x ↝ y) → id ∘ α ≈ α
    rneutr : ∀ {x y}(α : x ↝ y) → α ∘ id ≈ α
    assoc : ∀ {w x y z}(α : y ↝ z)(β : x ↝ y)(δ : w ↝ x) → (α ∘ β) ∘ δ ≈ α ∘ (β ∘ δ)
    equiv : ∀ {x y} → IsEquivalence (_≈_ {x} {y})
    linv : ∀ {x y}(α : x ↝ y) → α ⁻¹ ∘ α ≈ id {x}
    rinv : ∀ {x y}(α : x ↝ y) → α ∘ α ⁻¹ ≈ id {y}
    ∘-resp-≈ : ∀ {x y z} {f h : y ↝ z} {g i : x ↝ y} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

_[_,_] : (C : 1Groupoid) → 1Groupoid.set C → 1Groupoid.set C → Set
_[_,_] = 1Groupoid._↝_

open 1Groupoid

_⊎G_ : 1Groupoid → 1Groupoid → 1Groupoid
A ⊎G B = record 
  { set = A.set ⊎ B.set
  ; _↝_ =  _⇛_
  ; _≈_ = λ {x} → mk≈ {x}   
  ; id = λ {x} → id⇛ {x}
  ; _∘_ = λ {x} → _∙G_ {x = x}
  ; _⁻¹ = λ {x} → inv {x = x}
  ; lneutr = λ {x} → lid⇛ {x}
  ; rneutr = λ {x} → rid⇛ {x}
  ; assoc = λ {x} → assoc∙ {x}
  ; equiv = λ {x} → equiv≈ {x}
  ; linv = λ {x} → linv⇛ {x}
  ; rinv = λ {x} → rinv⇛ {x}
  ; ∘-resp-≈ = λ {x} → resp {x} }
  where
    module A = 1Groupoid A
    module B = 1Groupoid B
    C : Set
    C = set A ⊎ set B

    _⇛_ : set A ⊎ set B → set A ⊎ set B → Set
    _⇛_ (inj₁ x) (inj₁ y) = A._↝_ x y
    _⇛_ (inj₁ _) (inj₂ _) = ⊥
    _⇛_ (inj₂ _) (inj₁ _) = ⊥
    _⇛_ (inj₂ x) (inj₂ y) = B._↝_ x y

    mk≈ : {x y : set A ⊎ set B} → x ⇛ y → x ⇛ y → Set
    mk≈ {inj₁ z} {inj₁ z'} a b = A._≈_ a b
    mk≈ {inj₁ x} {inj₂ y}  () ()
    mk≈ {inj₂ y} {inj₁ x}  () ()
    mk≈ {inj₂ y} {inj₂ y'} a b = B._≈_ a b

    id⇛ : {x : set A ⊎ set B} → x ⇛ x
    id⇛ {inj₁ _} = id A
    id⇛ {inj₂ _} = id B

    _∙G_ : {x y z : set A ⊎ set B} → y ⇛ z → x ⇛ y → x ⇛ z
    _∙G_ {inj₁ _} {inj₁ _} {inj₁ _} a b = A._∘_ a b
    _∙G_ {inj₁ _} {inj₁ _} {inj₂ _} () b
    _∙G_ {inj₁ x} {inj₂ y} a ()
    _∙G_ {inj₂ y} {inj₁ x} a ()
    _∙G_ {inj₂ y} {inj₂ y₁} {inj₁ x} () b
    _∙G_ {inj₂ _} {inj₂ _} {inj₂ _} a b = B._∘_ a b

    inv : {x y : set A ⊎ set B} → x ⇛ y → y ⇛ x
    inv {inj₁ _} {inj₁ _} a = A._⁻¹ a
    inv {inj₁ _} {inj₂ _} ()
    inv {inj₂ _} {inj₁ _} ()
    inv {inj₂ _} {inj₂ _} a = B._⁻¹ a

    lid⇛ : {x y : C} (α : x ⇛ y) → mk≈ {x} (_∙G_ {x} (id⇛ {y}) α) α
    lid⇛ {inj₁ _} {inj₁ _} a = A.lneutr a
    lid⇛ {inj₁ _} {inj₂ _} ()
    lid⇛ {inj₂ _} {inj₁ _} ()
    lid⇛ {inj₂ _} {inj₂ _} a = B.lneutr a

    rid⇛ : {x y : A.set ⊎ B.set} (α : x ⇛ y) → mk≈ {x} (_∙G_ {x} α (id⇛ {x})) α
    rid⇛ {inj₁ _} {inj₁ _} = A.rneutr
    rid⇛ {inj₁ _} {inj₂ _} ()
    rid⇛ {inj₂ _} {inj₁ _} ()
    rid⇛ {inj₂ _} {inj₂ _} = B.rneutr

    assoc∙ : {w x y z : C} (α : y ⇛ z) (β : x ⇛ y) (δ : w ⇛ x) → 
             mk≈ {w} {z} (_∙G_ {w} (_∙G_ {x} α β) δ) (_∙G_ {w} α (_∙G_ {w} β δ))
    assoc∙ {inj₁ x} {inj₁ x₁} {inj₁ x₂} {inj₁ x₃} = A.assoc
    assoc∙ {inj₁ x} {inj₁ x₁} {inj₁ x₂} {inj₂ y} () _ _
    assoc∙ {inj₁ x} {inj₁ x₁} {inj₂ y} _ () _
    assoc∙ {inj₁ x} {inj₂ y} _ _ ()
    assoc∙ {inj₂ y} {inj₁ x} _ _ ()
    assoc∙ {inj₂ y} {inj₂ y₁} {inj₁ x} _ () _
    assoc∙ {inj₂ y} {inj₂ y₁} {inj₂ y₂} {inj₁ x} () _ _
    assoc∙ {inj₂ y} {inj₂ y₁} {inj₂ y₂} {inj₂ y₃} = B.assoc

    linv⇛ : {x y : C} (α : x ⇛ y) → mk≈ {x} (_∙G_ {x} (inv {x} α) α) (id⇛ {x})
    linv⇛ {inj₁ _} {inj₁ _} = A.linv
    linv⇛ {inj₁ x} {inj₂ y} ()
    linv⇛ {inj₂ y} {inj₁ x} ()
    linv⇛ {inj₂ _} {inj₂ _} = B.linv
    

    rinv⇛ : {x y : C} (α : x ⇛ y) → mk≈ {y} (_∙G_ {y} α (inv {x} α)) (id⇛ {y})
    rinv⇛ {inj₁ _} {inj₁ _} = A.rinv
    rinv⇛ {inj₁ x} {inj₂ y} ()
    rinv⇛ {inj₂ y} {inj₁ x} ()
    rinv⇛ {inj₂ _} {inj₂ _} = B.rinv

    refl≈ : {x y : C} → Reflexive (mk≈ {x} {y})
    refl≈ {inj₁ _} {inj₁ _} = IsEquivalence.refl A.equiv
    refl≈ {inj₁ _} {inj₂ _} {()}
    refl≈ {inj₂ _} {inj₁ _} {()}
    refl≈ {inj₂ y} {inj₂ y₁} = IsEquivalence.refl B.equiv

    sym≈ : {x y : C} → Symmetric (mk≈ {x} {y})
    sym≈ {inj₁ _} {inj₁ _} = IsEquivalence.sym A.equiv
    sym≈ {inj₁ _} {inj₂ _} {()}
    sym≈ {inj₂ _} {inj₁ _} {()}
    sym≈ {inj₂ y} {inj₂ y₁} = IsEquivalence.sym B.equiv

    trans≈ : {x y : C} → Transitive (mk≈ {x} {y})
    trans≈ {inj₁ _} {inj₁ _} = IsEquivalence.trans A.equiv
    trans≈ {inj₁ _} {inj₂ _} {()}
    trans≈ {inj₂ _} {inj₁ _} {()}
    trans≈ {inj₂ _} {inj₂ _} = IsEquivalence.trans B.equiv

    equiv≈ : {x y : C} → IsEquivalence (mk≈ {x} {y})
    equiv≈ {x} = record { refl = refl≈ {x}; sym = sym≈ {x}; trans = trans≈ {x} }

    resp : {x y z : C} {f h : y ⇛ z} {g i : x ⇛ y} → 
           mk≈ {y} f h → mk≈ {x} g i → mk≈ {x} (_∙G_ {x} f g) (_∙G_ {x} h i)
    resp {inj₁ _} {inj₁ _} {inj₁ _} = A.∘-resp-≈
    resp {inj₁ _} {inj₁ _} {inj₂ _} {()}
    resp {inj₁ _} {inj₂ _} {_} {_} {_} {()}
    resp {inj₂ _} {inj₁ _} {_} {_} {_} {()}
    resp {inj₂ _} {inj₂ _} {inj₁ _} {()}
    resp {inj₂ _} {inj₂ _} {inj₂ _} = B.∘-resp-≈

_×G_ : 1Groupoid → 1Groupoid → 1Groupoid
A ×G B = record 
  { set = A.set × B.set
  ; _↝_ =  liftG A._↝_ B._↝_
  ; _≈_ = liftG A._≈_ B._≈_
  ; id = A.id , B.id
  ; _∘_ = liftOp2 {Z₁ = A._↝_} {B._↝_} A._∘_ B._∘_
  ; _⁻¹ = λ x₁ → A._⁻¹ (proj₁ x₁) , B._⁻¹ (proj₂ x₁)
  ; lneutr = λ α → A.lneutr (proj₁ α) , B.lneutr (proj₂ α)
  ; rneutr = λ α → A.rneutr (proj₁ α) , B.rneutr (proj₂ α)
  ; assoc = λ α β δ → A.assoc (proj₁ α) (proj₁ β) (proj₁ δ) , B.assoc (proj₂ α) (proj₂ β) (proj₂ δ)
  ; equiv = λ {x} {y} → let module W = IsEquivalence (A.equiv {proj₁ x} {proj₁ y}) 
                            module Z = IsEquivalence (B.equiv {proj₂ x} {proj₂ y}) in
            record { refl = W.refl , Z.refl
                   ; sym = λ i≈j → W.sym (proj₁ i≈j) , Z.sym (proj₂ i≈j)
                   ; trans = λ i≈j j≈k → (W.trans (proj₁ i≈j) (proj₁ j≈k)) , 
                                        ((Z.trans (proj₂ i≈j) (proj₂ j≈k))) }
  ; linv = λ α → A.linv (proj₁ α) , B.linv (proj₂ α)
  ; rinv = λ α → A.rinv (proj₁ α) , B.rinv (proj₂ α)
  ; ∘-resp-≈ = λ x₁ x₂ → (A.∘-resp-≈ (proj₁ x₁) (proj₁ x₂)) , B.∘-resp-≈ (proj₂ x₁) (proj₂ x₂) }
  where
    module A = 1Groupoid A
    module B = 1Groupoid B
    C : Set
    C = A.set × B.set

    liftG : {X Y : Set} → Rel0 X → Rel0 Y → X × Y → X × Y → Set
    liftG F G =  λ x y → F (proj₁ x) (proj₁ y) × G (proj₂ x) (proj₂ y)

    liftOp2 : {A₁ A₂ : Set} {x y z : A₁ × A₂} {Z₁ : Rel0 A₁} {Z₂ : Rel0 A₂} →
             let _⇛_ = liftG Z₁ Z₂ in
             let _↝₁_ : (a b : A₁ × A₂) → Set
                 _↝₁_ = λ a b → Z₁ (proj₁ a) (proj₁ b)
                 _↝₂_ : (a b : A₁ × A₂) → Set
                 _↝₂_ = λ a b → Z₂ (proj₂ a) (proj₂ b) in
                   (y ↝₁ z → x ↝₁ y → x ↝₁ z) → (y ↝₂ z → x ↝₂ y → x ↝₂ z) 
                → y ⇛ z → x ⇛ y → x ⇛ z
    liftOp2 F G = λ x y → F (proj₁ x) (proj₁ y) , G (proj₂ x) (proj₂ y)

-- Discrete paths.  Essentially ≡.
data DPath {A : Set} (x : A) : A → Set where
  reflD : DPath x x

transD : {A : Set} {x y z : A} → DPath y z → DPath x y → DPath x z
transD reflD reflD = reflD

symD : {A : Set} {x y : A} → DPath x y → DPath y x
symD reflD = reflD

lidD : {A : Set} {x y : A} (α : DPath x y) → DPath (transD reflD α) α
lidD reflD = reflD

ridD : {A : Set} {x y : A} (α : DPath x y) → DPath (transD α reflD) α
ridD reflD = reflD

assocD : {A : Set} {w x y z : A} (α : DPath y z) (β : DPath x y) (δ : DPath w x) → DPath (transD (transD α β) δ) (transD α (transD β δ))
assocD reflD reflD reflD = reflD

linvD : {A : Set} {x y : A} (α : DPath x y) → DPath (transD (symD α) α) reflD
linvD reflD = reflD

rinvD : {A : Set} {x y : A} (α : DPath x y) → DPath (transD α (symD α)) reflD
rinvD reflD = reflD

equivD : {A : Set} {x y : A} → IsEquivalence {_} {_} {DPath x y} DPath
equivD = λ {A} {x} {y} → record 
  { refl = reflD
  ; sym = symD
  ; trans = flip transD }

respD : {A : Set} {x y z : A} {f h : DPath y z} {g i : DPath x y} → 
    DPath f h → DPath g i → DPath (transD f g) (transD h i)
respD reflD reflD = reflD

discrete : Set → 1Groupoid
discrete a =  record
    { set = a
    ; _↝_ = DPath
    ; _≈_ = DPath -- or could use _≡_ .
    ; id = reflD
    ; _∘_ = transD
    ; _⁻¹ = symD
    ; lneutr = lidD
    ; rneutr = ridD
    ; assoc = assocD
    ; linv = linvD
    ; rinv = rinvD
    ; equiv = equivD 
    ;  ∘-resp-≈ = respD }
