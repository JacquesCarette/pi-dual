{-# OPTIONS --without-K #-}

module HP where

-- Pi as a higher-order inductive type

open import Agda.Prim
open import Data.Product
open import Function renaming (_∘_ to _○_)

infixr 8  _∘_   -- path composition
infix  4  _≡_   -- propositional equality
infix  4  _∼_   -- homotopy between two functions 
infix  4  _≃_   -- type of equivalences
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

------------------------------------------------------------------------------
-- Identity types

-- Our own version of refl that makes 'a' explicit

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

pathInd : ∀ {u ℓ} → {A : Set u} → 
          (C : {x y : A} → x ≡ y → Set ℓ) → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

------------------------------------------------------------------------------
-- Ch. 2

-- Lemma 2.1.1

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

-- Lemma 2.1.2

_∘_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {u} {A} {x} {y} {z} p q = 
  pathInd 
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

-- Lemma 2.1.4

-- p = p . refl

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y) 
unitTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ p ∘ (refl y)) 
    (λ x → refl (refl x))
    {x} {y} p 

-- p = refl . p

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p 

-- ! p . p = refl

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ! p ∘ p ≡ refl y)
    (λ x → refl (refl x))
    {x} {y} p

-- p . ! p = refl

invTransR : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (p ∘ ! p ≡ refl x)
invTransR {ℓ} {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ∘ ! p ≡ refl x)
    (λ x → refl (refl x))
    {x} {y} p

-- ! (! p) = p

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd 
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- p . (q . r) = (p . q) . r

assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP {A} {x} {y} {z} {w} p q r =
  pathInd
    (λ {x} {y} p → (z : A) → (w : A) → (q : y ≡ z) → (r : z ≡ w) → 
      p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
    (λ x z w q r → 
      pathInd
        (λ {x} {z} q → (w : A) → (r : z ≡ w) → 
          (refl x) ∘ (q ∘ r) ≡ ((refl x) ∘ q) ∘ r)
        (λ x w r → 
          pathInd
            (λ {x} {w} r → 
              (refl x) ∘ ((refl x) ∘ r) ≡ 
              ((refl x) ∘ (refl x)) ∘ r)
            (λ x → (refl (refl x)))
            {x} {w} r)
        {x} {z} q w r)
    {x} {y} p z w q r

-- ! (p ∘ q) ≡ ! q ∘ ! p

invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → 
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp {A} {x} {y} {z} p q = 
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p)
    (λ x z q → 
      pathInd 
        (λ {x} {z} q → ! (refl x ∘ q) ≡ ! q ∘ ! (refl x))
        (λ x → refl (refl x)) 
        {x} {z} q)
    {x} {y} p z q

-- Introduce equational reasoning syntax to simplify proofs

_≡⟨_⟩_ : ∀ {u} → {A : Set u} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p ⟩ q = p ∘ q

bydef : ∀ {u} → {A : Set u} {x : A} → (x ≡ x)
bydef {u} {A} {x} = refl x

_∎ : ∀ {u} → {A : Set u} (x : A) → x ≡ x
_∎ x = refl x

------------------------------------------------------------------------------
-- Functions are functors

-- Lemma 2.2.1
-- computation rule: ap f (refl x) = refl (f x)

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

-- Lemma 2.2.2

-- f (p ∘ q) ≡ f p ∘ f q

apfTrans : ∀ {u} → {A B : Set u} {x y z : A} → 
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans {u} {A} {B} {x} {y} {z} f p q = 
  pathInd {u}
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → 
      ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q))
    (λ x z q → 
      pathInd {u}
        (λ {x} {z} q → 
          ap f (refl x ∘ q) ≡ (ap f (refl x)) ∘ (ap f q))
        (λ x → refl (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

-- f (! p) ≡ ! (f p)

apfInv : ∀ {u} → {A B : Set u} {x y : A} → (f : A → B) → (p : x ≡ y) → 
         ap f (! p) ≡ ! (ap f p) 
apfInv {u} {A} {B} {x} {y} f p =
  pathInd {u}
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    {x} {y} p

-- g (f p) ≡ (g ○ f) p

apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ○ f) p 
apfComp {A} {B} {C} {x} {y} f g p =
  pathInd 
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ○ f) p)
    (λ x → refl (ap g (ap f (refl x))))
    {x} {y} p

-- id p ≡ p

apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ap id p ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- Transport

-- Lemma 2.3.1

transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} → 
  (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} {x} {y} P p = 
  pathInd 
    (λ {x} {y} p → (P x → P y))
    (λ _ → id)
    {x} {y} p

-------------------------------------------------------------------------------
-- Homotopies and equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (_⊔_ ℓ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

-- Quasi-inverses

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (_⊔_ ℓ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

-- Example 2.4.7

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {ℓ} {ℓ} {A} {A} id
idqinv = record {
           g = id ;
           α = λ b → refl b ; 
           β = λ a → refl a
         } 

-- Equivalences

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (_⊔_ ℓ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ
       
_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (_⊔_ ℓ ℓ')
A ≃ B = Σ (A → B) isequiv

-- Lemma 2.4.12

idequiv : ∀ {ℓ} {A : Set ℓ} → A ≃ A
idequiv = (id , equiv₁ idqinv)

------------------------------------------------------------------------------
-- Sec. 2.11: Identity types

-- Thm 2.11.3

transportId : {A B : Set} {y z : A} → (f g : A → B) → 
  (p : y ≡ z) → (q : f y ≡ g y) → 
  transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ q ∘ (ap g p)
transportId {A} {B} {y} {z} f g p q = 
  pathInd 
    (λ {y} {z} p → (q : f y ≡ g y) → 
      transport (λ x → f x ≡ g x) p q ≡ ! (ap f p) ∘ q ∘ (ap g p))
    (λ y q → q 
               ≡⟨ unitTransR q ⟩
             q ∘ refl (g y)
               ≡⟨ unitTransL (q ∘ refl (g y)) ⟩
             refl (f y) ∘ q ∘ refl (g y) ∎)
    {y} {z} p q 

------------------------------------------------------------------------------
-- Pi as a higher-order inductive type

module PI where
  private 
    data FT* : Set where
      ZERO*  : FT*
      ONE*   : FT*
      PLUS*  : FT* → FT* → FT*
      TIMES* : FT* → FT* → FT*

  FT : Set
  FT = FT*

  ZERO : FT
  ZERO = ZERO*

  ONE : FT
  ONE = ZERO*

  PLUS : FT → FT → FT
  PLUS = PLUS*

  TIMES : FT → FT → FT
  TIMES = TIMES*

  postulate 
    -- additive structure
    unite₊≡  : { b : FT } → PLUS ZERO b ≡ b
    uniti₊≡  : { b : FT } → b ≡ PLUS ZERO b
    swap₊≡   : { b₁ b₂ : FT } → PLUS b₁ b₂ ≡ PLUS b₂ b₁
    assocl₊≡ : { b₁ b₂ b₃ : FT } → PLUS b₁ (PLUS b₂ b₃) ≡ PLUS (PLUS b₁ b₂) b₃
    assocr₊≡ : { b₁ b₂ b₃ : FT } → PLUS (PLUS b₁ b₂) b₃ ≡ PLUS b₁ (PLUS b₂ b₃)
    -- multiplicative structure
    unite⋆≡  : { b : FT } → TIMES ONE b ≡ b
    uniti⋆≡  : { b : FT } → b ≡ TIMES ONE b
    swap⋆≡   : { b₁ b₂ : FT } → TIMES b₁ b₂ ≡ TIMES b₂ b₁
    assocl⋆≡ : { b₁ b₂ b₃ : FT } → 
               TIMES b₁ (TIMES b₂ b₃) ≡ TIMES (TIMES b₁ b₂) b₃
    assocr⋆≡ : { b₁ b₂ b₃ : FT } → 
               TIMES (TIMES b₁ b₂) b₃ ≡ TIMES b₁ (TIMES b₂ b₃)
    -- distributivity
    distz≡   : { b : FT } → TIMES ZERO b ≡ ZERO
    factorz≡ : { b : FT } → ZERO ≡ TIMES ZERO b
    dist≡    : { b₁ b₂ b₃ : FT } → 
              TIMES (PLUS b₁ b₂) b₃ ≡ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
    factor≡  : { b₁ b₂ b₃ : FT } → 
              PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ≡ TIMES (PLUS b₁ b₂) b₃
    -- congruence is provable

  recPI : {C : Set} → 
    (czero : C) → 
    (cone : C) → 
    (cplus : C → C → C) → 
    (ctimes : C → C → C) →
    (cunite₊≡ : { b : C } → cplus czero b ≡ b) →
    (cuniti₊≡ : { b : C } → b ≡ cplus czero b) →
    (cswap₊≡ : { b₁ b₂ : C } → cplus b₁ b₂ ≡ cplus b₂ b₁) →
    (cassocl₊≡ : { b₁ b₂ b₃ : C } → cplus b₁ (cplus b₂ b₃) ≡ cplus (cplus b₁ b₂) b₃) →
    (cassocr₊≡ : { b₁ b₂ b₃ : C } → cplus (cplus b₁ b₂) b₃ ≡ cplus b₁ (cplus b₂ b₃)) →
    (cunite⋆≡  : { b : C } → ctimes cone b ≡ b) →
    (cuniti⋆≡  : { b : C } → b ≡ ctimes cone b) →
    (cswap⋆≡   : { b₁ b₂ : C } → ctimes b₁ b₂ ≡ ctimes b₂ b₁) →
    (cassocl⋆≡ : { b₁ b₂ b₃ : C } → 
               ctimes b₁ (ctimes b₂ b₃) ≡ ctimes (ctimes b₁ b₂) b₃) →
    (cassocr⋆≡ : { b₁ b₂ b₃ : C } → 
               ctimes (ctimes b₁ b₂) b₃ ≡ ctimes b₁ (ctimes b₂ b₃)) →
    (cdistz≡   : { b : C } → ctimes czero b ≡ czero) →
    (cfactorz≡ : { b : C } → czero ≡ ctimes czero b) →
    (cdist≡ : { b₁ b₂ b₃ : C } → 
              ctimes (cplus b₁ b₂) b₃ ≡ cplus (ctimes b₁ b₃) (ctimes b₂ b₃)) →
    (cfactor≡  : { b₁ b₂ b₃ : C } → 
              cplus (ctimes b₁ b₃) (ctimes b₂ b₃) ≡ ctimes (cplus b₁ b₂) b₃) →
    FT → C
  recPI {C} czero cone cplus ctimes _ _ _ _ _ _ _ _ _ _ _ _ _ _ ZERO* = czero
  recPI {C} czero cone cplus ctimes _ _ _ _ _ _ _ _ _ _ _ _ _ _ ONE* = cone
  recPI {C} czero cone cplus ctimes 
    cunite₊≡ cuniti₊≡ cswap₊≡ cassocl₊≡ cassocr₊≡
    cunite⋆≡ cuniti⋆≡ cswap⋆≡ cassocl⋆≡ cassocr⋆≡
    cdistz≡ cfactorz≡ cdist≡ cfactor≡ 
    (PLUS* B₁ B₂) = 
    cplus 
      (recPI {C} czero cone cplus ctimes 
         cunite₊≡ cuniti₊≡ cswap₊≡ cassocl₊≡ cassocr₊≡
         cunite⋆≡ cuniti⋆≡ cswap⋆≡ cassocl⋆≡ cassocr⋆≡
        cdistz≡ cfactorz≡ cdist≡ cfactor≡ B₁)
      (recPI {C} czero cone cplus ctimes 
         cunite₊≡ cuniti₊≡ cswap₊≡ cassocl₊≡ cassocr₊≡
         cunite⋆≡ cuniti⋆≡ cswap⋆≡ cassocl⋆≡ cassocr⋆≡
        cdistz≡ cfactorz≡ cdist≡ cfactor≡ B₂)
  recPI {C} czero cone cplus ctimes 
    cunite₊≡ cuniti₊≡ cswap₊≡ cassocl₊≡ cassocr₊≡
    cunite⋆≡ cuniti⋆≡ cswap⋆≡ cassocl⋆≡ cassocr⋆≡
    cdistz≡ cfactorz≡ cdist≡ cfactor≡ 
    (TIMES* B₁ B₂) = 
    ctimes 
      (recPI {C} czero cone cplus ctimes 
         cunite₊≡ cuniti₊≡ cswap₊≡ cassocl₊≡ cassocr₊≡
         cunite⋆≡ cuniti⋆≡ cswap⋆≡ cassocl⋆≡ cassocr⋆≡
        cdistz≡ cfactorz≡ cdist≡ cfactor≡ B₁)
      (recPI {C} czero cone cplus ctimes 
         cunite₊≡ cuniti₊≡ cswap₊≡ cassocl₊≡ cassocr₊≡
         cunite⋆≡ cuniti⋆≡ cswap⋆≡ cassocl⋆≡ cassocr⋆≡
        cdistz≡ cfactorz≡ cdist≡ cfactor≡ B₂)

{--

  recS¹ cbase cloop base* = cbase

  postulate
    βrecS¹ : {C : Set} → (cbase : C) → (cloop : cbase ≡ cbase) → 
      ap (recS¹ cbase cloop) loop ≡ cloop
 
  indS¹ : {C : S¹ → Set} → 
    (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
    (circle : S¹) → C circle
  indS¹ cbase cloop base* = cbase
--}

open PI public

{--
fcircle : S¹ → S¹'
fcircle = recS¹ south (east ∘ ! west)

floop : ap fcircle loop ≡ (east ∘ ! west)
floop = βrecS¹ south (east ∘ ! west)

gcircle : S¹' → S¹
gcircle = recS¹' base base loop (refl base)

geast : ap gcircle east ≡ loop
geast = βreceastS¹' base base loop (refl base)

gwest : ap gcircle west ≡ (refl base)
gwest = βrecwestS¹' base base loop (refl base)

gf : S¹ → S¹
gf = gcircle ○ fcircle

gfloop : ap gf loop ≡ loop
gfloop = ap gf loop
           ≡⟨ ! (apfComp fcircle gcircle loop) ⟩ 
         ap gcircle (ap fcircle loop)
           ≡⟨ ap (ap gcircle) floop ⟩
         ap gcircle (east ∘ ! west)
           ≡⟨ apfTrans gcircle east (! west) ⟩
         ap gcircle east ∘ ap gcircle (! west) 
           ≡⟨ ap (λ x → ap gcircle east ∘ x) (apfInv gcircle west) ⟩
         ap gcircle east ∘ ! (ap gcircle west)
           ≡⟨ ap (λ x → ap gcircle east ∘ ! x) gwest ⟩
         ap gcircle east ∘ (refl base)
           ≡⟨ ! (unitTransR (ap gcircle east)) ⟩ 
         ap gcircle east
           ≡⟨ geast ⟩ 
         loop ∎

αloop : transport (λ x → gf x ≡ x) loop (refl base) ≡ refl base
αloop = transport (λ x → gf x ≡ x) loop (refl base) 
          ≡⟨ transportId gf id loop (refl base) ⟩ -- Thm 2.11.3
        ! (ap gf loop) ∘ refl base ∘ ap id loop
          ≡⟨ ap (λ x → ! (ap gf loop) ∘ refl base ∘ x) (apfId loop) ⟩
        ! (ap gf loop) ∘ refl base ∘ loop
          ≡⟨ ap (λ x → ! (ap gf loop) ∘ x) (! (unitTransL loop)) ⟩ 
        ! (ap gf loop) ∘ loop
          ≡⟨ ap (λ x → ! x ∘ loop) gfloop ⟩ 
        ! loop ∘ loop
          ≡⟨ invTransL loop ⟩ 
        refl base ∎

βcircle : gf ∼ id
βcircle = 
  indS¹ {λ x → gf x ≡ x}
    (refl base)  
    αloop

fg : S¹' → S¹'
fg = fcircle ○ gcircle

fgeast : ap fg east ≡ east ∘ ! west
fgeast = ap fg east 
           ≡⟨ ! (apfComp gcircle fcircle east) ⟩
         ap fcircle (ap gcircle east)
           ≡⟨ ap (ap fcircle) geast ⟩
         ap fcircle loop
           ≡⟨ floop ⟩
         (east ∘ ! west) ∎

fgwest : ap fg west ≡ refl south
fgwest = ap fg west
           ≡⟨ ! (apfComp gcircle fcircle west) ⟩ 
         ap fcircle (ap gcircle west) 
           ≡⟨ ap (ap fcircle) gwest ⟩
         ap fcircle (refl base)
           ≡⟨ bydef ⟩
         refl south ∎

αeast : transport (λ x → fg x ≡ x) east (refl south) ≡ west
αeast = transport (λ x → fg x ≡ x) east (refl south) 
          ≡⟨ transportId fg id east (refl south) ⟩ -- Thm 2.11.3
        ! (ap fg east) ∘ refl south ∘ ap id east
          ≡⟨ ap (λ x → ! (ap fg east) ∘ refl south ∘ x) (apfId east) ⟩
        ! (ap fg east) ∘ refl south ∘ east
           ≡⟨ ap (λ x → ! (ap fg east) ∘ x) (! (unitTransL east)) ⟩
        ! (ap fg east) ∘ east
           ≡⟨ ap (λ x → ! x ∘ east) fgeast ⟩
        ! (east ∘ ! west) ∘ east
          ≡⟨ ap (λ x → x ∘ east) (invComp east (! west)) ⟩
        (! (! west) ∘ ! east) ∘ east
          ≡⟨ ! (assocP (! (! west)) (! east) east) ⟩ 
        ! (! west) ∘ ! east ∘ east
          ≡⟨ ap (λ x → ! (! west) ∘ x) (invTransL east) ⟩
        ! (! west) ∘ refl north
          ≡⟨ ! (unitTransR (! (! west)))  ⟩
        ! (! west)
          ≡⟨ invId west ⟩
        west ∎

αwest : transport (λ x → fg x ≡ x) west (refl south) ≡ west
αwest = transport (λ x → fg x ≡ x) west (refl south) 
          ≡⟨ transportId fg id west (refl south) ⟩ -- Thm 2.11.3
        ! (ap fg west) ∘ refl south ∘ ap id west
          ≡⟨ ap (λ x → ! (ap fg west) ∘ refl south ∘ x) (apfId west) ⟩
        ! (ap fg west) ∘ refl south ∘ west
           ≡⟨ ap (λ x → ! (ap fg west) ∘ x) (! (unitTransL west)) ⟩
        ! (ap fg west) ∘ west
           ≡⟨ ap (λ x → ! x ∘ west) fgwest ⟩
        ! (refl south) ∘ west
          ≡⟨ ! (unitTransL west) ⟩
        west ∎

αcircle : fg ∼ id
αcircle = 
  indS¹' {λ x → fg x ≡ x}
    (refl south) west
    αeast
    αwest

sequiv : S¹ ≃ S¹'
sequiv = (fcircle , equiv₁ (mkqinv gcircle αcircle βcircle))
--}
------------------------------------------------------------------------------
-- Sec. 2.10: Universes; univalence

idtoeqv : {A B : Set} → (A ≡ B) → (A ≃ B)
idtoeqv {A} {B} p = 
  pathInd 
    (λ {A} {B} p → A ≃ B)
    (λ A → idequiv)
    {A} {B} p

postulate 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

------------------------------------------------------------------------------
