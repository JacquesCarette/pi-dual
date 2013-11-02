{-# OPTIONS --without-K #-}

module F1b where

open import Level
open import Data.Unit
open import Data.Sum hiding (map; [_,_])
open import Data.Product hiding (map; ,_)
open import Data.List hiding ([_])
open import Function using (flip)
open import Relation.Binary.Core using (IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary

open import Groupoid

{--
infixr 90 _⊗_
infixr 80 _⊕_
infixr 60 _∘_
infix  30 _⟷_
--}

---------------------------------------------------------------------------
-- Paths

-- Path relation should be an equivalence 
data Path {A : Set} : A → A → Set where
  _⇛_ : (x : A) → (y : A) → Path x y

data _≣⇛_ {A : Set} {a b : A} (x : Path a b) : Path a b → Set where
  refl⇛ : x ≣⇛ x

id⇛ : {A : Set} → (a : A) → Path a a
id⇛ a = a ⇛ a

ap : {A B : Set} → (f : A → B) → {a a' : A} → Path a a' → Path (f a) (f a')
ap f (a ⇛ a') = (f a) ⇛ (f a')

_∙⇛_ : {A : Set} {a b c : A} → Path b c → Path a b → Path a c
(b ⇛ c) ∙⇛ (a ⇛ .b) = a ⇛ c

_⇚ : {A : Set} {a b : A} → Path a b → Path b a
(x ⇛ y) ⇚ = y ⇛ x

lid⇛ : {A : Set} {x y : A} (α : Path x y) → (id⇛ y ∙⇛ α) ≣⇛ α
lid⇛ (x ⇛ y) = refl⇛

rid⇛ : {A : Set} {x y : A} (α : Path x y) → (α ∙⇛ id⇛ x) ≣⇛ α
rid⇛ (x ⇛ y) = refl⇛

assoc⇛ : {A : Set} {w x y z : A} (α : Path y z) (β : Path x y) (δ : Path w x) → ((α ∙⇛ β) ∙⇛ δ) ≣⇛ (α ∙⇛ (β ∙⇛ δ))
assoc⇛ (y ⇛ z) (x ⇛ .y) (w ⇛ .x) = refl⇛

l⇚ : {A : Set}  {x y : A} (α : Path x y) → ((α ⇚) ∙⇛ α) ≣⇛ id⇛ x
l⇚ (x ⇛ y) = refl⇛

r⇚ : {A : Set} {x y : A} (α : Path x y) → (α ∙⇛ (α ⇚)) ≣⇛ id⇛ y
r⇚ (x ⇛ y) = refl⇛

sym⇛ : {A : Set} {x y : A} {α β : Path x y} → α ≣⇛ β → β ≣⇛ α
sym⇛ refl⇛ = refl⇛

trans⇛ : {A : Set} {x y : A} {α β δ : Path x y} → α ≣⇛ β → β ≣⇛ δ → α ≣⇛ δ
trans⇛ refl⇛ refl⇛ = refl⇛
 
equiv≣⇛ : {A : Set} {x y : A} → IsEquivalence {_} {_} {Path x y} (_≣⇛_)
equiv≣⇛ = record { refl = refl⇛; sym = sym⇛; trans = trans⇛ }

resp≣⇛ : {A : Set} {x y z : A} {f h : Path y z} {g i : Path x y} →
  f ≣⇛ h → g ≣⇛ i → (f ∙⇛ g) ≣⇛ (h ∙⇛ i)
resp≣⇛ refl⇛ refl⇛ = refl⇛

pathProd : {A B : Set} {a a' : A} {b b' : B} → Path a a' → Path b b' → Path (a , b) (a' , b')
pathProd (a ⇛ b) (a' ⇛ b') = (a , a') ⇛ (b , b')

prod : {X Y Z : Set} → (X → Y → Z) → List X → List Y → List Z
prod f l₁ l₂ = concatMap (λ b → map (f b) l₂) l₁

_×↝_ : {A B : Set} {a a' : A} {b b' : B} → List (Path a a') → List (Path b b') → List (Path (a , b) (a' , b'))
_×↝_ = prod pathProd

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

-- pi types with exactly one level of reciprocals

data B0 : Set where
  ONE    : B0
  PLUS0  : B0 → B0 → B0
  TIMES0 : B0 → B0 → B0

data B1 : Set where
  LIFT0  : B0 → B1
  PLUS1  : B1 → B1 → B1
  TIMES1 : B1 → B1 → B1
  RECIP1 : B0 → B1

-- interpretation of B0 as discrete groupoids

record 0-type : Set₁ where
  constructor G₀
  field
    ∣_∣₀ : Set

open 0-type public

plus : 0-type → 0-type → 0-type
plus t₁ t₂ = G₀ (∣ t₁ ∣₀ ⊎ ∣ t₂ ∣₀) 

times : 0-type → 0-type → 0-type
times t₁ t₂ = G₀ (∣ t₁ ∣₀ × ∣ t₂ ∣₀)

⟦_⟧₀ : B0 → 0-type
⟦ ONE ⟧₀ = G₀ ⊤ 
⟦ PLUS0 b₁ b₂ ⟧₀ = plus ⟦ b₁ ⟧₀ ⟦ b₂ ⟧₀
⟦ TIMES0 b₁ b₂ ⟧₀ = times ⟦ b₁ ⟧₀ ⟦ b₂ ⟧₀

ı₀ : B0 → Set
ı₀ b = ∣ ⟦ b ⟧₀ ∣₀ 

elems0 : (b : B0) → List (ı₀ b)
elems0 ONE = tt ∷ []
elems0 (PLUS0 b b') = map inj₁ (elems0 b) ++ map inj₂ (elems0 b')
elems0 (TIMES0 b b') = 
--  concatMap (λ a → map (λ b → (a , b)) (elems0 b')) (elems0 b)
    prod _,_ (elems0 b) (elems0 b')

point : (b : B0) → ı₀ b
point ONE = tt
point (PLUS0 b _) = inj₁ (point b)
point (TIMES0 b₀ b₁) = point b₀ , point b₁ 

-- interpretation of B1 types as 1-groupoids
open 1Groupoid

_⊎↝_ : {A B : Set} {a a' : A} {b b' : B} → List (Path a a') → List (Path b b') → List (Path a a' ⊎ Path b b')
p₁ ⊎↝ p₂ = map (inj₁) p₁ ++ map (inj₂) p₂

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
    ;  ∘-resp-≈ = respD}

allPaths : Set → 1Groupoid
allPaths a =  record
    { set = a
    ; _↝_ = Path
    ; _≈_ = _≣⇛_
    ; id = λ {x} → id⇛ x
    ; _∘_ = _∙⇛_
    ; _⁻¹ = _⇚
    ; lneutr = lid⇛
    ; rneutr = rid⇛
    ; assoc = assoc⇛
    ; linv = l⇚
    ; rinv = r⇚
    ; equiv = equiv≣⇛ 
    ;  ∘-resp-≈ = resp≣⇛}

⟦_⟧₁ : B1 → 1Groupoid
⟦ LIFT0 b0 ⟧₁ = discrete (ı₀ b0) 
⟦ PLUS1 b₁ b₂ ⟧₁ = ⟦ b₁ ⟧₁ ⊎G ⟦ b₂ ⟧₁
⟦ TIMES1 b₁ b₂ ⟧₁ =  ⟦ b₁ ⟧₁ ×G ⟦ b₂ ⟧₁
⟦ RECIP1 b0 ⟧₁ = allPaths (ı₀ b0)

ı₁ : B1 → Set
ı₁ b = set ⟦ b ⟧₁

test10 = ⟦ LIFT0 ONE ⟧₁
test11 = ⟦ LIFT0 (PLUS0 ONE ONE) ⟧₁
test12 = ⟦ RECIP1 (PLUS0 ONE ONE) ⟧₁

-- isos

data _⟷_ : B1 → B1 → Set where
  -- + 
  swap₊   : { b₁ b₂ : B1 } → PLUS1 b₁ b₂ ⟷ PLUS1 b₂ b₁
  -- *
  unite⋆  : { b : B1 } → TIMES1 (LIFT0 ONE) b ⟷ b
  uniti⋆  : { b : B1 } → b ⟷ TIMES1 (LIFT0 ONE) b
{-  assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
  swap⋆   : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
  -- * distributes over + 
  dist    : { b₁ b₂ b₃ : B } → 
            TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor  : { b₁ b₂ b₃ : B } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
  -- congruence
  id⟷   : { b : B } → b ⟷ b
  sym    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
  _∘_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)

  η⋆ : (b : B0) → LIFT0 ONE ⟷ TIMES1 (LIFT0 b) (RECIP1 b)
  ε⋆ : (b : B0) → TIMES1 (LIFT0 b) (RECIP1 b) ⟷ LIFT0 ONE
-}
-- interpret isos as functors

record 1-functor (A B : 1Groupoid) : Set where
  constructor 1F
  private module A = 1Groupoid A
  private module B = 1Groupoid B

  field
    F₀ : set A → set B
    F₁ : ∀ {X Y : set A} → A [ X , Y ] → B [ F₀ X , F₀ Y ]

open 1-functor public

ipath : (b : B1) → ı₁ b → ı₁ b → Set
ipath b x y = Path {ı₁ b} x y

swap⊎ : {A B : Set} → A ⊎ B → B ⊎ A
swap⊎ (inj₁ a) = inj₂ a
swap⊎ (inj₂ b) = inj₁ b

intro1⋆ : {b : B1} {x y : ı₁ b} → ipath b x y → ipath (TIMES1 (LIFT0 ONE) b) (tt , x) (tt , y)
intro1⋆ (y ⇛ z) = (tt , y) ⇛ (tt , z)

objη⋆ : (b : B0) → ı₁ (LIFT0 ONE) → ı₁ (TIMES1 (LIFT0 b) (RECIP1 b))
objη⋆ b tt = point b , point b

objε⋆ : (b : B0) → ı₁ (TIMES1 (LIFT0 b) (RECIP1 b)) → ı₁ (LIFT0 ONE)
objε⋆ b (x , y) = tt

elim1∣₁ : (b : B1) → ı₁ (TIMES1 (LIFT0 ONE) b) → ı₁ b
elim1∣₁ b (tt , x) = x

intro1∣₁ : (b : B1) → ı₁ b → ı₁ (TIMES1 (LIFT0 ONE) b)
intro1∣₁ b x = (tt , x)


swapF : {b₁ b₂ : B1} →
      let G = ⟦ b₁ ⟧₁ ⊎G ⟦ b₂ ⟧₁
          G' = ⟦ b₂ ⟧₁ ⊎G ⟦ b₁ ⟧₁ in
      {X Y : set G} → G [ X , Y ] → G' [ swap⊎ X , swap⊎ Y ]
swapF {X = inj₁ _} {inj₁ _} f = f
swapF {X = inj₁ _} {inj₂ _} ()
swapF {X = inj₂ _} {inj₁ _} ()
swapF {X = inj₂ _} {inj₂ _} f = f

{-
eta : (b : B0) → List (ipath (LIFT0 ONE)) → List (ipath (TIMES1 (LIFT0 b) (RECIP1 b)))
-- note how the input list is not used at all!
eta b _ = prod (λ a a' → _↝_ (a , tt) (a' , tt)) (elems0 b) (elems0 b)

eps : (b : B0) → ipath (TIMES1 (LIFT0 b) (RECIP1 b)) → ipath (LIFT0 ONE)
eps b0 (a ⇛ b) = tt ⇛ tt
-}

mutual
  eval : {b₁ b₂ : B1} → (b₁ ⟷ b₂) → 1-functor ⟦ b₁ ⟧₁ ⟦ b₂ ⟧₁
  eval (swap₊ {b₁} {b₂}) = 1F swap⊎ (λ {X Y} → swapF {b₁} {b₂} {X} {Y})
  eval (unite⋆ {b}) = 1F (elim1∣₁ b) {!!} -- (map (elim1⋆ {b}))
  eval (uniti⋆ {b}) = 1F (intro1∣₁ b) {!!} -- (map (intro1⋆ {b}))
--  eval (η⋆ b) = F₁ (objη⋆ b) (eta b )
--  eval (ε⋆ b) = F₁ (objε⋆ b) (map (eps b))

  evalB : {b₁ b₂ : B1} → (b₁ ⟷ b₂) → 1-functor ⟦ b₂ ⟧₁ ⟦ b₁ ⟧₁
  evalB (swap₊ {b₁} {b₂}) = 1F swap⊎ ((λ {X Y} → swapF {b₂} {b₁} {X} {Y}))
  evalB (unite⋆ {b}) = 1F (intro1∣₁ b) {!!} -- (map (intro1⋆ {b}))
  evalB (uniti⋆ {b}) = 1F (elim1∣₁ b) {!!} -- (map (elim1⋆ {b}))
--  evalB (η⋆ b) = F₁ (objε⋆ b) (map (eps b))
--  evalB (ε⋆ b) = F₁ (objη⋆ b) (eta b)

{- eval assocl₊ = ? -- : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
eval assocr₊ = ? -- : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
eval uniti⋆ = ? -- : { b : B } → b ⟷ TIMES ONE b
eval swap⋆ = ? --  : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
eval assocl⋆ = ? -- : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
eval assocr⋆ = ? -- : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
eval dist = ? -- : { b₁ b₂ b₃ : B } → TIMES (PLUS b₁ b₂) b₃ ⟷ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
eval factor = ? -- : { b₁ b₂ b₃ : B } → PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷ TIMES (PLUS b₁ b₂) b₃
eval id⟷ = ? --  : { b : B } → b ⟷ b
eval (sym c) = ? -- : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
eval (c₁ ∘ c₂) = ? -- : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
eval (c₁ ⊕ c₂) = ? -- : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
eval (c₁ ⊗ c₂) = ? -- : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)

---------------------------------------------------------------------------
--}

{-
lneutr≡ : {a : Set} {x y : a} (α : x ≡ y) → trans α refl ≡ α
lneutr≡ refl = refl

rneutr≡ : {b : Set} {x y : b} (α : x ≡ y) → trans refl α ≡ α
rneutr≡ refl = refl

assoc≡ : {b : Set} {w x y z : b} (α : y ≡ z) (β : x ≡ y) (δ : w ≡ x) →
    trans δ (trans β α) ≡ trans (trans δ β) α
assoc≡ refl refl refl = refl

linv≡ : {a : Set} {x y : a} (α : x ≡ y) → trans α (sym α) ≡ refl
linv≡ refl = refl

rinv≡ : {b : Set} {x y : b} (α : x ≡ y) → trans (sym α) α ≡ refl
rinv≡ refl = refl
-}