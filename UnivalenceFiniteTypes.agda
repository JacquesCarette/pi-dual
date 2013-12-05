{-# OPTIONS --without-K #-}

module UnivalenceFiniteTypes where

open import Agda.Prim
open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Maybe hiding (map) 
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Data.List
open import Function renaming (_∘_ to _○_)

infixr 8  _∘_   -- path composition
infix  4  _≡_   -- propositional equality
infix  4  _∼_   -- homotopy between two functions 
infix  4  _≃_   -- type of equivalences
infix  2  _∎       -- equational reasoning for paths
infixr 2  _≡⟨_⟩_   -- equational reasoning for paths
infix  2  _∎≃      -- equational reasoning for equivalences
infixr 2  _≃⟨_⟩_   -- equational reasoning for equivalences

------------------------------------------------------------------------------
-- Finite types

data FT : Set where
  ZERO  : FT
  ONE   : FT
  PLUS  : FT → FT → FT
  TIMES : FT → FT → FT

⟦_⟧ : FT → Set
⟦ ZERO ⟧ = ⊥
⟦ ONE ⟧ = ⊤
⟦ PLUS B₁ B₂ ⟧ = ⟦ B₁ ⟧ ⊎ ⟦ B₂ ⟧
⟦ TIMES B₁ B₂ ⟧ = ⟦ B₁ ⟧ × ⟦ B₂ ⟧

------------------------------------------------------------------------------
-- Generalized paths are pi-combinators

data _⇛_ : FT → FT → Set where
  -- additive structure
  unite₊⇛  : { b : FT } → PLUS ZERO b ⇛ b
  uniti₊⇛  : { b : FT } → b ⇛ PLUS ZERO b
  swap₊⇛   : { b₁ b₂ : FT } → PLUS b₁ b₂ ⇛ PLUS b₂ b₁
  assocl₊⇛ : { b₁ b₂ b₃ : FT } → PLUS b₁ (PLUS b₂ b₃) ⇛ PLUS (PLUS b₁ b₂) b₃
  assocr₊⇛ : { b₁ b₂ b₃ : FT } → PLUS (PLUS b₁ b₂) b₃ ⇛ PLUS b₁ (PLUS b₂ b₃)
  -- multiplicative structure
  unite⋆⇛  : { b : FT } → TIMES ONE b ⇛ b
  uniti⋆⇛  : { b : FT } → b ⇛ TIMES ONE b
  swap⋆⇛   : { b₁ b₂ : FT } → TIMES b₁ b₂ ⇛ TIMES b₂ b₁
  assocl⋆⇛ : { b₁ b₂ b₃ : FT } → 
             TIMES b₁ (TIMES b₂ b₃) ⇛ TIMES (TIMES b₁ b₂) b₃
  assocr⋆⇛ : { b₁ b₂ b₃ : FT } → 
             TIMES (TIMES b₁ b₂) b₃ ⇛ TIMES b₁ (TIMES b₂ b₃)
  -- distributivity
  distz⇛   : { b : FT } → TIMES ZERO b ⇛ ZERO
  factorz⇛ : { b : FT } → ZERO ⇛ TIMES ZERO b
  dist⇛    : { b₁ b₂ b₃ : FT } → 
            TIMES (PLUS b₁ b₂) b₃ ⇛ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor⇛  : { b₁ b₂ b₃ : FT } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⇛ TIMES (PLUS b₁ b₂) b₃
  -- congruence
  id⇛    : { b : FT } → b ⇛ b
  sym⇛   : { b₁ b₂ : FT } → (b₁ ⇛ b₂) → (b₂ ⇛ b₁)
  _◎_    : { b₁ b₂ b₃ : FT } → (b₁ ⇛ b₂) → (b₂ ⇛ b₃) → (b₁ ⇛ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : FT } → 
           (b₁ ⇛ b₃) → (b₂ ⇛ b₄) → (PLUS b₁ b₂ ⇛ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : FT } → 
           (b₁ ⇛ b₃) → (b₂ ⇛ b₄) → (TIMES b₁ b₂ ⇛ TIMES b₃ b₄)

------------------------------------------------------------------------------
-- Equivalences a la HoTT (using HoTT paths and path induction)

-- Our own version of refl that makes 'a' explicit
data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

-- J
pathInd : ∀ {u ℓ} → {A : Set u} → 
          (C : {x y : A} → x ≡ y → Set ℓ) → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

basedPathInd : {A : Set} → (a : A) → (C : (x : A) → (a ≡ x) → Set) →
  C a (refl a) → ((x : A) (p : a ≡ x) → C x p) 
basedPathInd a C c .a (refl .a) = c

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

_∘_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {u} {A} {x} {y} {z} p q = 
  pathInd {u}
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

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

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd -- on p
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

ap2 : ∀ {ℓ ℓ' ℓ''} → {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} 
     {x₁ y₁ : A} {x₂ y₂ : B} → 
     (f : A → B → C) → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (f x₁ x₂  ≡ f y₁ y₂)
ap2 {ℓ} {ℓ'} {ℓ''} {A} {B} {C} {x₁} {y₁} {x₂} {y₂} f p₁ p₂ = 
  pathInd -- on p₁
    (λ {x₁} {y₁} p₁ → f x₁ x₂ ≡ f y₁ y₂) 
    (λ x →
      pathInd -- on p₂
        (λ {x₂} {y₂} p₂ → f x x₂ ≡ f x y₂)
        (λ y → refl (f x y))
        {x₂} {y₂} p₂)
    {x₁} {y₁} p₁

-- Abbreviations for path compositions

_≡⟨_⟩_ : ∀ {u} → {A : Set u} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p ⟩ q = p ∘ q

bydef : ∀ {u} → {A : Set u} {x : A} → (x ≡ x)
bydef {u} {A} {x} = refl x

_∎ : ∀ {u} → {A : Set u} (x : A) → x ≡ x
_∎ x = refl x

-- Transport; Lifting

transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} → 
  (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} {x} {y} P p = 
  pathInd -- on p
    (λ {x} {y} p → (P x → P y))
    (λ _ → id)
    {x} {y} p

-- Lemma 2.3.10

transport-f : ∀ {ℓ ℓ' ℓ''} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
  (f : A → B) → (P : B → Set ℓ'') →
  (p : x ≡ y) → (u : P (f x)) → 
  transport (P ○ f) p u ≡ transport P (ap f p) u
transport-f {ℓ} {ℓ'} {ℓ''} {A} {B} {x} {y} f P p u = 
  pathInd -- on p
    (λ {x} {y} p → (u : P (f x)) → 
      transport (P ○ f) p u ≡ transport P (ap f p) u)
    (λ x u → refl u)
    {x} {y} p u

-- Lemma 2.11.2

transportIdR : {A : Set} {a y z : A} → (p : y ≡ z) → (q : a ≡ y) → 
  transport (λ x → a ≡ x) p q ≡ q ∘ p
transportIdR {A} {a} {y} {z} p q = 
  pathInd 
    (λ {y} {z} p → (q : a ≡ y) → transport (λ x → a ≡ x) p q ≡ q ∘ p)
    (λ y q → transport (λ x → a ≡ x) (refl y) q 
               ≡⟨ bydef ⟩
             q 
               ≡⟨ unitTransR q ⟩
             q ∘ refl y ∎)
    {y} {z} p q

transportIdL : {A : Set} {a y z : A} → (p : y ≡ z) → (q : y ≡ a) → 
  transport (λ x → x ≡ a) p q ≡ ! p ∘ q
transportIdL {A} {a} {y} {z} p q = 
  pathInd 
    (λ {y} {z} p → (q : y ≡ a) → transport (λ x → x ≡ a) p q ≡ ! p ∘ q)
    (λ y q → transport (λ x → x ≡ a) (refl y) q 
               ≡⟨ bydef ⟩
             q 
               ≡⟨ unitTransL q ⟩
             ! (refl y) ∘ q ∎)
    {y} {z} p q

transportIdRefl : {A : Set} {y z : A} → (p : y ≡ z) → (q : y ≡ y) → 
  transport (λ x → x ≡ x) p q ≡ ! p ∘ q ∘ p
transportIdRefl {A} {y} {z} p q = 
  pathInd 
    (λ {y} {z} p → (q : y ≡ y) → transport (λ x → x ≡ x) p q ≡ ! p ∘ q ∘ p)
    (λ y q → transport (λ x → x ≡ x) (refl y) q 
               ≡⟨ bydef ⟩
             q 
               ≡⟨ unitTransR q ⟩
             q ∘ refl y
               ≡⟨ unitTransL (q ∘ refl y) ⟩
             ! (refl y) ∘ q ∘ refl y ∎)
    {y} {z} p q

-- Equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    β : (g ○ f) ∼ id

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {ℓ} {ℓ} {A} {A} id
idqinv = record {
           g = id ;
           α = λ b → refl b ; 
           β = λ a → refl a
         } 

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ
       
equiv₂ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → isequiv f → qinv f
equiv₂ {f = f} (mkisequiv ig iα ih iβ) = 
  record {
    g = ig ;
    α = iα ;
    β = λ x → ig (f x)
                ≡⟨ ! (iβ (ig (f x))) ⟩
              ih (f (ig (f x)))
                ≡⟨ ap ih (iα (f x)) ⟩
              ih (f x)
                ≡⟨ iβ x ⟩
              x ∎
  }

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

id≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
id≃ = (id , equiv₁ idqinv)

sym≃ :  ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A ≃ B) → B ≃ A
sym≃ (A→B , equiv) with equiv₂ equiv
... | mkqinv g α β = g , equiv₁ (mkqinv A→B β α)

trans≃ : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
trans≃ (f , feq) (g , geq) with equiv₂ feq | equiv₂ geq
... | mkqinv ff fα fβ | mkqinv gg gα gβ = 
  (g ○ f , equiv₁ (mkqinv 
                    (ff ○ gg)
                    (λ c → g (f (ff (gg c)))
                             ≡⟨ ap g (fα (gg c)) ⟩
                           g (gg c)
                             ≡⟨ gα c ⟩
                           c ∎)
                    (λ a → ff (gg (g (f a)))
                             ≡⟨ ap ff (gβ (f a)) ⟩
                           ff (f a)
                             ≡⟨ fβ a ⟩
                           a ∎)))

-- equivalences are injective

_⋆_ : {A B : Set} → (A ≃ B) → (x : A) → B
(f , _) ⋆ x = f x 

inj≃ : {A B : Set} → (eq : A ≃ B) → (x y : A) → (eq ⋆ x ≡ eq ⋆ y → x ≡ y)
inj≃ (f , mkisequiv g α h β) x y p = ! (β x) ∘ (ap h p ∘ β y)
        
-- equivalences for coproducts (Sec. 2.12) 

indCP : {A B : Set} → (C : A ⊎ B → Set) → 
        ((a : A) → C (inj₁ a)) → ((b : B) → C (inj₂ b)) → ((x : A ⊎ B) → C x)
indCP C f g (inj₁ a) = f a
indCP C f g (inj₂ b) = g b

code : {A B : Set} → (a₀ : A) → A ⊎ B → Set
code a₀ (inj₁ a) = a₀ ≡ a
code a₀ (inj₂ b) = ⊥ 

encode : {A B : Set} → (a₀ : A) → (x : A ⊎ B) → (p : inj₁ a₀ ≡ x) → code a₀ x
encode {A} {B} a₀ x p = transport (code a₀) p (refl a₀)

decode : {A B : Set} → (a₀ : A) → (x : A ⊎ B) → (c : code a₀ x) → inj₁ a₀ ≡ x
decode a₀ (inj₁ a) c = ap inj₁ c 
decode a₀ (inj₂ b) () 

codeqinv : {A B : Set} {a₀ : A} {x : A ⊎ B} → qinv (encode a₀ x)
codeqinv {A} {B} {a₀} {x} = record {
  g = decode a₀ x ; 
  α = indCP 
        (λ x → (c : code a₀ x) → encode a₀ x (decode a₀ x c) ≡ c)
        (λ a c → encode a₀ (inj₁ a) (decode a₀ (inj₁ a) c) 
                   ≡⟨ bydef ⟩
                 encode a₀ (inj₁ a) (ap inj₁ c)
                   ≡⟨ bydef ⟩
                 transport (code a₀) (ap inj₁ c) (refl a₀)
                   ≡⟨ ! (transport-f inj₁ (code a₀) c (refl a₀)) ⟩ 
                 transport (λ a → code {A} {B} a₀ (inj₁ a)) c (refl a₀)
                   ≡⟨ bydef ⟩ 
                 transport (λ a → a₀ ≡ a) c (refl a₀)
                   ≡⟨ transportIdR c (refl a₀) ⟩ 
                 (refl a₀) ∘ c
                   ≡⟨ ! (unitTransL c) ⟩
                 c ∎)
        (λ b ())
        x ;
  β = λ p → basedPathInd 
              (inj₁ a₀) 
              (λ x p → decode a₀ x (encode a₀ x p) ≡ p)
              (decode a₀ (inj₁ a₀) 
                (encode {A} {B} a₀ (inj₁ a₀) (refl (inj₁ a₀)))
                 ≡⟨ bydef ⟩ 
              (decode a₀ (inj₁ a₀) 
                (transport (code {A} {B} a₀) (refl (inj₁ a₀)) (refl a₀)))
                 ≡⟨ bydef ⟩ 
              (decode a₀ (inj₁ a₀) (refl a₀))
                 ≡⟨ bydef ⟩ 
              (ap inj₁ (refl a₀))
                 ≡⟨ bydef ⟩ 
               refl (inj₁ a₀) ∎)
              x p }

thm2-12-5 : {A B : Set} → (a₀ : A) → (x : A ⊎ B) → (inj₁ a₀ ≡ x) ≃ code a₀ x
thm2-12-5 {A} {B} a₀ x = (encode a₀ x , equiv₁ codeqinv)

inj₁₁path : {A B : Set} → (a₁ a₂ : A) → 
          (inj₁ {A = A} {B = B} a₁ ≡ inj₁ a₂) ≃ (a₁ ≡ a₂)
inj₁₁path a₁ a₂ = thm2-12-5 a₁ (inj₁ a₂)

inj₁₂path : {A B : Set} → (a : A) (b : B) → (inj₁ a ≡ inj₂ b) ≃ ⊥
inj₁₂path a b = thm2-12-5 a (inj₂ b)

-- Abbreviations for equivalence compositions

_≃⟨_⟩_ : (A : Set) {B C : Set} → (A ≃ B) → (B ≃ C) → (A ≃ C) 
_ ≃⟨ p ⟩ q = trans≃ p q

_∎≃ : {ℓ : Level} {A : Set ℓ} → A ≃ A
_∎≃ {ℓ} {A} = id≃ {ℓ} {A}
 
------------------------------------------------------------------------------
-- Univalence

-- for each combinator, define two functions that are inverses, and
-- establish an equivalence

-- swap₊

swap₊ : {A B : Set} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

swapswap₊ : {A B : Set} → swap₊ ○ swap₊ {A} {B} ∼ id
swapswap₊ (inj₁ a) = refl (inj₁ a)
swapswap₊ (inj₂ b) = refl (inj₂ b)

swap₊equiv : {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
swap₊equiv = (swap₊ , equiv₁ (mkqinv swap₊ swapswap₊ swapswap₊))

-- unite₊ and uniti₊

unite₊ : {A : Set} → ⊥ ⊎ A → A
unite₊ (inj₁ ())
unite₊ (inj₂ y) = y

uniti₊ : {A : Set} → A → ⊥ ⊎ A
uniti₊ a = inj₂ a

uniti₊∘unite₊ : {A : Set} → uniti₊ ○ unite₊ ∼ id {A = ⊥ ⊎ A}
uniti₊∘unite₊ (inj₁ ())
uniti₊∘unite₊ (inj₂ y) = refl (inj₂ y)

-- this is so easy, Agda can figure it out by itself (see below)
unite₊∙uniti₊ : {A : Set} → unite₊ ○ uniti₊ ∼ id {A = A}
unite₊∙uniti₊ = refl

unite₊equiv : {A : Set} → (⊥ ⊎ A) ≃ A
unite₊equiv = (unite₊ , mkisequiv uniti₊ refl uniti₊ uniti₊∘unite₊)

uniti₊equiv : {A : Set} → A ≃ (⊥ ⊎ A)
uniti₊equiv = uniti₊ , mkisequiv unite₊ uniti₊∘unite₊ unite₊ unite₊∙uniti₊

-- unite⋆ and uniti⋆

unite⋆ : {A : Set} → ⊤ × A → A
unite⋆ (tt , x) = x

uniti⋆ : {A : Set} → A → ⊤ × A
uniti⋆ x = tt , x

uniti⋆∘unite⋆ : {A : Set} → uniti⋆ ○ unite⋆ ∼ id {A = ⊤ × A}
uniti⋆∘unite⋆ (tt , x) = refl (tt , x)

unite⋆equiv : {A : Set} → (⊤ × A) ≃ A
unite⋆equiv = unite⋆ , mkisequiv uniti⋆ refl uniti⋆ uniti⋆∘unite⋆

uniti⋆equiv : {A : Set} → A ≃ (⊤ × A)
uniti⋆equiv = uniti⋆ , mkisequiv unite⋆ uniti⋆∘unite⋆ unite⋆ refl

-- swap⋆

swap⋆ : {A B : Set} → A × B → B × A
swap⋆ (a , b) = (b , a)

swapswap⋆ : {A B : Set} → swap⋆ ○ swap⋆ ∼ id {A = A × B}
swapswap⋆ (a , b) = refl (a , b) 

swap⋆equiv : {A B : Set} → (A × B) ≃ (B × A)
swap⋆equiv = swap⋆ , mkisequiv swap⋆ swapswap⋆ swap⋆ swapswap⋆

-- assocl₊ and assocr₊

assocl₊ : {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
assocl₊ (inj₁ a) = inj₁ (inj₁ a)
assocl₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
assocl₊ (inj₂ (inj₂ c)) = inj₂ c

assocr₊ : {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
assocr₊ (inj₁ (inj₁ a)) = inj₁ a
assocr₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
assocr₊ (inj₂ c) = inj₂ (inj₂ c)

assocl₊∘assocr₊ : {A B C : Set} → assocl₊ ○ assocr₊ ∼ id {A = ((A ⊎ B) ⊎ C)}
assocl₊∘assocr₊ (inj₁ (inj₁ a)) = refl (inj₁ (inj₁ a))
assocl₊∘assocr₊ (inj₁ (inj₂ b)) = refl (inj₁ (inj₂ b))
assocl₊∘assocr₊ (inj₂ c) = refl (inj₂ c)

assocr₊∘assocl₊ : {A B C : Set} → assocr₊ ○ assocl₊ ∼ id {A = (A ⊎ (B ⊎ C))}
assocr₊∘assocl₊ (inj₁ a) = refl (inj₁ a)
assocr₊∘assocl₊ (inj₂ (inj₁ b)) = refl (inj₂ (inj₁ b))
assocr₊∘assocl₊ (inj₂ (inj₂ c)) = refl (inj₂ (inj₂ c))

assocl₊equiv : {A B C : Set} → (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
assocl₊equiv = 
  assocl₊ , mkisequiv assocr₊ assocl₊∘assocr₊ assocr₊ assocr₊∘assocl₊

assocr₊equiv : {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
assocr₊equiv = 
  assocr₊ , mkisequiv assocl₊ assocr₊∘assocl₊ assocl₊ assocl₊∘assocr₊

-- assocl⋆ and assocr⋆

assocl⋆ : {A B C : Set} → (A × (B × C)) → ((A × B) × C)
assocl⋆ (a , (b , c)) = ((a , b) , c)

assocr⋆ : {A B C : Set} → ((A × B) × C) → (A × (B × C))
assocr⋆ ((a , b) , c) = (a , (b , c))

assocl⋆∘assocr⋆ : {A B C : Set} → assocl⋆ ○ assocr⋆ ∼ id {A = ((A × B) × C)}
assocl⋆∘assocr⋆ x = refl x

assocr⋆∘assocl⋆ : {A B C : Set} → assocr⋆ ○ assocl⋆ ∼ id {A = (A × (B × C))}
assocr⋆∘assocl⋆ x = refl x

assocl⋆equiv : {A B C : Set} → (A × (B × C)) ≃ ((A × B) × C)
assocl⋆equiv = 
  assocl⋆ , mkisequiv assocr⋆ assocl⋆∘assocr⋆ assocr⋆ assocr⋆∘assocl⋆

assocr⋆equiv : {A B C : Set} → ((A × B) × C) ≃ (A × (B × C))
assocr⋆equiv = 
  assocr⋆ , mkisequiv assocl⋆ assocr⋆∘assocl⋆ assocl⋆ assocl⋆∘assocr⋆

-- distz and factorz

distz : { A : Set} → (⊥ × A) → ⊥
distz (() , _)

factorz : {A : Set} → ⊥ → (⊥ × A)
factorz ()
 
distz∘factorz : {A : Set} → distz ○ factorz {A} ∼ id
distz∘factorz ()

factorz∘distz : {A : Set} → factorz {A} ○ distz ∼ id
factorz∘distz (() , proj₂)

distzequiv : {A : Set} → (⊥ × A) ≃ ⊥
distzequiv {A} = 
  distz , mkisequiv factorz (distz∘factorz {A}) factorz factorz∘distz

factorzequiv : {A : Set} → ⊥ ≃ (⊥ × A)
factorzequiv {A} = 
  factorz , mkisequiv distz factorz∘distz distz (distz∘factorz {A})

-- dist and factor

dist : {A B C : Set} → ((A ⊎ B) × C) → (A × C) ⊎ (B × C)
dist (inj₁ x , c) = inj₁ (x , c)
dist (inj₂ y , c) = inj₂ (y , c)

factor : {A B C : Set} → (A × C) ⊎ (B × C) → ((A ⊎ B) × C)
factor (inj₁ (a , c)) = inj₁ a , c
factor (inj₂ (b , c)) = inj₂ b , c

dist∘factor : {A B C : Set} → dist {A} {B} {C} ○ factor ∼ id
dist∘factor (inj₁ x) = refl (inj₁ x)
dist∘factor (inj₂ y) = refl (inj₂ y)

factor∘dist : {A B C : Set} → factor {A} {B} {C} ○ dist ∼ id
factor∘dist (inj₁ x , c) = refl (inj₁ x , c)
factor∘dist (inj₂ y , c) = refl (inj₂ y , c)

distequiv : {A B C : Set} → ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
distequiv = dist , mkisequiv factor dist∘factor factor factor∘dist

factorequiv : {A B C : Set} →  ((A × C) ⊎ (B × C)) ≃ ((A ⊎ B) × C)
factorequiv = factor , (mkisequiv dist factor∘dist dist dist∘factor)

-- ⊕

_⊎∼_ : {A B C D : Set} {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ○ finv ∼ id) → (β : g ○ ginv ∼ id) → 
  (f ⊎→ g) ○ (finv ⊎→ ginv) ∼ id {A = C ⊎ D}
_⊎∼_ α β (inj₁ x) = ap inj₁ (α x) 
_⊎∼_ α β (inj₂ y) = ap inj₂ (β y)

path⊎ : {A B C D : Set} → A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)
path⊎ (fp , eqp) (fq , eqq) = 
  Data.Sum.map fp fq , 
  mkisequiv (P.g ⊎→ Q.g) (P.α ⊎∼ Q.α) (P.h ⊎→ Q.h) (P.β ⊎∼ Q.β)
  where module P = isequiv eqp
        module Q = isequiv eqq
        
-- ⊗

_×∼_ : {A B C D : Set} {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ○ finv ∼ id) → (β : g ○ ginv ∼ id) → 
  (f ×→ g) ○ (finv ×→ ginv) ∼ id {A = C × D}
_×∼_ α β (x , y) = ap2 _,_ (α x) (β y)
 
path× : {A B C D : Set} → A ≃ C → B ≃ D → (A × B) ≃ (C × D)
path× {A} {B} {C} {D} (fp , eqp) (fq , eqq) = 
  Data.Product.map fp fq , 
  mkisequiv 
    (P.g ×→ Q.g) 
    (_×∼_ {A} {B} {C} {D} {fp} {P.g} {fq} {Q.g} P.α Q.α) 
    (P.h ×→ Q.h) 
    (_×∼_ {C} {D} {A} {B} {P.h} {fp} {Q.h} {fq} P.β Q.β)
  where module P = isequiv eqp
        module Q = isequiv eqq

-- Now map each combinator to the corresponding equivalence

path2equiv : {B₁ B₂ : FT} → (B₁ ⇛ B₂) → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧)
path2equiv unite₊⇛  = unite₊equiv
path2equiv uniti₊⇛  = uniti₊equiv
path2equiv swap₊⇛   = swap₊equiv
path2equiv assocl₊⇛ = assocl₊equiv
path2equiv assocr₊⇛ = assocr₊equiv
path2equiv unite⋆⇛  = unite⋆equiv
path2equiv uniti⋆⇛  = uniti⋆equiv
path2equiv swap⋆⇛   = swap⋆equiv
path2equiv assocl⋆⇛ = assocl⋆equiv
path2equiv assocr⋆⇛ = assocr⋆equiv
path2equiv distz⇛   = distzequiv
path2equiv factorz⇛ = factorzequiv
path2equiv dist⇛    = distequiv
path2equiv factor⇛  = factorequiv
path2equiv id⇛      = id , mkisequiv id refl id refl
path2equiv (sym⇛ p) = sym≃ (path2equiv p)
path2equiv (p ◎ q)  = trans≃ (path2equiv p) (path2equiv q) 
path2equiv (p ⊕ q)  = path⊎ (path2equiv p) (path2equiv q)
path2equiv (p ⊗ q)  = path× (path2equiv p) (path2equiv q) 

-- Reverse direction

toℕ : FT → ℕ
toℕ ZERO = zero
toℕ ONE = suc zero
toℕ (PLUS b₀ b₁) = (toℕ b₀) + (toℕ b₁) 
toℕ (TIMES b₀ b₁) = (toℕ b₀) * (toℕ b₁)

fromℕ : ℕ → FT
fromℕ zero = ZERO
fromℕ (suc n) = PLUS ONE (fromℕ n)

toℕ∘fromℕ : toℕ ○ fromℕ ∼ id
toℕ∘fromℕ zero = refl zero
toℕ∘fromℕ (suc n) =
  pathInd
    (λ {x} {y} p → suc x ≡ suc y)
    (λ n → refl (suc n))
    (toℕ∘fromℕ n)

assocr : {m : ℕ} (n : ℕ) → (PLUS (fromℕ n) (fromℕ m)) ⇛ fromℕ (n + m)
assocr zero = unite₊⇛
assocr (suc n) = assocr₊⇛ ◎ (id⇛ ⊕ (assocr n))

distr : (n₀ : ℕ) {n₁ : ℕ} → TIMES (fromℕ n₀) (fromℕ n₁) ⇛ fromℕ (n₀ * n₁)
distr zero = distz⇛
distr (suc n) {m} = dist⇛ ◎ ((unite⋆⇛ ⊕ id⇛) ◎ ((id⇛ ⊕ distr n) ◎ assocr m))

-- normalize a finite type to (1 + (1 + (1 + ... + (1 + 0) ... )))
-- a bunch of ones ending with zero with left biased + in between

normalize : FT → FT
normalize = fromℕ ○ toℕ

normal : (b : FT) → b ⇛ normalize b
normal ZERO = id⇛
normal ONE = uniti₊⇛ ◎ swap₊⇛
normal (PLUS b₀ b₁) = (normal b₀ ⊕ normal b₁) ◎ assocr (toℕ b₀)
normal (TIMES b₀ b₁) = (normal b₀ ⊗ normal b₁) ◎ distr (toℕ b₀)

normalizeC : {B : FT} → ⟦ normalize B ⟧ ≃ ⟦ B ⟧
normalizeC {B} = path2equiv (sym⇛ (normal B))

mapNorm :  {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → ⟦ normalize B₁ ⟧ ≃ ⟦ normalize B₂ ⟧
mapNorm {B₁} {B₂} eq = trans≃ (trans≃ (normalizeC {B₁}) eq) (sym≃ (normalizeC {B₂}))

------------------------------------------------------------------------
-- Inspect on steroids (borrowed from standard library)

-- Inspect on steroids can be used when you want to pattern match on
-- the result r of some expression e, and you also need to "remember"
-- that r ≡ e.

data Reveal_is_ {a} {A : Set a} (x : Hidden A) (y : A) : Set a where
  ⟪_⟫ : (eq : reveal x ≡ y) → Reveal x is y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
inspect f x = ⟪ refl (f x) ⟫

sub1 : {A B : Set} → ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A → B
sub1 (f , mkisequiv g α h β) a with f (inj₂ a) | inspect f (inj₂ a)
... | inj₂ b | _ = b
... | inj₁ tt | ⟪ eqa ⟫ with f (inj₁ tt) | inspect f (inj₁ tt)
...     | inj₁ tt | ⟪ eq ⟫ with inj≃ (f , mkisequiv g α h β) (inj₂ a) (inj₁ tt) (eqa ∘ (! eq))
...         | eqc = {!!} -- impossible, but how to convince agda?
sub1 (f , mkisequiv g α h β) a | inj₁ tt | ⟪ eqa ⟫ | inj₂ b | _ = b

sub1congr : {A B : Set} → (eq : (⊤ ⊎ A) ≃ (⊤ ⊎ B)) → (((sub1 eq) ○ (sub1 (sym≃ eq))) ∼ id)
sub1congr (f , mkisequiv g α h β) b = {!!}

sub1congl : {A B : Set} → (eq : (⊤ ⊎ A) ≃ (⊤ ⊎ B)) → ((sub1 (sym≃ eq)) ○ (sub1 eq) ∼ id)
sub1congl (f , mkisequiv g α h β) a = {!!}

lemma⊤⊎ : {B₁ B₂ : FT} → ⟦ PLUS ONE B₁ ⟧ ≃ ⟦ PLUS ONE B₂ ⟧ → ⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧
lemma⊤⊎ eq with eq
... | (f , mkisequiv g α h β) = sub1 eq , mkisequiv (sub1 (sym≃ eq)) (sub1congr eq) (sub1 (sym≃ eq)) (sub1congl eq)

⟦_⟧ℕ : ℕ → Set
⟦ zero ⟧ℕ = ⊥
⟦ suc n ⟧ℕ = ⊤ ⊎ ⟦ n ⟧ℕ

ℕrespects⟦⟧ : {n : ℕ} → ⟦ fromℕ n ⟧ ≃ ⟦ n ⟧ℕ
ℕrespects⟦⟧ {zero} = id≃
ℕrespects⟦⟧ {suc n} = path⊎ id≃ (ℕrespects⟦⟧ {n})

lemmaℕ⊤⊎ : {n₁ n₂ : ℕ} → ⟦ suc n₁ ⟧ℕ ≃ ⟦ suc n₂ ⟧ℕ → ⟦ n₁ ⟧ℕ ≃ ⟦ n₂ ⟧ℕ
lemmaℕ⊤⊎ eq with eq
... | (f , mkisequiv g α h β) = sub1 eq , mkisequiv (sub1 (sym≃ eq)) (sub1congr eq) (sub1 (sym≃ eq)) (sub1congl eq)

liftℕ : (n₁ n₂ : ℕ) → ⟦ n₁ ⟧ℕ ≃ ⟦ n₂ ⟧ℕ → (fromℕ n₁) ≡ (fromℕ n₂)
liftℕ zero zero eq = refl ZERO
liftℕ zero (suc n₂) (_ , mkisequiv g α h β) with h (inj₁ tt)
liftℕ zero (suc n₂) (_ , mkisequiv g α h β) | ()
liftℕ (suc n₁) zero (f , _) with f (inj₁ tt)
liftℕ (suc n₁) zero (f , _) | ()
liftℕ (suc n₁) (suc n₂) eq = ap (λ x → PLUS ONE x) (liftℕ n₁ n₂ (lemmaℕ⊤⊎ eq))

liftNormal : {B₁ B₂ : FT} →  ⟦ normalize B₁ ⟧ ≃ ⟦ normalize B₂ ⟧ → (normalize B₁) ≡ (normalize B₂)
liftNormal {B₁} {B₂} eq =
  liftℕ (toℕ B₁) (toℕ B₂)
    (⟦ toℕ B₁ ⟧ℕ ≃⟨ sym≃ (ℕrespects⟦⟧ {toℕ B₁}) ⟩ ⟦ normalize B₁ ⟧ ≃⟨ eq ⟩ ⟦ normalize B₂ ⟧ ≃⟨ ℕrespects⟦⟧ {toℕ B₂} ⟩ id≃)

sameNorm : {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → (normalize B₁) ≡ (normalize B₂)
sameNorm {B₁} {B₂} eq = liftNormal {B₁} {B₂} (mapNorm eq)

bridge : {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → (normalize B₁) ⇛ (normalize B₂)
bridge eq =
  pathInd
    (λ {B₁} {B₂} p → B₁ ⇛ B₂)
    (λ B → id⇛)
    (sameNorm eq)

equiv2path : {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → (B₁ ⇛ B₂)
-- not sure why typechecking this fails to terminate for me
-- equiv2path {B₁} {B₂} eq = ((normal B₁) ◎ bridge eq) ◎ (sym⇛ (normal B₂))
equiv2path {B₁} {B₂} eq = {!!}

-- univalence

univalence₁ : {B₁ B₂ : FT} → 
  (e : ⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → path2equiv (equiv2path e) ≡ e
univalence₁ {B₁} {B₂} (f , feq) with equiv₂ feq
... | mkqinv g  α  β = {!!} 

univalence₂ : {B₁ B₂ : FT} → (p : B₁ ⇛ B₂) → equiv2path (path2equiv p) ≡ p
univalence₂ unite₊⇛ = {!!}
univalence₂ uniti₊⇛ = {!!}
univalence₂ swap₊⇛ = {!!}
univalence₂ assocl₊⇛ = {!!}
univalence₂ assocr₊⇛ = {!!}
univalence₂ unite⋆⇛ = {!!}
univalence₂ uniti⋆⇛ = {!!}
univalence₂ swap⋆⇛ = {!!}
univalence₂ assocl⋆⇛ = {!!}
univalence₂ assocr⋆⇛ = {!!}
univalence₂ distz⇛ = {!!}
univalence₂ factorz⇛ = {!!}
univalence₂ dist⇛ = {!!}
univalence₂ factor⇛ = {!!}
univalence₂ id⇛ = {!!}
univalence₂ (sym⇛ p) = {!!}
univalence₂ (p ◎ q) = {!!} 
univalence₂ (p ⊕ q) = {!!}
univalence₂ (p ⊗ q) = {!!} 

univalence : {B₁ B₂ : FT} → (B₁ ⇛ B₂) ≃ (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) 
univalence = 
  (path2equiv , equiv₁ (mkqinv equiv2path univalence₁ univalence₂))

------------------------------------------------------------------------------

{--

Not used

BOOL-FT : Set
BOOL-FT = ⟦ PLUS ONE ONE ⟧

true-FT : BOOL-FT
true-FT = inj₁ tt

false-FT : BOOL-FT
false-FT = inj₂ tt

witness : (B : FT) → Maybe ⟦ B ⟧
witness ZERO = nothing
witness ONE = just tt
witness (PLUS B₁ B₂) with witness B₁ | witness B₂ 
... | nothing | nothing = nothing
... | nothing | just b  = just (inj₂ b)
... | just b  | _ = just (inj₁ b) 
witness (TIMES B₁ B₂) with witness B₁ | witness B₂ 
... | nothing | _ = nothing
... | just b  | nothing = nothing
... | just b₁ | just b₂ = just (b₁ , b₂)

elems : (B : FT) → List ⟦ B ⟧
elems ZERO          = []
elems ONE           = [ tt ]
elems (PLUS B₁ B₂)  = map inj₁ (elems B₁) ++ map inj₂ (elems B₂) 
elems (TIMES B₁ B₂) = concatMap 
                        (λ e₁ → map (λ e₂ → (e₁ , e₂)) (elems B₂)) 
                        (elems B₁)
      
expandF : {B₁ B₂ : FT} → (⟦ B₁ ⟧ → ⟦ B₂ ⟧) → List (⟦ B₁ ⟧ × ⟦ B₂ ⟧)
expandF {B₁} {B₂} f = map (λ e → (e , f e)) (elems B₁)

test0 : List ((⊤ × BOOL-FT) × BOOL-FT)
test0 = expandF (unite⋆ {BOOL-FT})

exf : ⊤ ⊎ ℕ → ℕ
exf (inj₁ tt) = 0 
exf (inj₂ n) = suc n

exg : ℕ → ⊤ ⊎ ℕ
exg 0 = inj₁ tt
exg (suc n) = inj₂ n

exα : exf ○ exg ∼ id
exα 0 = refl 0
exα (suc n) = refl (suc n)

exβ : exg ○ exf ∼ id
exβ (inj₁ tt) = refl (inj₁ tt)
exβ (inj₂ n) = refl (inj₂ n) 

ex : (⊤ ⊎ ℕ) ≃ ℕ
ex = (exf , equiv₁ (mkqinv exg exα exβ))

exf2 : (⊤ ⊎ (⊤ ⊎ ℕ)) → (⊤ ⊎ ℕ)
exf2 (inj₁ tt) = inj₂ 0
exf2 (inj₂ (inj₁ tt)) = inj₂ 1
exf2 (inj₂ (inj₂ 0)) = inj₁ tt
exf2 (inj₂ (inj₂ (suc n))) = inj₂ (suc (suc n))

exg2 : (⊤ ⊎ ℕ) → (⊤ ⊎ (⊤ ⊎ ℕ))
exg2 (inj₁ tt) = inj₂ (inj₂ 0)
exg2 (inj₂ 0) = inj₁ tt
exg2 (inj₂ 1) = inj₂ (inj₁ tt)
exg2 (inj₂ (suc (suc n))) = inj₂ (inj₂ (suc n))

exα2 : exf2 ○ exg2 ∼ id
exα2 (inj₁ tt) = refl (inj₁ tt)
exα2 (inj₂ 0) = refl (inj₂ 0) 
exα2 (inj₂ 1) = refl (inj₂ 1) 
exα2 (inj₂ (suc (suc n))) = refl (inj₂ (suc (suc n))) 

exβ2 : exg2 ○ exf2 ∼ id
exβ2 (inj₁ tt) = refl (inj₁ tt) 
exβ2 (inj₂ (inj₁ tt)) = refl (inj₂ (inj₁ tt)) 
exβ2 (inj₂ (inj₂ 0)) = refl (inj₂ (inj₂ 0)) 
exβ2 (inj₂ (inj₂ (suc n))) = refl (inj₂ (inj₂ (suc n))) 

ex2 : (⊤ ⊎ (⊤ ⊎ ℕ)) ≃ (⊤ ⊎ ℕ)
ex2 = (exf2 , equiv₁ (mkqinv exg2 exα2 exβ2)) 

s1 : {A B : Set} → ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A ≃ B
s1 (f , mkisequiv g α h β) with f (inj₁ tt) | g (inj₁ tt) 
... | inj₁ tt | inj₁ tt = {!!} 
... | inj₁ tt | inj₂ x = {!!} 
... | inj₂ x | inj₁ tt = {!!} 
... | inj₂ x | inj₂ y = {!!} 

--}
