{-# OPTIONS --without-K #-}

module HP where

-- Pi as a higher-order inductive type

open import Agda.Prim
open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Maybe hiding (map) 
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Integer hiding (_⊔_) 
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Data.List
open import Data.Rational hiding (_≃_)
open import Function renaming (_∘_ to _○_)

infixr 8  _∘_   -- path composition
infix  4  _≡_   -- propositional equality
infix  4  _∼_   -- homotopy between two functions 
infix  4  _≃_   -- type of equivalences
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning
infix  2  _∎≃      -- equational reasoning for equivalences
infixr 2  _≃⟨_⟩_   -- equational reasoning for equivalences

------------------------------------------------------------------------------
-- Identity types and path induction principles

-- Our own version of refl that makes 'a' explicit

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

pathInd : ∀ {u ℓ} → {A : Set u} → 
          (C : {x y : A} → x ≡ y → Set ℓ) → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

basedPathInd : {A : Set} → (a : A) → (C : (x : A) → (a ≡ x) → Set) →
  C a (refl a) → ((x : A) (p : a ≡ x) → C x p) 
basedPathInd a C c .a (refl .a) = c

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

-- p ≡ p ∘ refl

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y) 
unitTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ p ∘ (refl y)) 
    (λ x → refl (refl x))
    {x} {y} p 

-- p ≡ refl ∘ p

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p 

-- ! p ∘ p ≡ refl

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ! p ∘ p ≡ refl y)
    (λ x → refl (refl x))
    {x} {y} p

-- p ∘ ! p ≡ refl

invTransR : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → (p ∘ ! p ≡ refl x)
invTransR {ℓ} {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ∘ ! p ≡ refl x)
    (λ x → refl (refl x))
    {x} {y} p

-- ! (! p) ≡ p

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd 
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r

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
ap f p = 
  pathInd 
    (λ {x} {y} _ → f x ≡ f y) 
    (λ x → refl (f x))
    p

ap₂ : ∀ {ℓ ℓ' ℓ''} → {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} 
     {x₁ y₁ : A} {x₂ y₂ : B} → 
     (f : A → B → C) → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (f x₁ x₂  ≡ f y₁ y₂)
ap₂ {ℓ} {ℓ'} {ℓ''} {A} {B} {C} {x₁} {y₁} {x₂} {y₂} f p₁ p₂ = 
  pathInd -- on p₁
    (λ {x₁} {y₁} p₁ → f x₁ x₂ ≡ f y₁ y₂) 
    (λ x →
      pathInd -- on p₂
        (λ {x₂} {y₂} p₂ → f x x₂ ≡ f x y₂)
        (λ y → refl (f x y))
        {x₂} {y₂} p₂)
    {x₁} {y₁} p₁

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
apfInv f p =
  pathInd
    (λ p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    p

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
transport {x = x} {y} P p = 
  pathInd 
    (λ {x'} {y'} _ → (P x' → P y'))
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

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (_⊔_ ℓ ℓ')
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

-- identities are equivalences

idtoeqv : {A B : Set} → (A ≡ B) → (A ≃ B)
idtoeqv {A} {B} p = 
  pathInd 
    (λ {A'} {B'} _ → A' ≃ B')
    (λ _ → id≃)
    {A} {B} p

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
-- Type equivalences

-- unite₊ and uniti₊

unite₊ : {A : Set} → ⊥ ⊎ A → A
unite₊ (inj₁ ())
unite₊ (inj₂ y) = y

uniti₊ : {A : Set} → A → ⊥ ⊎ A
uniti₊ a = inj₂ a

uniti₊∘unite₊ : {A : Set} → uniti₊ ○ unite₊ ∼ id {A = ⊥ ⊎ A}
uniti₊∘unite₊ (inj₁ ())
uniti₊∘unite₊ (inj₂ y) = refl (inj₂ y)

unite₊∙uniti₊ : {A : Set} → unite₊ ○ uniti₊ ∼ id {A = A}
unite₊∙uniti₊ = refl

unite₊≃ : {A : Set} → (⊥ ⊎ A) ≃ A
unite₊≃ = (unite₊ , mkisequiv uniti₊ refl uniti₊ uniti₊∘unite₊)

uniti₊≃ : {A : Set} → A ≃ (⊥ ⊎ A)
uniti₊≃ = uniti₊ , mkisequiv unite₊ uniti₊∘unite₊ unite₊ unite₊∙uniti₊

-- swap₊

swap₊ : {A B : Set} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

swapswap₊ : {A B : Set} → swap₊ ○ swap₊ {A} {B} ∼ id
swapswap₊ (inj₁ a) = refl (inj₁ a)
swapswap₊ (inj₂ b) = refl (inj₂ b)

swap₊≃ : {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
swap₊≃ = (swap₊ , equiv₁ (mkqinv swap₊ swapswap₊ swapswap₊))

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

assocl₊≃ : {A B C : Set} → (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
assocl₊≃ = 
  assocl₊ , mkisequiv assocr₊ assocl₊∘assocr₊ assocr₊ assocr₊∘assocl₊

assocr₊≃ : {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
assocr₊≃ = 
  assocr₊ , mkisequiv assocl₊ assocr₊∘assocl₊ assocl₊ assocl₊∘assocr₊

-- unite⋆ and uniti⋆

unite⋆ : {A : Set} → ⊤ × A → A
unite⋆ (tt , x) = x

uniti⋆ : {A : Set} → A → ⊤ × A
uniti⋆ x = tt , x

uniti⋆∘unite⋆ : {A : Set} → uniti⋆ ○ unite⋆ ∼ id {A = ⊤ × A}
uniti⋆∘unite⋆ (tt , x) = refl (tt , x)

unite⋆≃ : {A : Set} → (⊤ × A) ≃ A
unite⋆≃ = unite⋆ , mkisequiv uniti⋆ refl uniti⋆ uniti⋆∘unite⋆

uniti⋆≃ : {A : Set} → A ≃ (⊤ × A)
uniti⋆≃ = uniti⋆ , mkisequiv unite⋆ uniti⋆∘unite⋆ unite⋆ refl

-- swap⋆

swap⋆ : {A B : Set} → A × B → B × A
swap⋆ (a , b) = (b , a)

swapswap⋆ : {A B : Set} → swap⋆ ○ swap⋆ ∼ id {A = A × B}
swapswap⋆ (a , b) = refl (a , b) 

swap⋆≃ : {A B : Set} → (A × B) ≃ (B × A)
swap⋆≃ = swap⋆ , mkisequiv swap⋆ swapswap⋆ swap⋆ swapswap⋆

-- assocl⋆ and assocr⋆

assocl⋆ : {A B C : Set} → (A × (B × C)) → ((A × B) × C)
assocl⋆ (a , (b , c)) = ((a , b) , c)

assocr⋆ : {A B C : Set} → ((A × B) × C) → (A × (B × C))
assocr⋆ ((a , b) , c) = (a , (b , c))

assocl⋆∘assocr⋆ : {A B C : Set} → assocl⋆ ○ assocr⋆ ∼ id {A = ((A × B) × C)}
assocl⋆∘assocr⋆ x = refl x

assocr⋆∘assocl⋆ : {A B C : Set} → assocr⋆ ○ assocl⋆ ∼ id {A = (A × (B × C))}
assocr⋆∘assocl⋆ x = refl x

assocl⋆≃ : {A B C : Set} → (A × (B × C)) ≃ ((A × B) × C)
assocl⋆≃ = 
  assocl⋆ , mkisequiv assocr⋆ assocl⋆∘assocr⋆ assocr⋆ assocr⋆∘assocl⋆

assocr⋆≃ : {A B C : Set} → ((A × B) × C) ≃ (A × (B × C))
assocr⋆≃ = 
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

distz≃ : {A : Set} → (⊥ × A) ≃ ⊥
distz≃ {A} = 
  distz , mkisequiv factorz (distz∘factorz {A}) factorz factorz∘distz

factorz≃ : {A : Set} → ⊥ ≃ (⊥ × A)
factorz≃ {A} = 
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

dist≃ : {A B C : Set} → ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
dist≃ = dist , mkisequiv factor dist∘factor factor factor∘dist

factor≃ : {A B C : Set} →  ((A × C) ⊎ (B × C)) ≃ ((A ⊎ B) × C)
factor≃ = factor , (mkisequiv dist factor∘dist dist dist∘factor)

-- congruence 

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
_×∼_ α β (x , y) = ap₂ _,_ (α x) (β y)
 
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

------------------------------------------------------------------------------
-- Pi as a higher-order inductive type

module PI where

  -- hidden

  private 
    data FT* : Set where
      ZERO*  : FT*
      ONE*   : FT*
      PLUS*  : FT* → FT* → FT*
      TIMES* : FT* → FT* → FT*
      NEG*   : FT* → FT*
      RECIP* : FT* → FT*

  -- exported

  FT : Set
  FT = FT*

  ZERO : FT
  ZERO = ZERO*

  ONE : FT
  ONE = ONE*

  PLUS : FT → FT → FT
  PLUS = PLUS*

  TIMES : FT → FT → FT
  TIMES = TIMES*

  NEG : FT → FT
  NEG = NEG*

  RECIP : FT → FT
  RECIP = RECIP*

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
    -- negatives and fractionals
    η₊       : { b : FT } → ZERO ≡ PLUS (NEG b) b
    ε₊       : { b : FT } → PLUS (NEG b) b ≡ ZERO
    refe⋆    : { b : FT } → RECIP (RECIP b) ≡ b
    refi⋆    : { b : FT } → b ≡ RECIP (RECIP b) 
    rile⋆    : { b : FT } → TIMES b (TIMES b (RECIP b)) ≡ b
    rili⋆    : { b : FT } → b ≡ TIMES b (TIMES b (RECIP b)) 
    -- no need to postulate congruence; it will be provable

  -- Any function mapping PI to a type C must produce one of the following
  -- records that shows how both points and paths are mapped

  record PIR {ℓ : Level} (C : Set ℓ) : Set (lsuc ℓ) where
    field
      czero     : C
      cone      : C
      cplus     : C → C → C
      ctimes    : C → C → C
      cneg      : C → C 
      crecip    : C → C 
      cunite₊≡  : { c : C } → cplus czero c ≡ c
      cuniti₊≡  : { c : C } → c ≡ cplus czero c
      cswap₊≡   : { c₁ c₂ : C } → cplus c₁ c₂ ≡ cplus c₂ c₁
      cassocl₊≡ : { c₁ c₂ c₃ : C } → 
                  cplus c₁ (cplus c₂ c₃) ≡ cplus (cplus c₁ c₂) c₃
      cassocr₊≡ : { c₁ c₂ c₃ : C } → 
                  cplus (cplus c₁ c₂) c₃ ≡ cplus c₁ (cplus c₂ c₃)
      cunite⋆≡  : { c : C } → ctimes cone c ≡ c
      cuniti⋆≡  : { c : C } → c ≡ ctimes cone c
      cswap⋆≡   : { c₁ c₂ : C } → ctimes c₁ c₂ ≡ ctimes c₂ c₁
      cassocl⋆≡ : { c₁ c₂ c₃ : C } → 
                  ctimes c₁ (ctimes c₂ c₃) ≡ ctimes (ctimes c₁ c₂) c₃
      cassocr⋆≡ : { c₁ c₂ c₃ : C } → 
                  ctimes (ctimes c₁ c₂) c₃ ≡ ctimes c₁ (ctimes c₂ c₃)
      cdistz≡   : { c : C } → ctimes czero c ≡ czero
      cfactorz≡ : { c : C } → czero ≡ ctimes czero c
      cdist≡    : { c₁ c₂ c₃ : C } → 
                  ctimes (cplus c₁ c₂) c₃ ≡ cplus (ctimes c₁ c₃) (ctimes c₂ c₃)
      cfactor≡  : { c₁ c₂ c₃ : C } → 
                  cplus (ctimes c₁ c₃) (ctimes c₂ c₃) ≡ ctimes (cplus c₁ c₂) c₃
      cη₊       : { c : C } → czero ≡ cplus (cneg c) c
      cε₊       : { c : C } → cplus (cneg c) c ≡ czero
      crefe⋆    : { c : C } → crecip (crecip c) ≡ c
      crefi⋆    : { c : C } → c ≡ crecip (crecip c)
      crile⋆    : { c : C } → ctimes c (ctimes c (crecip c)) ≡ c
      crili⋆    : { c : C } → c ≡ ctimes c (ctimes c (crecip c))

  open PIR

  -- recursion principle for PI: given a target type C and a target record as
  -- above that has appropriate points and paths, recPI shows how points are
  -- mapped to points; the postulates assert that paths are transported as
  -- expected

  recPI : {ℓ : Level} {C : Set ℓ} → (PIR C) → FT → C
  recPI pir ZERO*          = czero pir
  recPI pir ONE*           = cone pir
  recPI pir (PLUS* B₁ B₂)  = cplus pir (recPI pir B₁) (recPI pir B₂)
  recPI pir (TIMES* B₁ B₂) = ctimes pir (recPI pir B₁) (recPI pir B₂)
  recPI pir (NEG* B)       = cneg pir (recPI pir B)
  recPI pir (RECIP* B)     = crecip pir (recPI pir B)
      
  postulate
    βreccunite₊≡  : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b : FT} → ap (recPI pir) (unite₊≡ {b}) ≡ cunite₊≡ pir
    βreccuniti₊≡  : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b : FT} → ap (recPI pir) (uniti₊≡ {b}) ≡ cuniti₊≡ pir
    βreccswap₊≡   : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b₁ b₂ : FT} → ap (recPI pir) (swap₊≡ {b₁} {b₂}) ≡ cswap₊≡ pir
    βreccassocl₊≡ : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b₁ b₂ b₃ : FT} → ap (recPI pir) (assocl₊≡ {b₁} {b₂} {b₃}) ≡ 
      cassocl₊≡ pir
    βreccassocr₊≡ : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b₁ b₂ b₃ : FT} → ap (recPI pir) (assocr₊≡ {b₁} {b₂} {b₃}) ≡ 
      cassocr₊≡ pir
    βreccunite⋆≡  : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b : FT} → ap (recPI pir) (unite⋆≡ {b}) ≡ cunite⋆≡ pir
    βreccuniti⋆≡  : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b : FT} → ap (recPI pir) (uniti⋆≡ {b}) ≡ cuniti⋆≡ pir
    βreccswap⋆≡   : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b₁ b₂ : FT} → ap (recPI pir) (swap⋆≡ {b₁} {b₂}) ≡ cswap⋆≡ pir
    βreccassocl⋆≡ : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b₁ b₂ b₃ : FT} → ap (recPI pir) (assocl⋆≡ {b₁} {b₂} {b₃}) ≡ 
      cassocl⋆≡ pir
    βreccassocr⋆≡ : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b₁ b₂ b₃ : FT} → ap (recPI pir) (assocr⋆≡ {b₁} {b₂} {b₃}) ≡ 
      cassocr⋆≡ pir
    βreccdistz≡   : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b : FT} → ap (recPI pir) (distz≡ {b}) ≡ cdistz≡ pir
    βreccfactorz≡ : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b : FT} → ap (recPI pir) (factorz≡ {b}) ≡ cfactorz≡ pir
    βreccdist≡    : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b₁ b₂ b₃ : FT} → ap (recPI pir) (dist≡ {b₁} {b₂} {b₃}) ≡ 
      cdist≡ pir
    βreccfactor≡  : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      {b₁ b₂ b₃ : FT} → ap (recPI pir) (factor≡ {b₁} {b₂} {b₃}) ≡ 
      cfactor≡ pir
    βreccη₊       : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      { b : FT } → ap (recPI pir) (η₊ {b}) ≡ cη₊ pir
    βreccε₊       : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      { b : FT } → ap (recPI pir) (ε₊ {b}) ≡ cε₊ pir
    βreccrefe⋆    : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      { b : FT } → ap (recPI pir) (refe⋆ {b}) ≡ crefe⋆ pir
    βreccrefi⋆    : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      { b : FT } → ap (recPI pir) (refi⋆ {b}) ≡ crefi⋆ pir
    βreccrile⋆    : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      { b : FT } → ap (recPI pir) (rile⋆ {b}) ≡ crile⋆ pir
    βreccrili⋆    : {ℓ : Level} {C : Set ℓ} → (pir : PIR C) → 
      { b : FT } → ap (recPI pir) (rili⋆ {b}) ≡ crili⋆ pir

open PI public

------------------------------------------------------------------------------
-- Semantics I
-- The rationals are a model of PI

{--
unitPlus : (n : ℕ) -> (n + 0) ≡ n
unitPlus 0       = refl 0
unitPlus (suc m) = ap suc (unitPlus m)

sPlus : (n m : ℕ) -> suc (n + m) ≡ (n + suc m)
sPlus 0 m       = refl (suc m) 
sPlus (suc n) m = ap suc (sPlus n m)

commPlus : (m n : ℕ) -> (m + n) ≡ (n + m)
commPlus 0 n       = ! (unitPlus n)
commPlus (suc m) n = (ap suc (commPlus m n)) ∘ (sPlus n m)

assocPlus : (m n o : ℕ) ->((m + n) + o) ≡ (m + (n + o))
assocPlus 0 n o       = refl (n + o)
assocPlus (suc m) n o = ap suc (assocPlus m n o)

--

unitMult : (i : ℕ) → 1 * i ≡ i
unitMult 0       = refl 0
unitMult (suc i) = ap suc (unitMult i) 

mulSuc : (m n : ℕ) → m * suc n ≡ m + m * n
mulSuc 0 n       = refl 0
mulSuc (suc m) n = ap (λ x → suc n + x) (mulSuc m n) ∘ 
                   ap suc (! (assocPlus n m (m * n))) ∘ 
                   ap (λ x → suc (x + m * n)) (commPlus n m) ∘ 
                   ap suc (assocPlus m n (m * n))
                
annMult : (i : ℕ) → i * 0 ≡ 0
annMult 0       = refl 0
annMult (suc i) = annMult i

commMult : (i j : ℕ) → i * j ≡ j * i
commMult 0 j       = ! (annMult j) 
commMult (suc i) j = ap (λ x → j + x) (commMult i j) ∘ 
                     (! (mulSuc j i))

distrib : (i j k : ℕ) → (j + k) * i ≡ j * i + k * i
distrib i 0 k       = refl (k * i)
distrib i (suc j) k = ap (_+_ i) (distrib i j k) ∘ 
                      (! (assocPlus i (j * i) (k * i))) 


assocMult : (i j k : ℕ) → (i * j) * k ≡ i * (j * k)
assocMult 0 j k       = refl 0
assocMult (suc i) j k = distrib k j (i * j) ∘ 
                        ap (λ x → j * k + x) (assocMult i j k)
--}

--

toℚ : FT → ℚ
toℚ b = recPI (record {
          czero     = + 0 ÷ 1 ;
          cone      = + 1 ÷ 1 ;
          cplus     = {!!} ; --_+_ ; 
          ctimes    = {!!} ; --_*_ ;
          cneg      = {!!} ;
          crecip    = {!!} ;
          cunite₊≡  = {!!} ; --λ {c} → refl c ;
          cuniti₊≡  = {!!} ; --λ {c} → refl c ;
          cswap₊≡   = {!!} ; --λ {a b} → commPlus a b ;
          cassocl₊≡ = {!!} ; --λ {a b c} → ! (assocPlus a b c) ;
          cassocr₊≡ = {!!} ; --λ {a b c} → assocPlus a b c ;
          cunite⋆≡  = {!!} ; --λ {a} → unitMult a ;
          cuniti⋆≡  = {!!} ; --λ {a} → ! (unitMult a) ;
          cswap⋆≡   = {!!} ; --λ {a b} → commMult a b  ;
          cassocl⋆≡ = {!!} ; --λ {a b c} → ! (assocMult a b c) ;
          cassocr⋆≡ = {!!} ; --λ {a b c} → assocMult a b c ;
          cdistz≡   = {!!} ; --refl 0  ;
          cfactorz≡ = {!!} ; --refl 0 ;
          cdist≡    = {!!} ; --λ {a b c} → distrib c a b ;
          cfactor≡  = {!!} ; --λ {a b c} → ! (distrib c a b) ;
          cη₊       = {!!} ;
          cε₊       = {!!} ;
          crefe⋆    = {!!} ;
          crefi⋆    = {!!} ;
          crile⋆    = {!!} ;
          crili⋆    = {!!} 
        }) b

------------------------------------------------------------------------------

