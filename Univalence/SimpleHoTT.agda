{-# OPTIONS --without-K #-}
module SimpleHoTT where

open import Data.Empty
open import Data.Sum renaming (map to _⊎→_)
open import Function renaming (_∘_ to _○_)

infixr 8  _∘_   -- path composition
infix  4  _≡_   -- propositional equality
infix  2  _∎       -- equational reasoning for paths
infixr 2  _≡⟨_⟩_   -- equational reasoning for paths

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

-- tools for coproducts (Sec. 2.12) 

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
