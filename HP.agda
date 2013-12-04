{-# OPTIONS --without-K #-}

module HP where

-- Pi as a higher-order inductive type

open import Agda.Prim
open import Data.Empty
open import Data.Unit
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
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning
infix  2  _∎≃      -- equational reasoning for equivalences
infixr 2  _≃⟨_⟩_   -- equational reasoning for equivalences

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
ap f p = 
  pathInd 
    (λ {x} {y} _ → f x ≡ f y) 
    (λ x → refl (f x))
    p

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

-- Abbreviations for equivalence compositions

_≃⟨_⟩_ : (A : Set) {B C : Set} → (A ≃ B) → (B ≃ C) → (A ≃ C) 
_ ≃⟨ p ⟩ q = trans≃ p q

_∎≃ : {ℓ : Level} {A : Set ℓ} → A ≃ A
_∎≃ {ℓ} {A} = id≃ {ℓ} {A}

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
-- Type equivalences

-- swap₊

swap₊ : {A B : Set} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

swapswap₊ : {A B : Set} → swap₊ ○ swap₊ {A} {B} ∼ id
swapswap₊ (inj₁ a) = refl (inj₁ a)
swapswap₊ (inj₂ b) = refl (inj₂ b)

swap₊≃ : {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
swap₊≃ = (swap₊ , equiv₁ (mkqinv swap₊ swapswap₊ swapswap₊))

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

unite₊≃ : {A : Set} → (⊥ ⊎ A) ≃ A
unite₊≃ = (unite₊ , mkisequiv uniti₊ refl uniti₊ uniti₊∘unite₊)

uniti₊≃ : {A : Set} → A ≃ (⊥ ⊎ A)
uniti₊≃ = uniti₊ , mkisequiv unite₊ uniti₊∘unite₊ unite₊ unite₊∙uniti₊

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

  record pi {ℓ : Level} {C : Set ℓ} : Set (lsuc ℓ) where
    field
      czero : C
      cone : C
      cplus : C → C → C
      ctimes : C → C → C
      cunite₊≡ : { b : C } → cplus czero b ≡ b
      cuniti₊≡ : { b : C } → b ≡ cplus czero b
      cswap₊≡ : { b₁ b₂ : C } → cplus b₁ b₂ ≡ cplus b₂ b₁
      cassocl₊≡ : { b₁ b₂ b₃ : C } → 
                  cplus b₁ (cplus b₂ b₃) ≡ cplus (cplus b₁ b₂) b₃
      cassocr₊≡ : { b₁ b₂ b₃ : C } → 
                  cplus (cplus b₁ b₂) b₃ ≡ cplus b₁ (cplus b₂ b₃)
      cunite⋆≡  : { b : C } → ctimes cone b ≡ b
      cuniti⋆≡  : { b : C } → b ≡ ctimes cone b
      cswap⋆≡   : { b₁ b₂ : C } → ctimes b₁ b₂ ≡ ctimes b₂ b₁
      cassocl⋆≡ : { b₁ b₂ b₃ : C } → 
                  ctimes b₁ (ctimes b₂ b₃) ≡ ctimes (ctimes b₁ b₂) b₃
      cassocr⋆≡ : { b₁ b₂ b₃ : C } → 
                  ctimes (ctimes b₁ b₂) b₃ ≡ ctimes b₁ (ctimes b₂ b₃)
      cdistz≡   : { b : C } → ctimes czero b ≡ czero
      cfactorz≡ : { b : C } → czero ≡ ctimes czero b
      cdist≡ : { b₁ b₂ b₃ : C } → 
               ctimes (cplus b₁ b₂) b₃ ≡ cplus (ctimes b₁ b₃) (ctimes b₂ b₃)
      cfactor≡  : { b₁ b₂ b₃ : C } → 
                   cplus (ctimes b₁ b₃) (ctimes b₂ b₃) ≡ ctimes (cplus b₁ b₂) b₃

  open pi

  recPI : {ℓ : Level} {C : Set ℓ} → (pi {ℓ} {C}) → FT → C
  recPI {ℓ} {C} pir ZERO* = czero pir
  recPI {ℓ} {C} pir ONE* = cone pir
  recPI {ℓ} {C} pir (PLUS* B₁ B₂) = 
    cplus pir (recPI {ℓ} {C} pir B₁) (recPI {ℓ} {C} pir B₂)
  recPI {ℓ} {C} pir (TIMES* B₁ B₂) = 
    ctimes pir (recPI {ℓ} {C} pir B₁) (recPI {ℓ} {C} pir B₂)

  postulate
    βreccunite₊≡ : {ℓ : Level} {C : Set ℓ} → (pir : pi {ℓ} {C}) → 
      ∀ {b} → ap {y = PLUS ONE b} (recPI pir) unite₊≡ ≡ cunite₊≡ pir  --cunite₊≡

{--    βreccuniti₊≡ 
    βreccswap₊≡ 
    βreccassocl₊≡ 
    βreccassocr₊≡
    βreccunite⋆≡ 
    βreccuniti⋆≡ 
    βreccswap⋆≡ 
    βreccassocl⋆≡ 
    βreccassocr⋆≡
    βreccdistz≡ 
    βreccfactorz≡  
    βreccdist≡ 
    βreccfactor≡ 
--}

open PI public

------------------------------------------------------------------------------
-- path2equiv



------------------------------------------------------------------------------
-- Sec. 2.10: Universes; univalence

idtoeqv : {A B : Set} → (A ≡ B) → (A ≃ B)
idtoeqv {A} {B} p = 
  pathInd 
    (λ {A'} {B'} _ → A' ≃ B')
    (λ _ → id≃)
    {A} {B} p

postulate 
  univalence : {A B : Set} → (A ≡ B) ≃ (A ≃ B)

------------------------------------------------------------------------------
