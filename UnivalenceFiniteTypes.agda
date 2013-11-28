{-# OPTIONS --without-K #-}
{-# OPTIONS --no-termination-check #-}

module UnivalenceFiniteTypes where

open import Agda.Prim
open import Data.Empty
open import Data.Maybe
open import Data.Unit
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Function renaming (_∘_ to _○_)

infixr 8  _∘_   -- path composition
infix  4  _≡_   -- propositional equality
infix  4  _∼_   -- homotopy between two functions 
infix  4  _≃_   -- type of equivalences
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

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
  assocl⋆⇛ : { b₁ b₂ b₃ : FT } → TIMES b₁ (TIMES b₂ b₃) ⇛ TIMES (TIMES b₁ b₂) b₃
  assocr⋆⇛ : { b₁ b₂ b₃ : FT } → TIMES (TIMES b₁ b₂) b₃ ⇛ TIMES b₁ (TIMES b₂ b₃)
  -- distributity
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

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

_∘_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {u} {A} {x} {y} {z} p q = 
  pathInd {u}
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd -- on p
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

ap2 : ∀ {ℓ ℓ' ℓ''} → {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} {x₁ y₁ : A} {x₂ y₂ : B} → 
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

-- Abbreviations

_≡⟨_⟩_ : ∀ {u} → {A : Set u} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p ⟩ q = p ∘ q

bydef : ∀ {u} → {A : Set u} {x : A} → (x ≡ x)
bydef {u} {A} {x} = refl x

_∎ : ∀ {u} → {A : Set u} (x : A) → x ≡ x
_∎ x = refl x

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
assocl₊equiv = assocl₊ , mkisequiv assocr₊ assocl₊∘assocr₊ assocr₊ assocr₊∘assocl₊

assocr₊equiv : {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
assocr₊equiv = assocr₊ , mkisequiv assocl₊ assocr₊∘assocl₊ assocl₊ assocl₊∘assocr₊

-- 

_⊎∼_ : {A B C D : Set} {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ○ finv ∼ id) → (β : g ○ ginv ∼ id) → 
  (f ⊎→ g) ○ (finv ⊎→ ginv) ∼ id {A = C ⊎ D}
_⊎∼_ α β (inj₁ x) = ap inj₁ (α x) 
_⊎∼_ α β (inj₂ y) = ap inj₂ (β y)

_×∼_ : {A B C D : Set} {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ○ finv ∼ id) → (β : g ○ ginv ∼ id) → 
  (f ×→ g) ○ (finv ×→ ginv) ∼ id {A = C × D}
_×∼_ α β (x , y) = ap2 _,_ (α x) (β y)
 
path⊎ : {A B C D : Set} → A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)
path⊎ (fp , eqp) (fq , eqq) = 
  Data.Sum.map fp fq , 
  mkisequiv (P.g ⊎→ Q.g) (P.α ⊎∼ Q.α) (P.h ⊎→ Q.h) (P.β ⊎∼ Q.β)
  where module P = isequiv eqp
        module Q = isequiv eqq
        
path× : {A B C D : Set} → A ≃ C → B ≃ D → (A × B) ≃ (C × D)
path× {A} {B} {C} {D} (fp , eqp) (fq , eqq) = 
  Data.Product.map fp fq , 
--  mkisequiv (P.g ×→ Q.g) (P.α ×∼ Q.α) (P.h ×→ Q.h) (P.β ×∼ Q.β)
  mkisequiv (P.g ×→ Q.g) (_×∼_ {A} {B} {C} {D} {fp} {P.g} {fq} {Q.g} P.α Q.α) (P.h ×→ Q.h) (_×∼_ {C} {D} {A} {B} {P.h} {fp} {Q.h} {fq} P.β Q.β)
  where module P = isequiv eqp
        module Q = isequiv eqq
-- Now map each combinator to the corresponding equivalence

path2equiv : {B₁ B₂ : FT} → (B₁ ⇛ B₂) → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧)
path2equiv unite₊⇛ = unite₊equiv
path2equiv uniti₊⇛ = uniti₊equiv
path2equiv swap₊⇛ = swap₊equiv
path2equiv assocl₊⇛ = assocl₊equiv
path2equiv assocr₊⇛ = assocr₊equiv
path2equiv unite⋆⇛ = unite⋆equiv
path2equiv uniti⋆⇛ = uniti⋆equiv
path2equiv swap⋆⇛ = swap⋆equiv
path2equiv assocl⋆⇛ = {!!}
path2equiv assocr⋆⇛ = {!!}
path2equiv distz⇛ = {!!}
path2equiv factorz⇛ = {!!}
path2equiv dist⇛ = {!!}
path2equiv factor⇛ = {!!}
path2equiv id⇛ = id , mkisequiv id refl id refl
path2equiv (sym⇛ p) = sym≃ (path2equiv p)
path2equiv (p ◎ q) = trans≃ (path2equiv p) (path2equiv q) 
path2equiv (p ⊕ q) = path⊎ (path2equiv p) (path2equiv q)
path2equiv (p ⊗ q) = path× (path2equiv p) (path2equiv q) 

-- Reverse direction

max : ⊤ ⊎ ℕ → ⊤ ⊎ ℕ → ⊤ ⊎ ℕ
max (inj₁ tt) b = b
max (inj₂ y) (inj₁ tt) = inj₂ y
max (inj₂ x) (inj₂ y) = inj₂ (x ⊔ℕ y)

dmult : ⊤ ⊎ ℕ → ⊤ ⊎ ℕ → ⊤ ⊎ ℕ
dmult (inj₁ tt) _ = inj₁ tt
dmult _ (inj₁ tt) = inj₁ tt
dmult (inj₂ x) (inj₂ y) = inj₂ (x * y)

degree : (B : FT) → ⊤ ⊎ ℕ -- ⊤ for -∞ for the degree of ZERO
degree ZERO = inj₁ tt
degree ONE = inj₂ zero
degree (PLUS b₀ b₁) =  max (degree b₀) (degree b₁)
degree (TIMES b₀ b₁) = dmult (degree b₀) (degree b₁)

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

-- normalize a finite type to (1 + (1 + (1 + ... + (1 + 0) ... )))
-- a bunch of ones ending with zero with left biased + in between
normalize : FT → FT
normalize ZERO = ZERO
normalize ONE = PLUS ONE ZERO
normalize (PLUS B₁ B₂) with normalize B₁
... | ZERO = normalize B₂ 
... | ONE = PLUS ONE (normalize B₂) 
... | PLUS B₃ B₄ = normalize (PLUS B₃ (PLUS B₄ B₂)) 
... | TIMES B₃ B₄ = normalize (PLUS B₂ (TIMES B₃ B₄))
normalize (TIMES B₁ B₂) with normalize B₁
... | ZERO = ZERO
... | ONE  = normalize B₂
... | PLUS B₃ B₄ = normalize (PLUS (TIMES B₃ B₂) (TIMES B₄ B₂))
... | TIMES B₃ B₄ = normalize (TIMES B₃ (TIMES B₄ B₂))

normalizeC : {B : FT} → ⟦ normalize B ⟧ ≃ ⟦ B ⟧
normalizeC {ZERO} = id≃
normalizeC {ONE} = {!!}
normalizeC {PLUS B₁ B₂} = {!!}
normalizeC {TIMES B₁ B₂} = {!!} 

⊥⇛ZERO : {B : FT} → ⟦ normalize B ⟧ ≃ ⊥ → B ⇛ ZERO
⊥⇛ZERO {ZERO} equiv = id⇛
⊥⇛ZERO {ONE} (f , feq) with equiv₂ feq
... | mkqinv g α β with f (inj₁ tt) 
... | () 
⊥⇛ZERO {PLUS B₁ B₂} equiv = {!!}
⊥⇛ZERO {TIMES B₁ B₂} equiv with normalize B₁ | normalize (TIMES B₁ B₂)
... | ZERO | ZERO = {!!} 
... | NB₁ | _ = {!!} 


equiv2path : {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → (B₁ ⇛ B₂)
equiv2path {B₁} {B₂} (f , feq) with equiv₂ feq
equiv2path {ZERO} {ZERO} (f , feq) | mkqinv g α β = id⇛
equiv2path {ZERO} {B} (f , feq) | mkqinv g α β with witness B 
... | nothing = {!!} 
... | just b with g b
... | () 
{--
equiv2path {ZERO} {ZERO} (f , feq) | mkqinv g α β = id⇛
equiv2path {ZERO} {ONE} (f , feq) | mkqinv g α β with g tt 
... | () 
equiv2path {ZERO} {PLUS ZERO ZERO} (f , feq) | mkqinv g α β = uniti₊⇛
equiv2path {ZERO} {PLUS ZERO ONE} (f , feq) | mkqinv g α β with g (inj₂ tt)
... | ()
equiv2path {ZERO} {PLUS ZERO B₂} (f , feq) | mkqinv g α β with degree B₂ 
equiv2path {ZERO} {PLUS ZERO B₂} (f , feq) | mkqinv g α β | inj₁ tt =  
  equiv2path ({!!} , {!!}) ◎ uniti₊⇛ {B₂}
equiv2path {ZERO} {PLUS ZERO B₂} (f , feq) | mkqinv g α β | inj₂ y = {!!}
equiv2path {ZERO} {PLUS ONE B₃} (f , feq) | mkqinv g α β = {!!}
equiv2path {ZERO} {PLUS (PLUS B₂ B₃) B₄} (f , feq) | mkqinv g α β = {!!}
equiv2path {ZERO} {PLUS (TIMES B₂ B₃) B₄} (f , feq) | mkqinv g α β = {!!} 
equiv2path {ZERO} {TIMES B₂ B₃} (f , feq) | mkqinv g α β = {!!}
--} 
equiv2path {ONE} {ZERO} (f , feq) | mkqinv g α β with f tt
... | ()
equiv2path {ONE} {ONE} (f , feq) | mkqinv g α β = id⇛
equiv2path {ONE} {PLUS B₂ B₃} (f , feq) | mkqinv g α β with f tt
equiv2path {ONE} {PLUS B₂ B₃} (f , feq) | mkqinv g α β | inj₁ x = {!!}
equiv2path {ONE} {PLUS B₂ B₃} (f , feq) | mkqinv g α β | inj₂ y = {!!}
equiv2path {ONE} {TIMES B₂ B₃} (f , feq) | mkqinv g α β = 
  {!!}
  -- f : ⊤ → ⟦ B₂ ⟧ × ⟦ B₃ ⟧
  -- g : ⟦ B₂ ⟧ × ⟦ B₃ ⟧ → ⊤ 
  -- α : (f ○ g) ∼ id
  -- β : (g ○ f) ∼ id
equiv2path {PLUS ZERO B₁} {B₂} (f , feq) | mkqinv g α β = {!!}
  -- f : ⟦ ⊥ ⟧ ⊎ ⟦ B₁ ⟧ → ⟦ B₂ ⟧
  -- g : ⟦ B₂ ⟧ → ⟦ ⊥ ⟧ ⊎ ⟦ B₁ ⟧ 
  -- α b₂ : f (g b₂) ≡ b₂
  -- β (inj₂ b₁) : g (f (inj₂ b₁)) ≡ inj₂ b₁
  -- can we use α and β to prove that B₁ must be equal to B₂
  -- and in that case we can use unite₊⇛ to fill the above hole
equiv2path {PLUS B₁ B₂} {B₃} (f , feq) | mkqinv g α β = {!!}
equiv2path {TIMES B₁ B₂} {ZERO} (f , feq) | mkqinv g α β = {!!}
equiv2path {TIMES B₁ B₂} {ONE} (f , feq) | mkqinv g α β = {!!}
equiv2path {TIMES B₁ B₂} {PLUS B₃ B₄} (f , feq) | mkqinv g α β = {!!}
equiv2path {TIMES B₁ B₂} {TIMES B₃ B₄} (f , feq) | mkqinv g α β = {!!}

-- univalence

univalence : {B₁ B₂ : FT} → (B₁ ⇛ B₂) ≃ (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) 
univalence = (path2equiv , equiv₁ (mkqinv equiv2path {!!} {!!}))

------------------------------------------------------------------------------
