module A3 where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

infix  4  _≡_     -- propositional equality
infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

------------------------------------------------------------------------------
-- Basic definitions

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

sym : ∀ {ℓ} {A : Set ℓ} {a b : A} → (a ≡ b) → (b ≡ a)
sym {a = a} {b = .a} (refl .a) = refl a

trans : ∀ {ℓ} {A : Set ℓ} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
trans {a = a} {b = .a} {c = .a} (refl .a) (refl .a) = refl a

_≡⟨_⟩_ : ∀ {ℓ} → {A : Set ℓ} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p ⟩ q = trans p q

bydef : ∀ {ℓ} → {A : Set ℓ} {x : A} → (x ≡ x)
bydef {ℓ} {A} {x} = refl x

_∎ : ∀ {ℓ} → {A : Set ℓ} (x : A) → (x ≡ x)
_∎ x = refl x

------------------------------------------------------------------------------
-- Level 0 

module Pi0 where

  -- types
  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
  
  -- values
  ⟦_⟧ : U → Set
  ⟦ ZERO ⟧        = ⊥
  ⟦ ONE ⟧         = ⊤
  ⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

  -- combinators 
  data _⟷_ : U → U → Set where
    unite₊  : {t : U} → PLUS ZERO t ⟷ t
    uniti₊  : {t : U} → t ⟷ PLUS ZERO t
    swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
    assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
    assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
    unite⋆  : {t : U} → TIMES ONE t ⟷ t
    uniti⋆  : {t : U} → t ⟷ TIMES ONE t
    swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
    assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
    assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
    distz   : {t : U} → TIMES ZERO t ⟷ ZERO
    factorz : {t : U} → ZERO ⟷ TIMES ZERO t
    dist    : {t₁ t₂ t₃ : U} → 
              TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) 
    factor  : {t₁ t₂ t₃ : U} → 
              PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
    id⟷     : {t : U} → t ⟷ t
    sym⟷    : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

------------------------------------------------------------------------------
-- Levels n+1 for all n should all be uniform
-- do level 1 explicitly though

module Pi1 where
  -- types
  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
    EQUIV : {t₁ t₂ : Pi0.U} → (t₁ Pi0.⟷ t₂) → Pi0.⟦ t₁ ⟧ → Pi0.⟦ t₂ ⟧ → U

  data Unite₊ {t : Pi0.U} : Pi0.⟦ Pi0.PLUS Pi0.ZERO t ⟧ → Pi0.⟦ t ⟧ → Set where
    path_unite₊ : (v₁ : Pi0.⟦ Pi0.PLUS Pi0.ZERO t ⟧) → (v₂ : Pi0.⟦ t ⟧) → Unite₊ v₁ v₂

  data Id⟷ {t : Pi0.U} : Pi0.⟦ t ⟧ → Pi0.⟦ t ⟧ → Set where
    path_id⟷ : (v₁ : Pi0.⟦ t ⟧) → (v₂ : Pi0.⟦ t ⟧) → Id⟷ v₁ v₂

  -- values
  mutual
    ⟦_⟧ : U → Set
    ⟦ ZERO ⟧          = ⊥
    ⟦ ONE ⟧           = ⊤
    ⟦ PLUS t₁ t₂ ⟧    = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
    ⟦ TIMES t₁ t₂ ⟧   = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
    ⟦ EQUIV c v₁ v₂ ⟧ = f c v₁ v₂

    f : {t₃ t₄ : Pi0.U} → (t₃ Pi0.⟷ t₄) → Pi0.⟦ t₃ ⟧ → Pi0.⟦ t₄ ⟧ → Set
    f Pi0.unite₊ (inj₁ ()) w₂
    f Pi0.unite₊ (inj₂ y) w₂ = Unite₊ (inj₂ y) w₂ × (y ≡ w₂)
    f Pi0.id⟷ w₁ w₂ = Id⟷ w₁ w₂ × (w₁ ≡ w₂)
    f (Pi0._◎_ {t₂ = s} x₁ x₂) w₁ w₂ = Σ Pi0.⟦ s ⟧ (λ t → f x₁ w₁ t × f x₂ t w₂)
    f c w₁ w₂ = ⊥ -- todo
 
  -- combinators 
  data _⟷_ : U → U → Set where
    unite₊  : {t : U} → PLUS ZERO t ⟷ t
    uniti₊  : {t : U} → t ⟷ PLUS ZERO t
    swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
    assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
    assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
    unite⋆  : {t : U} → TIMES ONE t ⟷ t
    uniti⋆  : {t : U} → t ⟷ TIMES ONE t
    swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
    assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
    assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
    distz   : {t : U} → TIMES ZERO t ⟷ ZERO
    factorz : {t : U} → ZERO ⟷ TIMES ZERO t
    dist    : {t₁ t₂ t₃ : U} → 
              TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) 
    factor  : {t₁ t₂ t₃ : U} → 
              PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
    id⟷     : {t : U} → t ⟷ t
    sym⟷    : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)
    lid     : {t₁ t₂ : Pi0.U} {v₁ : Pi0.⟦ t₁ ⟧} {v₂ : Pi0.⟦ t₂ ⟧} 
              {c : t₁ Pi0.⟷ t₂} → 
              EQUIV (Pi0.id⟷ Pi0.◎ c) v₁ v₂ ⟷ EQUIV c v₁ v₂

------------------------------------------------------------------------------
-- Level 2 explicitly...

module Pi2 where
  -- types
  data U : Set where
    ZERO  : U
    ONE   : U
    PLUS  : U → U → U
    TIMES : U → U → U
    EQUIV : {t₁ t₂ : Pi1.U} → (t₁ Pi1.⟷ t₂) → Pi1.⟦ t₁ ⟧ → Pi1.⟦ t₂ ⟧ → U

  data Unite₊ {t : Pi1.U} : Pi1.⟦ Pi1.PLUS Pi1.ZERO t ⟧ → Pi1.⟦ t ⟧ → Set where
    path_unite₊ : (v₁ : Pi1.⟦ Pi1.PLUS Pi1.ZERO t ⟧) → (v₂ : Pi1.⟦ t ⟧) → Unite₊ v₁ v₂

  data Id⟷ {t : Pi1.U} : Pi1.⟦ t ⟧ → Pi1.⟦ t ⟧ → Set where
    path_id⟷ : (v₁ : Pi1.⟦ t ⟧) → (v₂ : Pi1.⟦ t ⟧) → Id⟷ v₁ v₂

  -- values
  mutual 

    ⟦_⟧ : U → Set
    ⟦ ZERO ⟧          = ⊥
    ⟦ ONE ⟧           = ⊤
    ⟦ PLUS t₁ t₂ ⟧    = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
    ⟦ TIMES t₁ t₂ ⟧   = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
    ⟦ EQUIV c v₁ v₂ ⟧ = f c v₁ v₂

    f : {t₁ t₂ : Pi1.U} → (t₁ Pi1.⟷ t₂) → Pi1.⟦ t₁ ⟧ → Pi1.⟦ t₂ ⟧ → Set
    f (Pi1.id⟷ {t}) v v' = Id⟷ {t} v v' × (v ≡ v')
    f (Pi1._◎_ {t₂ = t₂} c₁ c₂) v₁ v₃ = 
      Σ[ v₂ ∈ Pi1.⟦ t₂ ⟧ ] (f c₁ v₁ v₂ × f c₂ v₂ v₃)
    f (Pi1.lid {t₁} {t₂} {v₁} {v₂} {c})
      (.v₁ , ((Pi1.path_id⟷ .v₁ .v₁ , refl .v₁) , q)) q' = (q ≡ q')
    f c v₁ v₂ = ⊥ -- to do 

  -- combinators 
  data _⟷_ : U → U → Set where
    unite₊  : {t : U} → PLUS ZERO t ⟷ t
    uniti₊  : {t : U} → t ⟷ PLUS ZERO t
    swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
    assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
    assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
    unite⋆  : {t : U} → TIMES ONE t ⟷ t
    uniti⋆  : {t : U} → t ⟷ TIMES ONE t
    swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
    assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
    assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
    distz   : {t : U} → TIMES ZERO t ⟷ ZERO
    factorz : {t : U} → ZERO ⟷ TIMES ZERO t
    dist    : {t₁ t₂ t₃ : U} → 
              TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) 
    factor  : {t₁ t₂ t₃ : U} → 
              PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
    id⟷     : {t : U} → t ⟷ t
    sym⟷    : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
    _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)
    lid     : {t₁ t₂ : Pi1.U} {v₁ : Pi1.⟦ t₁ ⟧} {v₂ : Pi1.⟦ t₂ ⟧} 
              {c : t₁ Pi1.⟷ t₂} → 
              EQUIV (Pi1.id⟷ Pi1.◎ c) v₁ v₂ ⟷ EQUIV c v₁ v₂

------------------------------------------------------------------------------

