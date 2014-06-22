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
    EQUIV : {t₁ t₂ : Pi0.U} → Pi0.⟦ t₁ ⟧ → (t₁ Pi0.⟷ t₂) → Pi0.⟦ t₂ ⟧ → U

  data Unite₊ {t : Pi0.U} : ⊥ ⊎ Pi0.⟦ t ⟧ → Pi0.⟦ t ⟧ → Set where
    path_unite₊ : (v₁ : ⊥ ⊎ Pi0.⟦ t ⟧) → (v₂ : Pi0.⟦ t ⟧) → Unite₊ v₁ v₂

  data Id⟷ {t : Pi0.U} : Pi0.⟦ t ⟧ → Pi0.⟦ t ⟧ → Set where
    path_id⟷ : (v₁ : Pi0.⟦ t ⟧) → (v₂ : Pi0.⟦ t ⟧) → Id⟷ v₁ v₂

  -- values
  ⟦_⟧ : U → Set
  ⟦ ZERO ⟧          = ⊥
  ⟦ ONE ⟧           = ⊤
  ⟦ PLUS t₁ t₂ ⟧    = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ TIMES t₁ t₂ ⟧   = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ EQUIV (inj₁ ()) Pi0.unite₊ v' ⟧ 
  ⟦ EQUIV (inj₂ v) Pi0.unite₊ v' ⟧ = Unite₊ (inj₂ v) v' × (v ≡ v')
  ⟦ EQUIV v₁ Pi0.uniti₊ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.swap₊ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.assocl₊ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.assocr₊ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.unite⋆ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.uniti⋆ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.swap⋆ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.assocl⋆ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.assocr⋆ v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.distz v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.factorz v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.dist v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ Pi0.factor v₂ ⟧ = {!!}
  ⟦ EQUIV v Pi0.id⟷ v' ⟧ = Id⟷ v v' × (v ≡ v')
  ⟦ EQUIV v₁ (Pi0.sym⟷ c) v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ (Pi0._◎_ {t₂ = t₂} c₁ c₂) v₃ ⟧ = 
    Σ[ v₂ ∈ Pi0.⟦ t₂ ⟧ ] (⟦ EQUIV v₁ c₁ v₂ ⟧ × ⟦ EQUIV v₂ c₂ v₃ ⟧)
  ⟦ EQUIV v₁ (c₁ Pi0.⊕ c₂) v₂ ⟧ = {!!}
  ⟦ EQUIV v₁ (c₁ Pi0.⊗ c₂) v₂ ⟧ = {!!} 
  
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
              EQUIV v₁ (Pi0.id⟷ Pi0.◎ c) v₂ ⟷ EQUIV v₁ c v₂

------------------------------------------------------------------------------

