{-# OPTIONS --without-K #-}

module Equiv where

open import Level using (_⊔_)
open import Function using (_∘_; id)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product using (Σ; _×_; _,_) renaming (map to _×→_) 
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

infix 4 _∼_
infix 4 _≃_
infixl 4 _●_

------------------------------------------------------------------------------
-- Extensional equivalence of functions

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

refl∼ : {A B : Set} {f : A → B} → (f ∼ f)
refl∼ {A} {B} {f} x = refl

sym∼ : {A B : Set} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = sym (H x) 

trans∼ : {A B : Set} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = trans (H x)  (G x)

------------------------------------------------------------------------------
-- Quasi-inverses a la HoTT: given a function f : A → B, a
-- quasi-inverse is a function g : B → A together two proofs that the
-- compositions of f and g are extensionally equivalent to the
-- identity

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {A = A} id
idqinv = record {
           g = id ;
           α = λ b → refl ; 
           β = λ a → refl
         }
         
------------------------------------------------------------------------------
-- Equivalences between sets A and B: a function f and a quasi-inverse for f. 

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) qinv

id≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
id≃ = (id , idqinv)

sym≃ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A ≃ B) → B ≃ A
sym≃ (A→B , equiv) = e.g , mkqinv A→B e.β e.α
  where module e = qinv equiv

trans≃ : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
trans≃ (f , feq) (g , geq) = (g ∘ f) , (mkqinv inv α' β')
  where
    module fm = qinv feq
    module gm = qinv geq
    inv = fm.g ∘ gm.g
    α' = λ x → trans (cong g (fm.α (gm.g x))) (gm.α x)
    β' = λ x → trans (cong fm.g (gm.β (f x))) (fm.β x)

-- more convenient infix version, flipped

_●_ : {A B C : Set} → B ≃ C → A ≃ B → A ≃ C
a ● b = trans≃ b a

≃IsEquiv : IsEquivalence {Level.suc Level.zero} {Level.zero} {Set} _≃_
≃IsEquiv = record {
  refl = id≃ ;
  sym = sym≃ ;
  trans = trans≃ 
  }

------------------------------------------------------------------------------
-- A few properties of equivalences

_⋆_ : {A B : Set} → (A ≃ B) → (x : A) → B
(f , _) ⋆ x = f x 

-- there-and-back is identity

p∘!p≡id : {A B : Set} {p : A ≃ B} → (_⋆_ (trans≃ p (sym≃ p))) ∼ (_⋆_ id≃)
p∘!p≡id {p = f , mkqinv q _ β} = β

!p∘p≡id : {A B : Set} {p : A ≃ B} → (_⋆_ (trans≃ (sym≃ p) p)) ∼ (_⋆_ id≃)
!p∘p≡id {p = p} = p∘!p≡id {p = sym≃ p}

-- equivalences are injective

inj≃ : {A B : Set} → (eq : A ≃ B) → (x y : A) → (eq ⋆ x ≡ eq ⋆ y → x ≡ y)
inj≃ (f , mkqinv g α β) x y p = trans (sym (β x)) (trans (cong g p) (β y))

-- equivalence is a congruence for plus/times

-- ⊕

_⊎∼_ : {A B C D : Set} {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ∘ finv ∼ id) → (β : g ∘ ginv ∼ id) → 
  (f ⊎→ g) ∘ (finv ⊎→ ginv) ∼ id {A = C ⊎ D}
_⊎∼_ α β (inj₁ x) = cong inj₁ (α x) 
_⊎∼_ α β (inj₂ y) = cong inj₂ (β y)

path⊎ : {A B C D : Set} → A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)
path⊎ (fp , eqp) (fq , eqq) = 
  Data.Sum.map fp fq , 
  mkqinv (P.g ⊎→ Q.g) (P.α ⊎∼ Q.α) (P.β ⊎∼ Q.β)
  where module P = qinv eqp
        module Q = qinv eqq

-- ⊗

_×∼_ : {A B C D : Set} {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ∘ finv ∼ id) → (β : g ∘ ginv ∼ id) → 
  (f ×→ g) ∘ (finv ×→ ginv) ∼ id {A = C × D}
_×∼_ α β (x , y) = cong₂ _,_ (α x) (β y)
 
path× : {A B C D : Set} → A ≃ C → B ≃ D → (A × B) ≃ (C × D)
path× {A} {B} {C} {D} (fp , eqp) (fq , eqq) = 
  Data.Product.map fp fq , 
  mkqinv 
    (P.g ×→ Q.g) 
    (_×∼_ {A} {B} {C} {D} {fp} {P.g} {fq} {Q.g} P.α Q.α) 
    (_×∼_ {C} {D} {A} {B} {P.g} {fp} {Q.g} {fq} P.β Q.β)
  where module P = qinv eqp
        module Q = qinv eqq

------------------------------------------------------------------------------

