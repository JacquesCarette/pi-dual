{-# OPTIONS --without-K #-}

module Equiv where

open import Level using (_⊔_)
open import Function using (_∘_; id)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂) renaming (map to _×→_) 
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

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
-- Equivalences a la HoTT:
record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor iseq
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    h : B → A
    β : (h ∘ f) ∼ id
    
------------------------------------------------------------------------------
-- Equivalences between sets A and B: a function f and a quasi-inverse for f. 

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

id≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
id≃ = (id , iseq id (λ _ → refl) id (λ _ → refl))

g-left-inv : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} →
  (eq : A ≃ B) → (isequiv.g (proj₂ eq) ∘ proj₁ eq ∼ id)
g-left-inv (f , iseq g α h β) = pf
  where
    open ≡-Reasoning
    pf : (g ∘ f) ∼ id
    pf x = begin (
      g (f x)
        ≡⟨ sym (β (g (f x))) ⟩
      h (f (g (f x)))
        ≡⟨ cong h (α (f x)) ⟩
      h (f x)
        ≡⟨ β x ⟩
      x ∎)
      
sym≃ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A ≃ B) → B ≃ A
sym≃ (A→B , equiv) = e.g , (iseq A→B (g-left-inv (A→B , equiv)) A→B e.α)
  where module e = isequiv equiv
  
trans≃ :  ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → A ≃ B → B ≃ C → A ≃ C
trans≃ (f , feq) (g , geq) = (g ∘ f) , (iseq g′ α' h′ β')
  where
    module fm = isequiv feq
    module gm = isequiv geq
    g′ = fm.g ∘ gm.g
    h′ = fm.h ∘ gm.h
    α' = λ x → trans (cong g (fm.α (gm.g x))) (gm.α x)
    β' = λ x → trans (cong fm.h (gm.β (f x))) (fm.β x)

-- more convenient infix version, flipped

_●_ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → B ≃ C → A ≃ B → A ≃ C
a ● b = trans≃ b a

≃IsEquiv : IsEquivalence {Level.suc Level.zero} {Level.zero} {Set} _≃_
≃IsEquiv = record {
  refl = id≃ ;
  sym = sym≃ ;
  trans = trans≃ 
  }

------------------------------------------------------------------------------
-- A few properties of equivalences

_⋆_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A ≃ B) → (x : A) → B
(f , _) ⋆ x = f x 

-- there-and-back is identity

p∘!p≡id : {A B : Set} {p : A ≃ B} → (_⋆_ (trans≃ p (sym≃ p))) ∼ (_⋆_ id≃)
p∘!p≡id {p = p} =  g-left-inv p

!p∘p≡id : {A B : Set} {p : A ≃ B} → (_⋆_ (trans≃ (sym≃ p) p)) ∼ (_⋆_ id≃)
!p∘p≡id {p = p} = p∘!p≡id {p = sym≃ p}

-- equivalences are injective

inj≃ : {A B : Set} → (eq : A ≃ B) → (x y : A) → (eq ⋆ x ≡ eq ⋆ y → x ≡ y)
inj≃ (f , iseq g α h β) x y p = trans
  (sym (β x)) (trans
  (cong h p) (
  β y))
  
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
  iseq (P.g ⊎→ Q.g) (P.α ⊎∼ Q.α) (P.h ⊎→ Q.h) (P.β ⊎∼ Q.β)
  where module P = isequiv eqp
        module Q = isequiv eqq

-- ⊗

_×∼_ : {A B C D : Set} {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ∘ finv ∼ id) → (β : g ∘ ginv ∼ id) → 
  (f ×→ g) ∘ (finv ×→ ginv) ∼ id {A = C × D}
_×∼_ α β (x , y) = cong₂ _,_ (α x) (β y)
 
path× : {A B C D : Set} → A ≃ C → B ≃ D → (A × B) ≃ (C × D)
path× {A} {B} {C} {D} (fp , eqp) (fq , eqq) = 
  Data.Product.map fp fq , 
  iseq 
    (P.g ×→ Q.g) 
    (_×∼_ {f = fp} {g = fq} P.α Q.α)
    (P.h ×→ Q.h)
    (_×∼_ {f = P.h} {g = Q.h} P.β Q.β)
  where module P = isequiv eqp
        module Q = isequiv eqq

------------------------------------------------------------------------------

