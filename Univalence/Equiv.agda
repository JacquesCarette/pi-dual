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
infixr 5 _●_

infix 8 _⊎≃_
infixr 7 _×≃_

------------------------------------------------------------------------------
-- Extensional equivalence of functions

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} →
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

refl∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} → (f ∼ f)
refl∼ {A} {B} {f} x = refl

sym∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = sym (H x)

trans∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = trans (H x)  (G x)

------------------------------------------------------------------------------
-- Quasi-equivalences a la HoTT:
record isqinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) :
  Set (ℓ ⊔ ℓ') where
  constructor qinv
  field
    g : B → A
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id

-- We explicitly choose quasi-equivalences, even though these
-- these are not a proposition.  This is fine for us, as we're
-- explicitly looking at equivalences-of-equivalences, and we
-- so we prefer a symmetric definition over a truncated one.

------------------------------------------------------------------------------
-- Equivalences between sets A and B: a function f and a quasi-inverse for f.

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isqinv

id≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
id≃ = (id , qinv id (λ _ → refl) (λ _ → refl))

sym≃ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A ≃ B) → B ≃ A
sym≃ (A→B , equiv) = e.g , qinv A→B e.β e.α
  where module e = isqinv equiv

trans≃ :  ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → A ≃ B → B ≃ C → A ≃ C
trans≃ (f , feq) (g , geq) = (g ∘ f) , (qinv g′ α' β')
  where
    module fm = isqinv feq
    module gm = isqinv geq
    g′ = fm.g ∘ gm.g
    α' = λ x → trans (cong g (fm.α (gm.g x))) (gm.α x)
    β' = λ x → trans (cong fm.g (gm.β (f x))) (fm.β x)

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

p∘!p≡id : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {p : A ≃ B} → (_⋆_ (trans≃ p (sym≃ p))) ∼ (_⋆_ id≃)
p∘!p≡id {p = p} = isqinv.β (proj₂ p)

!p∘p≡id : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {p : A ≃ B} → (_⋆_ (trans≃ (sym≃ p) p)) ∼ (_⋆_ id≃)
!p∘p≡id {p = p} = p∘!p≡id {p = sym≃ p}

-- equivalences are injective

inj≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (eq : A ≃ B) → (x y : A) → (eq ⋆ x ≡ eq ⋆ y → x ≡ y)
inj≃ (f , qinv g α β) x y p = trans
  (sym (β x)) (trans
  (cong g p) (
  β y))

-- equivalence is a congruence for plus/times

-- ⊕

_⊎∼_ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
  {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ∘ finv ∼ id) → (β : g ∘ ginv ∼ id) →
  (f ⊎→ g) ∘ (finv ⊎→ ginv) ∼ id {A = C ⊎ D}
_⊎∼_ α β (inj₁ x) = cong inj₁ (α x)
_⊎∼_ α β (inj₂ y) = cong inj₂ (β y)

_⊎≃_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
  → A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)
(fp , eqp) ⊎≃ (fq , eqq) =
  Data.Sum.map fp fq ,
  qinv (P.g ⊎→ Q.g) (P.α ⊎∼ Q.α) (P.β ⊎∼ Q.β)
  where module P = isqinv eqp
        module Q = isqinv eqq

-- ⊗

_×∼_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
  {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
  (α : f ∘ finv ∼ id) → (β : g ∘ ginv ∼ id) →
  (f ×→ g) ∘ (finv ×→ ginv) ∼ id {A = C × D}
_×∼_ α β (x , y) = cong₂ _,_ (α x) (β y)

_×≃_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
  → A ≃ C → B ≃ D → (A × B) ≃ (C × D)
(fp , eqp) ×≃ (fq , eqq) =
  Data.Product.map fp fq ,
  qinv
    (P.g ×→ Q.g)
    (_×∼_ {f = fp} {g = fq} P.α Q.α)
    (_×∼_ {f = P.g} {g = Q.g} P.β Q.β)
  where module P = isqinv eqp
        module Q = isqinv eqq

------------------------------------------------------------------------------
