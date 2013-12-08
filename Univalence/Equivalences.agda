{-# OPTIONS --without-K #-}
module Equivalences where

open import Agda.Prim
open import Data.Empty
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Function renaming (_∘_ to _○_)

open import HoTT

infix  4  _∼_   -- homotopy between two functions 
infix  4  _≃_   -- type of equivalences
infix  2  _∎≃      -- equational reasoning for equivalences
infixr 2  _≃⟨_⟩_   -- equational reasoning for equivalences

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

