-- {-# OPTIONS --without-K #-}

module F2a where

open import Agda.Prim
open import Data.Unit
open import Data.Nat hiding (_⊔_)
open import Data.Sum 
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Paths
open import Evaluator

------------------------------------------------------------------------------
-- 
-- General structure and idea
-- 
-- We have pointed types (Paths.agda) 
-- We have paths between pointed types (Paths.agda) 
-- We have functions between pointed types (that use ≡ to make sure the
--   basepoint is respected) (F2a.agda) 
-- Then we use univalence to connect these two independently developed
--   notions (F2a.agda) 
-- Because our paths are richer than just refl and our functions are 
--   more restricted than arbitrary functions, and in fact because our 
--   path constructors are sound and complete for the class of functions
--   we consider, we hope to _prove_ univalence
-- 
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Equivalences between raw functions and types
-- This is generalized below to pointed types

-- Two functions are ∼ is they map each argument to related results

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

-- quasi-inverses

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {ℓ} {ℓ} {A} {A} id
idqinv = record {
           g = id ;
           α = λ b → refl ; 
           β = λ a → refl 
         } 

-- equivalences

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    h : B → A
    β : (h ∘ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

idequiv : ∀ {ℓ} {A : Set ℓ} → A ≃ A
idequiv = (id , equiv₁ idqinv)

-- Function extensionality

{--
happly : ∀ {ℓ} {A B : Set ℓ} {f g : A → B} → (Path f g) → (f ∼ g)
happly {ℓ} {A} {B} {f} {g} p = 
  (pathInd 
    (λ _ → f ∼ g) -- f ∼ g
    (λ {AA} a x → {!!}) {!!} 
    {!!} {!!} {!!} {!!} {!!} {!!} 
    {!!} {!!} (λ a b x → {!cong (evalB p) (eval-resp-• (p))!}) 
    {!!} {!!} {!!} {!!} {!!} {!!} 
    (λ a x → {!!}) (λ p₁ q x x₁ x₂ → x x₂) 
    (λ p₁ q x x₁ x₂ → x x₂) (λ p₁ q x x₁ x₂ → x x₂) (λ p₁ q x x₁ x₂ → x₁ x₂))
  {A → B} {A → B} {f} {g} p 

postulate
  funextP : {A B : Set} {f g : A → B} → 
            isequiv {A = Path f g} {B = f ∼ g} happly

funext : {A B : Set} {f g : A → B} → (f ∼ g) → (Path f g)
funext = isequiv.g funextP

-- Universes; univalence

idtoeqv : {A B : Set} → (Path A B) → (A ≃ B)
idtoeqv {A} {B} p = {!!}
{--
  (pathInd 
    (λ {S₁} {S₂} {A} {B} p → {!!})
    {!!} {!!} 
    {!!} {!!} {!!} {!!} {!!} {!!} 
    {!!} {!!} {!!} 
    {!!} {!!} {!!} {!!} {!!} {!!} 
    {!!} {!!} {!!} {!!} {!!})
  {Set} {Set} {A} {B} p
--}

postulate 
  univalence : {ℓ : Level} {A B : Set ℓ} → (Path A B) ≃ (A ≃ B)

--}

path2fun : {ℓ : Level} {A B : Set ℓ} → (Path A B) → (A ≃ B)
path2fun p = ( {!!} , {!!})

------------------------------------------------------------------------------
-- Functions and equivalences between pointed types

-- Univalence as a postulate for now but hopefully we can actually prove it
-- since the pi-combinators are sound and complete for isomorphisms between
-- finite types

--postulate 
--  univalence• : {ℓ : Level} {A• B• : Set• {ℓ}} → (Path A• B•) ≃• (A• ≃• B•)
                

{--
record isequiv• {ℓ} {A B : Set} {A• B• : Set• {ℓ}} (f• : A• →• B•) : 
  Set (lsuc ℓ) where
  constructor mkisequiv•
  field
    equi : isequiv (fun f•)  
    path' : Path (• A•) (• B•)

_≈•_ : ∀ {ℓ} {A B : Set} (A• B• : Set• {ℓ}) → Set (lsuc ℓ)
_≈•_ {_} {A} {B} A• B• = Σ (A• →• B•) (isequiv• {_} {A} {B})
--}


------------------------------------------------------------------------------
-- Univalence for pointed types

eval• :  {ℓ : Level} {A• B• : Set• {ℓ}} → A• ⇛ B• → (A• →• B•)
eval• c = record { fun = eval c ; resp• = eval-resp-• c } 

evalB• :  {ℓ : Level} {A• B• : Set• {ℓ}} → A• ⇛ B• → (B• →• A•)
evalB• c = record { fun = evalB c ; resp• = evalB-resp-• c } 

-- This is at the wrong level... We need to define equivalences ≃ between
-- pointed sets too...

{--
path2iso : {ℓ : Level} {A• B• : Set• {ℓ}} → A• ⇛ B• → ∣ A• ∣ ≃ ∣ B• ∣
path2iso {ℓ} {a} {b} p = (eval p , 
  mkisequiv (evalB p) (λ x → {!!}) (evalB p) (λ x → {!eval∘evalB p!}))
--}

------------------------------------------------------------------------------
--}
