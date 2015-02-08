{-# OPTIONS --without-K #-}

module ConcretePermutation where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import VecHelpers using (_!!_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; trans; module ≡-Reasoning)
open import VecOps
open import Function using (_∘_; id)
open import RepresPerm
open import Equiv
open import Enumeration
open import Data.Product using (_,_)

open import FiniteFunctions

infix 4 _∼p_

_∼p_ : {n : ℕ} (p₁ p₂ : Vec (Fin n) n) → Set
_∼p_ {n} p₁ p₂ = (i : Fin n) → p₁ !! i ≡ p₂ !! i

_∘̂_ : {n : ℕ} → Vec (Fin n) n → Vec (Fin n) n → Vec (Fin n) n
_∘̂_ {n} = F.scompcauchy

-- not the flip!
∘̂⇒∘ : {n : ℕ} → (f g : Fin n → Fin n) → tabulate f ∘̂ tabulate g ∼p tabulate (g ∘ f)
∘̂⇒∘ f g i = 
  begin (
    (tabulate f ∘̂ tabulate g) !! i
      ≡⟨ lookup∘tabulate _ i ⟩
    (tabulate g) !! (tabulate f !! i)
      ≡⟨ lookup∘tabulate _ (tabulate f !! i) ⟩
    g (tabulate f !! i)
      ≡⟨ cong g (lookup∘tabulate f i) ⟩
    g (f i)
      ≡⟨ sym (lookup∘tabulate (g ∘ f) i) ⟩
    tabulate (g ∘ f) !! i ∎)
  where open ≡-Reasoning

-- a concrete permutation has 4 components:
-- - the permutation
-- - its inverse
-- - and 2 proofs that it is indeed inverse
record CPerm (size : ℕ) : Set where
  constructor cp
  field
    π : Vec (Fin size) size
    πᵒ : Vec (Fin size) size
    αp : (π ∘̂ πᵒ) ∼p (F.idcauchy size)
    βp : (πᵒ ∘̂ π) ∼p (F.idcauchy size)

idp : ∀ {n} → CPerm n
idp {n} = cp (F.idcauchy n) (F.idcauchy n) pf₁ pf₁
  where
    pf₁ : F.idcauchy n ∘̂ F.idcauchy n ∼p F.idcauchy n
    pf₁ = ∘̂⇒∘ id id 

symp : ∀ {n} → CPerm n → CPerm n
symp (cp p₁ p₂ α β) = cp p₂ p₁ β α

-- the big (semantic) theorem.
-- for convenience, use only a single size, even though we could use 2.
thm2 : ∀ {n} {A B : Set} → Enum A n → Enum B n → (A ≃ B) ≃ CPerm n
thm2 {n} {A} {B} (enum A≃Fn) (enum B≃Fn) = fwd , (mkqinv bwd α β)  
  where
    open ≡-Reasoning
    fwd : (A ≃ B) → CPerm n
    fwd A≃B = cp (tabulate f) (tabulate g) αp βp
      where
        f : Fin n → Fin n
        f j = B≃Fn ⋆ (A≃B ⋆ ((sym≃ A≃Fn) ⋆ j)) 

        g : Fin n → Fin n
        g j =  A≃Fn ⋆ (sym≃ A≃B ⋆ (sym≃ B≃Fn ⋆ j)) 

        α : f ∘ g ∼ id
        α i = {!!}

        β : g ∘ f ∼ id
        β i = {!!}

        αp : (tabulate f ∘̂ tabulate g) ∼p (F.idcauchy n)
        αp i = 
          begin (
            (tabulate f ∘̂ tabulate g) !! i
              ≡⟨ ∘̂⇒∘ f g i ⟩
           tabulate (g ∘ f) !! i
              ≡⟨ cong (λ x → x !! i) (finext β) ⟩
           tabulate id !! i ∎)

        -- see the αp proof for why this is ok
        βp : (tabulate g ∘̂ tabulate f) ∼p (F.idcauchy n)
        βp i = trans (∘̂⇒∘ g f i) (cong (λ x → x !! i) (finext α))

    bwd : CPerm n → (A ≃ B)
    bwd (cp p₁ p₂ αp βp) = f , (mkqinv g α β )
      where
        f : A → B
        f a = (sym≃ B≃Fn) ⋆ (p₁ !! (A≃Fn ⋆ a))

        g : B → A
        g b = (sym≃ A≃Fn) ⋆ (p₂ !! (B≃Fn ⋆ b))

        α : f ∘ g ∼ id
        α i = {!!}

        β : g ∘ f ∼ id
        β i = {!!}

    α : fwd ∘ bwd ∼ id
    α (cp π πᵒ αp βp) = {!!}

    β : bwd ∘ fwd ∼ id
    β (f , mkqinv g α β) = {!!}
