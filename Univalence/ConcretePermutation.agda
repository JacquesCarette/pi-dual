{-# OPTIONS --without-K #-}

module ConcretePermutation where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate; tabulate∘lookup; lookup-allFin)
open import VecHelpers using (_!!_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; proof-irrelevance; 
    module ≡-Reasoning)
open import VecOps
open import Function using (_∘_; id)
open import RepresPerm
open import Equiv
open import Enumeration
open import Data.Product using (_,_; proj₁; proj₂)

open import FiniteFunctions

infix 4 _∼p_

_∼p_ : {n : ℕ} (p₁ p₂ : Vec (Fin n) n) → Set
_∼p_ {n} p₁ p₂ = (i : Fin n) → p₁ !! i ≡ p₂ !! i

∼p⇒≡ : {n : ℕ} {p₁ p₂ : Vec (Fin n) n} → (p₁ ∼p p₂) → p₁ ≡ p₂
∼p⇒≡ {n} {p₁} {p₂} equiv = 
  begin (
    p₁                                    ≡⟨ sym (tabulate∘lookup p₁) ⟩
    tabulate (_!!_ p₁)            ≡⟨ finext equiv ⟩
    tabulate (_!!_ p₂)            ≡⟨ tabulate∘lookup p₂ ⟩
    p₂ ∎)
  where open ≡-Reasoning

_∘̂_ : {n : ℕ} → Vec (Fin n) n → Vec (Fin n) n → Vec (Fin n) n
_∘̂_ {n} = F.scompcauchy

-- note the flip!
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

!!⇒∘̂ : {n : ℕ} → (π₁ π₂ : Vec (Fin n) n) → (i : Fin n) → π₁ !! (π₂ !! i) ≡ (π₁ ∘̂ π₂) !! i
!!⇒∘̂ π₁ π₂ i = 
  begin (
    π₁ !! (π₂ !! i)
          ≡⟨ {!!} ⟩
    (π₁ ∘̂ π₂) !! i ∎)
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
    αp : π ∘̂ πᵒ ≡ F.idcauchy size
    βp : πᵒ ∘̂ π ≡ F.idcauchy size

p≡ : ∀ {n} → (π₁ π₂ : CPerm n) → (CPerm.π π₁ ≡ CPerm.π π₂) → (CPerm.πᵒ π₁ ≡ CPerm.πᵒ π₂) → π₁ ≡ π₂
p≡ (cp π πᵒ αp βp) (cp .π .πᵒ αp₁ βp₁) refl refl with proof-irrelevance αp αp₁ | proof-irrelevance βp βp₁
p≡ (cp π πᵒ αp βp) (cp .π .πᵒ .αp .βp) refl refl | refl | refl = refl

idp : ∀ {n} → CPerm n
idp {n} = cp (F.idcauchy n) (F.idcauchy n) pf₁ pf₁
  where
    pf₁ : F.idcauchy n ∘̂ F.idcauchy n ≡ F.idcauchy n
    pf₁ = finext (λ i → trans (lookup-allFin (F.idcauchy n !! i)) (lookup-allFin i)) 

symp : ∀ {n} → CPerm n → CPerm n
symp (cp p₁ p₂ α β) = cp p₂ p₁ β α

-- the big (semantic) theorem.
-- for convenience, use only a single size, even though we could use 2.
thm2 : ∀ {n} {A B : Set} → Enum A n → Enum B n → (A ≃ B) ≃ CPerm n
thm2 {n} {A} {B} (enum A≃Fn) (enum B≃Fn) = fwd , (mkqinv bwd α β)  
  where
    open ≡-Reasoning
    fwd : (A ≃ B) → CPerm n
    fwd A≃B = cp (tabulate f) (tabulate g) (∼p⇒≡ αp) (∼p⇒≡ βp)
      where
        f : Fin n → Fin n
        f j = B≃Fn ⋆ (A≃B ⋆ ((sym≃ A≃Fn) ⋆ j)) 

        g : Fin n → Fin n
        g j =  A≃Fn ⋆ (sym≃ A≃B ⋆ (sym≃ B≃Fn ⋆ j)) 

        α : f ∘ g ∼ id
        α i =
          begin
            (B≃Fn ⋆ (A≃B ⋆ ((sym≃ A≃Fn) ⋆ (A≃Fn ⋆ (sym≃ A≃B ⋆ (sym≃ B≃Fn ⋆ i)))))
                ≡⟨ cong (λ x → B≃Fn ⋆ (A≃B ⋆ x)) (qinv.β (proj₂ A≃Fn) ((sym≃ A≃B  ⋆ (sym≃ B≃Fn ⋆ i)))) ⟩
            B≃Fn ⋆ (A≃B ⋆ (sym≃ A≃B ⋆ (sym≃ B≃Fn ⋆ i)))
                ≡⟨ cong (λ x → B≃Fn ⋆ x) (qinv.α (proj₂ A≃B) (sym≃ B≃Fn ⋆ i)) ⟩
            B≃Fn ⋆ (sym≃ B≃Fn ⋆ i)
                ≡⟨ qinv.α (proj₂ B≃Fn) i ⟩
            i ∎)

        β : g ∘ f ∼ id
        β i = {!!}

        αp : (tabulate f ∘̂ tabulate g) ∼p (F.idcauchy n)
        αp i = 
          begin (
            (tabulate f ∘̂ tabulate g) !! i
              ≡⟨  ∘̂⇒∘ f g i ⟩
           tabulate (g ∘ f) !! i
              ≡⟨ cong (λ x → x !! i) (finext β) ⟩
           tabulate id !! i ∎)

        -- see the αp proof for why this proof is ok
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
        α i = 
          let fB = proj₁ B≃Fn in
          let gB = qinv.g (proj₂ B≃Fn) in
          let fA  = proj₁ A≃Fn in
          let gA = qinv.g (proj₂ A≃Fn) in
          begin (
            f (g i)
                     ≡⟨ refl ⟩
            gB (p₁ !! fA (gA (p₂ !! fB i)))
                     ≡⟨ cong (λ x → gB (p₁ !! x)) (qinv.α (proj₂ A≃Fn) (p₂ !! fB i)) ⟩
            gB (p₁ !! (p₂ !! fB i))
                     ≡⟨ cong gB (!!⇒∘̂ p₁ p₂ (fB i)) ⟩
            gB ((p₁ ∘̂ p₂) !! fB i)
                     ≡⟨ cong (λ x → gB (x !! fB i)) αp ⟩
            gB (tabulate id !! fB i)
                     ≡⟨ cong gB (lookup∘tabulate id (fB i)) ⟩
            gB (fB i)
                     ≡⟨ qinv.β (proj₂ B≃Fn) i ⟩
            i ∎ )

        β : g ∘ f ∼ id
        β i = {!!}

    α : fwd ∘ bwd ∼ id
    α (cp π πᵒ αp βp) = p≡ (fwd (bwd i)) i pf₁ {!!}
      where
        i = cp π πᵒ αp βp
        pf₁ : CPerm.π (fwd (bwd i)) ≡ π
        pf₁ = {!!}

    β : bwd ∘ fwd ∼ id
    β (f , mkqinv g α β) = ≃≡ {!!} {!!} bwd∘fwd A≃B bwd∘fwd∼A≃B {!!}
      where
        open ≡-Reasoning
        A≃B = (f , mkqinv g α β)
        module qB≃Fn = qinv (proj₂ B≃Fn)
        module qA≃Fn = qinv (proj₂ A≃Fn)
        f₁ : A → B
        f₁ a = qB≃Fn.g (CPerm.π (fwd A≃B) !! (A≃Fn ⋆ a))
        g₁ : B → A
        g₁ b = qA≃Fn.g (CPerm.πᵒ (fwd A≃B) !! (B≃Fn ⋆ b))
        α₁ : f₁ ∘ g₁ ∼ id
        α₁ i = {!!}
        β₁ : g₁ ∘ f₁ ∼ id
        β₁ i = {!!}
        bwd∘fwd : A ≃ B
        bwd∘fwd = (f₁ , mkqinv g₁ α₁ β₁)
        bwd∘fwd∼A≃B : proj₁ bwd∘fwd ∼ proj₁ A≃B
        bwd∘fwd∼A≃B i = {!!}

