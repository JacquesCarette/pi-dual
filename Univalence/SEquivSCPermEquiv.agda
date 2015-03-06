{-# OPTIONS --without-K #-}

module SEquivSCPermEquiv where

-- open import Level
open import Data.Nat using (ℕ;_+_)
-- open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate; tabulate∘lookup; lookup-allFin)
open import VecHelpers using (_!!_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans;
--    proof-irrelevance; subst;
    module ≡-Reasoning)
open import Relation.Binary using (Setoid; module Setoid)
-- open import Data.Product using (_,′_; _×_)

open import VecOps -- and below, import from that
open F
open FPf

open import Function using (_∘_; id)
-- open import RepresPerm
open import Equiv
open import Enumeration
open import Data.Product using (_,_; proj₁; proj₂)
open import EquivSetoid
open import SetoidUtils 
open import Function.Equality using (_⟶_; Π; _⟨$⟩_; _⇨_) renaming (_∘_ to _⊚_; id to id⊚)

open import ConcretePermutation
open import FiniteFunctions using (finext)

-- the big (semantic) theorem.
-- for convenience, use only a single size, even though we could use 2.
thm2 : ∀ {n} {A B : Set} → Enum A n → Enum B n → 
  (≃S-Setoid A B) ≃S ≡-Setoid (CPerm n)
thm2 {n} {A} {B} (enumA , mkqinv labelA αA βA) (enumB , mkqinv labelB αB βB) = 
  equiv fwd' bwd' α β
  where
    open ≡-Reasoning
    AS = ≡-Setoid A
    BS = ≡-Setoid B
    A≃Fn : A ≃ Fin n
    A≃Fn = (enumA , mkqinv labelA αA βA)
    B≃Fn : B ≃ Fin n
    B≃Fn = (enumB , mkqinv labelB αB βB)
    CP⇨ = SCPerm n ⇨ SCPerm n

    fwd : (AS ≃S BS) → CPerm n
    fwd A≃B = cp (tabulate f) (tabulate g) (∼p⇒≡ αp) (∼p⇒≡ βp)
      where
        module A≃SB = _≃S_ A≃B
        f : Fin n → Fin n
        f j = enumB (A≃SB.f ⟨$⟩ labelA j)

        g : Fin n → Fin n
        g j =  enumA (A≃SB.g ⟨$⟩ labelB j) 

        α : f ∘ g ∼ id
        α i =
          begin
            (enumB (A≃SB.f ⟨$⟩ (labelA (enumA (A≃SB.g ⟨$⟩ labelB i))))
                ≡⟨ cong (λ x → enumB (A≃SB.f ⟨$⟩ x)) (βA ((A≃SB.g  ⟨$⟩ labelB i))) ⟩
            enumB (A≃SB.f ⟨$⟩ (A≃SB.g  ⟨$⟩ labelB i))
                ≡⟨ cong enumB (A≃SB.α refl) ⟩
            enumB (labelB i)
                ≡⟨ αB i ⟩
            i ∎)

        β : g ∘ f ∼ id
        β i = 
          begin (
            enumA (A≃SB.g ⟨$⟩ labelB (enumB (A≃SB.f ⟨$⟩ labelA i)))
                ≡⟨ cong (λ x → enumA (A≃SB.g ⟨$⟩ x)) (βB _) ⟩
            enumA (A≃SB.g ⟨$⟩ (A≃SB.f ⟨$⟩ labelA i))
                ≡⟨ cong enumA (A≃SB.β refl) ⟩
            enumA (labelA i)
               ≡⟨ αA i ⟩
            i ∎)

        αp : (tabulate f ∘̂ tabulate g) ∼p F.1C
        αp i = 
          begin (
            (tabulate f ∘̂ tabulate g) !! i
              ≡⟨  ∘̂⇒∘ f g i ⟩
           tabulate (g ∘ f) !! i
              ≡⟨ cong (λ x → x !! i) (finext β) ⟩
           tabulate id !! i ∎)

        -- see the αp proof for why this proof is ok
        βp : (tabulate g ∘̂ tabulate f) ∼p F.1C
        βp i = trans (∘̂⇒∘ g f i) (cong (λ x → x !! i) (finext α))

    fwd' : ≃S-Setoid A B ⟶ ≡-Setoid (CPerm n)
    fwd' = record 
     { _⟨$⟩_ = fwd 
      ; cong = λ {i} {j} i≋j → p≡ (finext (λ k → cong enumB (f≡ i≋j (labelA k)) ))
     }
       where open _≋_

    bwd : CPerm n → (AS ≃S BS)
    bwd (cp p₁ p₂ αp βp) = equiv f g α β
      where
        f : AS ⟶ BS
        f = →to⟶ (λ a → labelB (p₁ !! enumA a))

        g : BS ⟶ AS
        g = →to⟶ (λ b → labelA (p₂ !! (enumB b)))

        α : Setoid._≈_ (BS ⇨ BS) (f ⊚ g) id⊚
        α {b} {.b} refl = 
          begin (
            labelB (p₁ !! (enumA (labelA (p₂ !! (enumB b)))))
              ≡⟨ cong (λ x → labelB (p₁ !! x)) (αA _) ⟩
            labelB (p₁ !! (p₂ !! enumB b))
              ≡⟨ cong labelB (!!⇒∘̂ _ _ (enumB b)) ⟩
            labelB ((p₂ ∘̂ p₁) !! enumB b)
              ≡⟨ cong (λ x → (labelB (x !! enumB b))) βp ⟩
           labelB (F.1C !! enumB b)
              ≡⟨ cong labelB (lookup∘tabulate id _) ⟩
           labelB (enumB b)
              ≡⟨ βB b ⟩
            b ∎)

        β : Setoid._≈_ (AS ⇨ AS) (g ⊚ f) id⊚
        β {a} {.a} refl = 
          begin (
            labelA (p₂ !! (enumB (labelB (p₁ !! enumA a))))
              ≡⟨ cong (λ x → labelA (p₂ !! x)) (αB _) ⟩
            labelA (p₂ !! (p₁ !! enumA a))
              ≡⟨ cong labelA (!!⇒∘̂ _ _ (enumA a)) ⟩
            labelA ((p₁ ∘̂ p₂) !! enumA a)
              ≡⟨ cong (λ x → labelA (x !! enumA a)) αp ⟩
            labelA (F.1C !! enumA a)
              ≡⟨ cong labelA (lookup∘tabulate id _) ⟩
            labelA (enumA a)
              ≡⟨ βA a ⟩
            a ∎)

    bwd' : ≡-Setoid (CPerm n) ⟶ ≃S-Setoid A B
    bwd' = record 
      { _⟨$⟩_ = bwd 
      ; cong = λ { {π} {.π} refl → equivS (λ a → refl) (λ b → refl) }
      }

    α : Setoid._≈_ CP⇨ (fwd' ⊚ bwd') id⊚
    α {cp π πᵒ αp βp} refl = p≡ (trans (finext pf₁) (tabulate∘lookup π))
      where
        p = cp π πᵒ αp βp
        pf₁ : (j : Fin n) → enumB (labelB (π !! enumA (labelA j))) ≡ π !! j
        pf₁ j = 
          begin (
            enumB (labelB (π !! enumA (labelA j)))
              ≡⟨ αB _ ⟩
            π !! enumA (labelA j) 
              ≡⟨ cong (_!!_ π) (αA _) ⟩
            π !! j ∎)

    β : {x y : AS ≃S BS} → x ≋ y → ((bwd' ⊚ fwd') ⟨$⟩ x) ≋ y
    β {equiv f g α β} {equiv f₁ g₁ α₁ β₁} (equivS f≡ g≡) =
      equivS (λ a → trans (pf₁ a) (f≡ a)) (λ b → trans (pf₂ b) (g≡ b))
      where
        pf₁ : ∀ a → labelB (tabulate (λ j → enumB (f ⟨$⟩ labelA j)) !! (enumA a)) ≡ f ⟨$⟩ a
        pf₁ a =
          begin (
            labelB (tabulate (λ j → enumB (f ⟨$⟩ labelA j)) !! enumA a)
              ≡⟨ cong labelB (lookup∘tabulate _ (enumA a)) ⟩
            labelB (enumB (f ⟨$⟩ labelA (enumA a)))
              ≡⟨ βB _ ⟩
            f ⟨$⟩ labelA (enumA a)
              ≡⟨ cong (_⟨$⟩_ f) (βA _) ⟩
            f ⟨$⟩ a ∎)
        pf₂ : ∀ b → labelA (tabulate (λ j → enumA (g ⟨$⟩ labelB j)) !! (enumB b)) ≡ g ⟨$⟩ b
        pf₂ b = 
          begin (
            labelA (tabulate (λ j → enumA (g ⟨$⟩ labelB j)) !! enumB b)
              ≡⟨ cong labelA (lookup∘tabulate _ (enumB b)) ⟩
            labelA (enumA (g ⟨$⟩ labelB (enumB b)))
              ≡⟨ βA _ ⟩
            g ⟨$⟩ labelB (enumB b)
              ≡⟨ cong (_⟨$⟩_ g) (βB _) ⟩
            g ⟨$⟩ b ∎ )

-- Start proving some of the transport lemmas.  To make things simpler,
-- use a global Enum A and Enum B
-- (which turns out not so helpful after all, refactor! -- JC)

-- Need to do:
-- 1. prove that we have a bijective morphism of carriers: done, this is thm2 (fwd is the morphism)
-- 2.  prove that it preserves:
--   a. id (done)
--   b. 0 (done)
--   c. +
--   d. *

module Transport  {n : ℕ} {A B : Set} (EA : Enum A n) (EB : Enum B n) where
  open import TypeEquivalences using (path⊎)

  enumA = proj₁ EA
  module qA = qinv (proj₂ EA)
  enumB = proj₁ EB
  module qB = qinv (proj₂ EB)
  open _≃S_

  transportAB :   (≃S-Setoid A B) ≃S ≡-Setoid (CPerm n)
  transportAB = thm2 EA EB
  fwdAB = f transportAB
  bwdAB = g transportAB

  transportAA = thm2 EA EA
  fwdAA = f transportAA
  bwdAA = g transportAA

  lemma_1a : fwdAA ⟨$⟩ id≃S ≡ idp
  lemma_1a = p≡ (finext qA.α)

  -- this is redundant, as it follows from lemma_1a.
  lemma_1b : (bwdAA ⟨$⟩ idp) ≋ id≃S
  lemma_1b = equivS (λ x → trans (cong qA.g (lookup∘tabulate id (enumA x))) (qA.β x)) 
                                   (λ x → trans (cong qA.g (lookup∘tabulate id (enumA x))) (qA.β x))

  lemma2 : f (thm2 0E 0E) ⟨$⟩ 0≃S ≡ 0p
  lemma2 = p≡ refl

{-
  lemma3 : ∀ {x y} → fwdAB (path⊎ x y) ≡ fwdAB x ⊎p fwdAB y
  lemma3 = ? -- needs a complete definition of ⊎p
-}
