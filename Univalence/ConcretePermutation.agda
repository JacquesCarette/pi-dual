{-# OPTIONS --allow-unsolved-metas #-}

module ConcretePermutation where

open import Level
open import Data.Nat using (ℕ;_+_)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate; tabulate∘lookup; lookup-allFin)
open import VecHelpers using (_!!_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans;
    proof-irrelevance; subst;
    module ≡-Reasoning)
open import Relation.Binary using (Setoid; module Setoid)
open import Data.Product using (_,′_; _×_)

open import VecOps -- and below, import from that
open F
open FPf

open import Function using (_∘_; id)
open import RepresPerm
open import Equiv
open import Enumeration
open import Data.Product using (_,_; proj₁; proj₂)
open import EquivSetoid
open import SetoidUtils 
open import Function.Equality using (_⟶_; Π; _⟨$⟩_; _⇨_) renaming (_∘_ to _⊚_; id to id⊚)

open import FiniteFunctions

infix 4 _∼p_

_∼p_ : {n : ℕ} (p₁ p₂ : Vec (Fin n) n) → Set
_∼p_ {n} p₁ p₂ = (i : Fin n) → p₁ !! i ≡ p₂ !! i

∼p⇒≡ : {n : ℕ} {p₁ p₂ : Vec (Fin n) n} → (p₁ ∼p p₂) → p₁ ≡ p₂
∼p⇒≡ {n} {p₁} {p₂} eqv = 
  begin (
    p₁                                    ≡⟨ sym (tabulate∘lookup p₁) ⟩
    tabulate (_!!_ p₁)            ≡⟨ finext eqv ⟩
    tabulate (_!!_ p₂)            ≡⟨ tabulate∘lookup p₂ ⟩
    p₂ ∎)
  where open ≡-Reasoning

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

πᵒ≡ : ∀ {n} → (π₁ π₂ : CPerm n) → (CPerm.π π₁ ≡ CPerm.π π₂) → (CPerm.πᵒ π₁ ≡ CPerm.πᵒ π₂)
πᵒ≡ {n} (cp π πᵒ αp βp) (cp .π πᵒ₁ αp₁ βp₁) refl =
  begin (
    πᵒ                  ≡⟨ sym (∘̂-rid πᵒ) ⟩
    πᵒ ∘̂ F.idcauchy n   ≡⟨  cong (_∘̂_ πᵒ) (sym αp₁)  ⟩
    πᵒ ∘̂ (π ∘̂ πᵒ₁)      ≡⟨ ∘̂-assoc πᵒ π πᵒ₁ ⟩
    (πᵒ ∘̂ π) ∘̂ πᵒ₁      ≡⟨ cong (λ x → x ∘̂ πᵒ₁) βp ⟩
    F.idcauchy n ∘̂ πᵒ₁  ≡⟨ ∘̂-lid πᵒ₁ ⟩
    πᵒ₁ ∎)
  where open ≡-Reasoning

p≡ : ∀ {n} → (π₁ π₂ : CPerm n) → (CPerm.π π₁ ≡ CPerm.π π₂) → π₁ ≡ π₂
p≡ (cp π πᵒ αp βp) (cp .π πᵒ₁ αp₁ βp₁) refl with πᵒ≡ (cp π πᵒ αp βp) (cp π πᵒ₁ αp₁ βp₁) refl
p≡ (cp π πᵒ αp βp) (cp .π .πᵒ αp₁ βp₁) refl | refl with proof-irrelevance αp αp₁ | proof-irrelevance βp βp₁
p≡ (cp π πᵒ αp βp) (cp .π .πᵒ .αp .βp) refl | refl | refl | refl = refl

idp : ∀ {n} → CPerm n
idp {n} = cp (F.idcauchy n) (F.idcauchy n) (∘̂-rid _) (∘̂-lid _)

symp : ∀ {n} → CPerm n → CPerm n
symp (cp p₁ p₂ α β) = cp p₂ p₁ β α

transp : ∀ {n} → CPerm n → CPerm n → CPerm n
transp {n} (cp π πᵒ αp βp) (cp π₁ πᵒ₁ αp₁ βp₁) = cp (π ∘̂ π₁) (πᵒ₁ ∘̂ πᵒ) pf₁ pf₂
  where
    open ≡-Reasoning
    pf₁ : (π ∘̂ π₁) ∘̂ (πᵒ₁ ∘̂ πᵒ) ≡ F.idcauchy n
    pf₁ = 
      begin (
        (π ∘̂ π₁) ∘̂ (πᵒ₁ ∘̂ πᵒ)      ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((π ∘̂ π₁) ∘̂ πᵒ₁) ∘̂ πᵒ      ≡⟨ cong (λ x → x ∘̂ πᵒ) (sym (∘̂-assoc _ _ _)) ⟩
        (π ∘̂ (π₁ ∘̂ πᵒ₁)) ∘̂ πᵒ      ≡⟨ cong (λ x → (π ∘̂ x) ∘̂ πᵒ) (αp₁) ⟩
        (π ∘̂ F.idcauchy n) ∘̂ πᵒ    ≡⟨ cong (λ x → x ∘̂ πᵒ) (∘̂-rid _) ⟩
        π ∘̂ πᵒ                     ≡⟨ αp ⟩
        F.idcauchy n ∎)
    pf₂ : (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁) ≡ F.idcauchy n
    pf₂ = 
      begin (
        (πᵒ₁ ∘̂ πᵒ) ∘̂ (π ∘̂ π₁)     ≡⟨ ∘̂-assoc _ _ _ ⟩
        ((πᵒ₁ ∘̂ πᵒ) ∘̂ π) ∘̂ π₁     ≡⟨ cong (λ x → x ∘̂ π₁) (sym (∘̂-assoc _ _ _)) ⟩
        (πᵒ₁ ∘̂ (πᵒ ∘̂ π)) ∘̂ π₁     ≡⟨ cong (λ x → (πᵒ₁ ∘̂ x) ∘̂ π₁) βp ⟩
        (πᵒ₁ ∘̂ F.idcauchy n) ∘̂ π₁ ≡⟨ cong (λ x → x ∘̂ π₁) (∘̂-rid _) ⟩
         πᵒ₁ ∘̂ π₁                 ≡⟨ βp₁ ⟩
        F.idcauchy n ∎)

_⊎p_ : ∀ {m n} → CPerm m → CPerm n → CPerm (m + n)
_⊎p_ {m} {n} π₀ π₁ = cp ((π π₀) ⊎c (π π₁)) ((πᵒ π₀) ⊎c (πᵒ π₁)) {!!} {!!}
  where open CPerm
        open F

SCPerm : ℕ → Setoid zero zero
SCPerm n = ≡-Setoid (CPerm n)

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

    fwd' : ≃S-Setoid A B ⟶ ≡-Setoid (CPerm n)
    fwd' = record 
     { _⟨$⟩_ = fwd 
      ; cong = λ {i} {j} i≋j → 
                       p≡ (fwd i) (fwd j) 
                             (finext (λ k → cong enumB (f≡ i≋j (labelA k)) ))
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
           labelB (F.idcauchy n !! enumB b)
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
            labelA (F.idcauchy n !! enumA a)
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
    α {cp π πᵒ αp βp} refl = p≡ (fwd (bwd p)) p (trans (finext pf₁) (tabulate∘lookup π))
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
