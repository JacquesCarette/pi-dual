{-# OPTIONS --without-K #-}

module SEquivSCPermEquiv where

-- open import Level
open import Data.Nat using (ℕ;_+_)
-- open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Fin using (Fin; inject+; raise)
open import Data.Vec using (tabulate) renaming (_++_ to _++V_)
open import Data.Vec.Properties using (lookup∘tabulate)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans;
    cong₂;
    module ≡-Reasoning)
open import Relation.Binary using (Setoid; module Setoid)
-- open import Data.Product using (_,′_; _×_)

open import FinVec using (module F) -- and below, import from that
open F using (~⇒≡; !!⇒∘̂; _∘̂_; 1C!!i≡i; cauchyext)

open import Function using (_∘_; id)
-- open import RepresPerm
open import Equiv
open import Enumeration
open import Data.Product using (_,_; proj₁; proj₂)
open import EquivSetoid
open import SetoidUtils 
open import Function.Equality using (_⟶_; Π; _⟨$⟩_; _⇨_) renaming (_∘_ to _⊚_; id to id⊚)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import ConcretePermutation
open import FiniteFunctions using (finext)
open import VectorLemmas using (_!!_; tabulate-split)

-- the big (semantic) theorem.
-- for convenience, use only a single size, even though we could use 2.
thm2 : ∀ {n} {A B : Set} → Enum A n → Enum B n → 
  (≃S-Setoid A B) ≃S ≡-Setoid (CPerm n n)
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
    CP⇨ = SCPerm n n ⇨ SCPerm n n

    fwd : (AS ≃S BS) → CPerm n n
    fwd A≃B = cp (tabulate f) (tabulate g) (~⇒≡ {o = n} β) (~⇒≡ {o = n} α)
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

    fwd' : ≃S-Setoid A B ⟶ ≡-Setoid (CPerm n n)
    fwd' = record 
     { _⟨$⟩_ = fwd 
      ; cong = λ {i} {j} i≋j → p≡ (finext (λ k → cong enumB (f≡ i≋j (labelA k)) ))
     }
       where open _≋_

    bwd : CPerm n n → (AS ≃S BS)
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
              ≡⟨ cong labelB 1C!!i≡i ⟩
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
              ≡⟨ cong labelA 1C!!i≡i ⟩
            labelA (enumA a)
              ≡⟨ βA a ⟩
            a ∎)

    bwd' : ≡-Setoid (CPerm n n) ⟶ ≃S-Setoid A B
    bwd' = record 
      { _⟨$⟩_ = bwd 
      ; cong = λ { {π} {.π} refl → equivS (λ _ → refl) (λ _ → refl) }
      }

    α : Setoid._≈_ CP⇨ (fwd' ⊚ bwd') id⊚
    α {cp π πᵒ αp βp} refl = p≡ (trans (finext pf₁) (cauchyext π))
      where
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

-- Start proving some of the transport lemmas. 
-- Need to do:
-- 1. prove that we have a bijective morphism of carriers: done, this is thm2 (fwd is the morphism)
-- 2.  prove that it preserves:
--   a. id (done)
--   b. 0 (done)
--   c. + (done)
--   d. *

open _≃S_

lemma_1a : ∀ {n} {A : Set} → (EA : Enum A n) → f (thm2 EA EA) ⟨$⟩ id≃S ≡ idp
lemma_1a (f' , mkqinv g α _) = p≡ (trans (finext α) F.reveal1C)

-- this is redundant, as it follows from lemma_1a.
lemma_1b : ∀ {n} {A : Set} → (EA : Enum A n) → (g (thm2 EA EA) ⟨$⟩ idp) ≋ id≃S
lemma_1b (enumA , mkqinv g _ β) = 
  equivS (λ x → trans (cong g 1C!!i≡i) (β x)) (λ x → trans (cong g 1C!!i≡i) (β x))

lemma2 : f (thm2 0E 0E) ⟨$⟩ 0≃S ≡ 0p
lemma2 = p≡ F.reveal0C -- p≡ refl

lemma3 : ∀ {n₁ n₂} {A B C D : Set} {EA : Enum A n₁} {EB : Enum B n₁}
  {EC : Enum C n₂} {ED : Enum D n₂} → (x : A ≃S≡ B) → (y : C ≃S≡ D) →
   f (thm2 (EA ⊕e EC) (EB ⊕e ED)) ⟨$⟩ (x ⊎≃S y) ≡ 
   (f (thm2 EA EB) ⟨$⟩ x) ⊎p (f (thm2 EC ED) ⟨$⟩ y)
lemma3 {n₁} {n₂} {EA = EA} {EB} {EC} {ED} (equiv f₄ g₄ α₄ β₄) (equiv f₅ g₅ α₅ β₅) = 
  p≡ (
    begin (
       CPerm.π (f (thm2 (EA ⊕e EC) (EB ⊕e ED)) ⟨$⟩ (x ⊎≃S y))
         ≡⟨ refl ⟩ -- inline f, fwd and π
       tabulate {n₁ + n₂} (λ j → enumBD (x⊎y.f ⟨$⟩ qAC.g j))
         ≡⟨ tabulate-split {n₁} {n₂} {f =  λ j → enumBD (x⊎y.f ⟨$⟩ qAC.g j)} ⟩
       tabulate {n₁} (λ j → enumBD (x⊎y.f ⟨$⟩ qAC.g (inject+ n₂ j))) ++V
       tabulate {n₂} (λ j → enumBD (x⊎y.f ⟨$⟩ qAC.g (raise n₁ j)))
         ≡⟨ cong₂ _++V_ (finext {n₁} pf₁) (finext pf₂) ⟩
       tabulate {n₁} (λ j → inject+ n₂ (tabulate (λ i → enumB (f₄ ⟨$⟩ qA.g i)) !! j)) ++V 
       tabulate {n₂} (λ j → raise n₁ (tabulate (λ i → enumD (f₅ ⟨$⟩ qC.g i)) !! j))
         ≡⟨ sym F.reveal⊎c ⟩ -- going up, inline f, fwd, ⊎p and π 
       CPerm.π ((f (thm2 EA EB) ⟨$⟩ x) ⊎p (f (thm2 EC ED) ⟨$⟩ y)) ∎))
  where 
    open ≡-Reasoning
    x = equiv f₄ g₄ α₄ β₄
    y = equiv f₅ g₅ α₅ β₅
    enumB = proj₁ EB
    enumD = proj₁ ED
    enumAC = proj₁ (EA ⊕e EC)
    module qAC = qinv (proj₂ (EA ⊕e EC))
    module qA = qinv (proj₂ EA)
    module qC = qinv (proj₂ EC)
    enumBD = proj₁ (EB ⊕e ED)
    module x⊎y = _≃S_ (x ⊎≃S y)

    pf₁ :  (i : Fin n₁) →
      enumBD (x⊎y.f ⟨$⟩ qAC.g (inject+ n₂ i)) ≡
      inject+ n₂ (tabulate (λ i₁ → enumB (f₄ ⟨$⟩ qA.g i₁)) !! i)
    pf₁ i =
      begin (
        enumBD (x⊎y.f ⟨$⟩ qAC.g (inject+ n₂ i))
          ≡⟨ cong (λ j → enumBD (x⊎y.f ⟨$⟩ j)) (eval-left {eA = EA} {EC} i) ⟩
        enumBD (x⊎y.f ⟨$⟩ inj₁ (qA.g i))
          ≡⟨ refl ⟩ -- once the inj₁ is exposed, the rest happens by β-reduction
        inject+ n₂ (enumB (f₄ ⟨$⟩ qA.g i))
           ≡⟨ cong (inject+ n₂) (sym (lookup∘tabulate _ i)) ⟩
        inject+ n₂ (tabulate (λ j → enumB (f₄ ⟨$⟩ qA.g j)) !! i) ∎)

    pf₂ :  (i : Fin n₂) →
      enumBD (x⊎y.f ⟨$⟩ qAC.g (raise n₁ i)) ≡
      raise n₁ (tabulate (λ i₁ → enumD (f₅ ⟨$⟩ qC.g i₁)) !! i)
    pf₂ i = 
      begin (
           enumBD (x⊎y.f ⟨$⟩ qAC.g (raise n₁ i))
             ≡⟨ cong (λ j → enumBD (x⊎y.f ⟨$⟩ j)) (eval-right {eA = EA} {EC} i) ⟩
           enumBD (x⊎y.f ⟨$⟩ inj₂ (qC.g i))
             ≡⟨ refl ⟩
           raise n₁ (enumD (f₅ ⟨$⟩ qC.g i))
             ≡⟨ cong (raise n₁) (sym (lookup∘tabulate _ i)) ⟩
           raise n₁ (tabulate (λ i₁ → enumD (f₅ ⟨$⟩ qC.g i₁)) !! i) ∎)
