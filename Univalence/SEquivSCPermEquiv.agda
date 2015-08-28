{-# OPTIONS --without-K #-}

module SEquivSCPermEquiv where

open import Level        using (Level; _⊔_)
open import Data.Fin     using (Fin) 
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec     using (tabulate)
open import Function     using (_∘_; id)

open import Data.Vec.Properties using    (lookup∘tabulate)
open import Relation.Binary     using    (Setoid)
open import Function.Equality   using    (_⟨$⟩_; _⟶_)
                                renaming (_∘_ to _⊚_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
     
--

open import Proofs using (_!!_; finext)
open import Equiv using (_≃_; iseq; module isequiv; g-left-inv)
open import EquivEquiv using (_S≃_; eq; _≋_; id≋)
open import ConcretePermutation using (CPerm; cp; _∘̂_; 1C; cauchyext; SCPerm)
open import ConcretePermutationProperties using (p≡)

--

infix 4 _≃S_

------------------------------------------------------------------------------
-- The big (semantic) theorem!

-- On one side we have the setoid of permutations under ≡
-- On the other we have the setoid of equivalences under ≋
-- 
-- The regular equivalence ≃ relates sets. To relate the above two
-- setoids, this regular equivalence is generalized to an equivalence
-- ≃S that relates setoids each with its own equivalence relation.

record _≃S_ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (A : Setoid ℓ₁ ℓ₂) (B : Setoid ℓ₃ ℓ₄) : 
  Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  constructor equiv
  field
    f : A ⟶ B
    g : B ⟶ A
    α : ∀ {x y} → Setoid._≈_ B x y → Setoid._≈_ B ((f ⊚ g) ⟨$⟩ x) y
    β : ∀ {x y} → Setoid._≈_ A x y → Setoid._≈_ A ((g ⊚ f) ⟨$⟩ x) y

-- Big theorem

univalence : ∀ {m n} → (SCPerm m n) ≃S (Fin m S≃ Fin n)
univalence {m} {n} = equiv fwd bwd α β 
  where

    fwd' : (CPerm m n) → (Fin m ≃ Fin n)
    fwd' (cp π πᵒ αp βp) =
      (λ m → πᵒ !! m) ,
      let index = (λ n → π !! n) in iseq index pf₁ index pf₂  
      where
        open ≡-Reasoning
        pf₁ : ∀ m → πᵒ !! (π !! m) ≡ m
        pf₁ m = begin (
          πᵒ !! (π !! m)
            ≡⟨ sym (lookup∘tabulate (λ x → πᵒ !! (π !! x)) m) ⟩
          (π ∘̂ πᵒ) !! m
            ≡⟨ cong (λ x → x !! m) αp ⟩
          1C !! m
            ≡⟨ lookup∘tabulate id m ⟩
          m ∎)
        pf₂ : ∀ m → π !! (πᵒ !! m) ≡ m
        pf₂ m = begin (
          π !! (πᵒ !! m)
            ≡⟨ sym (lookup∘tabulate (λ x → π !! (πᵒ !! x)) m) ⟩
          (πᵒ ∘̂ π) !! m
            ≡⟨ cong (λ x → x !! m) βp ⟩
          1C !! m
            ≡⟨ lookup∘tabulate id m ⟩
          m ∎)
        
    bwd' : (Fin m ≃ Fin n) → (CPerm m n)
    bwd' (f , iseq g α h β) =
      cp (tabulate g) (tabulate f) g∘̂f≡1C f∘̂g≡1C
      where
       open ≡-Reasoning
       g∘̂f≡1C : tabulate g ∘̂ tabulate f ≡ 1C
       g∘̂f≡1C = finext (λ i → begin (
         tabulate f !! (tabulate g !! i)
           ≡⟨ lookup∘tabulate f (tabulate g !! i) ⟩
         f (tabulate g !! i)
           ≡⟨ cong f (lookup∘tabulate g i) ⟩
         f (g i)
           ≡⟨ α i ⟩
         i ∎))
       f∘̂g≡1C : tabulate f ∘̂ tabulate g ≡ 1C
       f∘̂g≡1C = finext (λ i → begin (
         tabulate g !! (tabulate f !! i)
           ≡⟨ lookup∘tabulate g (tabulate f !! i) ⟩
         g (tabulate f !! i)
           ≡⟨ cong g (lookup∘tabulate f i) ⟩
         g (f i)
           ≡⟨ g-left-inv ((f , iseq g α h β)) i ⟩
         i ∎))

    fwd : (SCPerm m n) ⟶ (Fin m S≃ Fin n)
    fwd = record
      { _⟨$⟩_ = fwd'
      ; cong = λ { {π} {.π} refl → id≋ }
      }

    bwd : (Fin m S≃ Fin n) ⟶ (SCPerm m n)
    bwd = record
      { _⟨$⟩_ = bwd'
      ; cong = λ eq₁≋eq₂ → p≡ (finext (_≋_.g≡ eq₁≋eq₂))
      }

    α : {eq₁ eq₂ : Fin m ≃ Fin n} → eq₁ ≋ eq₂ → (fwd ⊚ bwd ⟨$⟩ eq₁) ≋ eq₂
    α {eq₁} {eq₂} eq₁≋eq₂ =
      eq (λ x → trans (lookup∘tabulate (proj₁ eq₁) x) (_≋_.f≡ eq₁≋eq₂ x))
         (λ x → trans (lookup∘tabulate (isequiv.g (proj₂ eq₁)) x) (_≋_.g≡ eq₁≋eq₂ x)) 

    β : {π₁ π₂ : CPerm m n} → π₁ ≡ π₂ → (bwd ⊚ fwd ⟨$⟩ π₁) ≡ π₂
    β {π} {.π} refl = p≡ (cauchyext (CPerm.π π)) 


