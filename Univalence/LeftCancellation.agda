{-# OPTIONS --without-K #-}
module LeftCancellation where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product using (_,_; _,′_; proj₁; proj₂)
open import Function renaming (_∘_ to _○_)

-- explicit 'using', to show how little of HoTT is needed
open import HoTT using (refl; ap; _∘_; !; _≡_; _≡⟨_⟩_ ; _∎)  
open import Equivalences
open import TypeEquivalences using (swap₊)
open import Inspect

----------------------------------------------------------------------------
-- Very complex proof that we can cancel units on the left of ⊎

-- Some repeated patterns:
-- use injectivity of equivalences to go from f x ≡ f y to x ≡ y
injectivity : {A B : Set} (equiv : (⊤ ⊎ A) ≃ (⊤ ⊎ B)) → (a : A) → equiv ⋆ inj₁ tt ≡ equiv ⋆ inj₂ a → (inj₁ tt ≡ inj₂ a) 
injectivity equiv x path = inj≃ equiv (inj₁ tt) (inj₂ x) path

-- Use that disjoint unions are, well, disjoint, to derive a contradiction
bad-path : {A : Set} → (x : A) → inj₁ tt ≡ inj₂ x → ⊥
bad-path x path = proj₁ (thm2-12-5 tt (inj₂ x)) path

sub2 : {A B : Set} →  ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A ≃ B
sub2 {A} {B}  (f₁ , mkisequiv g₁ α₁ h₁ β₁) with f₁ (inj₁ tt) | inspect f₁ (inj₁ tt) | g₁ (inj₁ tt) | inspect g₁ (inj₁ tt)
sub2 {A} {B} (f₁ , mkisequiv g₁ α₁ h₁ β₁) | inj₁ tt | ⟪ eq₁ ⟫ | inj₁ tt | ⟪ eq₂ ⟫ = f , equiv₁ (mkqinv g α β)
  where equiv = (f₁ , mkisequiv g₁ α₁ h₁ β₁)
        f : A → B
        f a with f₁ (inj₂ a) | inspect f₁ (inj₂ a)
        f a | inj₂ b  | _ = b
        f a | inj₁ tt | ⟪ eq ⟫ with bad-path a inject
          where inject = injectivity equiv a (eq₁ ∘ ! eq)
        f a | inj₁ tt | ⟪ eq ⟫ | ()
        g : B → A
        g b with g₁ (inj₂ b) | inspect g₁ (inj₂ b)
        g b | inj₂ a  | _ = a
        g b | inj₁ tt | ⟪ eq ⟫ with bad-path b inject
          where inject = injectivity (sym≃ equiv) b (eq₂ ∘ ! eq) 
        g b | inj₁ tt | ⟪ eq ⟫ | () 
        α : f ○ g ∼ id
        α b with g₁ (inj₂ b) | inspect g₁ (inj₂ b)
        α b | inj₁ tt | ⟪ eq ⟫ with bad-path b inject 
          where inject = injectivity (sym≃ equiv) b (eq₂ ∘ ! eq) 
        α b | inj₁ tt | ⟪ eq ⟫ | ()
        α b | inj₂ a  | ⟪ eq ⟫ with f₁ (inj₂ a) | inspect f₁ (inj₂ a) 
        α b | inj₂ a | ⟪ eq ⟫ | inj₁ tt | ⟪ eq₃ ⟫ with bad-path a inject
          where inject = injectivity equiv a (eq₁ ∘ ! eq₃)
        α b | inj₂ a | ⟪ eq ⟫ | inj₁ tt | ⟪ eq₃ ⟫ | ()
        α b | inj₂ a | ⟪ eq ⟫ | inj₂ b′ | ⟪ eq₃ ⟫ = 
            proj₁ (inj₁₁path b′ b) (ap swap₊ (! (ap f₁ eq ∘ eq₃) ∘ α₁ (inj₂ b)))
        β : g ○ f ∼ id
        β a with f₁ (inj₂ a) | inspect f₁ (inj₂ a) 
        β a | inj₁ tt | ⟪ eq ⟫ with bad-path a inject
          where inject = injectivity equiv a (! (eq ∘ ! eq₁))
        ... | ()
        β a | inj₂ b | ⟪ eq ⟫ with g₁ (inj₂ b) | inspect g₁ (inj₂ b)
        ... | inj₁ tt | ⟪ eq₃ ⟫ with bad-path a inject
          where inject = injectivity equiv a (! (ap f₁ eq₃) ∘ (α₁ (inj₂ b)) ∘ ! eq)
        β a | inj₂ b | ⟪ eq ⟫ | inj₁ tt | ⟪ eq₃ ⟫ | ()
        β a | inj₂ b | ⟪ eq ⟫ | inj₂ a′ | ⟪ eq₃ ⟫ = proj₁ (inj₁₁path a′ a) (ap swap₊ ((! eq₃) ∘ ap g₁ (! eq) ∘ β₂ (inj₂ a)))
            where module EQ = qinv (equiv₂ {f = f₁} (proj₂ equiv))
                  β₂ = EQ.β

sub2 (f₁ , mkisequiv g α h β) | inj₁ tt | ⟪ eq₁ ⟫ | inj₂ a | ⟪ eq₂ ⟫ with bad-path a inject
  where equiv = (f₁ , mkisequiv g α h β)
        inject = injectivity equiv a (eq₁ ∘ ! (α (inj₁ tt)) ∘ (ap f₁ eq₂))
sub2 (f₁ , mkisequiv g α h β) | inj₁ tt | ⟪ eq₁ ⟫ | inj₂ a | ⟪ eq₂ ⟫ | ()

sub2 (f₁ , mkisequiv g α h β) | inj₂ b | ⟪ eq₁ ⟫ | inj₁ tt | ⟪ eq₂ ⟫ with bad-path b (! (α (inj₁ tt)) ∘ (ap f₁ eq₂) ∘ eq₁ )
... | ()
sub2 {A} {B} (f₁ , mkisequiv g₁ α₁ h₁ β₁) | inj₂ b₁ | ⟪ eq₁ ⟫ | inj₂ a₁ | ⟪ eq₂ ⟫ = f , equiv₁ (mkqinv g α β)
  where equiv = (f₁ ,′ mkisequiv g₁ α₁ h₁ β₁)
        module EQ = qinv (equiv₂ {f = f₁} (proj₂ equiv))
        β₂ = EQ.β
        f : A → B
        f a with f₁ (inj₂ a)
        f a | inj₂ b′  = b′
        f a | inj₁ tt  = b₁
        g : B → A
        g b with g₁ (inj₂ b)
        g b | inj₂ a′ = a′
        g b | inj₁ tt = a₁
        α : f ○ g ∼ id
        α b with g₁ (inj₂ b) | inspect g₁ (inj₂ b)
        ... |  inj₂ a′ | ⟪ eq ⟫ with f₁ (inj₂ a′) | inspect f₁ (inj₂ a′)
        ...     | inj₂ b′ | ⟪ eq₃ ⟫ = ! (proj₁ (inj₁₁path b b′) (ap swap₊ (! (α₁ (inj₂ b)) ∘ ap f₁ eq ∘ eq₃)))
        ...     | inj₁ tt | ⟪ eq₃ ⟫ with bad-path b (! (! (α₁ (inj₂ b)) ∘ (ap f₁ eq) ∘ eq₃))
        α b | inj₂ a′ | ⟪ eq ⟫ | inj₁ tt | ⟪ eq₃ ⟫ | ()
        α b | inj₁ tt | ⟪ eq ⟫ with f₁ (inj₂ a₁) | inspect f₁ (inj₂ a₁)
        α b | inj₁ tt | ⟪ eq ⟫ | inj₁ tt | ⟪ eq₃ ⟫ = proj₁ (inj₁₁path b₁ b) (ap swap₊ (!(! (α₁ (inj₂ b)) ∘ ap f₁ eq ∘ eq₁)))
        α b | inj₁ tt | ⟪ eq ⟫ | inj₂ b′ | ⟪ eq₃ ⟫ with bad-path b′ (! (α₁ (inj₁ tt)) ∘ ap f₁ eq₂ ∘ eq₃)
        ... | ()
        β : g ○ f ∼ id
        β a with f₁ (inj₂ a) | inspect f₁ (inj₂ a)
        β a | inj₁ tt | ⟪ eq ⟫ with g₁ (inj₂ b₁) | inspect g₁ (inj₂ b₁)
        ...    | inj₁ tt | ⟪ eq₃ ⟫ = proj₁ (inj₁₁path a₁ a) (ap swap₊ (! eq₂ ∘ ! (ap g₁ eq) ∘ β₂ (inj₂ a)))
        β a | inj₁ tt | ⟪ eq ⟫ | inj₂ a′ | ⟪ eq₃ ⟫ with bad-path a′ ((! (β₂ (inj₁ tt)) ∘ ap g₁ eq₁) ∘ eq₃)
        ... | () 
        β a | inj₂ b | ⟪ eq ⟫ with g₁ (inj₂ b) | inspect g₁ (inj₂ b)
        β a | inj₂ b | ⟪ eq₃ ⟫ | inj₁ tt | ⟪ eq ⟫ with bad-path a (! eq ∘ ap g₁ (! eq₃) ∘ β₂ (inj₂ a))
        ... | ()
        β a | inj₂ b | ⟪ eq₃ ⟫ | inj₂ a′ | ⟪ eq ⟫ = proj₁ (inj₁₁path a′ a) (ap swap₊ (! eq ∘ ap g₁ (! eq₃) ∘ β₂ (inj₂ a)))

