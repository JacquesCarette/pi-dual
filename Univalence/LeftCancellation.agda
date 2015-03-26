{-# OPTIONS --without-K #-}
module LeftCancellation where

open import Data.Empty 
open import Data.Unit
open import Data.Sum
open import Data.Product using (_,_; _,′_; proj₁; proj₂)
open import Function renaming (_∘_ to _○_)

open import Relation.Binary.PropositionalEquality 
  using (refl; cong; _≡_; subst; module ≡-Reasoning; inspect; [_]; Reveal_is_)  
  renaming (trans to _∘_; sym to !_)

open import Equiv
open import TypeEquiv using (swap₊)

-- This is WAY simpler than using 'with' and 'inspect'!
record Ev {A B : Set} (f : A → B) (x : A) : Set where
  constructor ev
  field
    v : B
    fx=v : f x ≡ v

mkV : {A B : Set} → (f : A → B) → (x : A) → Ev f x
mkV f x = ev (f x) refl

private
  bad-path : {A B : Set} → (a : A) → (b : B) → inj₁ a ≡ inj₂ b → ⊥
  bad-path x y ()

----------------------------------------------------------------------------
-- Very complex proof that we can cancel units on the left of ⊎

-- Some repeated patterns:
-- use injectivity of equivalences to go from f x ≡ f y to x ≡ y
injectivity : {A B : Set} (equiv : (⊤ ⊎ A) ≃ (⊤ ⊎ B)) → (a : A) → equiv ⋆ inj₁ tt ≡ equiv ⋆ inj₂ a → (inj₁ tt ≡ inj₂ a) 
injectivity equiv x path = inj≃ equiv (inj₁ tt) (inj₂ x) path


left-cancel-⊤ : {A B : Set} →  ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A ≃ B
left-cancel-⊤ {A} {B} (f₁ , mkqinv g₁ α₁ β₁) =
  let eqv = (f₁ , mkqinv g₁ α₁ β₁) in
  let v₁ = mkV f₁ (inj₁ tt) in
  let v₂ = mkV g₁ (inj₁ tt) in
  mk₁ {A} {B} eqv v₁ v₂
  where
    mk₁ : {A B : Set} (e : (⊤ ⊎ A) ≃ (⊤ ⊎ B)) → 
              let (f₁ , mkqinv g₁ α₁ β₁) = e in 
              Ev f₁ (inj₁ tt) → Ev g₁ (inj₁ tt) → A ≃ B
    mk₁ {A} {B} (f , mkqinv g α β) (ev (inj₁ tt) eq₁) (ev (inj₁ tt) eq₂) = A≃B
      where
        equiv : (⊤ ⊎ A) ≃ (⊤ ⊎ B)
        equiv = (f , mkqinv g α β)

        elim-path : {X Y Z : Set} → (e : (⊤ ⊎ X) ≃ (⊤ ⊎ Y)) → (x : X) → 
           (proj₁ e) (inj₁ tt) ≡ (proj₁ e) (inj₂ x) → Z
        elim-path e a path = ⊥-elim (bad-path tt a (injectivity e a path))

        mkf : (a : A) → Ev f (inj₂ a) → B
        mkf a (ev (inj₁ tt) eq) = elim-path equiv a (eq₁ ∘ ! eq)
        mkf a (ev (inj₂ y) fx≡v) = y

        ff : A → B
        ff a = mkf a (mkV f (inj₂ a))

        mkg : (b : B) → Ev g (inj₂ b) → A
        mkg b (ev (inj₁ tt) eq) = elim-path (sym≃ equiv) b (eq₂ ∘ ! eq)
        mkg b (ev (inj₂ a) eq) = a

        gg : B → A
        gg b = mkg b (mkV g (inj₂ b))

        mkα : (b : B) →  (e : Ev g (inj₂ b)) → ff (mkg b e) ≡ b
        mkα b (ev (inj₁ tt) eq) = elim-path (sym≃ equiv) b (eq₂ ∘ ! eq)
        mkα b (ev (inj₂ a) eq) = mkα' (mkV f (inj₂ a))
          where
            mkα' : (ev : Ev f (inj₂ a)) → mkf a ev ≡ b
            mkα' (ev (inj₁ tt) eq₃) = elim-path equiv a (eq₁ ∘ ! eq₃)
            mkα' (ev (inj₂ _) eq₃) = inj₂≡ (! (cong f eq ∘ eq₃) ∘ α (inj₂ b))

        αα : ff ○ gg ∼ id
        αα b = mkα b (mkV g (inj₂ b))

        -- need to expand the definition of ff and gg "by hand" otherwise there is 
        -- nowhere to 'stick in' the explicit e₁ and e₂ we have.
        mkβ : (a : A) → (e₁ : Ev f (inj₂ a)) → (e₂ : Ev g (inj₂ (mkf a e₁))) → mkg (mkf a e₁) e₂ ≡ a
        mkβ a (ev (inj₁ tt) eq) _ = elim-path equiv a (eq₁ ∘ ! eq)
        mkβ a (ev (inj₂ y) eq) (ev (inj₁ tt) eq₃) = elim-path (sym≃ equiv) y (eq₂ ∘ ! eq₃)
        mkβ a (ev (inj₂ _) eq) (ev (inj₂ _) eq₃) = inj₂≡ (((! eq₃) ∘ cong g (! eq)) ∘ β (inj₂ a))

        ββ : gg ○ ff ∼ id
        ββ a = let ev₁ = mkV f (inj₂ a) in mkβ a ev₁ (mkV g (inj₂ (mkf a ev₁)))

        A≃B : A ≃ B
        A≃B = ff , mkqinv gg αα ββ

    mk₁ (f , mkqinv g α β) (ev (inj₁ tt) eq₁) (ev (inj₂ a) eq₂) = 
          let e = (f , mkqinv g α β) in
         ⊥-elim (bad-path tt a (injectivity e a ((eq₁ ∘ ! (α (inj₁ tt))) ∘ cong f eq₂)))
    mk₁ (f , mkqinv g α β) (ev (inj₂ b) eq₁) (ev (inj₁ tt) eq₂) = 
         ⊥-elim (bad-path tt b (((! α (inj₁ tt)) ∘ cong f eq₂) ∘ eq₁))
    mk₁ {A} {B} (f , mkqinv g α β) (ev (inj₂ x) ftt=x) (ev (inj₂ y) gtt=y) = A≃B
      where
        equiv : (⊤ ⊎ A) ≃ (⊤ ⊎ B)
        equiv = (f , mkqinv g α β)

        elim-path : {X Y Z : Set} → (e : (⊤ ⊎ X) ≃ (⊤ ⊎ Y)) → (x : X) → 
           (proj₁ e) (inj₁ tt) ≡ (proj₁ e) (inj₂ x) → Z
        elim-path e a path = ⊥-elim (bad-path tt a (injectivity e a path))

        mkf : (a : A) → Ev f (inj₂ a) → B
        mkf a (ev (inj₁ tt) _) = x
        mkf a (ev (inj₂ y) _) = y

        ff : A → B
        ff a = mkf a (mkV f (inj₂ a))

        mkg : (b : B) → Ev g (inj₂ b) → A
        mkg b (ev (inj₁ tt) eq) = y
        mkg b (ev (inj₂ a) eq) = a

        gg : B → A
        gg b = mkg b (mkV g (inj₂ b))

        mkα : (b : B) →  (e₁ : Ev g (inj₂ b)) → (e₂ : Ev f (inj₂ (mkg b e₁))) → mkf (mkg b e₁) e₂ ≡ b
        mkα b (ev (inj₁ tt) gb=tt) (ev (inj₁ tt) fgb=tt) = inj₂≡ ((! ftt=x ∘ ! cong f gb=tt) ∘ α (inj₂ b))
        mkα b (ev (inj₁ tt) gb=tt) (ev (inj₂ y₁) fy=y₁) = elim-path (sym≃ equiv) y₁ ( ! ((! cong g fy=y₁ ∘ β (inj₂ y)) ∘ (! gtt=y)))
        mkα b (ev (inj₂ z) gb=z) (ev (inj₁ tt) fgb=tt) = elim-path (sym≃ equiv) b ((cong g (! fgb=tt) ∘ β (inj₂ z)) ∘ (! gb=z))
        mkα b (ev (inj₂ z) gb=z) (ev (inj₂ z₂) fgb=z₂) = 
            let path = (cong g (! fgb=z₂) ∘ β (inj₂ z)) ∘ ! gb=z in
            inj₂≡ (inj≃ (sym≃ equiv) (inj₂ z₂) (inj₂ b)  path)

        αα : ff ○ gg ∼ id
        αα b = let ev₁ = mkV g (inj₂ b) in mkα b ev₁ (mkV f (inj₂ (mkg b ev₁)))

        -- need to expand the definition of ff and gg "by hand" otherwise there is 
        -- nowhere to 'stick in' the explicit e₁ and e₂ we have.
        mkβ : (a : A) → (e₁ : Ev f (inj₂ a)) → (e₂ : Ev g (inj₂ (mkf a e₁))) → mkg (mkf a e₁) e₂ ≡ a
        mkβ a (ev (inj₁ tt) eq) (ev (inj₁ _) eq₃) = inj₂≡ (! (cong g eq ∘ gtt=y) ∘ β (inj₂ a))
        mkβ a (ev (inj₁ tt) eq) (ev (inj₂ y₁) eq₃) = elim-path equiv y₁ ((ftt=x ∘ (! α (inj₂ x))) ∘ cong f eq₃)
        mkβ a (ev (inj₂ z) fa=z) (ev (inj₁ tt) eq₃) = elim-path equiv a ((cong f (! eq₃) ∘ α (inj₂ z)) ∘ (! fa=z) )
        mkβ a (ev (inj₂ _) fa=y) (ev (inj₂ _) eq₃) = inj₂≡ (((! eq₃) ∘ cong g (! fa=y)) ∘ β (inj₂ a))

        ββ : gg ○ ff ∼ id
        ββ a = let ev₁ = mkV f (inj₂ a) in mkβ a ev₁ (mkV g (inj₂ (mkf a ev₁)))

        A≃B : A ≃ B
        A≃B = ff , mkqinv gg αα ββ
