{-# OPTIONS --without-K #-}
module Inspect where

open import Data.Unit.Core

open import SimpleHoTT using (refl;_≡_)

------------------------------------------------------------------------
-- Inspect on steroids (borrowed from standard library)

-- Inspect on steroids can be used when you want to pattern match on
-- the result r of some expression e, and you also need to "remember"
-- that r ≡ e.

data Reveal_is_ {a} {A : Set a} (x : Hidden A) (y : A) : Set a where
  ⟪_⟫ : (eq : reveal x ≡ y) → Reveal x is y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
inspect f x = ⟪ refl (f x) ⟫


