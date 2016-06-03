{-# OPTIONS --without-K #-}

module PiPointed where

open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)

open import PiU using (U; ZERO; ONE; PLUS; TIMES; toℕ)
open import PiLevel0
open import PiEquiv renaming (eval to ap; evalB to apB)

data Pointed (t : U) : Set where
  ∙ : ⟦ t ⟧ → Pointed t

-- yes, re-use name eval on purpose here
eval : {t₁ t₂ : U} → (t₁ ⟷ t₂) → Pointed t₁ → Pointed t₂
eval c (∙ x) = ∙ (ap c x)

record V (t : U) : Set where
  constructor v
  field
    pt : ⟦ t ⟧
    auto : t ⟷ t

evalV : {t₁ t₂ : U} → (t₁ ⟷ t₂) → V t₁ → V t₂
evalV c (v pt auto) = v (ap c pt) (! c ◎ auto ◎ c)

data U↑ : Set where
  ↑ : U → U↑
  1/ : U → U↑
  DTimes : U↑ → U↑ → U↑

infix 40 _⇿_

data _⇿_ : U↑ → U↑ → Set where
  ↑ : {t₁ t₂ : U} → t₁ ⟷ t₂  → ↑ t₁ ⇿ ↑ t₂
  ev : {t₁ : U} → DTimes (↑ t₁) (1/ t₁) ⇿ ↑ ONE
  coev : {t₁ : U} {base : Pointed t₁} → ↑ ONE ⇿ DTimes (↑ t₁) (1/ t₁)
  id⇿ : {t₁ : U↑} → t₁ ⇿ t₁ -- needed for coev of DTimes

⟦_⟧↑ : U↑ → Set
⟦ ↑ x ⟧↑ = ⟦ x ⟧
⟦ 1/ x ⟧↑ = (z : ⟦ x ⟧) → ⟦ ONE ⟧ -- not dependent (yet)
⟦ DTimes x t ⟧↑ = ⟦ x ⟧↑ × ⟦ t ⟧↑

record W (t : U↑) : Set where
  constructor w
  field
    pt : ⟦ t ⟧↑
    auto : t ⇿ t
  
eval3 : {t₁ t₂ : U↑} → t₁ ⇿ t₂ → W t₁ → W t₂
eval3 (↑ c) (w pt (↑ a)) = 
  let vv = evalV c (v pt a) in
  w (V.pt vv) (↑ (V.auto vv))
eval3 (↑ c) (w pt id⇿) = 
  let vv = evalV c (v pt id⟷) in
  w (V.pt vv) (↑ (V.auto vv))
eval3 ev (w (p₁ , f) auto) = w (f p₁) (↑ id⟷)
eval3 (coev {base = ∙ p}) (w tt x) = w (p , (λ _ → tt)) id⇿
eval3 id⇿ x = x
