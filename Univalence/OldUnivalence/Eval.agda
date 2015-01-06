module Eval where

open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import FT -- Finite Types

_∘_ = trans

mutual
  evalComb : {a b : FT} → a ⇛ b → ⟦ a ⟧ → ⟦ b ⟧
  evalComb unite₊⇛ (inj₁ ())
  evalComb unite₊⇛ (inj₂ y) = y
  evalComb uniti₊⇛ v = inj₂ v
  evalComb swap₊⇛ (inj₁ x) = inj₂ x
  evalComb swap₊⇛ (inj₂ y) = inj₁ y
  evalComb assocl₊⇛ (inj₁ x) = inj₁ (inj₁ x)
  evalComb assocl₊⇛ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalComb assocl₊⇛ (inj₂ (inj₂ y)) = inj₂ y
  evalComb assocr₊⇛ (inj₁ (inj₁ x)) = inj₁ x
  evalComb assocr₊⇛ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalComb assocr₊⇛ (inj₂ y) = inj₂ (inj₂ y)
  evalComb unite⋆⇛ (tt , proj₂) = proj₂
  evalComb uniti⋆⇛ v = tt , v
  evalComb swap⋆⇛ (proj₁ , proj₂) = proj₂ , proj₁
  evalComb assocl⋆⇛ (proj₁ , proj₂ , proj₃) = (proj₁ , proj₂) , proj₃
  evalComb assocr⋆⇛ ((proj₁ , proj₂) , proj₃) = proj₁ , proj₂ , proj₃
  evalComb distz⇛ (() , proj₂)
  evalComb factorz⇛ ()
  evalComb dist⇛ (inj₁ x , proj₂) = inj₁ (x , proj₂)
  evalComb dist⇛ (inj₂ y , proj₂) = inj₂ (y , proj₂)
  evalComb factor⇛ (inj₁ (proj₁ , proj₂)) = inj₁ proj₁ , proj₂
  evalComb factor⇛ (inj₂ (proj₁ , proj₂)) = inj₂ proj₁ , proj₂
  evalComb id⇛ v = v
  evalComb (sym⇛ c) v = evalBComb c v 
  evalComb (c₁ ◎ c₂) v = evalComb c₂ (evalComb c₁ v)
  evalComb (c ⊕ c₁) (inj₁ x) = inj₁ (evalComb c x)
  evalComb (c ⊕ c₁) (inj₂ y) = inj₂ (evalComb c₁ y)
  evalComb (c ⊗ c₁) (proj₁ , proj₂) = evalComb c proj₁ , evalComb c₁ proj₂

  evalBComb : {a b : FT} → a ⇛ b → ⟦ b ⟧ → ⟦ a ⟧
  evalBComb unite₊⇛ v = inj₂ v
  evalBComb uniti₊⇛ (inj₁ ())
  evalBComb uniti₊⇛ (inj₂ y) = y
  evalBComb swap₊⇛ (inj₁ x) = inj₂ x
  evalBComb swap₊⇛ (inj₂ y) = inj₁ y
  evalBComb assocl₊⇛ (inj₁ (inj₁ x)) = inj₁ x
  evalBComb assocl₊⇛ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalBComb assocl₊⇛ (inj₂ y) = inj₂ (inj₂ y)
  evalBComb assocr₊⇛ (inj₁ x) = inj₁ (inj₁ x)
  evalBComb assocr₊⇛ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalBComb assocr₊⇛ (inj₂ (inj₂ y)) = inj₂ y
  evalBComb unite⋆⇛ x = tt , x
  evalBComb uniti⋆⇛ (tt , x) = x
  evalBComb swap⋆⇛ (x , y) = y , x
  evalBComb assocl⋆⇛ ((x , y) , z) = x , y , z
  evalBComb assocr⋆⇛ (x , y , z) = (x , y) , z
  evalBComb distz⇛ ()
  evalBComb factorz⇛ (() , _)
  evalBComb dist⇛ (inj₁ (proj₁ , proj₂)) = inj₁ proj₁ , proj₂
  evalBComb dist⇛ (inj₂ (proj₁ , proj₂)) = inj₂ proj₁ , proj₂
  evalBComb factor⇛ (inj₁ x , proj₂) = inj₁ (x , proj₂)
  evalBComb factor⇛ (inj₂ y , proj₂) = inj₂ (y , proj₂)
  evalBComb id⇛ x = x
  evalBComb (sym⇛ c) x = evalComb c x
  evalBComb (c ◎ c₁) x = evalBComb c (evalBComb c₁ x)
  evalBComb (c ⊕ c₁) (inj₁ x) = inj₁ (evalBComb c x)
  evalBComb (c ⊕ c₁) (inj₂ y) = inj₂ (evalBComb c₁ y)
  evalBComb (c ⊗ c₁) (proj₁ , proj₂) = evalBComb c proj₁ , evalBComb c₁ proj₂

mutual
  Comb∘BComb : {a b : FT} → (c : a ⇛ b) → ∀ x → evalBComb c (evalComb c x) ≡ x
  Comb∘BComb unite₊⇛ (inj₁ ())
  Comb∘BComb unite₊⇛ (inj₂ y) = refl 
  Comb∘BComb uniti₊⇛ x = refl 
  Comb∘BComb swap₊⇛ (inj₁ x) = refl
  Comb∘BComb swap₊⇛ (inj₂ y) = refl
  Comb∘BComb assocl₊⇛ (inj₁ x) = refl 
  Comb∘BComb assocl₊⇛ (inj₂ (inj₁ x)) = refl 
  Comb∘BComb assocl₊⇛ (inj₂ (inj₂ y)) = refl 
  Comb∘BComb assocr₊⇛ (inj₁ (inj₁ x)) = refl 
  Comb∘BComb assocr₊⇛ (inj₁ (inj₂ y)) = refl 
  Comb∘BComb assocr₊⇛ (inj₂ y) = refl
  Comb∘BComb unite⋆⇛ (tt , y) = refl
  Comb∘BComb uniti⋆⇛ x = refl
  Comb∘BComb swap⋆⇛ (x , y) = refl
  Comb∘BComb assocl⋆⇛ (x , y , z) = refl
  Comb∘BComb assocr⋆⇛ ((x , y) , z) = refl
  Comb∘BComb distz⇛ (() , _)
  Comb∘BComb factorz⇛ ()
  Comb∘BComb dist⇛ (inj₁ x , y) = refl
  Comb∘BComb dist⇛ (inj₂ x , y) = refl
  Comb∘BComb factor⇛ (inj₁ (x , y)) = refl
  Comb∘BComb factor⇛ (inj₂ (x , y)) = refl
  Comb∘BComb id⇛ x = refl 
  Comb∘BComb (sym⇛ c) x = BComb∘Comb c x
  Comb∘BComb (c₀ ◎ c₁) x = 
    cong (evalBComb c₀)  (Comb∘BComb c₁ (evalComb c₀ x)) ∘ Comb∘BComb c₀ x
  Comb∘BComb (c₀ ⊕ c₁) (inj₁ x) = cong inj₁ (Comb∘BComb c₀ x)
  Comb∘BComb (c₀ ⊕ c₁) (inj₂ y) = cong inj₂ (Comb∘BComb c₁ y)
  Comb∘BComb (c₀ ⊗ c₁) (x , y) = cong₂ _,_ (Comb∘BComb c₀ x) (Comb∘BComb c₁ y)

  BComb∘Comb : {a b : FT} → (c : a ⇛ b) → ∀ x → evalComb c (evalBComb c x) ≡ x
  BComb∘Comb unite₊⇛ x = refl 
  BComb∘Comb uniti₊⇛ (inj₁ ())
  BComb∘Comb uniti₊⇛ (inj₂ y) = refl 
  BComb∘Comb swap₊⇛ (inj₁ x) = refl 
  BComb∘Comb swap₊⇛ (inj₂ y) = refl 
  BComb∘Comb assocl₊⇛ (inj₁ (inj₁ x)) = refl 
  BComb∘Comb assocl₊⇛ (inj₁ (inj₂ y)) = refl 
  BComb∘Comb assocl₊⇛ (inj₂ y) = refl 
  BComb∘Comb assocr₊⇛ (inj₁ x) = refl 
  BComb∘Comb assocr₊⇛ (inj₂ (inj₁ x)) = refl 
  BComb∘Comb assocr₊⇛ (inj₂ (inj₂ y)) = refl
  BComb∘Comb unite⋆⇛ x = refl 
  BComb∘Comb uniti⋆⇛ (tt , proj₂) = refl 
  BComb∘Comb swap⋆⇛ (proj₁ , proj₂) = refl 
  BComb∘Comb assocl⋆⇛ ((proj₁ , proj₂) , proj₃) = refl 
  BComb∘Comb assocr⋆⇛ (proj₁ , proj₂ , proj₃) = refl 
  BComb∘Comb distz⇛ ()
  BComb∘Comb factorz⇛ (() , _)
  BComb∘Comb dist⇛ (inj₁ (proj₁ , proj₂)) = refl 
  BComb∘Comb dist⇛ (inj₂ (proj₁ , proj₂)) = refl 
  BComb∘Comb factor⇛ (inj₁ x , proj₂) = refl 
  BComb∘Comb factor⇛ (inj₂ y , proj₂) = refl 
  BComb∘Comb id⇛ x = refl 
  BComb∘Comb (sym⇛ c) x = Comb∘BComb c x
  BComb∘Comb (c₀ ◎ c₁) x = 
    cong (evalComb c₁) (BComb∘Comb c₀ (evalBComb c₁ x)) ∘ BComb∘Comb c₁ x
  BComb∘Comb (c ⊕ c₁) (inj₁ x) = cong inj₁ (BComb∘Comb c x)
  BComb∘Comb (c ⊕ c₁) (inj₂ y) = cong inj₂ (BComb∘Comb c₁ y)
  BComb∘Comb (c ⊗ c₁) (x , y) = cong₂ _,_ (BComb∘Comb c x) (BComb∘Comb c₁ y)

-----------------------------------------------------------------------------------

-- evaluate the alternative interpretation; A needs to be a pointed type.
mutual
  evalComb′ : {a b : FT} {A : Set} {pt : A} → a ⇛ b → ⟦ a ⟧′ A → ⟦ b ⟧′ A
  evalComb′ unite₊⇛ (inj₁ ())
  evalComb′ unite₊⇛ (inj₂ y) = y
  evalComb′ uniti₊⇛ x = inj₂ x
  evalComb′ swap₊⇛ (inj₁ x) = inj₂ x
  evalComb′ swap₊⇛ (inj₂ y) = inj₁ y
  evalComb′ assocl₊⇛ (inj₁ x) = inj₁ (inj₁ x)
  evalComb′ assocl₊⇛ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalComb′ assocl₊⇛ (inj₂ (inj₂ y)) = inj₂ y
  evalComb′ assocr₊⇛ (inj₁ (inj₁ x)) = inj₁ x
  evalComb′ assocr₊⇛ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalComb′ assocr₊⇛ (inj₂ y) = inj₂ (inj₂ y)
  evalComb′ unite⋆⇛ (_ , x) = x
  evalComb′ {pt = a} uniti⋆⇛ x = a , x
  evalComb′ swap⋆⇛ (x , y) = y , x
  evalComb′ assocl⋆⇛ (x , y , z) = (x , y) , z
  evalComb′ assocr⋆⇛ ((x , y) , z) = x , y , z
  evalComb′ distz⇛ (() , _)
  evalComb′ factorz⇛ ()
  evalComb′ dist⇛ (inj₁ x , z) = inj₁ (x , z)
  evalComb′ dist⇛ (inj₂ y , z) = inj₂ (y , z)
  evalComb′ factor⇛ (inj₁ (x , y)) = inj₁ x , y
  evalComb′ factor⇛ (inj₂ (x , y)) = inj₂ x , y
  evalComb′ id⇛ x = x
  evalComb′ {pt = a} (sym⇛ c) x = evalBComb′ {pt = a} c x
  evalComb′ {pt = a} (c₀ ◎ c₁) x = evalComb′ {pt = a} c₁ (evalComb′ {pt = a} c₀ x)
  evalComb′ {pt = a} (c₀ ⊕ c₁) (inj₁ x) = inj₁ (evalComb′ {pt = a} c₀ x)
  evalComb′ {pt = a} (c₀ ⊕ c₁) (inj₂ y) = inj₂ (evalComb′ {pt = a} c₁ y)
  evalComb′ {pt = a} (c₀ ⊗ c₁) (x , y) = evalComb′ {pt = a} c₀ x , evalComb′ {pt = a} c₁ y

  evalBComb′ : {a b : FT} {A : Set} {pt : A} → a ⇛ b → ⟦ b ⟧′ A → ⟦ a ⟧′ A
  evalBComb′ unite₊⇛ x = inj₂ x
  evalBComb′ uniti₊⇛ (inj₁ ())
  evalBComb′ uniti₊⇛ (inj₂ y) = y
  evalBComb′ swap₊⇛ (inj₁ x) = inj₂ x
  evalBComb′ swap₊⇛ (inj₂ y) = inj₁ y
  evalBComb′ assocl₊⇛ (inj₁ (inj₁ x)) = inj₁ x
  evalBComb′ assocl₊⇛ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalBComb′ assocl₊⇛ (inj₂ y) = inj₂ (inj₂ y)
  evalBComb′ assocr₊⇛ (inj₁ x) = inj₁ (inj₁ x)
  evalBComb′ assocr₊⇛ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalBComb′ assocr₊⇛ (inj₂ (inj₂ y)) = inj₂ y
  evalBComb′ {pt = a} unite⋆⇛ x = a , x
  evalBComb′ uniti⋆⇛ (_ , y) = y
  evalBComb′ swap⋆⇛ (x , y) = y , x
  evalBComb′ assocl⋆⇛ ((x , y) , z) = x , y , z
  evalBComb′ assocr⋆⇛ (x , y , z) = (x , y) , z
  evalBComb′ distz⇛ ()
  evalBComb′ factorz⇛ (() , _)
  evalBComb′ dist⇛ (inj₁ (x , y)) = inj₁ x , y
  evalBComb′ dist⇛ (inj₂ (x , y)) = inj₂ x , y
  evalBComb′ factor⇛ (inj₁ x , z) = inj₁ (x , z)
  evalBComb′ factor⇛ (inj₂ y , z) = inj₂ (y , z)
  evalBComb′ id⇛ x = x
  evalBComb′ {pt = a} (sym⇛ c) x = evalComb′ {pt = a} c x
  evalBComb′ {pt = a} (c₀ ◎ c₁) x = evalBComb′ {pt = a} c₀ (evalBComb′ {pt = a} c₁ x)
  evalBComb′ {pt = a} (c₀ ⊕ c₁) (inj₁ x) = inj₁ (evalBComb′ {pt = a} c₀ x)
  evalBComb′ {pt = a} (c₀ ⊕ c₁) (inj₂ y) = inj₂ (evalBComb′ {pt = a} c₁ y)
  evalBComb′ {pt = a} (c₀ ⊗ c₁) (x , y) = evalBComb′ {pt = a} c₀ x , evalBComb′ {pt = a} c₁ y

---

SWAP12 SWAP23 SWAP13 : PLUS ONE (PLUS ONE ONE) ⇛ PLUS ONE (PLUS ONE ONE)
SWAP12 = assocl₊⇛ ◎ (swap₊⇛ ⊕ id⇛) ◎ assocr₊⇛
SWAP23 = id⇛ ⊕ swap₊⇛
SWAP13 = SWAP23 ◎ SWAP12 ◎ SWAP23 

x121 = evalComb SWAP12 (inj₁ tt)         -- 0 -> 1
x122 = evalComb SWAP12 (inj₂ (inj₁ tt))  -- 1 -> 0
x123 = evalComb SWAP12 (inj₂ (inj₂ tt))  -- 2 -> 2

x231 = evalComb SWAP23 (inj₁ tt)         -- 0 -> 0
x232 = evalComb SWAP23 (inj₂ (inj₁ tt))  -- 1 -> 2
x233 = evalComb SWAP23 (inj₂ (inj₂ tt))  -- 2 -> 1

x131 = evalComb SWAP13 (inj₁ tt)         -- 0 -> 2
x132 = evalComb SWAP13 (inj₂ (inj₁ tt))  -- 1 -> 1
x133 = evalComb SWAP13 (inj₂ (inj₂ tt))  -- 2 -> 0

