module J where

open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.Product

data T : Set where
  N : T
  B : T

⟦_⟧ : T → Set
⟦ N ⟧ = ℕ
⟦ B ⟧ = Bool

data Fun : T → T → Set where
  square : Fun N N
  isZero :   Fun N B
  compose : {C1 C2 C3 : T} → Fun C2 C3 → Fun C1 C2 → Fun C1 C3

eval : {C1 C2 : T} → Fun C1 C2 → ⟦ C1 ⟧ → ⟦ C2 ⟧
eval square n = n * n
eval isZero 0 = true
eval isZero (suc _) = false
eval (compose g f) v = eval g (eval f v)

data T● : Set where
  _#_ : (C : T) → (v : ⟦ C ⟧) → T●

⟦_⟧● : T● → Σ[ A ∈ Set ] A
⟦ C # v ⟧● = ⟦ C ⟧ , v

data Fun● : T● → T● → Set where
  lift : {C1 C2 : T} {v : ⟦ C1 ⟧} →
         (f : Fun C1 C2) → 
         Fun● (C1 # v) (C2 # (eval f v))

test1 : Fun● (N # 3) (B # false)
test1 = lift (compose isZero square)

test2 : Fun● (N # 0) (B # true)
test2 = lift (compose isZero square)

test3 : ∀ {n} → Fun● (N # (suc n)) (B # false)
test3 = lift (compose isZero square)
