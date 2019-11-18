
module J where

open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.Product

data Code : Set where
  N : Code
  B : Code

⟦_⟧ : Code → Set
⟦ N ⟧ = ℕ
⟦ B ⟧ = Bool

data Fun : Code → Code → Set where
  square : Fun N N
  isZero :   Fun N B
  compose : {C1 C2 C3 : Code} → Fun C2 C3 → Fun C1 C2 → Fun C1 C3


eval : {C1 C2 : Code} → Fun C1 C2 → ⟦ C1 ⟧ → ⟦ C2 ⟧
eval square n = n * n
eval isZero 0 = true
eval isZero (suc _) = false
eval (compose g f) v = eval g (eval f v)

data Code● : Set where
  _#_ : (C : Code) → (v : ⟦ C ⟧) → Code●

⟦_⟧● : Code● → Σ[ A ∈ Set ] A
⟦ C # v ⟧● = ⟦ C ⟧ , v

data Fun● : Code● → Code● → Set where
  lift : {C1 C2 : Code} {v : ⟦ C1 ⟧} →
         (f : Fun C1 C2) → 
         Fun● (C1 # v) (C2 # (eval f v))

test1 : Fun● (N # 3) (B # false)
test1 = lift (compose isZero square)
