\newcommand{\Jone}{%
\begin{code}
module J where

open import Data.Bool hiding (T)
open import Data.Nat
open import Data.Sum
open import Data.Product
\end{code}}
\newcommand{\Jexample}{%
\begin{code}
data T : Set where
  N  : T
  B  : T

⟦_⟧ : T → Set
⟦ N ⟧  = ℕ
⟦ B ⟧  = Bool

data Fun : T → T → Set where
  square   : Fun N N
  isZero   : Fun N B
  compose  : {a b c : T} → Fun b c → Fun a b → Fun a c

eval : {a b : T} → Fun a b → ⟦ a ⟧ → ⟦ b ⟧
eval square n = n * n
eval isZero 0 = true
eval isZero (suc _) = false
eval (compose g f) v = eval g (eval f v)
\end{code}}
\newcommand{\Jexamplecont}{%
\begin{code}
data T∙ : Set where
  _#_ : (a : T) → (v : ⟦ a ⟧) → T∙

⟦_⟧∙ : T∙ → Σ[ A ∈ Set ] A
⟦ T # v ⟧∙ = ⟦ T ⟧ , v

data Fun∙ : T∙ → T∙ → Set where
  lift : {a b : T} {v : ⟦ a ⟧} → (f : Fun a b) → 
         Fun∙ (a # v) (b # (eval f v))
\end{code}}
\newcommand{\Jexampletest}{%
\begin{code}
test1 : Fun∙ (N # 3) (B # false)
test1 = lift (compose isZero square)

test2 : Fun∙ (N # 0) (B # true)
test2 = lift (compose isZero square)

test3 : ∀ {n} → Fun∙ (N # (suc n)) (B # false)
test3 = lift (compose isZero square)
\end{code}}
