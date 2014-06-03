module Pin where 

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

infixr 30 _⟷_
infixr 30 _⟺_

-- N-dimensional version of Pi

-- Types indexed by dimension... n-dimensional cubes

-- base are 0d types which are the usual finite types

data T : Set where
  Zero  : T
  One   : T
  Plus  : T → T → T
  Times : T → T → T

⟦_⟧ : T → Set
⟦ Zero ⟧         = ⊥
⟦ One ⟧          = ⊤
⟦ Plus t1 t2 ⟧   = ⟦ t1 ⟧ ⊎ ⟦ t2 ⟧
⟦ Times t1 t2 ⟧  = ⟦ t1 ⟧ × ⟦ t2 ⟧

-- n-dimensional types represented as trees of depth n

data C : (n : ℕ) → Set where
  ZD   : T → C 0
  Node : {n : ℕ} → C n → C n → C (suc n)

zeroN : (n : ℕ) → C n
zeroN 0 = ZD Zero
zeroN (suc n) = Node (zeroN n) (zeroN n)

oneN : (n : ℕ) → C n
oneN 0 = ZD One
oneN (suc n) = Node (oneN n) (zeroN n)

plus : {n : ℕ} → C n → C n → C n
plus (ZD t1) (ZD t2) = ZD (Plus t1 t2)
plus (Node c1 c2) (Node c1' c2') = Node (plus c1 c1') (plus c2 c2')

times : {m n : ℕ} → C m → C n → C (m + n)
times (ZD t1) (ZD t2) = ZD (Times t1 t2)
times (ZD t) (Node c1 c2) = Node (times (ZD t) c1) (times (ZD t) c2)
times (Node c1 c2) c = Node (times c1 c) (times c2 c)

-- Combinators on 0d types

data _⟷_ : T → T → Set where
  unite₊  : { t : T } → Plus Zero t ⟷ t
  uniti₊  : { t : T } → t ⟷ Plus Zero t
  swap₊   : { t₁ t₂ : T } → Plus t₁ t₂ ⟷ Plus t₂ t₁
  assocl₊ : { t₁ t₂ t₃ : T } → Plus t₁ (Plus t₂ t₃) ⟷ Plus (Plus t₁ t₂) t₃
  assocr₊ : { t₁ t₂ t₃ : T } → Plus (Plus t₁ t₂) t₃ ⟷ Plus t₁ (Plus t₂ t₃)
  unite⋆  : { t : T } → Times One t ⟷ t
  uniti⋆  : { t : T } → t ⟷ Times One t
  swap⋆   : { t₁ t₂ : T } → Times t₁ t₂ ⟷ Times t₂ t₁
  assocl⋆ : { t₁ t₂ t₃ : T } → Times t₁ (Times t₂ t₃) ⟷ Times (Times t₁ t₂) t₃
  assocr⋆ : { t₁ t₂ t₃ : T } → Times (Times t₁ t₂) t₃ ⟷ Times t₁ (Times t₂ t₃)
  distz    : { t : T } → Times Zero t ⟷ Zero
  factorz  : { t : T } → Zero ⟷ Times Zero t
  dist    : { t₁ t₂ t₃ : T } → 
            Times (Plus t₁ t₂) t₃ ⟷ Plus (Times t₁ t₃) (Times t₂ t₃) 
  factor  : { t₁ t₂ t₃ : T } → 
            Plus (Times t₁ t₃) (Times t₂ t₃) ⟷ Times (Plus t₁ t₂) t₃
  id⟷   : { t : T } → t ⟷ t
  sym    : { t₁ t₂ : T } → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
  _◎_    : { t₁ t₂ t₃ : T } → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_    : { t₁ t₂ t₃ t₄ : T } → 
           (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (Plus t₁ t₂ ⟷ Plus t₃ t₄)
  _⊗_    : { t₁ t₂ t₃ t₄ : T } → 
           (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (Times t₁ t₂ ⟷ Times t₃ t₄)

-- Combinators on nd types
  
data _⟺_ : {m n : ℕ} → C m → C n → Set where
  base : { t₁ t₂ : T } → (t₁ ⟷ t₂) → (ZD t₁ ⟺ ZD t₂)
  unite₊  : { n : ℕ } { c : C n } → plus (zeroN n) c ⟺ c
  uniti₊  : { n : ℕ } { c : C n } → c ⟺ plus (zeroN n) c 
  swap₊   : { n : ℕ } { c₁ c₂ : C n } → plus c₁ c₂ ⟺ plus c₂ c₁
  assocl₊ : { n : ℕ } { c₁ c₂ c₃ : C n } → 
            plus c₁ (plus c₂ c₃) ⟺ plus (plus c₁ c₂) c₃
  assocr₊ : { n : ℕ } { c₁ c₂ c₃ : C n } → 
            plus (plus c₁ c₂) c₃ ⟺ plus c₁ (plus c₂ c₃)
  unite⋆  : { m n : ℕ } { c : C n } → times (oneN m) c ⟺ c
  uniti⋆  : { m n : ℕ } { c : C n } → c ⟺ times (oneN m) c
  swap⋆   : { m n : ℕ } { c₁ : C m } { c₂ : C n } → times c₁ c₂ ⟺ times c₂ c₁
  assocl⋆ : { m n k : ℕ } { c₁ : C m } { c₂ : C n } { c₃ : C k } → 
            times c₁ (times c₂ c₃) ⟺ times (times c₁ c₂) c₃
  assocr⋆ : { m n k : ℕ } { c₁ : C m } { c₂ : C n } { c₃ : C k } → 
            times (times c₁ c₂) c₃ ⟺ times c₁ (times c₂ c₃)
  distz    : { m n : ℕ } { c : C n } → times (zeroN m) c ⟺ zeroN m
  factorz  : { m n : ℕ } { c : C n } → zeroN m ⟺ times (zeroN m) c
  dist    : { m n : ℕ } { c₁ c₂ : C m } { c₃ : C n } → 
            times (plus c₁ c₂) c₃ ⟺ plus (times c₁ c₃) (times c₂ c₃) 
  factor  : { m n : ℕ } { c₁ c₂ : C m } { c₃ : C n } → 
            plus (times c₁ c₃) (times c₂ c₃) ⟺ times (plus c₁ c₂) c₃
  id⟷   : { n : ℕ } { c : C n } → c ⟺ c
  sym    : { m n : ℕ } { c₁ : C m } { c₂ : C n } → (c₁ ⟺ c₂) → (c₂ ⟺ c₁)
  _◎_    : { m n k : ℕ } { c₁ : C m } { c₂ : C n } { c₃ : C k } → 
           (c₁ ⟺ c₂) → (c₂ ⟺ c₃) → (c₁ ⟺ c₃) 
  _⊕_    : { m n : ℕ } { c₁ c₃ : C m } { c₂ c₄ : C n } → 
           (c₁ ⟺ c₂) → (c₃ ⟺ c₄) → (plus c₁ c₃ ⟺ plus c₂ c₄)
  _⊗_    : { m n k p : ℕ } { c₁ : C m } { c₂ : C n } { c₃ : C k } { c₄ : C p } → 
           (c₁ ⟺ c₂) → (c₃ ⟺ c₄) → (times c₁ c₃ ⟺ times c₂ c₄)

