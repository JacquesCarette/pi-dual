module Pin where 

-- N-dimensional version of Pi

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum 
open import Data.Product 
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

infixr 30 _⟷_
infixr 30 _⟺_

------------------------------------------------------------------------------
-- base types (or 0d types) are the usual finite types

data T : Set where
  Zero  : T
  One   : T
  Plus  : T → T → T
  Times : T → T → T

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

-- Semantics 

⟦_⟧ : T → Set
⟦ Zero ⟧         = ⊥
⟦ One ⟧          = ⊤
⟦ Plus t1 t2 ⟧   = ⟦ t1 ⟧ ⊎ ⟦ t2 ⟧
⟦ Times t1 t2 ⟧  = ⟦ t1 ⟧ × ⟦ t2 ⟧

mutual

  eval : {t₁ t₂ : T} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
  eval unite₊ (inj₁ ())
  eval unite₊ (inj₂ v) = v
  eval uniti₊ v = inj₂ v
  eval swap₊ (inj₁ v) = inj₂ v
  eval swap₊ (inj₂ v) = inj₁ v
  eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
  eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
  eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
  eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
  eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
  eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
  eval unite⋆ (tt , v) = v
  eval uniti⋆ v = (tt , v)
  eval swap⋆ (v1 , v2) = (v2 , v1)
  eval assocl⋆ (v1 , (v2 , v3)) = ((v1 , v2) , v3)
  eval assocr⋆ ((v1 , v2) , v3) = (v1 , (v2 , v3))
  eval distz (() , v)
  eval factorz ()
  eval dist (inj₁ v1 , v3) = inj₁ (v1 , v3)
  eval dist (inj₂ v2 , v3) = inj₂ (v2 , v3)
  eval factor (inj₁ (v1 , v3)) = (inj₁ v1 , v3)
  eval factor (inj₂ (v2 , v3)) = (inj₂ v2 , v3)
  eval id⟷ v = v
  eval (sym c) v = evalB c v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
  eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
  eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

  evalB : {t₁ t₂ : T} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
  evalB unite₊ v = inj₂ v
  evalB uniti₊ (inj₁ ())
  evalB uniti₊ (inj₂ v) = v
  evalB swap₊ (inj₁ v) = inj₂ v
  evalB swap₊ (inj₂ v) = inj₁ v
  evalB assocl₊ (inj₁ (inj₁ v)) = inj₁ v
  evalB assocl₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
  evalB assocl₊ (inj₂ v) = inj₂ (inj₂ v)
  evalB assocr₊ (inj₁ v) = inj₁ (inj₁ v)
  evalB assocr₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
  evalB assocr₊ (inj₂ (inj₂ v)) = inj₂ v
  evalB unite⋆ v = (tt , v)
  evalB uniti⋆ (tt , v) = v
  evalB swap⋆ (v1 , v2) = (v2 , v1)
  evalB assocl⋆ ((v1 , v2) , v3) = (v1 , (v2 , v3))
  evalB assocr⋆ (v1 , (v2 , v3)) = ((v1 , v2) , v3)
  evalB distz ()
  evalB factorz (() , v)
  evalB dist (inj₁ (v1 , v3)) = (inj₁ v1 , v3)
  evalB dist (inj₂ (v2 , v3)) = (inj₂ v2 , v3)
  evalB factor (inj₁ v1 , v3) = inj₁ (v1 , v3)
  evalB factor (inj₂ v2 , v3) = inj₂ (v2 , v3)
  evalB id⟷ v = v
  evalB (sym c) v = eval c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (inj₁ v) = inj₁ (evalB c₁ v)
  evalB (c₁ ⊕ c₂) (inj₂ v) = inj₂ (evalB c₂ v)
  evalB (c₁ ⊗ c₂) (v₁ , v₂) = (evalB c₁ v₁ , evalB c₂ v₂)

------------------------------------------------------------------------------
-- Types indexed by dimension... n-dimensional cubes
-- n-dimensional types represented as trees of depth n

data C : ℕ → Set where
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


-- Combinators on nd types
  
data _⟺_ : {m n : ℕ} → C m → C n → Set where
  baseC : { t₁ t₂ : T } → (t₁ ⟷ t₂) → (ZD t₁ ⟺ ZD t₂)
  nodeC : { m n : ℕ } { c₁ c₃ : C m } { c₂ c₄ : C n } → 
           (c₁ ⟺ c₂) → (c₃ ⟺ c₄) → (Node c₁ c₃ ⟺ Node c₂ c₄)

raiseC : {m n : ℕ} → C n → C (m + n)
raiseC {0} {n} c = c
raiseC {suc m} {n} c = {!!} -- raiseC {m} {suc n} (Node c (zeroN n))

uniteN₊ : { n : ℕ } { c : C n } → plus (zeroN n) c ⟺ c
uniteN₊ {0} {ZD t} = baseC (unite₊ {t})
uniteN₊ {suc n} {Node c₁ c₂} = 
  nodeC (uniteN₊ {n} {c₁}) (uniteN₊ {n} {c₂})

unitiN₊ : { n : ℕ } { c : C n } → c ⟺ plus (zeroN n) c 
unitiN₊ {0} {ZD t} = baseC (uniti₊ {t})
unitiN₊ {suc n} {Node c₁ c₂} = 
  nodeC (unitiN₊ {n} {c₁}) (unitiN₊ {n} {c₂})

swapN₊ : { n : ℕ } { c₁ c₂ : C n } → plus c₁ c₂ ⟺ plus c₂ c₁
swapN₊ {0} {ZD t₁} {ZD t₂} = baseC (swap₊ {t₁} {t₂})
swapN₊ {suc n} {Node c₁ c₂} {Node c₁' c₂'} = 
  nodeC (swapN₊ {n} {c₁} {c₁'}) (swapN₊ {n} {c₂} {c₂'})

assoclN₊ : { n : ℕ } { c₁ c₂ c₃ : C n } → 
           plus c₁ (plus c₂ c₃) ⟺ plus (plus c₁ c₂) c₃
assoclN₊ {0} {ZD t₁} {ZD t₂} {ZD t₃} = baseC (assocl₊ {t₁} {t₂} {t₃})
assoclN₊ {suc n} {Node c₁ c₂} {Node c₃ c₄} {Node c₅ c₆} = 
  nodeC (assoclN₊ {n} {c₁} {c₃} {c₅}) (assoclN₊ {n} {c₂} {c₄} {c₆})

assocrN₊ : { n : ℕ } { c₁ c₂ c₃ : C n } → 
           plus (plus c₁ c₂) c₃ ⟺ plus c₁ (plus c₂ c₃)
assocrN₊ {0} {ZD t₁} {ZD t₂} {ZD t₃} = baseC (assocr₊ {t₁} {t₂} {t₃})
assocrN₊ {suc n} {Node c₁ c₂} {Node c₃ c₄} {Node c₅ c₆} = 
  nodeC (assocrN₊ {n} {c₁} {c₃} {c₅}) (assocrN₊ {n} {c₂} {c₄} {c₆})

distzN : {m n : ℕ} {c : C n} → times (zeroN m) c ⟺ zeroN (m + n)
distzN {0} {0} {ZD t} = baseC (distz {t})
distzN {0} {suc n} {Node c₁ c₂} = 
  nodeC (distzN {0} {n} {c₁}) (distzN {0} {n} {c₂})
distzN {suc m} {n} {c} = 
  nodeC (distzN {m} {n} {c}) (distzN {m} {n} {c})

uniteN⋆ : { m n : ℕ } { c : C n } → times (oneN m) c ⟺ c
uniteN⋆ {0} {0} {ZD t} = baseC (unite⋆ {t})
uniteN⋆ {0} {suc n} {Node c₁ c₂} = 
  nodeC (uniteN⋆ {0} {n} {c₁}) (uniteN⋆ {0} {n} {c₂})
uniteN⋆ {suc m} {n} {c} = {!!} 
  -- nodeC (uniteN⋆ {m} {n} {c}) (distzN {m} {n} {c})


------------------------------------------------------------------------------

{--


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
--}

------------------------------------------------------------------------------

-- Semantics
⟦_⟧C : {n : ℕ} → C n → Set
⟦_⟧C {zero} (ZD x) = ⟦ x ⟧
⟦_⟧C {suc n} (Node c c₁) = ⟦ c ⟧C × ⟦ c₁ ⟧C -- probably should have our own × ?

-- combinators respect dimension:
∙⟺∙⇒m≡n : {m n : ℕ} {c₁ : C m} {c₂ : C n} → c₁ ⟺ c₂ → m ≡ n
∙⟺∙⇒m≡n {zero} {zero} (baseC _) = refl
∙⟺∙⇒m≡n {zero} {suc n} ()
∙⟺∙⇒m≡n {suc m} {zero} ()
∙⟺∙⇒m≡n {suc m} {suc n} (nodeC c _) = cong suc (∙⟺∙⇒m≡n c)

-- WLOG, use the same dimension
evalC : {n : ℕ} {c₁ c₂ : C n} → c₁ ⟺ c₂ → ⟦ c₁ ⟧C → ⟦ c₂ ⟧C
evalC {zero} (baseC c) v =  eval c v
evalC {suc n} (nodeC d₀ d₁) (x₀ , x₁) = evalC d₀ x₀ , evalC d₁ x₁
