module Pin where 

-- N-dimensional version of Pi

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum 
open import Data.Product 
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; cong₂; trans; sym; module ≡-Reasoning)
open ≡-Reasoning

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
  sym⟷    : { t₁ t₂ : T } → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
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
  eval (sym⟷ c) v = evalB c v
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
  evalB (sym⟷ c) v = eval c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (inj₁ v) = inj₁ (evalB c₁ v)
  evalB (c₁ ⊕ c₂) (inj₂ v) = inj₂ (evalB c₂ v)
  evalB (c₁ ⊗ c₂) (v₁ , v₂) = (evalB c₁ v₁ , evalB c₂ v₂)

------------------------------------------------------------------------------
-- Silly lemmas that should be in the library somewhere

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj {0} {0} refl = refl
suc-inj {0} {suc i} ()
suc-inj {suc i} {suc .i} refl = refl

------------------------------------------------------------------------------
-- Types indexed by dimension... n-dimensional cubes
-- n-dimensional types represented as trees of depth n

data C : ℕ → Set where
  ZD   : T → C 0
  Node : {m n : ℕ} → C m → C n → (m ≡ n) → C (suc n)

zeroN : (n : ℕ) → C n
zeroN 0 = ZD Zero
zeroN (suc n) = Node (zeroN n) (zeroN n) refl

plus : {m n : ℕ} → C m → C n → (m ≡ n) → C n
plus (ZD _) (Node _ _ _) ()
plus (Node _ _ _) (ZD _) ()
plus (ZD t1) (ZD t2) refl = ZD (Plus t1 t2)
plus {suc .m₂} {suc .m₂'} 
     (Node {m₁} {m₂} c1 c2 p₁) 
     (Node {m₁'} {m₂'} c1' c2' p₁') p = 
  Node (plus c1 c1' q)
       (plus c2 c2' (suc-inj p)) 
       p₁'
  where q = begin
             m₁ 
              ≡⟨ p₁ ⟩ 
             m₂
              ≡⟨ suc-inj p ⟩
             m₂'
              ≡⟨ sym p₁' ⟩
             m₁' ∎

times : {m n : ℕ} → C m → C n → C (m + n)
times (ZD t1) (ZD t2) = ZD (Times t1 t2)
times (ZD t) (Node c1 c2 p) = Node (times (ZD t) c1) (times (ZD t) c2) p 
times {n = n} (Node c1 c2 p) c = 
  Node (times c1 c) (times c2 c) (cong (λ z → z + n) p) 

-- Combinators on nd types
  
data _⟺_ : {m n : ℕ} → C m → C n → (m ≡ n) → Set where
  baseC : { t₁ t₂ : T } → (t₁ ⟷ t₂) → (_⟺_ (ZD t₁) (ZD t₂) refl)
  nodeC : {m n k l : ℕ} {c₁ : C m} {c₂ : C n} {c₃ : C k} {c₄ : C l} 
          {p₁ : m ≡ n} {p₂ : k ≡ l} {p : k ≡ m} → 
           (_⟺_ c₁ c₂ p₁) → (_⟺_ c₃ c₄ p₂) → 
           (_⟺_ (Node c₁ c₃ (sym p)) 
                (Node c₂ c₄ (trans (trans (sym p₁) (sym p)) p₂)) 
                (cong suc p₂))

-- Def. 2.1 lists the conditions for J-graded bipermutative category

-- (0)
-- the additive unit and assoc are implicit in the paper

uniteN₊ : {m : ℕ} {c : C m} → _⟺_ (plus (zeroN m) c refl) c refl
uniteN₊ {0} {ZD t} = baseC (unite₊ {t})
uniteN₊ {suc .n₂} {Node {n₁} {n₂} c₁ c₂ n₁≡n₂} = {!!}

{--
unitiN₊ : { n : ℕ } { c : C n } → c ⟺ plus (zeroN n) c 
unitiN₊ {0} {ZD t} = baseC (uniti₊ {t})
unitiN₊ {suc n} {Node c₁ c₂} = 
  nodeC (unitiN₊ {n} {c₁}) (unitiN₊ {n} {c₂})

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

-- (1) have times functor on objects
-- define times functor on combinators
-- timesF should satisfying assoc and unitality conditions...
-- diagram on top of p.6 should commute

timesF : { m n : ℕ } { c₁ : C m } { c₂ : C m } { c₃ : C n } { c₄ : C n } → 
         (c₁ ⟺ c₂) → (c₃ ⟺ c₄) → (times c₁ c₃ ⟺ times c₂ c₄)
timesF {0} {0} {ZD t₁} {ZD t₂} {ZD t₃} {ZD t₄} (baseC f) (baseC g) = 
  baseC (_⊗_ {t₁} {t₃} {t₂} {t₄} f g)
timesF {0} {suc n} {ZD t₁} {ZD t₂} {Node c₁ c₂} {Node c₃ c₄} 
       (baseC f) (nodeC g₁ g₂) = nodeC (timesF (baseC f) g₁) (timesF (baseC f) g₂)
timesF {suc m} {n} {Node c₁ c₂} {Node c₃ c₄} {c₅} {c₆} 
       (nodeC f₁ f₂) g = nodeC (timesF f₁ g) (timesF f₂ g)

-- (2) there is a unit object One of dimension 0

uniteN⋆ : {n : ℕ} {c : C n} → times (ZD One) c ⟺ c
uniteN⋆ {0} {ZD t} = baseC (unite⋆ {t})
uniteN⋆ {suc n} {Node c₁ c₂} = nodeC (uniteN⋆ {n} {c₁}) (uniteN⋆ {n} {c₂})

unitiN⋆ : {n : ℕ} {c : C n} → c ⟺ times (ZD One) c
unitiN⋆ {0} {ZD t} = baseC (uniti⋆ {t})
unitiN⋆ {suc n} {Node c₁ c₂} = nodeC (unitiN⋆ {n} {c₁}) (unitiN⋆ {n} {c₂})

-- (3) swap

swapN⋆ : {m n : ℕ} {c₁ : C m} {c₂ : C n} → times c₁ c₂ ⟺ times c₂ c₁
swapN⋆ {0} {0} {ZD t₁} {ZD t₂} = baseC (swap⋆ {t₁} {t₂})
swapN⋆ = ? 





swapN₊ : { n : ℕ } { c₁ c₂ : C n } → plus c₁ c₂ ⟺ plus c₂ c₁
swapN₊ {0} {ZD t₁} {ZD t₂} = baseC (swap₊ {t₁} {t₂})
swapN₊ {suc n} {Node c₁ c₂} {Node c₁' c₂'} = 
  nodeC (swapN₊ {n} {c₁} {c₁'}) (swapN₊ {n} {c₂} {c₂'})



distzN : {m n : ℕ} {c : C n} → times (zeroN m) c ⟺ zeroN (m + n)
distzN {0} {0} {ZD t} = baseC (distz {t})
distzN {0} {suc n} {Node c₁ c₂} = 
  nodeC (distzN {0} {n} {c₁}) (distzN {0} {n} {c₂})
distzN {suc m} {n} {c} = 
  nodeC (distzN {m} {n} {c}) (distzN {m} {n} {c})

--}

------------------------------------------------------------------------------

{--

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
--}

------------------------------------------------------------------------------

{--
-- Semantics
⟦_⟧C : {n : ℕ} → C n → Set
⟦_⟧C {zero} (ZD x) = ⟦ x ⟧
⟦_⟧C {suc n} (Node c c₁) = ⟦ c ⟧C × ⟦ c₁ ⟧C -- probably should have our own × ?
--}

{--
-- combinators respect dimension:
∙⟺∙⇒m≡n : {m n : ℕ} {c₁ : C m} {c₂ : C n} → c₁ ⟺ c₂ → m ≡ n
∙⟺∙⇒m≡n {zero} {zero} (baseC _) = refl
∙⟺∙⇒m≡n {zero} {suc n} ()
∙⟺∙⇒m≡n {suc m} {zero} ()
∙⟺∙⇒m≡n {suc m} {suc n} (nodeC c _) = cong suc (∙⟺∙⇒m≡n c)
--}

{--
-- This is odd - there are 3 cases which should be 'impossible' but Agda can't see it.
evalC : {n m : ℕ} {c₁ : C n} {c₂ : C m} → c₁ ⟺ c₂ → ⟦ c₁ ⟧C → ⟦ c₂ ⟧C
evalC {zero} {zero} (baseC x) v = eval x v
--evalC {zero} {zero} raise0 ()
--evalC {zero} {zero} raise1 tt = tt
--evalC {zero} {suc m} raise0 ()
--evalC {zero} {suc m} raise1 tt = evalC {zero} {m} raise1 tt , evalC {zero} {m} raise0 {!!} -- hole is ⊥
--evalC {suc n} {zero} raise0 (v , _) = evalC {n} {zero} raise0 v  -- v is a shape full of ⊥
--evalC {suc n} {zero} raise1 v = tt -- v is a pair where snd is ⊥ ?
evalC {suc n} {suc m} (nodeC c c′) (x , y) = evalC c x , evalC c′ y
--evalC {suc n} {suc m} raise0 (proj₁ , proj₂) = evalC {n} {m} raise0 proj₁ , evalC {n} {m} raise0 proj₂
--evalC {suc n} {suc m} raise1 (proj₁ , proj₂) = evalC {n} {m} raise1 proj₁ , evalC {n} {m} raise0 proj₂
--}

