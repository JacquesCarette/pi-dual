{-# OPTIONS --without-K #-}

module Pin where 

-- N-dimensional version of Pi

open import Data.Fin
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum 
open import Data.Product 
open import Function renaming (_∘_ to _○_)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning
open import Algebra
open import Data.Nat.Properties
open CommutativeSemiring commutativeSemiring using (+-commutativeMonoid)
open CommutativeMonoid +-commutativeMonoid using () 
     renaming (comm to +-comm) 

infix  4  _≡_   -- propositional equality
infixr 8  _∘_   -- path composition
infixr 10 _◎_
infixr 30 _⟷_
-- infixr 30 _⟺_

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
-- Paths; HoTT

-- Our own version of refl that makes 'a' explicit

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

pathInd : ∀ {ℓ ℓ'} → {A : Set ℓ} → 
          (C : {x y : A} → (x ≡ y) → Set ℓ') → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

! : ∀ {ℓ} → {A : Set ℓ} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

_∘_ : ∀ {ℓ} → {A : Set ℓ} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {ℓ} {A} {x} {y} {z} p q = 
  pathInd 
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

-- p ≡ p ∘ refl

unitTransR : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ p ∘ refl y) 
unitTransR {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ p ∘ (refl y)) 
    (λ x → refl (refl x))
    {x} {y} p 

-- p ≡ refl ∘ p

unitTransL : {A : Set} {x y : A} → (p : x ≡ y) → (p ≡ refl x ∘ p) 
unitTransL {A} {x} {y} p = 
  pathInd
    (λ {x} {y} p → p ≡ (refl x) ∘ p)
    (λ x → refl (refl x))
    {x} {y} p 

-- ! p ∘ p ≡ refl

invTransL : {A : Set} {x y : A} → (p : x ≡ y) → (! p ∘ p ≡ refl y)
invTransL {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ! p ∘ p ≡ refl y)
    (λ x → refl (refl x))
    {x} {y} p

-- ! (! p) ≡ p

invId : {A : Set} {x y : A} → (p : x ≡ y) → (! (! p) ≡ p)
invId {A} {x} {y} p =
  pathInd 
    (λ {x} {y} p → ! (! p) ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r

assocP : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
         (p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
assocP {A} {x} {y} {z} {w} p q r =
  pathInd
    (λ {x} {y} p → (z : A) → (w : A) → (q : y ≡ z) → (r : z ≡ w) → 
      p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r)
    (λ x z w q r → 
      pathInd
        (λ {x} {z} q → (w : A) → (r : z ≡ w) → 
          (refl x) ∘ (q ∘ r) ≡ ((refl x) ∘ q) ∘ r)
        (λ x w r → 
          pathInd
            (λ {x} {w} r → 
              (refl x) ∘ ((refl x) ∘ r) ≡ 
              ((refl x) ∘ (refl x)) ∘ r)
            (λ x → (refl (refl x)))
            {x} {w} r)
        {x} {z} q w r)
    {x} {y} p z w q r

-- ! (p ∘ q) ≡ ! q ∘ ! p

invComp : {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → 
          ! (p ∘ q) ≡ ! q ∘ ! p
invComp {A} {x} {y} {z} p q = 
  pathInd
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p)
    (λ x z q → 
      pathInd 
        (λ {x} {z} q → ! (refl x ∘ q) ≡ ! q ∘ ! (refl x))
        (λ x → refl (refl x)) 
        {x} {z} q)
    {x} {y} p z q

-- computation rule: ap f (refl x) = refl (f x)

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd 
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

-- f (p ∘ q) ≡ f p ∘ f q

apfTrans : ∀ {ℓ} → {A B : Set ℓ} {x y z : A} → 
  (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q)
apfTrans {ℓ} {A} {B} {x} {y} {z} f p q = 
  pathInd {ℓ}
    (λ {x} {y} p → (z : A) → (q : y ≡ z) → 
      ap f (p ∘ q) ≡ (ap f p) ∘ (ap f q))
    (λ x z q → 
      pathInd {ℓ}
        (λ {x} {z} q → 
          ap f (refl x ∘ q) ≡ (ap f (refl x)) ∘ (ap f q))
        (λ x → refl (refl (f x)))
        {x} {z} q)
    {x} {y} p z q

-- f (! p) ≡ ! (f p)

apfInv : ∀ {ℓ} → {A B : Set ℓ} {x y : A} → (f : A → B) → (p : x ≡ y) → 
         ap f (! p) ≡ ! (ap f p) 
apfInv {ℓ} {A} {B} {x} {y} f p =
  pathInd {ℓ}
    (λ {x} {y} p → ap f (! p) ≡ ! (ap f p))
    (λ x → refl (ap f (refl x)))
    {x} {y} p

-- g (f p) ≡ (g ○ f) p

apfComp : {A B C : Set} {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ○ f) p 
apfComp {A} {B} {C} {x} {y} f g p =
  pathInd 
    (λ {x} {y} p → ap g (ap f p) ≡ ap (g ○ f) p)
    (λ x → refl (ap g (ap f (refl x))))
    {x} {y} p

-- id p ≡ p

apfId : {A : Set} {x y : A} → (p : x ≡ y) → ap id p ≡ p
apfId {A} {x} {y} p = 
  pathInd 
    (λ {x} {y} p → ap id p ≡ p)
    (λ x → refl (refl x))
    {x} {y} p

-- Transport

transport : ∀ {ℓ ℓ'} → {A : Set ℓ} {x y : A} → 
  (P : A → Set ℓ') → (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} {x} {y} P p = 
  pathInd 
    (λ {x} {y} p → (P x → P y))
    (λ _ → id)
    {x} {y} p

------------------------------------------------------------------------------
-- Dimensions

module Dim where
  private
    data D* : Set where
      0d* : D*
      1d* : D*
      plusd* : D* → D* → D*

  D : Set
  D = D*

  0d : D
  0d = 0d*

  1d : D
  1d = 1d*

  plusd : D → D → D
  plusd = plusd*

  postulate 
    united  : {d : D} → plusd 0d d ≡ d
    unitid  : {d : D} → d ≡ plusd 0d d
    swapd   : {d₁ d₂ : D} → plusd d₁ d₂ ≡ plusd d₂ d₁
    assocld : {d₁ d₂ d₃ : D} → plusd d₁ (plusd d₂ d₃) ≡ plusd (plusd d₁ d₂) d₃
    assocrd : {d₁ d₂ d₃ : D} → plusd (plusd d₁ d₂) d₃ ≡ plusd d₁ (plusd d₂ d₃)

  recD : {C : Set} → 
         (c0d : C) → (c1d : C) → 
         (cplusd : C → C → C) → 
         (cunited  : {c : C} → cplusd c0d c ≡ c) → 
         (cunitid  : {c : C} → c ≡ cplusd c0d c) → 
         (cswapd   : {c₁ c₂ : C} → cplusd c₁ c₂ ≡ cplusd c₂ c₁) → 
         (cassocld : {c₁ c₂ c₃ : C} → 
           cplusd c₁ (cplusd c₂ c₃) ≡ cplusd (cplusd c₁ c₂) c₃) → 
         (cassocrd : {c₁ c₂ c₃ : C} → 
           cplusd (cplusd c₁ c₂) c₃ ≡ cplusd c₁ (cplusd c₂ c₃)) → 
         D → C
  recD c0d c1d cplusd _ _ _ _ _ 0d* = c0d
  recD c0d c1d cplusd _ _ _ _ _ 1d* = c1d
  recD c0d c1d cplusd p₁ p₂ p₃ p₄ p₅ (plusd* d₁ d₂) =  
    cplusd 
      (recD c0d c1d cplusd p₁ p₂ p₃ p₄ p₅ d₁)
      (recD c0d c1d cplusd p₁ p₂ p₃ p₄ p₅ d₁)

open Dim public

------------------------------------------------------------------------------
-- N dimensional version

data C : D → Set where
  ZD   : T → C 0d
  Node : {d : D} → C d → C d → C (plusd 1d d)

{--
zeroN : (d : D) → C d
zeroN d = 
  recD {C d}
    (ZD Zero) -- what dim 0 maps to
    ? -- what dim 1 maps to
    (λ c₁ c₂ → -- type at d1 and type at d2; construct type at d1+d2
      ?)
    -- proof that the type construct at 0+d is the same as the one
    -- constructed at d
    ?
    -- etc.
    ?
    ?
    ?
    ?          

--    

liftN : (n : ℕ) → (t : T) → C n
liftN 0 t = ZD t
liftN (suc n) t = Node (liftN n t) (liftN n Zero)

zeroN : (n : ℕ) → C n
zeroN n = liftN n Zero

oneN : (n : ℕ) → C n
oneN n = liftN n One

plus : {n : ℕ} → C n → C n → C n
plus (ZD t₁) (ZD t₂) = ZD (Plus t₁ t₂)
plus (Node c₁ c₂) (Node c₁' c₂') = Node (plus c₁ c₁') (plus c₂ c₂')

times : {m n : ℕ} → C m → C n → C (m + n)
times (ZD t1) (ZD t2) = ZD (Times t1 t2)
times (ZD t) (Node c1 c2) = Node (times (ZD t) c1) (times (ZD t) c2) 
times (Node c1 c2) c = Node (times c1 c) (times c2 c) 

-- Combinators on nd types
  
data _⟺_ : {n : ℕ} → C n → C n → Set where
  baseC : { t₁ t₂ : T } → (t₁ ⟷ t₂) → ((ZD t₁) ⟺ (ZD t₂))
  nodeC : {n : ℕ} {c₁ : C n} {c₂ : C n} {c₃ : C n} {c₄ : C n} → 
          (c₁ ⟺ c₂) → (c₃ ⟺ c₄) → 
          ((Node c₁ c₃) ⟺ (Node c₂ c₄))
  promoteC : {n : ℕ} {c : C n} → (c ⟺ c) → 
             (Node c c ⟺ zeroN (suc n))
  demoteC : {n : ℕ} {c : C n} → (c ⟺ c) → 
             (zeroN (suc n) ⟺ Node c c)
             
-- Def. 2.1 lists the conditions for J-graded bipermutative category

uniteN₊ : {n : ℕ} {c : C n} → (plus (zeroN n) c) ⟺ c
uniteN₊ {0} {ZD t} = baseC (unite₊ {t})
uniteN₊ {suc n} {Node c₁ c₂} = nodeC (uniteN₊ {n} {c₁}) (uniteN₊ {n} {c₂}) 

unitiN₊ : {n : ℕ} {c : C n} → c ⟺ (plus (zeroN n) c)
unitiN₊ {0} {ZD t} = baseC (uniti₊ {t})
unitiN₊ {suc n} {Node c₁ c₂} = nodeC (unitiN₊ {n} {c₁}) (unitiN₊ {n} {c₂})

swapN₊ : { n : ℕ } { c₁ c₂ : C n } → plus c₁ c₂ ⟺ plus c₂ c₁
swapN₊ {0} {ZD t₁} {ZD t₂} = baseC (swap₊ {t₁} {t₂})
swapN₊ {suc n} {Node c₁ c₂} {Node c₁' c₂'} = 
  nodeC ((swapN₊ {n} {c₁} {c₁'})) ((swapN₊ {n} {c₂} {c₂'})) 

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

uniteN⋆ : {n : ℕ} {c : C n} → times (ZD One) c ⟺ c
uniteN⋆ {0} {ZD t} = baseC (unite⋆ {t})
uniteN⋆ {suc n} {Node c₁ c₂} = nodeC (uniteN⋆ {n} {c₁}) (uniteN⋆ {n} {c₂})

unitiN⋆ : {n : ℕ} {c : C n} → c ⟺ times (ZD One) c
unitiN⋆ {0} {ZD t} = baseC (uniti⋆ {t})
unitiN⋆ {suc n} {Node c₁ c₂} = nodeC (unitiN⋆ {n} {c₁}) (unitiN⋆ {n} {c₂})

-- Ugly hack or feature ???

times' : {m n : ℕ} → C n → C m → C (m + n)
times' {m} {n} c₁ c₂ rewrite +-comm m n = times c₁ c₂

swapN⋆ : {m n : ℕ} {c₁ : C m} {c₂ : C n} → times c₁ c₂ ⟺ times' c₂ c₁
swapN⋆ {0} {0} {ZD t₁} {ZD t₂} = baseC (swap⋆ {t₁} {t₂})
swapN⋆ {0} {suc n} {ZD t} {Node c₁ c₂} = {!!} 
--nodeC (swapN⋆ {0} {n} {ZD t} {c₁}) (swapN⋆ {0} {n} {ZD t} {c₂})
swapN⋆ {suc m} {0} {Node c₁ c₂} {ZD t} = {!!} 
--nodeC (swapN⋆ {0} {n} {c₁} {ZD t}) (swapN⋆ {0} {n} {c₂} {ZD t})
swapN⋆ {suc m} {n} {Node c₁ c₂} {c} = {!!}
--nodeC (swapN⋆ {m} {n} {c₁} {c}) (swapN⋆ {m} {n} {c₂} {c})

TODO : Set
TODO = {!!} 

assoclN⋆ : {m n k : ℕ} {c₁ : C m} {c₂ : C n} {c₃ : C k} → TODO
--           times c₁ (times c₂ c₃) ⟺ times (times c₁ c₂) c₃
assoclN⋆ = {!!} 

assocrN⋆ : { m n k : ℕ } { c₁ : C m } { c₂ : C n } { c₃ : C k } → TODO
--            times (times c₁ c₂) c₃ ⟺ times c₁ (times c₂ c₃)
assocrN⋆ = {!!} 

distzN : {m n : ℕ} {c : C n} → times (zeroN m) c ⟺ zeroN (m + n)
distzN {0} {0} {ZD t} = baseC (distz {t})
distzN {0} {suc n} {Node c₁ c₂} = 
  nodeC (distzN {0} {n} {c₁}) (distzN {0} {n} {c₂})
distzN {suc m} {n} {c} = 
  nodeC (distzN {m} {n} {c}) (distzN {m} {n} {c})

factorzN : { m n : ℕ } { c : C n } → zeroN (m + n) ⟺ times (zeroN m) c
factorzN {0} {0} {ZD t} = baseC (factorz {t})
factorzN {0} {suc n} {Node c₁ c₂} = 
  nodeC (factorzN {0} {n} {c₁}) (factorzN {0} {n} {c₂})
factorzN {suc m} {n} {c} = 
  nodeC (factorzN {m} {n} {c}) (factorzN {m} {n} {c})

distN : {m n : ℕ} {c₁ c₂ : C m} {c₃ : C n} → 
        times (plus c₁ c₂) c₃ ⟺ plus (times c₁ c₃) (times c₂ c₃) 
distN {0} {0} {ZD t₁} {ZD t₂} {ZD t₃} = baseC (dist {t₁} {t₂} {t₃})
distN {0} {suc n} {ZD t₁} {ZD t₂} {Node c₁ c₂} = 
  nodeC 
    (distN {0} {n} {ZD t₁} {ZD t₂} {c₁}) 
    (distN {0} {n} {ZD t₁} {ZD t₂} {c₂})
distN {suc m} {n} {Node c₁ c₂} {Node c₃ c₄} {c} =
  nodeC 
    ((distN {m} {n} {c₁} {c₃} {c})) 
    ((distN {m} {n} {c₂} {c₄} {c})) 

factorN : {m n : ℕ} {c₁ c₂ : C m} {c₃ : C n} → 
          plus (times c₁ c₃) (times c₂ c₃) ⟺ times (plus c₁ c₂) c₃
factorN {0} {0} {ZD t₁} {ZD t₂} {ZD t₃} = baseC (factor {t₁} {t₂} {t₃})
factorN {0} {suc n} {ZD t₁} {ZD t₂} {Node c₁ c₂} = 
  nodeC 
    (factorN {0} {n} {ZD t₁} {ZD t₂} {c₁}) 
    (factorN {0} {n} {ZD t₁} {ZD t₂} {c₂})
factorN {suc m} {n} {Node c₁ c₂} {Node c₃ c₄} {c} =
  nodeC 
    ((factorN {m} {n} {c₁} {c₃} {c})) 
    ((factorN {m} {n} {c₂} {c₄} {c})) 

idN⟷ : {n : ℕ} {c : C n} → c ⟺ c
idN⟷ {0} {ZD t} = baseC (id⟷ {t})
idN⟷ {suc n} {Node c₁ c₂} = nodeC (idN⟷ {n} {c₁}) (idN⟷ {n} {c₂})

symN⟷ : {n : ℕ} {c₁ c₂ : C n} → (c₁ ⟺ c₂) → (c₂ ⟺ c₁)
symN⟷ (baseC f) = baseC (sym⟷ f)
symN⟷ (nodeC f g) = nodeC (symN⟷ f) (symN⟷ g)
symN⟷ (promoteC f) = {!!} 
symN⟷ (demoteC f) = {!!} 

seqF : {n : ℕ} {c₁ c₂ c₃ : C n} → 
       (c₁ ⟺ c₂) → (c₂ ⟺ c₃) → (c₁ ⟺ c₃) 
seqF (baseC f) (baseC g) = baseC (f ◎ g)
seqF (nodeC f f') (nodeC g g') = nodeC (seqF f g) (seqF f' g')
seqF (nodeC f f') (promoteC c) = {!!}
seqF (nodeC f f') (demoteC c) = {!!}
seqF (promoteC c) (nodeC f f') = {!!}
seqF (promoteC c) (promoteC c') = {!!}
seqF (promoteC c) (demoteC c') = {!!}
seqF (demoteC c) (nodeC f f') = {!!}
seqF (demoteC c) (promoteC c') = {!!}
seqF (demoteC c) (demoteC c') = {!!} 

plusF : {n : ℕ} {c₁ c₂ c₃ c₄ : C n} → 
        (c₁ ⟺ c₂) → (c₃ ⟺ c₄) → (plus c₁ c₃ ⟺ plus c₂ c₄)
plusF (baseC f) (baseC g) = baseC (f ⊕ g)
plusF (nodeC f₁ f₂) (nodeC g₁ g₂) = nodeC (plusF f₁ g₁) (plusF f₂ g₂) 
plusF (nodeC f₁ f₂) (promoteC c) = {!!}
plusF (nodeC f₁ f₂) (demoteC c) = {!!}
plusF (promoteC c) (nodeC f₁ f₂) = {!!}
plusF (promoteC c) (promoteC c') = {!!}
plusF (promoteC c) (demoteC c') = {!!}
plusF (demoteC c) (nodeC f₁ f₂) = {!!}
plusF (demoteC c) (promoteC c') = {!!}
plusF (demoteC c) (demoteC c') = {!!} 

timesF : {m n : ℕ} {c₁ c₂ : C m} {c₃ c₄ : C n} → 
         (c₁ ⟺ c₂) → (c₃ ⟺ c₄) → (times c₁ c₃ ⟺ times c₂ c₄)
timesF (baseC f) (baseC g) = baseC (f ⊗ g)
timesF (baseC f) (nodeC g₁ g₂) = 
  nodeC (timesF (baseC f) g₁) (timesF (baseC f) g₂) 
timesF (nodeC f₁ f₂) g = nodeC (timesF f₁ g) (timesF f₂ g) 
timesF (baseC f) (promoteC c) = {!!}
timesF (baseC f) (demoteC c) = {!!}
timesF (promoteC c) (baseC f) = {!!}
timesF (promoteC c) (nodeC f₁ f₂) = {!!}
timesF (promoteC c) (promoteC c') = {!!}
timesF (promoteC c) (demoteC c') = {!!}
timesF (demoteC c) (baseC f) = {!!}
timesF (demoteC c) (nodeC f₁ f₂) = {!!}
timesF (demoteC c) (promoteC c') = {!!}
timesF (demoteC c) (demoteC c') = {!!} 

------------------------------------------------------------------------------
-- Semantics

⟦_⟧C : {n : ℕ} → C n → Set
⟦_⟧C (ZD t) = ⟦ t ⟧
⟦_⟧C (Node c₁ c₂) = ⟦ c₁ ⟧C ⊎ ⟦ c₂ ⟧C 

evalC : {n : ℕ} {c₁ c₂ : C n} → (c₁ ⟺ c₂) → ⟦ c₁ ⟧C → ⟦ c₂ ⟧C
evalC (baseC iso) v = eval iso v
evalC (nodeC isoL isoR) (inj₁ v) = inj₁ (evalC isoL v) 
evalC (nodeC isoL isoR) (inj₂ v) = inj₂ (evalC isoR v) 
evalC (promoteC c) v = {!!}
evalC (demoteC c) v = {!!} 

------------------------------------------------------------------------------
-- Example

-- Let's try a 3d program

Bool : T
Bool = Plus One One

vtrue : ⟦ Bool ⟧
vtrue = inj₁ tt

vfalse : ⟦ Bool ⟧
vfalse = inj₂ tt

Bool² : T
Bool² = Times Bool Bool

Bool³ : T
Bool³ = Times Bool² Bool

cond : {t₁ t₂ : T} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → 
       ((Times Bool t₁) ⟷ (Times Bool t₂))
cond f g = dist ◎ ((id⟷ ⊗ f) ⊕ (id⟷ ⊗ g)) ◎ factor 

controlled : {t : T} → (t ⟷ t) → ((Times Bool t) ⟷ (Times Bool t))
controlled f = cond f id⟷

cnot : Bool² ⟷ Bool²
cnot = controlled swap₊

toffoli : Bool³ ⟷ Bool³
toffoli = assocr⋆ ◎ controlled cnot ◎ assocl⋆ 

test₁ : ⟦ Bool³ ⟧
test₁ = eval toffoli ((vtrue , vtrue) , vfalse)

--

condN : {n : ℕ} {c₁ c₂ : C n} → (c₁ ⟺ c₂) → (c₁ ⟺ c₂) → 
        ((times (ZD Bool) c₁) ⟺ (times (ZD Bool) c₂))
condN {n} {c₁} {c₂} f g = 
  (seqF (distN {0} {n} {ZD One} {ZD One} {c₁})
  (seqF (plusF {n} 
          (timesF {0} {n} (idN⟷ {0} {ZD One}) f) 
          (timesF {0} {n} (idN⟷ {0} {ZD One}) g))
  (factorN {0} {n} {ZD One} {ZD One} {c₂})))

controlledN : {n : ℕ} {c : C n} → 
              (c ⟺ c) → ((times (ZD Bool) c) ⟺ (times (ZD Bool) c))
controlledN f = condN f idN⟷

BoolN : (n : ℕ) → C n
BoolN n = plus (oneN n) (oneN n)
{--
Note: liftN 3 Bool is not quite the same as plus (oneN 3) (oneN 3)

plus (oneN 3) (oneN 3) 
= 
Node
(Node 
  (Node (ZD (Plus One One)) (ZD (Plus Zero Zero)))
  (Node (ZD (Plus Zero Zero)) (ZD (Plus Zero Zero))))
(Node 
  (Node (ZD (Plus Zero Zero)) (ZD (Plus Zero Zero)))
  (Node (ZD (Plus Zero Zero)) (ZD (Plus Zero Zero))))

liftN 3 Bool
= 
Node
(Node 
  (Node (ZD (Plus One One)) (ZD Zero))
  (Node (ZD Zero) (ZD Zero)))
(Node 
  (Node (ZD Zero) (ZD Zero)) 
  (Node (ZD Zero) (ZD Zero)))
--}

cnotN : {n : ℕ} → ((times (ZD Bool) (BoolN n)) ⟺ (times (ZD Bool) (BoolN n)))
cnotN {n} = controlledN {n} (swapN₊ {n} {oneN n} {oneN n})

{--

Can't do toffoliN until we get all the products done

--}




--}

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

{--

CODE THAT TRIED TO KEEP PROOF THAT DIMENSIONS ARE EQUAL


------------------------------------------------------------------------------
-- Types indexed by dimension... n-dimensional cubes
-- n-dimensional types represented as trees of depth n

-- Silly lemmas that should be in the library somewhere

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj {0} {0} refl = refl
suc-inj {0} {suc i} ()
suc-inj {suc i} {suc .i} refl = refl

data C : ℕ → Set where
  ZD   : T → C 0
  Node : {m n : ℕ} → C m → C n → (m ≡ n) → C (suc n)
  Lower : {n : ℕ} → (c₁ c₂ : C n) → (c₁ ≡ c₂) → C 0

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
plus _ _ _ = {!!}

times : {m n : ℕ} → C m → C n → C (m + n)
times (ZD t1) (ZD t2) = ZD (Times t1 t2)
times (ZD t) (Node c1 c2 p) = Node (times (ZD t) c1) (times (ZD t) c2) p 
times {n = n} (Node c1 c2 p) c = 
  Node (times c1 c) (times c2 c) (cong (λ z → z + n) p) 
times _ _ = {!!} 

-- Combinators on nd types
  
data _⟺_ : {m n : ℕ} → C m → C n → (m ≡ n) → Set where
  baseC : { t₁ t₂ : T } → (t₁ ⟷ t₂) → (_⟺_ (ZD t₁) (ZD t₂) refl)
  nodeC : {m n k l : ℕ} {c₁ : C m} {c₂ : C n} {c₃ : C k} {c₄ : C l} 
          {p₁ : m ≡ n} {p₂ : k ≡ l} {p : k ≡ m} → 
           (_⟺_ c₁ c₂ p₁) → (_⟺_ c₃ c₄ p₂) → 
           (_⟺_ (Node c₁ c₃ (sym p)) 
                (Node c₂ c₄ (trans (trans (sym p₁) (sym p)) p₂)) 
                (cong suc p₂))
  eta : {m : ℕ} {c : C m} → _⟺_ (ZD Zero) (Lower c c refl) refl

-- Def. 2.1 lists the conditions for J-graded bipermutative category

-- (0)
-- the additive unit and assoc are implicit in the paper

uniteN₊ : {m : ℕ} {c : C m} → _⟺_ (plus (zeroN m) c refl) c refl
uniteN₊ {0} {ZD t} = baseC (unite₊ {t})
uniteN₊ {suc m} {Node {n} {.m} c₁ c₂ n≡m} = {!!} 
uniteN₊ {_} {_} = {!!} 

unitiN₊ : {m : ℕ} {c : C m} → _⟺_ c (plus (zeroN m) c refl) refl
unitiN₊ {0} {ZD t} = baseC (uniti₊ {t})
unitiN₊ {suc m} {Node {n} {.m} c₁ c₂ n≡m} = {!!}
--  nodeC (unitiN₊ {n} {c₁}) (unitiN₊ {n} {c₂})
unitiN₊ {_} {_} = {!!} 

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

------------------------------------------------------------------------------

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

------------------------------------------------------------------------------
-- Semantics

-- probably should have our own × ?
-- should be a sum ! 
-- we have a value in one of the corners; not in all of them at once

⟦_⟧C : {n : ℕ} → C n → Set
⟦_⟧C (ZD t) = ⟦ t ⟧
⟦_⟧C (Node c₁ c₂ _) = ⟦ c₁ ⟧C ⊎ ⟦ c₂ ⟧C 
⟦_⟧C (Lower c₁ c₂ _) = ⊥

evalC : {n m : ℕ} {c₁ : C n} {c₂ : C m} {p : n ≡ m} → 
        _⟺_ c₁ c₂ p → ⟦ c₁ ⟧C → ⟦ c₂ ⟧C
evalC (baseC iso) v = eval iso v 
evalC (nodeC isoL isoR) (inj₁ v) = inj₁ (evalC isoL v) 
evalC (nodeC isoL isoR) (inj₂ v) = inj₂ (evalC isoR v) 
evalC _ _ = {!!} 

-- now add etas and epsilons...
--}

