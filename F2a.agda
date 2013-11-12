module F2a where

open import Agda.Prim
open import Data.Sum 
open import Data.Product

infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_   -- equational reasoning

---------------------------------------------------------------------------
-- Pointed types

record •_ {ℓ : Level} (A : Set ℓ) : Set ℓ where
  constructor ↑
  field 
    focus : A

open •_

{--
-- Examples:

test1 : • ℕ
test1 = ↑ 3

test2 : ℕ 
test2 = focus test1 {-- 3 --}

-- impossible to have:
bot : • ⊥

-- It is higher-order!
test3 : {A : Set} {a : • A} → • (a ⇛ a)
test3 {A} {a} = ↑ id⇛
--}

data Unit {ℓ : Level} : Set ℓ where
  tt : Unit

One : ∀ {ℓ} → • Unit {ℓ}
One = ↑ tt

PlusL : ∀ {ℓ} {A B : Set ℓ} → • A → • (A ⊎ B)
PlusL (↑ a) = ↑ (inj₁ a)

PlusR : ∀ {ℓ} {A B : Set ℓ} → • B → • (A ⊎ B)
PlusR (↑ b) = ↑ (inj₂ b)

Times : ∀ {ℓ} {A B : Set ℓ} → • A → • B → • (A × B)
Times (↑ a) (↑ b) = ↑ (a , b)

---------------------------------------------------------------------------
-- Paths

data _⇛_ {ℓ : Level} : {A B : Set ℓ} → • A → • B → Set (lsuc ℓ) where
  -- + 
  swap₁₊⇛    : {A B : Set ℓ} {a : • A} → 
               _⇛_ {ℓ} {A ⊎ B} {B ⊎ A} (PlusL a) (PlusR a) 
  swap₂₊⇛    : {A B : Set ℓ} {b : • B} → 
               _⇛_ {ℓ} {A ⊎ B} {B ⊎ A} (PlusR b) (PlusL b)
  assocl₁₊⇛  : {A B C : Set ℓ} {a : • A} → 
               _⇛_ {ℓ} {A ⊎ (B ⊎ C)} {(A ⊎ B) ⊎ C} (PlusL a) (PlusL (PlusL a))
  assocl₂₁₊⇛ : {A B C : Set ℓ} {b : • B} → 
               _⇛_ {ℓ} {A ⊎ (B ⊎ C)} {(A ⊎ B) ⊎ C} 
                   (PlusR (PlusL b)) (PlusL (PlusR b))
  assocl₂₂₊⇛ : {A B C : Set ℓ} {c : • C} → 
               _⇛_ {ℓ} {A ⊎ (B ⊎ C)} {(A ⊎ B) ⊎ C} (PlusR (PlusR c)) (PlusR c)
  assocr₁₁₊⇛ : {A B C : Set ℓ} {a : • A} → 
               _⇛_ {ℓ} {(A ⊎ B) ⊎ C} {A ⊎ (B ⊎ C)} (PlusL (PlusL a)) (PlusL a)
  assocr₁₂₊⇛ : {A B C : Set ℓ} {b : • B} → 
               _⇛_ {ℓ} {(A ⊎ B) ⊎ C} {A ⊎ (B ⊎ C)} 
                   (PlusL (PlusR b)) (PlusR (PlusL b))
  assocr₂₊⇛  : {A B C : Set ℓ} {c : • C} → 
               _⇛_ {ℓ} {(A ⊎ B) ⊎ C} {A ⊎ (B ⊎ C)} 
                   (PlusR c) (PlusR (PlusR c))
  -- *
  unite⋆⇛    : {A : Set ℓ} {a : • A} → Times One a ⇛ a
  uniti⋆⇛    : {A : Set ℓ} {a : • A} → a ⇛ Times One a
  swap⋆⇛     : {A B : Set ℓ} {a : • A} {b : • B} → Times a b ⇛ Times b a
  assocl⋆⇛   : {A B C : Set ℓ} {a : • A} {b : • B} {c : • C} → 
               Times a (Times b c) ⇛ Times (Times a b) c
  assocr⋆⇛   : {A B C : Set ℓ} {a : • A} {b : • B} {c : • C} → 
               Times (Times a b) c ⇛ Times a (Times b c)
  -- distributivity
  dist₁⇛     : {A B C : Set ℓ} {a : • A} {c : • C} → 
               _⇛_ {ℓ} {(A ⊎ B) × C} {(A × C) ⊎ (B × C)} 
                   (Times (PlusL a) c) (PlusL (Times a c))
  dist₂⇛     : {A B C : Set ℓ} {b : • B} {c : • C} → 
               _⇛_ {ℓ} {(A ⊎ B) × C} {(A × C) ⊎ (B × C)} 
                   (Times (PlusR b) c) (PlusR (Times b c))
  factor₁⇛   : {A B C : Set ℓ} {a : • A} {c : • C} → 
               _⇛_ {ℓ} {(A × C) ⊎ (B × C)} {(A ⊎ B) × C} 
                   (PlusL (Times a c)) (Times (PlusL a) c)
  factor₂⇛   : {A B C : Set ℓ} {b : • B} {c : • C} → 
               _⇛_ {ℓ} {(A × C) ⊎ (B × C)} {(A ⊎ B) × C}  
                   (PlusR (Times b c)) (Times (PlusR b) c)
  -- congruence
  id⇛        : {A : Set ℓ} {a : • A} → a ⇛ a
  sym⇛       : {A B : Set ℓ} {a : • A} {b : • B} → (a ⇛ b) → (b ⇛ a)
  trans⇛     : {A B C : Set ℓ} {a : • A} {b : • B} {c : • C} → 
               (a ⇛ b) → (b ⇛ c) → (a ⇛ c)
  plus₁⇛     : {A B C D : Set ℓ} {a : • A} {c : • C} → (a ⇛ c) → 
               _⇛_ {ℓ} {A ⊎ B} {C ⊎ D} (PlusL a) (PlusL c)
  plus₂⇛     : {A B C D : Set ℓ} {b : • B} {d : • D} → (b ⇛ d) → 
               _⇛_ {ℓ} {A ⊎ B} {C ⊎ D} (PlusR b) (PlusR d)
  times⇛     : {A B C D : Set ℓ} {a : • A} {b : • B} {c : • C} {d : • D} → 
               (a ⇛ c) → (b ⇛ d) → (Times a b ⇛ Times c d)
  -- create and annihilate
  create⇛     : {A : Set ℓ} {a : • A} → (One ⇛ a)
  annihilate⇛ : {A : Set ℓ} {a : • A} → (a ⇛ One)

-- Paths as data

Path : ∀ {ℓ} {A B : Set ℓ} {a : • A} {b : • B} → (a ⇛ b) → • (a ⇛ b)
Path p = ↑ p

data _2⇛_ {ℓ : Level} : {A B : Set ℓ} → • A → • B → Set (lsuc ℓ) where

xη⇛ : ∀ {ℓ} {A : Set ℓ} {a : • A} → 
     One ⇛ (Times (Path (create⇛ {ℓ} {A} {a})) (Path (annihilate⇛ {ℓ} {A} {a})))
xη⇛ = {!!}

---------------------------------------------------------------------------
-- Introduce equational reasoning syntax to simplify proofs

_≡⟨_⟩_ : ∀ {ℓ} {A B C : Set ℓ} (a : • A) {b : • B} {c : • C} → 
        (a ⇛ b) → (b ⇛ c) → (a ⇛ c)
_ ≡⟨ p ⟩ q = trans⇛ p q

bydef : ∀ {ℓ} {A : Set ℓ} {a : • A} → (a ⇛ a)
bydef = id⇛ 

_∎ : ∀ {ℓ} {A : Set ℓ} {a : • A} → (a ⇛ a)
_∎ = id⇛ 

---------------------------------------------------------------------------

{--
-- Now interpret a path (x ⇛ y) as a value of type (1/x , y)

Recip : {A : Set} → (x : • A) → Set₁
Recip {A} x = (x ⇛ x) 

η : {A : Set} {x : • A} → ⊤ → Recip x × • A 
η {A} {x} tt = (id⇛ x , x)

lower : {A : Set} {x : • A} → x ⇛ x -> ⊤
lower c = tt

-- The problem here is that we can't assert that y == x.
ε : {A : Set} {x : • A} → Recip x × • A → ⊤
ε {A} {x} (rx , y) = lower (id⇛ ( ↑ (fun (ap rx) (focus y)) )) -- makes insufficient sense

apr : {A B : Set} {x : • A} {y : • B} → (x ⇛ y) → Recip y → Recip x
apr {A} {B} {x} {y} q ry = trans⇛ q (trans⇛ ry (sym⇛ q))
  x 
    ≡⟨ q ⟩
  y
    ≡⟨ ry ⟩
  y
    ≡⟨ sym⇛ q ⟩
  x ∎

ε : {A B : Set} {x : A} {y : B} → Recip x → Singleton y → x ⇛ y
ε rx (singleton y) = rx y

pathV : {A B : Set} {x : A} {y : B} → (x ⇛ y) → Recip x × Singleton y
pathV unite₊⇛ = {!!}
pathV uniti₊⇛ = {!!}
--  swap₁₊⇛ : {A B : Set} {x : A} → _⇛_ {A ⊎ B} {B ⊎ A} (inj₁ x) (inj₂ x)
pathV (swap₁₊⇛ {A} {B} {x}) = ((λ x' → {!!}) , singleton (inj₂ x)) 
pathV swap₂₊⇛ = {!!}
pathV assocl₁₊⇛ = {!!}
pathV assocl₂₁₊⇛ = {!!}
pathV assocl₂₂₊⇛ = {!!}
pathV assocr₁₁₊⇛ = {!!}
pathV assocr₁₂₊⇛ = {!!}
pathV assocr₂₊⇛ = {!!}
pathV unite⋆⇛ = {!!}
pathV uniti⋆⇛ = {!!}
pathV swap⋆⇛ = {!!} 
pathV assocl⋆⇛ = {!!}
pathV assocr⋆⇛ = {!!}
pathV dist₁⇛ = {!!}
pathV dist₂⇛ = {!!}
pathV factor₁⇛ = {!!}
pathV factor₂⇛ = {!!}
pathV dist0⇛ = {!!}
pathV factor0⇛ = {!!}
pathV {A} {.A} {x} (id⇛ .x) = {!!}
pathV (sym⇛ p) = {!!}
pathV (trans⇛ p p₁) = {!!}
pathV (plus₁⇛ p) = {!!}
pathV (plus₂⇛ p) = {!!}
pathV (times⇛ p p₁) = {!!} 

-- these are individual paths so to speak
-- should we represent a path like swap+ as a family explicitly:
-- swap+ : (x : A) -> x ⇛ swapF x
-- I guess we can: swap+ : (x : A) -> case x of inj1 -> swap1 x else swap2 x
{--
If A={x0,x1,x2}, 1/A has three values:
(x0<-x0, x0<-x1, x0<-x2)
(x1<-x0, x1<-x1, x1<-x2)
(x2<-x0, x2<-x1, x2<-x2)
It is a fake choice between x0, x1, and x2 (some negative information). You base
yourself at x0 for example and enforce that any other value can be mapped to x0.
So think of a value of type 1/A as an uncertainty about which value of A we 
have. It could be x0, x1, or x2 but at the end it makes no difference. There is
no choice.

You can manipulate a value of type 1/A (x0<-x0, x0<-x1, x0<-x2) by with a
path to some arbitrary path to b0 for example:

(b0<-x0<-x0, b0<-x0<-x1, b0<-x0<-x2)

eta_3 will give (x0<-x0, x0<-x1, x0<-x2, x0) for example but any other
combination is equivalent.

epsilon_3 will take (x0<-x0, x0<-x1, x0<-x2) and one actual xi which is now
certain; we can resolve our previous uncertainty by following the path from
xi to x0 thus eliminating the fake choice we seemed to have. 

Explain connection to negative information.

Knowing head or tails is 1 bits. Giving you a choice between heads and tails
and then cooking this so that heads=tails takes away your choice. 

--}

-- transp⇛ : {A B : Set} {x y : • A} → 
-- (f : A → B) → x ⇛ y → ↑ (f (focus x)) ⇛ ↑ (f (focus y)) 

-- Morphism of pointed space: contains a path!
record _⟶_ {A B : Set} (pA : • A) (pB : • B) : Set₁ where
  field
    fun : A → B
    eq : ↑ (fun (focus pA)) ⇛ pB

open _⟶_

_○_ : {A B C : Set} {pA : • A} {pB : • B} {pC : • C} → pA ⟶ pB → pB ⟶ pC → pA ⟶ pC
f ○ g = record { fun = λ x → (fun g) ((fun f) x) ; eq = trans⇛ (transp⇛ (fun g) (eq f)) (eq g)}

mutual 

  ap : {A B : Set} {x : • A} {y : • B} → x ⇛ y → x ⟶ y
  ap {y = y} unite₊⇛ = record { fun = λ { (inj₁ ()) 
                                        ; (inj₂ x) → x } ; eq = id⇛ y }
  ap uniti₊⇛ (singleton x) = singleton (inj₂ x)
  ap (swap₁₊⇛ {A} {B} {x}) (singleton .(inj₁ x)) = singleton (inj₂ x)
  ap (swap₂₊⇛ {A} {B} {y}) (singleton .(inj₂ y)) = singleton (inj₁ y)
  ap (assocl₁₊⇛ {A} {B} {C} {x}) (singleton .(inj₁ x)) = 
    singleton (inj₁ (inj₁ x))
  ap (assocl₂₁₊⇛ {A} {B} {C} {y}) (singleton .(inj₂ (inj₁ y))) = 
    singleton (inj₁ (inj₂ y))
  ap (assocl₂₂₊⇛ {A} {B} {C} {z}) (singleton .(inj₂ (inj₂ z))) = 
    singleton (inj₂ z)
  ap (assocr₁₁₊⇛ {A} {B} {C} {x}) (singleton .(inj₁ (inj₁ x))) = 
    singleton (inj₁ x)
  ap (assocr₁₂₊⇛ {A} {B} {C} {y}) (singleton .(inj₁ (inj₂ y))) = 
    singleton (inj₂ (inj₁ y))
  ap (assocr₂₊⇛ {A} {B} {C} {z}) (singleton .(inj₂ z)) = 
    singleton (inj₂ (inj₂ z))
  ap {.(⊤ × A)} {A} {.(tt , x)} {x} unite⋆⇛ (singleton .(tt , x)) = 
    singleton x
  ap uniti⋆⇛ (singleton x) = singleton (tt , x)
  ap (swap⋆⇛ {A} {B} {x} {y}) (singleton .(x , y)) = singleton (y , x)
  ap (assocl⋆⇛ {A} {B} {C} {x} {y} {z}) (singleton .(x , (y , z))) = 
    singleton ((x , y) , z)
  ap (assocr⋆⇛ {A} {B} {C} {x} {y} {z}) (singleton .((x , y) , z)) = 
    singleton (x , (y , z))
  ap (dist₁⇛ {A} {B} {C} {x} {z}) (singleton .(inj₁ x , z)) = 
    singleton (inj₁ (x , z))
  ap (dist₂⇛ {A} {B} {C} {y} {z}) (singleton .(inj₂ y , z)) = 
    singleton (inj₂ (y , z))
  ap (factor₁⇛ {A} {B} {C} {x} {z}) (singleton .(inj₁ (x , z))) = 
    singleton (inj₁ x , z)
  ap (factor₂⇛ {A} {B} {C} {y} {z}) (singleton .(inj₂ (y , z))) = 
    singleton (inj₂ y , z)
  ap {.(⊥ × A)} {.⊥} {.(• , x)} {•} (dist0⇛ {A} {.•} {x}) (singleton .(• , x)) = 
    singleton • 
  ap factor0⇛ (singleton ()) 
  ap {x = x} (id⇛ .x) = record { fun = λ x → x; eq = id⇛ x }
  ap (sym⇛ c) = apI c
  ap (trans⇛ c₁ c₂) = (ap c₁) ○ (ap c₂)
  ap (transp⇛ f a) = record { fun = λ x → x; eq = transp⇛ f a }

  ap (plus₁⇛ {A} {B} {C} {D} {x} {z} c) (singleton .(inj₁ x)) 
    with ap c (singleton x)
  ... | singleton .z = singleton (inj₁ z)
  ap (plus₂⇛ {A} {B} {C} {D} {y} {w} c) (singleton .(inj₂ y)) 
    with ap c (singleton y)
  ... | singleton .w = singleton (inj₂ w)
  ap (times⇛ {A} {B} {C} {D} {x} {y} {z} {w} c₁ c₂) (singleton .(x , y)) 
    with ap c₁ (singleton x) | ap c₂ (singleton y) 
  ... | singleton .z | singleton .w = singleton (z , w)


  apI : {A B : Set} {x : • A} {y : • B} → x ⇛ y → y ⟶ x
  apI {y = y} unite₊⇛ = record { fun = inj₂; eq = id⇛ (↑ (inj₂ (focus y))) }

 
 apI {A} {.(⊥ ⊎ A)} {x} uniti₊⇛ (singleton .(inj₂ x)) = singleton x
  apI (swap₁₊⇛ {A} {B} {x}) (singleton .(inj₂ x)) = singleton (inj₁ x)
  apI (swap₂₊⇛ {A} {B} {y}) (singleton .(inj₁ y)) = singleton (inj₂ y)
  apI (assocl₁₊⇛ {A} {B} {C} {x}) (singleton .(inj₁ (inj₁ x))) = 
    singleton (inj₁ x)
  apI (assocl₂₁₊⇛ {A} {B} {C} {y}) (singleton .(inj₁ (inj₂ y))) = 
    singleton (inj₂ (inj₁ y))
  apI (assocl₂₂₊⇛ {A} {B} {C} {z}) (singleton .(inj₂ z)) = 
    singleton (inj₂ (inj₂ z))
  apI (assocr₁₁₊⇛ {A} {B} {C} {x}) (singleton .(inj₁ x)) = 
    singleton (inj₁ (inj₁ x))
  apI (assocr₁₂₊⇛ {A} {B} {C} {y}) (singleton .(inj₂ (inj₁ y))) = 
    singleton (inj₁ (inj₂ y))
  apI (assocr₂₊⇛ {A} {B} {C} {z}) (singleton .(inj₂ (inj₂ z))) = 
    singleton (inj₂ z)
  apI unite⋆⇛ (singleton x) = singleton (tt , x)
  apI {A} {.(⊤ × A)} {x} uniti⋆⇛ (singleton .(tt , x)) = singleton x
  apI (swap⋆⇛ {A} {B} {x} {y}) (singleton .(y , x)) = singleton (x , y)
  apI (assocl⋆⇛ {A} {B} {C} {x} {y} {z}) (singleton .((x , y) , z)) = 
    singleton (x , (y , z))
  apI (assocr⋆⇛ {A} {B} {C} {x} {y} {z}) (singleton .(x , (y , z))) = 
    singleton ((x , y) , z)
  apI (dist₁⇛ {A} {B} {C} {x} {z}) (singleton .(inj₁ (x , z))) = 
    singleton (inj₁ x , z)
  apI (dist₂⇛ {A} {B} {C} {y} {z}) (singleton .(inj₂ (y , z))) = 
    singleton (inj₂ y , z)
  apI (factor₁⇛ {A} {B} {C} {x} {z}) (singleton .(inj₁ x , z)) = 
    singleton (inj₁ (x , z))
  apI (factor₂⇛ {A} {B} {C} {y} {z}) (singleton .(inj₂ y , z)) = 
    singleton (inj₂ (y , z))
  apI dist0⇛ (singleton ()) 
  apI {.⊥} {.(⊥ × A)} {•} (factor0⇛ {A} {.•} {x}) (singleton .(• , x)) = 
    singleton •

  apI {x = x} (id⇛ .x) = record { fun = λ x → x; eq = id⇛ x }
  apI (sym⇛ c) = ap c
  apI (trans⇛ c₁ c₂) = (apI c₂) ○ (apI c₁)
  apI (transp⇛ f a) = record { fun = λ x → x; eq = transp⇛ f (sym⇛ a) }

  apI (plus₁⇛ {A} {B} {C} {D} {x} {z} c) (singleton .(inj₁ z)) 
    with apI c (singleton z)
  ... | singleton .x = singleton (inj₁ x)
  apI (plus₂⇛ {A} {B} {C} {D} {y} {w} c) (singleton .(inj₂ w)) 
    with apI c (singleton w) 
  ... | singleton .y = singleton (inj₂ y)
  apI (times⇛ {A} {B} {C} {D} {x} {y} {z} {w} c₁ c₂) (singleton .(z , w)) 
    with apI c₁ (singleton z) | apI c₂ (singleton w) 
  ... | singleton .x | singleton .y = singleton (x , y)

-- Path induction

pathInd : 
  (C : (A : Set) → (B : Set) → (x : A) → (y : B) → x ⇛ y → Set) → 
  (c : (A : Set) → (x : A) → C A A x x (id⇛ x)) → 
  -- add more cases, one for each constructor
  (A : Set) → (B : Set) → (x : A) → (y : B) → (p : x ⇛ y) → C A B x y p
pathInd C c .(⊥ ⊎ B) B .(inj₂ y) y unite₊⇛ = {!!}
pathInd C c A .(⊥ ⊎ A) x .(inj₂ x) uniti₊⇛ = {!!}
pathInd C c .(A ⊎ B) .(B ⊎ A) .(inj₁ x) .(inj₂ x) (swap₁₊⇛ {A} {B} {x}) = {!!}
pathInd C c .(A ⊎ B) .(B ⊎ A) .(inj₂ y) .(inj₁ y) (swap₂₊⇛ {A} {B} {y}) = {!!}
pathInd C c .(A ⊎ B ⊎ C₁) .((A ⊎ B) ⊎ C₁) .(inj₁ x) .(inj₁ (inj₁ x)) 
  (assocl₁₊⇛ {A} {B} {C₁} {x}) = {!!}
pathInd C c .(A ⊎ B ⊎ C₁) .((A ⊎ B) ⊎ C₁) .(inj₂ (inj₁ y)) .(inj₁ (inj₂ y)) 
  (assocl₂₁₊⇛ {A} {B} {C₁} {y}) = {!!}
pathInd C c .(A ⊎ B ⊎ C₁) .((A ⊎ B) ⊎ C₁) .(inj₂ (inj₂ z)) .(inj₂ z) 
  (assocl₂₂₊⇛ {A} {B} {C₁} {z}) = {!!}
pathInd C c .((A ⊎ B) ⊎ C₁) .(A ⊎ B ⊎ C₁) .(inj₁ (inj₁ x)) .(inj₁ x) 
  (assocr₁₁₊⇛ {A} {B} {C₁} {x}) = {!!}
pathInd C c .((A ⊎ B) ⊎ C₁) .(A ⊎ B ⊎ C₁) .(inj₁ (inj₂ y)) .(inj₂ (inj₁ y)) 
  (assocr₁₂₊⇛ {A} {B} {C₁} {y}) = {!!}
pathInd C c .((A ⊎ B) ⊎ C₁) .(A ⊎ B ⊎ C₁) .(inj₂ z) .(inj₂ (inj₂ z)) 
  (assocr₂₊⇛ {A} {B} {C₁} {z}) = {!!}
pathInd C c .(Σ ⊤ (λ x₁ → B)) B .(tt , y) y unite⋆⇛ = {!!}
pathInd C c A .(Σ ⊤ (λ x₁ → A)) x .(tt , x) uniti⋆⇛ = {!!}
pathInd C c .(Σ A (λ x₁ → B)) .(Σ B (λ x₁ → A)) .(x , y) .(y , x) 
  (swap⋆⇛ {A} {B} {x} {y}) = {!!}
pathInd C c .(Σ A (λ x₁ → Σ B (λ x₂ → C₁))) .(Σ (Σ A (λ x₁ → B)) (λ x₁ → C₁)) 
  .(x , y , z) .((x , y) , z) (assocl⋆⇛ {A} {B} {C₁} {x} {y} {z}) = {!!}
pathInd C c .(Σ (Σ A (λ x₁ → B)) (λ x₁ → C₁)) .(Σ A (λ x₁ → Σ B (λ x₂ → C₁))) 
  .((x , y) , z) .(x , y , z) (assocr⋆⇛ {A} {B} {C₁} {x} {y} {z}) = {!!}
pathInd C c .(Σ (A ⊎ B) (λ x₁ → C₁)) .(Σ A (λ x₁ → C₁) ⊎ Σ B (λ x₁ → C₁)) 
  .(inj₁ x , z) .(inj₁ (x , z)) (dist₁⇛ {A} {B} {C₁} {x} {z}) = {!!}
pathInd C c .(Σ (A ⊎ B) (λ x₁ → C₁)) .(Σ A (λ x₁ → C₁) ⊎ Σ B (λ x₁ → C₁)) 
  .(inj₂ y , z) .(inj₂ (y , z)) (dist₂⇛ {A} {B} {C₁} {y} {z}) = {!!}
pathInd C c .(Σ A (λ x₁ → C₁) ⊎ Σ B (λ x₁ → C₁)) .(Σ (A ⊎ B) (λ x₁ → C₁)) 
  .(inj₁ (x , z)) .(inj₁ x , z) (factor₁⇛ {A} {B} {C₁} {x} {z}) = {!!}
pathInd C c .(Σ A (λ x₁ → C₁) ⊎ Σ B (λ x₁ → C₁)) .(Σ (A ⊎ B) (λ x₁ → C₁)) 
  .(inj₂ (y , z)) .(inj₂ y , z) (factor₂⇛ {A} {B} {C₁} {y} {z}) = {!!}
pathInd C c .(Σ ⊥ (λ x₁ → A)) .⊥ .(y , x) y (dist0⇛ {A} {.y} {x}) = {!!}
pathInd C c .⊥ .(Σ ⊥ (λ x₁ → A)) x .(x , x₁) (factor0⇛ {A} {.x} {x₁}) = {!!}
pathInd C c A .A x .x (id⇛ .x) = c A x
pathInd C c A B x y (sym⇛ p) = {!!}
pathInd C c A B x y (trans⇛ p p₁) = {!!}
pathInd C c .(A ⊎ B) .(C₁ ⊎ D) .(inj₁ x) .(inj₁ z) 
  (plus₁⇛ {A} {B} {C₁} {D} {x} {z} p) = {!!}
pathInd C c .(A ⊎ B) .(C₁ ⊎ D) .(inj₂ y) .(inj₂ w) 
  (plus₂⇛ {A} {B} {C₁} {D} {y} {w} p) = {!!}
pathInd C c .(Σ A (λ x₁ → B)) .(Σ C₁ (λ x₁ → D)) .(x , y) .(z , w) 
  (times⇛ {A} {B} {C₁} {D} {x} {y} {z} {w} p p₁) = {!!}

--}
