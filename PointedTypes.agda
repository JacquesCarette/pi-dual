{-# OPTIONS --without-K #-}

module PointedTypes where

open import Agda.Prim
open import Data.Unit
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Data.Sum 
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Pointed types

-- We need pointed types because paths are ultimately between points. A path
-- between false and 0 for example would be expressed as a path between
-- (pt false) and (pt 0) which expand to •[ Bool , false ] and •[ ℕ , 0 ]

-- First we define a pointed set as a carrier with a distinguished point

record Set• (ℓ : Level) : Set (lsuc ℓ) where
  constructor •[_,_]
  field
    ∣_∣ : Set ℓ
    • : ∣_∣

open Set• public

⊤• : Set• lzero
⊤• = •[ ⊤ , tt ]

_⊎•₁_ : {ℓ ℓ' : Level} → (A• : Set• ℓ) → (B• : Set• ℓ') → Set• (ℓ ⊔ ℓ')
A• ⊎•₁ B• = •[ ∣ A• ∣ ⊎ ∣ B• ∣ , inj₁ (• A•) ]

_⊎•₂_ : {ℓ ℓ' : Level} → (A• : Set• ℓ) → (B• : Set• ℓ') → Set• (ℓ ⊔ ℓ')
A• ⊎•₂ B• = •[ ∣ A• ∣ ⊎ ∣ B• ∣ , inj₂ (• B•) ]

_×•_ : {ℓ ℓ' : Level} → (A• : Set• ℓ) → (B• : Set• ℓ') → Set• (ℓ ⊔ ℓ')
A• ×• B• = •[ ∣ A• ∣ × ∣ B• ∣ , (• A• , • B•) ]

test0 : Set• lzero
test0 = •[ ℕ , 3 ]

test1 : Set• (lsuc lzero)
test1 = •[ Set , ℕ ]

test2 : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} {a : A} → Set• (ℓ ⊔ ℓ')
test2 {ℓ} {ℓ'} {A} {B} {a} = •[ A ⊎ B , inj₁ a ]

test3 : ∀ {ℓ} → Set• (lsuc (lsuc ℓ))
test3 {ℓ} = •[ Set (lsuc ℓ) , Set ℓ ]

test4 : Set• lzero
test4 = •[ (Bool → Bool) , not ]

-- Now we focus on the points and move the carriers to the background

pt : {ℓ : Level} {A : Set ℓ} → (a : A) → Set• ℓ
pt {ℓ} {A} a = •[ A , a ]

test5 : Set• lzero
test5 = pt 3

test6 : Set• (lsuc lzero) 
test6 = pt ℕ

test7 : {ℓ : Level} → Set• (lsuc (lsuc ℓ))
test7 {ℓ} = pt (Set ℓ) 

-- See:
-- http://homotopytypetheory.org/2012/11/21/on-heterogeneous-equality/

beta : {ℓ : Level} {A : Set ℓ} {a : A} → • •[ A , a ] ≡ a
beta {ℓ} {A} {a} = refl

eta : {ℓ : Level} → (A• : Set• ℓ) → •[ ∣ A• ∣ , • A• ] ≡ A•
eta {ℓ} A• = refl

------------------------------------------------------------------------------
-- Functions between pointed types; our focus is on how the functions affect
-- the basepoint. We don't care what the functions do on the rest of the type.

record _→•_ {ℓ ℓ' : Level} (A• : Set• ℓ) (B• : Set• ℓ') : Set (ℓ ⊔ ℓ') where
  field 
    fun   : ∣ A• ∣ → ∣ B• ∣
    resp• : fun (• A•) ≡ • B•

open _→•_ public

id• : {ℓ : Level} {A• : Set• ℓ} → (A• →• A•)
id• = record { fun = id ; resp• = refl } 

f1 : pt 2 →• pt 4
f1 = record { fun = suc ∘ suc ; resp• = refl } 

f2 : pt 2 →• pt 4
f2 = record { fun = λ x → 2 * x ; resp• = refl } 

-- composition of functions between pointed types
_⊚_ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A• : Set• ℓ₁} {B• : Set• ℓ₂} {C• : Set• ℓ₃} →
      (B• →• C•) → (A• →• B•) → (A• →• C•)
h ⊚ g = record { 
          fun   = fun h ∘ fun g ; 
          resp• = trans (cong (fun h) (resp• g)) (resp• h) 
        }

f3 : pt 4 →• pt 2
f3 = record { fun = pred ∘ pred ; resp• = refl } 

f1∘f3 : pt 4 →• pt 4
f1∘f3 = f1 ⊚ f3

-- two pointed functions are ∼ if they agree on the basepoints; we DON'T CARE
-- what they do on the rest of the type.

_∼•_ : {ℓ ℓ' : Level} {A• : Set• ℓ} {B• : Set• ℓ'} → 
       (f• g• : A• →• B•) → Set ℓ'
_∼•_ {ℓ} {ℓ'} {A•} {B•} f• g• = fun f• (• A•) ≡ fun g• (• A•)

f1∼f2 : f1 ∼• f2
f1∼f2 = refl

f1∘f3∼id : f1∘f3 ∼• id•
f1∘f3∼id = refl

-- quasi-inverses

record qinv• {ℓ ℓ'} {A• : Set• ℓ} {B• : Set• ℓ'} (f• : A• →• B•) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv•
  field
    g• : B• →• A•
    α• : (f• ⊚ g•) ∼• id•
    β• : (g• ⊚ f•) ∼• id•

idqinv• : ∀ {ℓ} → {A• : Set• ℓ} → qinv• {ℓ} {ℓ} {A•} {A•} id•
idqinv• = record { g• = id• ; α• = refl ; β• = refl }

f1qinv : qinv• f1
f1qinv = record { g• = f3 ; α• = refl ; β• = refl }

-- equivalences

record isequiv• {ℓ ℓ'} {A• : Set• ℓ} {B• : Set• ℓ'} (f• : A• →• B•) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv•
  field
    g• : B• →• A• 
    α• : (f• ⊚ g•) ∼• id•
    h• : B• →• A•
    β• : (h• ⊚ f•) ∼• id•

equiv•₁ : ∀ {ℓ ℓ'} {A• : Set• ℓ} {B• : Set• ℓ'} {f• : A• →• B•} → 
          qinv• f• → isequiv• f•
equiv•₁ (mkqinv• qg qα qβ) = mkisequiv• qg qα qg qβ 

f1equiv : isequiv• f1
f1equiv = equiv•₁ f1qinv

_≃•_ : ∀ {ℓ ℓ'} (A• : Set• ℓ) (B• : Set• ℓ') → Set (ℓ ⊔ ℓ')
A ≃• B = Σ (A →• B) isequiv•

idequiv• : ∀ {ℓ} {A• : Set• ℓ} → A• ≃• A•
idequiv• = ( id• , equiv•₁ idqinv•) 

pt24equiv : pt 2 ≃• pt 4
pt24equiv = (f1 , f1equiv) 

------------------------------------------------------------------------------
{-- old stuff which we might need again

idright : {A B : Set} {a : A} {b : B} {p : •[ A , a ] ⇛ •[ B , b ]} →
          (trans⇛ p (id⇛ {B} {b})) 2⇛ p
idright = 2Path id⇛ id⇛ 
        
idleft : {A B : Set} {a : A} {b : B} {p : •[ A , a ] ⇛ •[ B , b ]} →
         (trans⇛ (id⇛ {A} {a}) p) 2⇛ p
idleft = 2Path id⇛ id⇛
        
assoc  : {A B C D : Set} {a : A} {b : B} {c : C} {d : D}
         {p : •[ A , a ] ⇛ •[ B , b ]}
         {q : •[ B , b ] ⇛ •[ C , c ]}
         {r : •[ C , c ] ⇛ •[ D , d ]} →
         (trans⇛ p (trans⇛ q r)) 2⇛ (trans⇛ (trans⇛ p q) r)
assoc = 2Path id⇛ id⇛

bifunctorid⋆ : {A B : Set} {a : A} {b : B} → 
  (times⇛ (id⇛ {A} {a}) (id⇛ {B} {b})) 2⇛ (id⇛ {A × B} {(a , b)})
bifunctorid⋆ = 2Path id⇛ id⇛

bifunctorid₊₁ : {A B : Set} {a : A} → 
  (plus₁⇛ {A} {B} {A} {B} (id⇛ {A} {a})) 2⇛ (id⇛ {A ⊎ B} {inj₁ a})
bifunctorid₊₁ = 2Path id⇛ id⇛

bifunctorid₊₂ : {A B : Set} {b : B} → 
  (plus₂⇛ {A} {B} {A} {B} (id⇛ {B} {b})) 2⇛ (id⇛ {A ⊎ B} {inj₂ b})
bifunctorid₊₂ = 2Path id⇛ id⇛

bifunctorC⋆ : {A B C D E F : Set} 
              {a : A} {b : B} {c : C} {d : D} {e : E} {f : F}
              {p : •[ A , a ] ⇛ •[ B , b ]}
              {q : •[ B , b ] ⇛ •[ C , c ]}
              {r : •[ D , d ] ⇛ •[ E , e ]} 
              {s : •[ E , e ] ⇛ •[ F , f ]} →
  (trans⇛ (times⇛ p r) (times⇛ q s)) 2⇛ (times⇛ (trans⇛ p q) (trans⇛ r s))
bifunctorC⋆ = 2Path id⇛ id⇛

bifunctorC₊₁₁ : {A B C D E F : Set} 
                {a : A} {b : B} {c : C}
                {p : •[ A , a ] ⇛ •[ B , b ]}
                {q : •[ B , b ] ⇛ •[ C , c ]} →
  (trans⇛ (plus₁⇛ {A} {D} {B} {E} p) (plus₁⇛ {B} {E} {C} {F} q)) 2⇛ 
  (plus₁⇛ {A} {D} {C} {F} (trans⇛ p q))
bifunctorC₊₁₁ = 2Path id⇛ id⇛

bifunctorC₊₂₂ : {A B C D E F : Set} 
                {d : D} {e : E} {f : F}
                {r : •[ D , d ] ⇛ •[ E , e ]} 
                {s : •[ E , e ] ⇛ •[ F , f ]} →
  (trans⇛ (plus₂⇛ {A} {D} {B} {E} r) (plus₂⇛ {B} {E} {C} {F} s)) 2⇛ 
  (plus₂⇛ {A} {D} {C} {F} (trans⇛ r s))
bifunctorC₊₂₂ = 2Path id⇛ id⇛

triangle : {A B : Set} {a : A} {b : B} → 
  (trans⇛ (assocr⋆⇛ {A} {⊤} {B} {a} {tt} {b}) (times⇛ id⇛ unite⋆⇛)) 2⇛
  (times⇛ (trans⇛ swap⋆⇛ unite⋆⇛) id⇛)
triangle = 2Path id⇛ id⇛

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

--}


