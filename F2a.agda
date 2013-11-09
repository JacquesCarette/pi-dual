module F2a where

open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map; [_,_])
open import Data.Product hiding (map; ,_)
open import Function using (flip)
open import Relation.Binary.Core 
  using (IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary

open import Groupoid

-- infix  2  _∎      -- equational reasoning
-- infixr 2  _≡⟨_⟩_  -- equational reasoning

---------------------------------------------------------------------------
-- Paths

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

-- Pointed type
record P (A : Set) : Set where
  constructor ↑
  field
    p : A

open P

data _⇛_ : {A B : Set} → P A → P B → Set₁ where
  -- + 
  unite₊⇛    : {A : Set} {x : P A} → ↑ (inj₂ {A = ⊥ ⊎ A} (p x)) ⇛ x
{-
  uniti₊⇛    : {A : Set} {x : A} → _⇛_ {A} {⊥ ⊎ A} x (inj₂ x)
  swap₁₊⇛    : {A B : Set} {x : A} → _⇛_ {A ⊎ B} {B ⊎ A} (inj₁ x) (inj₂ x)
  swap₂₊⇛    : {A B : Set} {y : B} → _⇛_ {A ⊎ B} {B ⊎ A} (inj₂ y) (inj₁ y)
  assocl₁₊⇛  : {A B C : Set} {x : A} → 
               _⇛_ {A ⊎ (B ⊎ C)} {(A ⊎ B) ⊎ C} (inj₁ x) (inj₁ (inj₁ x)) 
  assocl₂₁₊⇛ : {A B C : Set} {y : B} → 
               _⇛_ {A ⊎ (B ⊎ C)} {(A ⊎ B) ⊎ C} (inj₂ (inj₁ y)) (inj₁ (inj₂ y)) 
  assocl₂₂₊⇛ : {A B C : Set} {z : C} → 
               _⇛_ {A ⊎ (B ⊎ C)} {(A ⊎ B) ⊎ C} (inj₂ (inj₂ z)) (inj₂ z)
  assocr₁₁₊⇛ : {A B C : Set} {x : A} → 
               _⇛_ {(A ⊎ B) ⊎ C} {A ⊎ (B ⊎ C)} (inj₁ (inj₁ x)) (inj₁ x)
  assocr₁₂₊⇛ : {A B C : Set} {y : B} → 
               _⇛_ {(A ⊎ B) ⊎ C} {A ⊎ (B ⊎ C)} (inj₁ (inj₂ y)) (inj₂ (inj₁ y))
  assocr₂₊⇛  : {A B C : Set} {z : C} → 
               _⇛_ {(A ⊎ B) ⊎ C} {A ⊎ (B ⊎ C)} (inj₂ z) (inj₂ (inj₂ z))
  -- *
  unite⋆⇛    : {A : Set} {x : A} → _⇛_ {⊤ × A} {A} (tt , x) x
  uniti⋆⇛    : {A : Set} {x : A} → _⇛_ {A} {⊤ × A} x (tt , x)
  swap⋆⇛     : {A B : Set} {x : A} {y : B} → _⇛_ {A × B} {B × A} (x , y) (y , x)
  assocl⋆⇛   : {A B C : Set} {x : A} {y : B} {z : C} → 
               _⇛_ {A × (B × C)} {(A × B) × C} (x , (y , z)) ((x , y) , z)
  assocr⋆⇛   : {A B C : Set} {x : A} {y : B} {z : C} → 
               _⇛_ {(A × B) × C} {A × (B × C)} ((x , y) , z) (x , (y , z))
  -- distributivity
  dist₁⇛     : {A B C : Set} {x : A} {z : C} → 
               _⇛_ {(A ⊎ B) × C} {(A × C) ⊎ (B × C)} (inj₁ x , z) (inj₁ (x , z))
  dist₂⇛     : {A B C : Set} {y : B} {z : C} → 
               _⇛_ {(A ⊎ B) × C} {(A × C) ⊎ (B × C)} (inj₂ y , z) (inj₂ (y , z))
  factor₁⇛   : {A B C : Set} {x : A} {z : C} → 
               _⇛_ {(A × C) ⊎ (B × C)} {(A ⊎ B) × C} (inj₁ (x , z)) (inj₁ x , z)
  factor₂⇛   : {A B C : Set} {y : B} {z : C} → 
               _⇛_ {(A × C) ⊎ (B × C)} {(A ⊎ B) × C}  
                   (inj₂ (y , z)) (inj₂ y , z)
  dist0⇛     : {A : Set} {• : ⊥} {x :  A} → _⇛_ {⊥ × A} {⊥} (• , x) •
  factor0⇛   : {A : Set} {• : ⊥} {x : A} → _⇛_ {⊥} {⊥ × A} • (• , x) -}
  -- congruence
  id⇛        : {A : Set} → (x : P A) → x ⇛ x
  sym⇛       : {A B : Set} {x : P A} {y : P B} → x ⇛ y → y ⇛ x 
  trans⇛     : {A B C : Set} {x : P A} {y : P B} {z : P C} → x ⇛ y → y ⇛ z → x ⇛ z
{-  plus₁⇛     : {A B C D : Set} {x : A} {z : C} → 
               x ⇛ z → _⇛_ {A ⊎ B} {C ⊎ D} (inj₁ x) (inj₁ z)
  plus₂⇛     : {A B C D : Set} {y : B} {w : D} → 
               y ⇛ w → _⇛_ {A ⊎ B} {C ⊎ D} (inj₂ y) (inj₂ w)
  times⇛     : {A B C D : Set} {x : A} {y : B} {z : C} {w : D} → 
               x ⇛ z → y ⇛ w → _⇛_ {A × B} {C × D} (x , y) (z , w)
-}
-- Introduce equational reasoning syntax to simplify proofs

_≡⟨_⟩_ : {A B C : Set} (x : P A) {y : P B} {z : P C} → (x ⇛ y) → (y ⇛ z) → (x ⇛ z)
_ ≡⟨ p ⟩ q = trans⇛ p q

bydef : {A : Set} {x : P A} → (x ⇛ x)
bydef {A} {x} = id⇛ x

_∎ : {A : Set} (x : P A) → x ⇛ x
_∎ x = id⇛ x

{-
data Singleton {A : Set} : A → Set where
  singleton : (x : A) → Singleton x
-}
mutual 

  ap : {A B : Set} {x : P A} {y : P B} → x ⇛ y → P A → P B
  ap t x = ?
  {-
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
  ap factor0⇛ (singleton ()) -}
  ap (id⇛ x) y = y
  ap (sym⇛ c) x = apI c x
  ap (trans⇛ c₁ c₂) x = ap c₂ (ap c₁ x)
  {-
  ap (plus₁⇛ {A} {B} {C} {D} {x} {z} c) (singleton .(inj₁ x)) 
    with ap c (singleton x)
  ... | singleton .z = singleton (inj₁ z)
  ap (plus₂⇛ {A} {B} {C} {D} {y} {w} c) (singleton .(inj₂ y)) 
    with ap c (singleton y)
  ... | singleton .w = singleton (inj₂ w)
  ap (times⇛ {A} {B} {C} {D} {x} {y} {z} {w} c₁ c₂) (singleton .(x , y)) 
    with ap c₁ (singleton x) | ap c₂ (singleton y) 
  ... | singleton .z | singleton .w = singleton (z , w)
-}

  apI : {A B : Set} {x : P A} {y : P B} → x ⇛ y → A → B
  apI unite₊⇛ x = (inj₂ x)
{-
 
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
  -}
  apI (id⇛ .x) x = x
  apI (sym⇛ c) x = ap c x
  apI {A} {B} {x} {y} (trans⇛ c₁ c₂) .y = 
    apI c₁ (apI c₂ y)
  {-
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

------------------------------------------------------------------------------
-- Now interpret a path (x ⇛ y) as a value of type (1/x , y)

Recip : {A : Set} → (x : A) → Set₁
Recip {A} x = (x ⇛ x) 

η : {A : Set} {x : A} → ⊤ → Recip x × Singleton x
η {A} {x} tt = (id⇛ x , singleton x)

ε : {A : Set} {x : A} → Recip x × Singleton x → ⊤
ε {A} {x} (rx , singleton .x) = tt -- makes no sense

apr : {A B : Set} {x : A} {y : B} → (x ⇛ y) → Recip y → Recip x
apr {A} {B} {x} {y} p ry = 
  x 
    ≡⟨ p ⟩
  y
    ≡⟨ ry ⟩
  y
    ≡⟨ sym⇛ p ⟩
  x ∎

-}

{--
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

--}


