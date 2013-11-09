module F2 where

open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map; [_,_])
open import Data.Product hiding (map; ,_)
open import Function using (flip)
open import Relation.Binary.Core 
  using (IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary

open import Groupoid

infix  2  _∎      -- equational reasoning
infixr 2  _≡⟨_⟩_  -- equational reasoning

---------------------------------------------------------------------------
-- Paths

-- these are individual paths so to speak
-- should we represent a path like swap+ as a family explicitly:
-- swap+ : (x : A) -> x ⇛ swapF x
-- I guess we can: swap+ : (x : A) -> case x of inj1 -> swap1 x else swap2 x
{--
Use pointed types instead of singletons
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

data _⇛_ : {A B : Set} → (x : A) → (y : B) → Set₁ where
  -- + 
  unite₊⇛    : {A : Set} {x : A} → _⇛_ {⊥ ⊎ A} {A} (inj₂ x) x
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
  factor0⇛   : {A : Set} {• : ⊥} {x : A} → _⇛_ {⊥} {⊥ × A} • (• , x)
  -- congruence
  id⇛        : {A : Set} → (x : A) → x ⇛ x
  sym⇛       : {A B : Set} {x : A} {y : B} → x ⇛ y → y ⇛ x
  trans⇛     : {A B C : Set} {x : A} {y : B} {z : C} → x ⇛ y → y ⇛ z → x ⇛ z
  plus₁⇛     : {A B C D : Set} {x : A} {z : C} → 
               x ⇛ z → _⇛_ {A ⊎ B} {C ⊎ D} (inj₁ x) (inj₁ z)
  plus₂⇛     : {A B C D : Set} {y : B} {w : D} → 
               y ⇛ w → _⇛_ {A ⊎ B} {C ⊎ D} (inj₂ y) (inj₂ w)
  times⇛     : {A B C D : Set} {x : A} {y : B} {z : C} {w : D} → 
               x ⇛ z → y ⇛ w → _⇛_ {A × B} {C × D} (x , y) (z , w)

-- Introduce equational reasoning syntax to simplify proofs

_≡⟨_⟩_ : {A B C : Set} (x : A) {y : B} {z : C} → (x ⇛ y) → (y ⇛ z) → (x ⇛ z)
_ ≡⟨ p ⟩ q = trans⇛ p q

bydef : {A : Set} {x : A} → (x ⇛ x)
bydef {A} {x} = id⇛ x

_∎ : {A : Set} (x : A) → x ⇛ x
_∎ x = id⇛ x

data Singleton {A : Set} : A → Set where
  singleton : (x : A) → Singleton x

mutual 

  ap : {A B : Set} {x : A} {y : B} → x ⇛ y → Singleton x → Singleton y
  ap {.(⊥ ⊎ A)} {A} {.(inj₂ x)} {x} unite₊⇛ (singleton .(inj₂ x)) = 
    singleton x
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
  ap (id⇛ .x) (singleton x) = singleton x
  ap (sym⇛ c) (singleton x) = apI c (singleton x)
  ap (trans⇛ c₁ c₂) (singleton x) = ap c₂ (ap c₁ (singleton x))
  ap (plus₁⇛ {A} {B} {C} {D} {x} {z} c) (singleton .(inj₁ x)) 
    with ap c (singleton x)
  ... | singleton .z = singleton (inj₁ z)
  ap (plus₂⇛ {A} {B} {C} {D} {y} {w} c) (singleton .(inj₂ y)) 
    with ap c (singleton y)
  ... | singleton .w = singleton (inj₂ w)
  ap (times⇛ {A} {B} {C} {D} {x} {y} {z} {w} c₁ c₂) (singleton .(x , y)) 
    with ap c₁ (singleton x) | ap c₂ (singleton y) 
  ... | singleton .z | singleton .w = singleton (z , w)

  apI : {A B : Set} {x : A} {y : B} → x ⇛ y → Singleton y → Singleton x
  apI unite₊⇛ (singleton x) = singleton (inj₂ x)
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
  apI (id⇛ .x) (singleton x) = singleton x
  apI (sym⇛ c) (singleton x) = ap c (singleton x)
  apI {A} {B} {x} {y} (trans⇛ c₁ c₂) (singleton .y) = 
    apI c₁ (apI c₂ (singleton y))
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

data _⇛_ : {A B : Set} → (x : A) → (y : B) → Set₁ where
------------------------------------------------------------------------------
-- pi types with exactly one level of reciprocals
-- interpretation of B1 types as 1-groupoids

data B0 : Set where
  ZERO : B0
  ONE : B0
  PLUS0 : B0 → B0 → B0
  TIMES0 : B0 → B0 → B0

⟦_⟧₀ : B0 → Set
⟦ ZERO ⟧₀ = ⊥
⟦ ONE ⟧₀ = ⊤
⟦ PLUS0 b₁ b₂ ⟧₀ = ⟦ b₁ ⟧₀ ⊎ ⟦ b₂ ⟧₀
⟦ TIMES0 b₁ b₂ ⟧₀ = ⟦ b₁ ⟧₀ × ⟦ b₂ ⟧₀

data B1 : Set where
  LIFT0  : B0 → B1
  PLUS1  : B1 → B1 → B1
  TIMES1 : B1 → B1 → B1
  RECIP1 : B0 → B1

open 1Groupoid

⟦_⟧₁ : B1 → 1Groupoid
⟦ LIFT0 b0 ⟧₁ = discrete ⟦ b0 ⟧₀ 
⟦ PLUS1 b₁ b₂ ⟧₁ = ⟦ b₁ ⟧₁ ⊎G ⟦ b₂ ⟧₁
⟦ TIMES1 b₁ b₂ ⟧₁ =  ⟦ b₁ ⟧₁ ×G ⟦ b₂ ⟧₁
⟦ RECIP1 b0 ⟧₁ = {!!} -- allPaths (ı₀ b0)

ı₁ : B1 → Set
ı₁ b = set ⟦ b ⟧₁

test10 = ⟦ LIFT0 ONE ⟧₁
test11 = ⟦ LIFT0 (PLUS0 ONE ONE) ⟧₁
test12 = ⟦ RECIP1 (PLUS0 ONE ONE) ⟧₁

-- interpret isos as functors

data _⟷₁_ : B1 → B1 → Set where
  -- + 
  swap₊   : { b₁ b₂ : B1 } → PLUS1 b₁ b₂ ⟷₁ PLUS1 b₂ b₁
  assocl₊ : { b₁ b₂ b₃ : B1 } → PLUS b₁ (PLUS b₂ b₃) ⟷₁ PLUS (PLUS b₁ b₂) b₃
  assocr₊ : { b₁ b₂ b₃ : B1 } → PLUS (PLUS b₁ b₂) b₃ ⟷₁ PLUS b₁ (PLUS b₂ b₃)
  -- *
  unite⋆  : { b : B1 } → TIMES1 (LIFT0 ONE) b ⟷₁ b
  uniti⋆  : { b : B1 } → b ⟷₁ TIMES1 (LIFT0 ONE) b
  swap⋆   : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷₁ TIMES b₂ b₁
  assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷₁ TIMES (TIMES b₁ b₂) b₃
  assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷₁ TIMES b₁ (TIMES b₂ b₃)
  -- * distributes over + 
  dist    : { b₁ b₂ b₃ : B } → 
            TIMES (PLUS b₁ b₂) b₃ ⟷₁ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor  : { b₁ b₂ b₃ : B } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷₁ TIMES (PLUS b₁ b₂) b₃
  -- congruence
  id⟷₁   : { b : B } → b ⟷₁ b
  sym    : { b₁ b₂ : B } → (b₁ ⟷₁ b₂) → (b₂ ⟷₁ b₁)
  _∘_    : { b₁ b₂ b₃ : B } → (b₁ ⟷₁ b₂) → (b₂ ⟷₁ b₃) → (b₁ ⟷₁ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷₁ b₃) → (b₂ ⟷₁ b₄) → (PLUS b₁ b₂ ⟷₁ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
           (b₁ ⟷₁ b₃) → (b₂ ⟷₁ b₄) → (TIMES b₁ b₂ ⟷₁ TIMES b₃ b₄)
  η⋆ : (b : B0) → LIFT0 ONE ⟷₁ TIMES1 (LIFT0 b) (RECIP1 b)
  ε⋆ : (b : B0) → TIMES1 (LIFT0 b) (RECIP1 b) ⟷₁ LIFT0 ONE

record 1-functor (A B : 1Groupoid) : Set where
  constructor 1F
  private module A = 1Groupoid A
  private module B = 1Groupoid B

  field
    F₀ : set A → set B
    F₁ : ∀ {X Y : set A} → A [ X , Y ] → B [ F₀ X , F₀ Y ]
    -- identity : ∀ {X} → B._≈_ (F₁ (A.id {X})) B.id
    -- F-resp-≈ : ∀ {X Y} {F G : A [ X , Y ]} → A._≈_ F G → B._≈_ (F₁ F) (F₁ G)

open 1-functor public

ipath : (b : B1) → ı₁ b → ı₁ b → Set
ipath b x y = Path {ı₁ b} x y

swap⊎ : {A B : Set} → A ⊎ B → B ⊎ A
swap⊎ (inj₁ a) = inj₂ a
swap⊎ (inj₂ b) = inj₁ b

intro1⋆ : {b : B1} {x y : ı₁ b} → ipath b x y → ipath (TIMES1 (LIFT0 ONE) b) (tt , x) (tt , y)
intro1⋆ (y ⇛ z) = (tt , y) ⇛ (tt , z)

objη⋆ : (b : B0) → ı₁ (LIFT0 ONE) → ı₁ (TIMES1 (LIFT0 b) (RECIP1 b))
objη⋆ b tt = point b , point b

objε⋆ : (b : B0) → ı₁ (TIMES1 (LIFT0 b) (RECIP1 b)) → ı₁ (LIFT0 ONE)
objε⋆ b (x , y) = tt

elim1∣₁ : (b : B1) → ı₁ (TIMES1 (LIFT0 ONE) b) → ı₁ b
elim1∣₁ b (tt , x) = x

intro1∣₁ : (b : B1) → ı₁ b → ı₁ (TIMES1 (LIFT0 ONE) b)
intro1∣₁ b x = (tt , x)

swapF : {b₁ b₂ : B1} →
      let G = ⟦ b₁ ⟧₁ ⊎G ⟦ b₂ ⟧₁
          G' = ⟦ b₂ ⟧₁ ⊎G ⟦ b₁ ⟧₁ in
      {X Y : set G} → G [ X , Y ] → G' [ swap⊎ X , swap⊎ Y ]
swapF {X = inj₁ _} {inj₁ _} f = f
swapF {X = inj₁ _} {inj₂ _} ()
swapF {X = inj₂ _} {inj₁ _} ()
swapF {X = inj₂ _} {inj₂ _} f = f

eta : (b : B0) → List (ipath (LIFT0 ONE)) → List (ipath (TIMES1 (LIFT0 b) (RECIP1 b)))
-- note how the input list is not used at all!
eta b _ = prod (λ a a' → _↝_ (a , tt) (a' , tt)) (elems0 b) (elems0 b)

eps : (b : B0) → ipath (TIMES1 (LIFT0 b) (RECIP1 b)) → ipath (LIFT0 ONE)
eps b0 (a ⇛ b) = tt ⇛ tt

Funite⋆ : {b₁ : B1} → ∀ {X Y : set (discrete (ı₀ ONE) ×G ⟦ b₁ ⟧₁)} →  DPath (proj₁ X) (proj₁ Y) ×  (_↝_ ⟦ b₁ ⟧₁) (proj₂ X) (proj₂ Y) →  _↝_ ⟦ b₁ ⟧₁ (proj₂ X) (proj₂ Y) 
Funite⋆ {b₁} {tt , _} {tt , _} (reflD , y) = y

Funiti⋆ : {b₁ : B1} → ∀ {X Y : set (discrete (ı₀ ONE) ×G ⟦ b₁ ⟧₁)} →  _↝_ ⟦ b₁ ⟧₁ (proj₂ X) (proj₂ Y) → DPath (proj₁ X) (proj₁ Y) ×  (_↝_ ⟦ b₁ ⟧₁) (proj₂ X) (proj₂ Y)
Funiti⋆ y = reflD , y

mutual
  eval : {b₁ b₂ : B1} → (b₁ ⟷₁ b₂) → 1-functor ⟦ b₁ ⟧₁ ⟦ b₂ ⟧₁
  eval (swap₊ {b₁} {b₂}) = 1F swap⊎ (λ {X Y} → swapF {b₁} {b₂} {X} {Y}) 
  eval (unite⋆ {b}) = 1F (elim1∣₁ b) (Funite⋆ {b})
  eval (uniti⋆ {b}) = 1F (intro1∣₁ b) (Funiti⋆ {b})
--  eval (η⋆ b) = F₁ (objη⋆ b) (eta b )
--  eval (ε⋆ b) = F₁ (objε⋆ b) (map (eps b))

  evalB : {b₁ b₂ : B1} → (b₁ ⟷₁ b₂) → 1-functor ⟦ b₂ ⟧₁ ⟦ b₁ ⟧₁
  evalB (swap₊ {b₁} {b₂}) = 1F swap⊎ ((λ {X Y} → swapF {b₂} {b₁} {X} {Y}))
  evalB (unite⋆ {b}) = 1F (intro1∣₁ b) (Funiti⋆ {b})
  evalB (uniti⋆ {b}) = 1F (elim1∣₁ b) (Funite⋆ {b})
--  evalB (η⋆ b) = F₁ (objε⋆ b) (map (eps b))
--  evalB (ε⋆ b) = F₁ (objη⋆ b) (eta b)

eval assocl₊ = ? -- : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷₁ PLUS (PLUS b₁ b₂) b₃
eval assocr₊ = ? -- : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷₁ PLUS b₁ (PLUS b₂ b₃)
eval uniti⋆ = ? -- : { b : B } → b ⟷₁ TIMES ONE b
eval swap⋆ = ? --  : { b₁ b₂ : B } → TIMES b₁ b₂ ⟷₁ TIMES b₂ b₁
eval assocl⋆ = ? -- : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷₁ TIMES (TIMES b₁ b₂) b₃
eval assocr⋆ = ? -- : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷₁ TIMES b₁ (TIMES b₂ b₃)
eval dist = ? -- : { b₁ b₂ b₃ : B } → TIMES (PLUS b₁ b₂) b₃ ⟷₁ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
eval factor = ? -- : { b₁ b₂ b₃ : B } → PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⟷₁ TIMES (PLUS b₁ b₂) b₃
eval id⟷₁ = ? --  : { b : B } → b ⟷₁ b
eval (sym c) = ? -- : { b₁ b₂ : B } → (b₁ ⟷₁ b₂) → (b₂ ⟷₁ b₁)
eval (c₁ ∘ c₂) = ? -- : { b₁ b₂ b₃ : B } → (b₁ ⟷₁ b₂) → (b₂ ⟷₁ b₃) → (b₁ ⟷₁ b₃)
eval (c₁ ⊕ c₂) = ? -- : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟷₁ b₃) → (b₂ ⟷₁ b₄) → (PLUS b₁ b₂ ⟷₁ PLUS b₃ b₄)
eval (c₁ ⊗ c₂) = ? -- : { b₁ b₂ b₃ b₄ : B } → (b₁ ⟷₁ b₃) → (b₂ ⟷₁ b₄) → (TIMES b₁ b₂ ⟷₁ TIMES b₃ b₄)

-- lid⇛ : {A B : Set} {x : A} {y : B} → (trans⇛ (id⇛ x) (x ⇛ y)) ⇛ (x ⇛ y)
-- lid⇛ {A} {B} {x} {y} = 
--  pathInd ? 

ap : {A B : Set} → (f : A → B) → {a a' : A} → Path a a' → Path (f a) (f a')
ap f (a ⇛ a') = (f a) ⇛ (f a')

_∙⇛_ : {A : Set} {a b c : A} → Path b c → Path a b → Path a c
(b ⇛ c) ∙⇛ (a ⇛ .b) = a ⇛ c

_⇚ : {A : Set} {a b : A} → Path a b → Path b a
(x ⇛ y) ⇚ = y ⇛ x

lid⇛ : {A : Set} {x y : A} (α : Path x y) → (id⇛ y ∙⇛ α) ≣⇛ α
lid⇛ (x ⇛ y) = refl⇛

rid⇛ : {A : Set} {x y : A} (α : Path x y) → (α ∙⇛ id⇛ x) ≣⇛ α
rid⇛ (x ⇛ y) = refl⇛

assoc⇛ : {A : Set} {w x y z : A} (α : Path y z) (β : Path x y) (δ : Path w x) → ((α ∙⇛ β) ∙⇛ δ) ≣⇛ (α ∙⇛ (β ∙⇛ δ))
assoc⇛ (y ⇛ z) (x ⇛ .y) (w ⇛ .x) = refl⇛

l⇚ : {A : Set}  {x y : A} (α : Path x y) → ((α ⇚) ∙⇛ α) ≣⇛ id⇛ x
l⇚ (x ⇛ y) = refl⇛

r⇚ : {A : Set} {x y : A} (α : Path x y) → (α ∙⇛ (α ⇚)) ≣⇛ id⇛ y
r⇚ (x ⇛ y) = refl⇛

sym⇛ : {A : Set} {x y : A} {α β : Path x y} → α ≣⇛ β → β ≣⇛ α
sym⇛ refl⇛ = refl⇛

trans⇛ : {A : Set} {x y : A} {α β δ : Path x y} → α ≣⇛ β → β ≣⇛ δ → α ≣⇛ δ
trans⇛ refl⇛ refl⇛ = refl⇛
 
equiv≣⇛ : {A : Set} {x y : A} → IsEquivalence {_} {_} {Path x y} (_≣⇛_)
equiv≣⇛ = record { refl = refl⇛; sym = sym⇛; trans = trans⇛ }

resp≣⇛ : {A : Set} {x y z : A} {f h : Path y z} {g i : Path x y} →
  f ≣⇛ h → g ≣⇛ i → (f ∙⇛ g) ≣⇛ (h ∙⇛ i)
resp≣⇛ refl⇛ refl⇛ = refl⇛

record 0-type : Set₁ where
  constructor G₀
  field
    ∣_∣₀ : Set

open 0-type public

plus : 0-type → 0-type → 0-type
plus t₁ t₂ = G₀ (∣ t₁ ∣₀ ⊎ ∣ t₂ ∣₀) 

times : 0-type → 0-type → 0-type
times t₁ t₂ = G₀ (∣ t₁ ∣₀ × ∣ t₂ ∣₀)

⟦_⟧₀ : B0 → 0-type
⟦ ONE ⟧₀ = G₀ ⊤ 
⟦ PLUS0 b₁ b₂ ⟧₀ = plus ⟦ b₁ ⟧₀ ⟦ b₂ ⟧₀
⟦ TIMES0 b₁ b₂ ⟧₀ = times ⟦ b₁ ⟧₀ ⟦ b₂ ⟧₀

ı₀ : B0 → Set
ı₀ b = ∣ ⟦ b ⟧₀ ∣₀ 

point : (b : B0) → ı₀ b
point ONE = tt
point (PLUS0 b _) = inj₁ (point b)
point (TIMES0 b₀ b₁) = point b₀ , point b₁ 

allPaths : Set → 1Groupoid
allPaths a =  record
    { set = a
    ; _↝_ = Path
    ; _≈_ = _≣⇛_
    ; id = λ {x} → id⇛ x
    ; _∘_ = _∙⇛_
    ; _⁻¹ = _⇚
    ; lneutr = lid⇛
    ; rneutr = rid⇛
    ; assoc = assoc⇛
    ; linv = l⇚
    ; rinv = r⇚
    ; equiv = equiv≣⇛ 
    ;  ∘-resp-≈ = resp≣⇛}

--}


