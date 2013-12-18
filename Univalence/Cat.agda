{-# OPTIONS --without-K #-}
module Cat where

import Level as L
open import Data.Fin hiding (fromℕ; toℕ)
open import Data.Nat
open import Data.Product
open import Data.List
open import Function renaming (_∘_ to _○_)

open import HoTT
open import FT
open import FT-Nat
import Equivalences as E 
open import Path2Equiv

{--
1. postulate path2equiv
2. show that (FT, path) is equivalent to (FinSet, bijections) as categories
3. show that [[ ]]: (B, <->) -> (Set, function) is a functor
   [where (Set is Agda's Set)].
--}

{--
Categories, functors, etc. adapted from:
http://wiki.portal.chalmers.se/agda/uploads/Main.Libraries/20110915Category.agda

Consider using: 
https://github.com/tomprince/agda-categories
https://github.com/tomprince/agda-categories/blob/master/Categories/Category.agda
--}

------------------------------------------------------------------
-- Categories

record Setoid (a b : L.Level) : Set (L.suc (a L.⊔ b)) where
  infix 2 _∼_
  field
    object : Set a
    _∼_ : object → object → Set b
    refl∼ : {x : object} → x ∼ x
    sym∼ : {x y : object} → x ∼ y → y ∼ x
    trans∼ : {x y z : object} → y ∼ z → x ∼ y → x ∼ z

strictSetoid : ∀ {a} → Set a → Setoid a a
strictSetoid A = record
  { object = A
  ; _∼_ = _≡_
  ; refl∼ = λ {x} → refl x
  ; sym∼ = !
  ; trans∼ = λ q p → p ∘ q
  }

∥_∥ : ∀ {a b c} {X : Set a} → (h : X → X → Setoid b c) → (x y : X) → Set b
∥ h ∥ x y = Setoid.object (h x y)

record Cat (a b c : L.Level) : Set (L.suc (a L.⊔ b L.⊔ c)) where
  field
    object : Set a
    hom : object → object → Setoid b c
    identity : (x : object) → ∥ hom ∥ x x
    comp : {x y z : object} → ∥ hom ∥ y z → ∥ hom ∥ x y → ∥ hom ∥ x z
    comp∼ : {x y z : object} →
             {g0 g1 : ∥ hom ∥ y z} → {f0 f1 : ∥ hom ∥ x y} →
             (g0∼g1 : let open Setoid (hom y z) in g0 ∼ g1) →
             (f0∼f1 : let open Setoid (hom x y) in f0 ∼ f1) →
             let open Setoid (hom x z) in comp g0 f0 ∼ comp g1 f1
    associativity∼ : {w x y z : object} →
      (f : ∥ hom ∥ y z) → (g : ∥ hom ∥ x y) → (h : ∥ hom ∥ w x) →
      let open Setoid (hom w z) in comp (comp f g) h ∼ comp f (comp g h)
    left-identity∼ : {x y : object} → (f : ∥ hom ∥ x y) →
      let open Setoid (hom x y) in comp (identity y) f ∼ f
    right-identity∼ : {x y : object} → (f : ∥ hom ∥ x y) →
      let open Setoid (hom x y) in comp f (identity x) ∼ f

-- the type of objects in category C
ob : ∀ {a b c} → Cat a b c → Set a
ob C = Cat.object C

-- the type of morphisms between two given objects in C
_〈_,_〉 : ∀ {a b c} → (C : Cat a b c) → ob C → ob C → Set b
C 〈 X , Y 〉 = ∥ Cat.hom C ∥ X Y

-- the type of identities of morphisms
_∣_∼_ : ∀ {a b c} → (C : Cat a b c) → {X Y : ob C} → 
        C 〈 X , Y 〉 → C 〈 X , Y 〉 → Set c
_∣_∼_ C {X} {Y} f g = Setoid._∼_ (Cat.hom C X Y) f g

-- convenient abbreviation for identity morphism
idC : ∀ {a b c} → (C : Cat a b c) → (x : ob C) → C 〈 x , x 〉
idC C x = Cat.identity C x

-- convenient abbreviation for composition of morphisms
_∣_∘_ : ∀ {a b c} → (C : Cat a b c) → {x y z : ob C } →
        C 〈 y , z 〉 → C 〈 x , y 〉 → C 〈 x , z 〉
C ∣ g ∘ f = Cat.comp C g f

------------------------------------------------------------------
-- Functors
record _=>_ {a b c a' b' c'} (C : Cat a b c) (D : Cat a' b' c') : 
  Set (a L.⊔ a' L.⊔ b L.⊔ b' L.⊔ c L.⊔ c') where
  field
    object : ob C  → ob D 
    hom : {X Y : ob C} →
      C 〈 X , Y 〉 → D 〈 object X , object Y 〉
    hom∼ : {X Y : ob C} → (f g : C 〈 X , Y 〉) →
      (f∼g : C ∣ f ∼ g) → D ∣ hom f ∼ hom g
    identity∼ : {X : ob C} →
      D ∣ hom (idC C X) ∼ idC D (object X)
    comp∼ : {X Y Z : ob C} → (f : C 〈 Y , Z 〉) → (g : C 〈 X , Y 〉) →
      D ∣ hom (C ∣ f ∘ g) ∼ (D ∣ hom f ∘ hom g)

-- Applying the functor to objects
_`_ : ∀ {a b c a' b' c'} {X : Cat a b c} → {Y : Cat a' b' c'} →
  X => Y → ob X → ob Y
F ` x = _=>_.object F x

-- Applying the functor to morphisms
_``_ : ∀ {a b c a' b' c'} {X : Cat a b c} → {Y : Cat a' b' c'} →
  {x0 x1 : ob X} → (F : X => Y) → X 〈 x0 , x1 〉 → Y 〈 F ` x0 , F ` x1 〉
F `` f = _=>_.hom F f

------------------------------------------------------------------
-- The category (FinSet,bijections)
-- M, N, L are finite sets witnessed by their sizes m, n, l
-- F, G, H are bijections

-- bijections between two sets M and N
record Bijection (m n : ℕ) : Set where
  field 
    f : Fin m → Fin n
    g : Fin n → Fin m
    injective  : {x y : Fin m} → f x ≡ f y → x ≡ y
    surjective : {x : Fin n} → f (g x) ≡ x

-- there is a bijection from each set to itself
idBijection : (m : ℕ) → Bijection m m
idBijection m = record {
    f = id ;
    g = id ;
    injective = id ; 
    surjective = λ {x} → refl x
  } 

-- composition of bijections
∘Bijection : {m n l : ℕ} → Bijection n l → Bijection m n → Bijection m l
∘Bijection G F = record {
    f = Bijection.f G ○ Bijection.f F ;
    g = Bijection.g F ○ Bijection.g G ;
    injective = λ α → Bijection.injective F (Bijection.injective G α) ;
    surjective = λ {x} → 
      Bijection.f G (Bijection.f F (Bijection.g F (Bijection.g G x)))
        ≡⟨ ap (λ x → Bijection.f G x) (Bijection.surjective F) ⟩
      Bijection.f G (Bijection.g G x) 
        ≡⟨ Bijection.surjective G ⟩ 
      x ∎
  } 

-- two bijections are the "same" if they agree modulo ≡ 
∼Bijection : {m n : ℕ} → Bijection m n → Bijection m n → Set
∼Bijection F G = (Bijection.f F) E.∼ (Bijection.f G)

-- the set of all bijections between two sets M and N taken modulo ≡
BijectionSetoid : (m n : ℕ) → Setoid L.zero L.zero
BijectionSetoid m n = record {
    object = Bijection m n ;
    _∼_ = ∼Bijection ; 
    refl∼ = λ {F} → E.refl∼ {f = Bijection.f F} ; 
    sym∼ = λ {F} {G} → 
             E.sym∼ {f = Bijection.f F} {g = Bijection.f G} ;
    trans∼ = λ {F} {G} {H} P Q → 
               E.trans∼ {f = Bijection.f F}
                        {g = Bijection.f G} 
                        {h = Bijection.f H}
                        Q P 
    }

-- the category of finite sets and bijections
FinCat : Cat L.zero L.zero L.zero
FinCat = record {
          object = ℕ ; 
          hom = λ m n → BijectionSetoid m n ; 
          identity = idBijection ;
          comp = λ G F → ∘Bijection G F ;
          comp∼ = λ {m} {n} {l} {G₀} {G₁} {F₀} {F₁} Q P x →
                    Bijection.f (∘Bijection G₀ F₀) x
                      ≡⟨ bydef ⟩
                    Bijection.f G₀ (Bijection.f F₀ x)
                      ≡⟨ ap (λ z → Bijection.f G₀ z) (P x) ⟩ 
                    Bijection.f G₀ (Bijection.f F₁ x)
                      ≡⟨ Q (Bijection.f F₁ x) ⟩ 
                    Bijection.f (∘Bijection G₁ F₁) x ∎ ;
          associativity∼  = λ F G H x →
            Bijection.f (∘Bijection F G) (Bijection.f H x)
              ≡⟨ bydef ⟩
            Bijection.f F (Bijection.f G (Bijection.f H x)) ∎ ;
          left-identity∼  = λ {m} {n} F x →
            Bijection.f (idBijection n) (Bijection.f F x) 
              ≡⟨ bydef ⟩ 
            Bijection.f F x ∎ ;
          right-identity∼ = λ {m} {n} F x →
            Bijection.f F (Bijection.f (idBijection m) x)
              ≡⟨ bydef ⟩ 
            Bijection.f F x ∎ 
      }

------------------------------------------------------------------
-- The category (FinSet,HoTT-equivalence)
-- M, N, L are finite sets witnessed by their sizes m, n, l
-- F, G, H are equivalences

-- the set of all equivalences between two sets M and N taken modulo ≡
EqSetoid : (m n : ℕ) → Setoid L.zero L.zero
EqSetoid m n = record {
    object = (Fin m) E.≃ (Fin n) ; 
    _∼_ = {!!} ;
    refl∼ = {!!} ;
    sym∼ = {!!} ;
    trans∼ = {!!} 
    }



FinCat' : Cat L.zero L.zero L.zero
FinCat' = record {
          object = ℕ ; 
          hom = EqSetoid ;
          identity = λ m → E.id≃ {A = Fin m} ;
          comp = λ q p → E.trans≃ p q ;
          comp∼ = {!!} ; 
          associativity∼  = {!!} ;
          left-identity∼  = {!!} ;
          right-identity∼ = {!!} 
      }

------------------------------------------------------------------
-- The category (FT,path)

-- evaluation
evalF : {b₁ b₂ : FT} → (b₁ ⇛ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
evalF p = proj₁ (path2equiv p)

-- could equivalently use sym≃ on the result of path2equiv p
evalB : {b₁ b₂ : FT} → (b₁ ⇛ b₂) → ⟦ b₂ ⟧ → ⟦ b₁ ⟧
evalB p = proj₁ (path2equiv (sym⇛ p)) 

-- equivalence of combinators
_∼c_ : {b₁ b₂ : FT} → (c₁ c₂ : b₁ ⇛ b₂) → Set
_∼c_ {b₁} {b₂} c₁ c₂ = (v : ⟦ b₁ ⟧) → evalF c₁ v ≡ evalF c₂ v

-- equivalence class of paths between two types
paths : FT → FT → Setoid L.zero L.zero 
paths b₁ b₂ = record {
               object = b₁ ⇛ b₂ ;
               _∼_ = _∼c_ ;
               refl∼  = λ {c} v → refl (evalF c v) ;
               sym∼ = λ p v → ! (p v) ;
               trans∼ = λ q p v → (p v) ∘ (q v) 
             } 

-- the category of finite types and paths
FTCat : Cat L.zero L.zero L.zero
FTCat = record {
          object = FT ;
          hom = paths ;
          identity = λ b → id⇛ {b}  ;
          comp = λ c₂ c₁ → c₁ ◎ c₂ ;
          comp∼ = λ {b₀} {b₁} {b₂} {c₂} {c₂'} {c₁} {c₁'} q p v →
                    evalF (c₁ ◎ c₂) v
                      ≡⟨ bydef  ⟩
                    evalF c₂ (evalF c₁ v)
                      ≡⟨ ap (λ z → evalF c₂ z) (p v) ⟩ 
                    evalF c₂ (evalF c₁' v)
                      ≡⟨ q (evalF c₁' v) ⟩
                    evalF (c₁' ◎ c₂') v ∎ ;
          associativity∼  = λ r q p v →
            evalF (p ◎ (q ◎ r)) v 
              ≡⟨ bydef ⟩
            evalF r (evalF q (evalF p v))
              ≡⟨ bydef ⟩ 
            evalF ((p ◎ q) ◎ r) v ∎ ;
          left-identity∼  = λ p v → 
            evalF id⇛ (evalF p v)
              ≡⟨ bydef ⟩
             evalF p v ∎ ; 
          right-identity∼ = λ p v → 
            evalF p (evalF id⇛ v) 
              ≡⟨ bydef ⟩
            evalF p v ∎
      }

------------------------------------------------------------------
{-- 
Two categories C and D are equivalent if we have: 
- a functor F : C -> D
- a functor G : D -> C
- two natural isomorphisms ε : F ∘ G -> I_D and η : G ∘ F -> I_C

--} 

-- functor from FinCat to FTCat
fin2ft : FinCat => FTCat
fin2ft = record {
    object = fromℕ ;
    hom = {!!} ;
    hom∼ = {!!} ;
    identity∼ = {!!} ;
    comp∼ = {!!}
  }

-- functor from FTCat to FinCat 
ft2fin : FTCat => FinCat
ft2fin = record {
    object = toℕ ;
    hom = {!!} ;
    hom∼ = {!!} ;
    identity∼ = {!!} ;
    comp∼ = {!!}
  }

------------------------------------------------------------------

