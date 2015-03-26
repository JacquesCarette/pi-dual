{-# OPTIONS --without-K #-}

module VecHelpers where

open import Data.Nat
import Data.Fin as F

open import Data.Vec
open import Function renaming (_∘_ to _○_) 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infixl 10 _∘̬_     -- vector composition

------------------------------------------------------------------
-- VECTOR LEMMAS AND HELPERS

vmap : {n : ℕ} → {A B : Set} → (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x ∷ xs) = (f x) ∷ (vmap f xs)

-- Syntactic sugar for lookup that's a lot nicer
_!!_ : {A : Set} → {n : ℕ} → Vec A n → F.Fin n → A
_!!_ v i = lookup i v

-- XXX: is this in the right order?
_∘̬_ : {m n : ℕ} {A : Set} → Vec (F.Fin n) m → Vec A n → Vec A m 
v₁ ∘̬ v₂ = tabulate (λ i → v₂ !! (v₁ !! i))

_∘̬′_ : {m n : ℕ} {A : Set} → Vec (F.Fin n) m → Vec A n → Vec A m 
[] ∘̬′ v₂ = []
(i ∷ is) ∘̬′  v₂ = (v₂ !! i) ∷ (is ∘̬′ v₂)

∘̬≡∘̬′ : {m n : ℕ} {A : Set} (v₁ : Vec (F.Fin n) m) (v₂ : Vec A n) → 
       (v₁ ∘̬ v₂) ≡ (v₁ ∘̬′ v₂)
∘̬≡∘̬′ [] v₂ = refl
∘̬≡∘̬′ (x ∷ v₁) v₂ = cong (_∷_ (v₂ !! x)) (∘̬≡∘̬′ v₁ v₂)

ntimes : {A : Set} → ℕ → (f : A → A) → A → A
ntimes zero f a = a
ntimes (suc n) f a = f (ntimes n f a)

ntimesD : {A : Set} → {B : A → Set} → {g : A → A} → (n : ℕ) →
          (f : {a : A} → B a → B (g a)) →
          {a : A} →
          B a → B (ntimes n g a)
ntimesD zero f b = b
ntimesD {g = g} (suc n) f {a = a} b =
  f {ntimes n g a} (ntimesD {g = g} n (λ {a} → f {a}) {a = a} b)

ntails : {A : Set} → {n k : ℕ} → Vec A (ntimes k suc n) → Vec A n
ntails {k = zero} v = v
ntails {k = suc n} (x ∷ xs) = ntails {k = n} xs

ntails₀ : {A : Set} → {k : ℕ} → (v : Vec A (ntimes k suc zero)) → 
          [] ≡ ntails {k = k} v
ntails₀ {k = zero} [] = refl
ntails₀ {k = suc k} (x ∷ v) = ntails₀ {k = k} v

-- Important lemma about lookup; for some reason it doesn't seem to be in the
-- library even though it's in the main agda tutorial, iirc
map!! : {n : ℕ} → {A B : Set} → (f : A → B) → (v : Vec A n) → (i : F.Fin n) → 
        (vmap f v) !! i ≡ f (v !! i)
map!! {zero}  f  [] ()
map!! {suc n} f (x ∷ xs) F.zero    = refl
map!! {suc n} f (x ∷ xs) (F.suc i) = map!! f xs i

lookupTab : {A : Set} {n : ℕ} {f : F.Fin n → A} →  (i : F.Fin n) → 
            (tabulate f) !! i ≡ (f i)
lookupTab {f = f} F.zero   = refl
lookupTab        (F.suc i) = lookupTab i

mapTab : {A B : Set} → {n : ℕ} → (f : A → B) → (g : F.Fin n → A) →
         vmap f (tabulate g) ≡ tabulate (f ○ g)
mapTab {n = zero}  f g = refl
mapTab {n = suc n} f g = 
  cong (_∷_ (f (g F.zero))) (mapTab {n = n} f (g ○ F.suc))
  
-- Lemma for proving that two vectors are equal if their tabulates agree
-- on all inputs.
tabf∼g : {n : ℕ} → {A : Set} → (f g : F.Fin n → A) → (∀ x → f x ≡ g x) →
         tabulate f ≡ tabulate g
tabf∼g {zero} f g p = refl
tabf∼g {suc n} f g p with f F.zero | g F.zero | p F.zero
tabf∼g {suc n} f g p | x | .x | refl =
  cong (_∷_ x) (tabf∼g {n} (f ○ F.suc) (g ○ F.suc) (p ○ F.suc))

lookup∼vec : {n : ℕ} → {A : Set} → 
             (v₁ v₂ : Vec A n) → (∀ i → v₁ !! i ≡ v₂ !! i) → v₁ ≡ v₂
lookup∼vec []          []           p = refl
lookup∼vec (x ∷ v₁) (x₁ ∷ v₂) p with p F.zero
lookup∼vec (x ∷ v₁) (.x ∷ v₂) p | refl = 
  cong (_∷_ x) (lookup∼vec v₁ v₂ (p ○ F.suc))

∘̬id : {A : Set} → {n : ℕ} → (k : ℕ) → (v : Vec A (ntimes k suc n)) →
       (tabulate {n} (ntimesD {ℕ} {F.Fin} {suc} k F.suc)) ∘̬ v ≡
       (tabulate (λ i → v !! (ntimesD {ℕ} {F.Fin} {suc} k F.suc i)))
∘̬id {n = n} k v = begin
       (tabulate {n} (ntimesD {ℕ} {F.Fin} {suc} k F.suc)) ∘̬ v
         ≡⟨ refl ⟩
       (tabulate 
         (λ i → v !! (tabulate (ntimesD {ℕ} {F.Fin} {suc} k F.suc) !! i)))
         ≡⟨ tabf∼g
              (λ i → v !! (tabulate (ntimesD {ℕ} {F.Fin} {suc} k F.suc) !! i))
              (λ i → v !! ntimesD {ℕ} {F.Fin} {suc} k F.suc i)
              (λ i → cong (_!!_ v) (lookupTab i)) ⟩
       (tabulate (λ i → v !! (ntimesD {ℕ} {F.Fin} {suc} k F.suc i))) ∎

map2+id : {m n : ℕ} → (v : Vec (F.Fin n) m) → {x y : F.Fin (suc (suc n))} →
          (vmap F.suc (vmap F.suc v)) ∘̬′
            (x ∷ y ∷ tabulate {n} (F.suc ○ F.suc)) ≡
          (vmap F.suc (vmap F.suc v))
map2+id [] = refl
map2+id {suc m} {n} (i ∷ v) {x} {y} =
  begin
  (vmap F.suc (vmap F.suc (i ∷ v))) ∘̬′ (x ∷ y ∷ tabulate (F.suc ○ F.suc))
    ≡⟨ refl ⟩
  (tabulate (F.suc ○ F.suc) !! i) ∷
    (vmap F.suc (vmap F.suc v)) ∘̬′ (x ∷ y ∷ tabulate (F.suc ○ F.suc))
    ≡⟨ cong (λ z → z ∷ ((vmap F.suc (vmap F.suc v))) ∘̬′ (x ∷ y ∷ tabulate (F.suc ○ F.suc)))
            (lookupTab i) ⟩
  F.suc (F.suc i) ∷ (vmap F.suc (vmap F.suc v) ∘̬′ (x ∷ y ∷ tabulate (F.suc ○ F.suc)))
    ≡⟨ cong (_∷_ (F.suc (F.suc i))) (map2+id v) ⟩
  F.suc (F.suc i) ∷ (vmap F.suc (vmap F.suc v))
    ≡⟨ refl ⟩
  (vmap F.suc (vmap F.suc (i ∷ v))) ∎

head!!0 : {n : ℕ} {A : Set} (v : Vec A (suc n)) → v !! F.zero ≡ head v
head!!0 (x ∷ v) = refl

headmap : {n : ℕ} {A B : Set} {f : A → B} (v : Vec A (suc n)) →
          head (vmap f v) ≡ f (head v)
headmap (x ∷ v) = refl

tailmap : {n : ℕ} {A B : Set} {f : A → B} (v : Vec A (suc n)) →
          tail (vmap f v) ≡ vmap f (tail v)
tailmap (x ∷ v) = refl

2suc∘̬2tail : {n : ℕ} {A : Set} (v : Vec A (suc (suc n))) →
             (tabulate (F.suc ○ F.suc)) ∘̬ v ≡ (tail (tail v))
2suc∘̬2tail (x ∷ x₁ ∷ v) =
  begin
  (tabulate (F.suc ○ F.suc)) ∘̬ (x ∷ x₁ ∷ v)
    ≡⟨ refl ⟩
  tabulate (λ i → (x ∷ x₁ ∷ v) !! (tabulate (F.suc ○ F.suc) !! i))
    ≡⟨ lookup∼vec
         (tabulate (λ i → (x ∷ x₁ ∷ v) !! (tabulate (F.suc ○ F.suc) !! i)))
         v
         (λ i →
           begin
           tabulate (λ j → (x ∷ x₁ ∷ v) !! (tabulate (F.suc ○ F.suc) !! j)) !! i
             ≡⟨ lookupTab i ⟩
           (x ∷ x₁ ∷ v) !! (tabulate (F.suc ○ F.suc) !! i)
             ≡⟨ cong (λ q → (x ∷ x₁ ∷ v) !! q) (lookupTab i) ⟩
           v !! i ∎) ⟩
  v ∎

-- upTo n returns [0, 1, ..., n-1] as Fins
upTo : (n : ℕ) → Vec (F.Fin n) n
upTo n = tabulate {n} id

upToTail : (n : ℕ) → (tail (tail (upTo (suc (suc n))))) ≡ (vmap F.suc (tail (upTo (suc n))))
upToTail n =
  begin
  tail (tail (upTo (suc (suc n))))
    ≡⟨ refl ⟩
  tabulate (F.suc ○ F.suc)
    ≡⟨ sym (mapTab F.suc F.suc) ⟩    
  vmap F.suc (tabulate F.suc) ∎

sidfn : {A : Set} {n : ℕ} (v : Vec A n) (i : F.Fin n) →
        ((upTo n) ∘̬ v) !! i ≡ v !! i
sidfn {n = n} v i =
  begin
  ((upTo n) ∘̬ v) !! i
    ≡⟨ lookupTab {f = λ x → v !! ((upTo n) !! x)} i ⟩
  v !! ((upTo n) !! i)
    ≡⟨ cong (_!!_ v) (lookupTab {f = id} i) ⟩
  v !! i ∎

∘̬simpleid : {A : Set} {n : ℕ} (v : Vec A n) → (upTo n) ∘̬ v ≡ v
∘̬simpleid {n = n} v = lookup∼vec (upTo n ∘̬ v) v (sidfn v)
       
lookupMap : {A B : Set} → {n : ℕ} → {f : A → B} → 
            (i : F.Fin n) → (v : Vec A n) → 
            lookup i (vmap f v) ≡ f (lookup i v)
lookupMap F.zero    (x ∷ _)      = refl
lookupMap (F.suc i) (_ ∷ v) = lookupMap i v

lookup∘tabulate : ∀ {a n} → {A : Set a} → 
                  (i : F.Fin n) → (f : F.Fin n → A) → 
                  lookup i (tabulate f) ≡ f i
lookup∘tabulate F.zero    f = refl
lookup∘tabulate (F.suc i) f = lookup∘tabulate i (f ○ F.suc)

vmap∘vmap : {n : ℕ} {A B C : Set} (f : B → C) (g : A → B) (v : Vec A n) → 
    vmap f (vmap g v) ≡ vmap (f ○ g) v
vmap∘vmap {zero} f g [] = refl
vmap∘vmap {suc n} f g (x ∷ v) = cong (λ y → f (g x) ∷ y) (vmap∘vmap f g v)

vmap∘id : {n : ℕ} {A : Set} {v : Vec A n} {f : A → A } → (∀ {x} → f x ≡ x) → vmap f v ≡ v
vmap∘id {zero} {v = []} eq = refl
vmap∘id {suc n} {v = (x ∷ v)} {f} eq = cong₂ _∷_  eq (vmap∘id {v = v} eq)
