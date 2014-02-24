module VecHelpers where

open import Data.Nat
import Data.Fin as F
--
-- open import Data.Empty
-- open import Data.Unit
-- open import Data.Unit.Core
-- open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
-- open import Data.Sum renaming (map to _⊎→_)
-- open import Data.Product renaming (map to _×→_)
open import Data.Vec
open import Function renaming (_∘_ to _○_) 

open import SimpleHoTT using (_≡_ ; refl ; pathInd ; ! ; _∘_ ; ap ; _≡⟨_⟩_ ; _∎ ; hetType)
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

∘̬≡∘̬′ : {m n : ℕ} {A : Set} (v₁ : Vec (F.Fin n) m) (v₂ : Vec A n) → (v₁ ∘̬ v₂) ≡ (v₁ ∘̬′ v₂)
∘̬≡∘̬′ [] v₂ = refl _
∘̬≡∘̬′ (x ∷ v₁) v₂ = ap (_∷_ (v₂ !! x)) (∘̬≡∘̬′ v₁ v₂)

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

ntails₀ : {A : Set} → {k : ℕ} → (v : Vec A (ntimes k suc zero)) → [] ≡ ntails {k = k} v
ntails₀ {k = zero} [] = refl _
ntails₀ {k = suc k} (x ∷ v) = ntails₀ {k = k} v

-- Important lemma about lookup; for some reason it doesn't seem to be in the
-- library even though it's in the main agda tutorial, iirc
map!! : {A B : Set} → {n : ℕ} → (f : A → B) → (v : Vec A n) → (i : F.Fin n) → 
        (vmap f v) !! i ≡ f (v !! i)
map!! {n = zero}  f  [] ()
map!! {n = suc n} f (x ∷ xs) F.zero    = refl (f x)
map!! {n = suc n} f (x ∷ xs) (F.suc i) = map!! f xs i

lookupTab : {A : Set} {n : ℕ} {f : F.Fin n → A} →  (i : F.Fin n) → (tabulate f) !! i ≡ (f i)
lookupTab {f = f} F.zero   = refl (f F.zero)
lookupTab        (F.suc i) = lookupTab i

mapTab : {A B : Set} → {n : ℕ} → (f : A → B) → (g : F.Fin n → A) →
         vmap f (tabulate g) ≡ tabulate (f ○ g)
mapTab {n = zero}  f g = refl _
mapTab {n = suc n} f g = ap (_∷_ (f (g F.zero))) (mapTab {n = n} f (g ○ F.suc))

-- Lemma for proving that two vectors are equal if their tabulates agree
-- on all inputs.
tabf∼g : {n : ℕ} → {A : Set} → (f g : F.Fin n → A) → (∀ x → f x ≡ g x) →
         tabulate f ≡ tabulate g
tabf∼g {zero} f g p = refl _
tabf∼g {suc n} f g p with f F.zero | g F.zero | p F.zero
tabf∼g {suc n} f g p | x | .x | refl .x =
  ap (_∷_ x) (tabf∼g {n} (f ○ F.suc) (g ○ F.suc) (p ○ F.suc))

lookup∼vec : {n : ℕ} → {A : Set} → (v₁ v₂ : Vec A n) → (∀ i → v₁ !! i ≡ v₂ !! i) → v₁ ≡ v₂
lookup∼vec []          []           p = refl []
lookup∼vec (x ∷ v₁) (x₁ ∷ v₂) p with p F.zero
lookup∼vec (x ∷ v₁) (.x ∷ v₂) p | (refl .x) = ap (_∷_ x) (lookup∼vec v₁ v₂ (p ○ F.suc))

∘̬id : {A : Set} → {n : ℕ} → (k : ℕ) → (v : Vec A (ntimes k suc n)) →
       (tabulate {n} (ntimesD {ℕ} {F.Fin} {suc} k F.suc)) ∘̬ v ≡
       (tabulate (λ i → v !! (ntimesD {ℕ} {F.Fin} {suc} k F.suc i)))
∘̬id {n = n} k v =
       (tabulate {n} (ntimesD {ℕ} {F.Fin} {suc} k F.suc)) ∘̬ v
         ≡⟨ refl _ ⟩
       (tabulate (λ i → v !! (tabulate (ntimesD {ℕ} {F.Fin} {suc} k F.suc) !! i)))
         ≡⟨ tabf∼g
              (λ i → v !! (tabulate (ntimesD {ℕ} {F.Fin} {suc} k F.suc) !! i))
              (λ i → v !! ntimesD {ℕ} {F.Fin} {suc} k F.suc i)
              (λ i → ap (_!!_ v) (lookupTab i)) ⟩
       (tabulate (λ i → v !! (ntimesD {ℕ} {F.Fin} {suc} k F.suc i))) ∎
  
-- upTo n returns [0, 1, ..., n-1] as Fins
upTo : (n : ℕ) → Vec (F.Fin n) n
upTo n = tabulate {n} id

lookupMap : {A B : Set} → {n : ℕ} → {f : A → B} → (i : F.Fin n) → (v : Vec A n) →
            lookup i (vmap f v) ≡ f (lookup i v)
lookupMap F.zero    (x ∷ _)      = refl _
lookupMap (F.suc i) (_ ∷ v) = lookupMap i v

lookup∘tabulate : ∀ {a n} → {A : Set a} → (i : F.Fin n) → (f : F.Fin n → A) → lookup i (tabulate f) ≡ f i
lookup∘tabulate F.zero    f = refl (f F.zero)
lookup∘tabulate (F.suc i) f = lookup∘tabulate i (f ○ F.suc)

