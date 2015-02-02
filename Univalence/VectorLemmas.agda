{-# OPTIONS --without-K #-}

module VectorLemmas where

open import Level using (Level)

open import Data.Vec
  using (Vec; tabulate; []; _∷_; lookup)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import  Data.Vec.Properties
  using (lookup-++-≥; lookup∘tabulate)
open import Function using (id;_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; proof-irrelevance; module ≡-Reasoning)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Fin using (Fin; zero; suc; inject+; raise; reduce≥)

open import SubstLemmas

------------------------------------------------------------------------------
-- Lemmas about map and tabulate

-- this is actually in Data.Vec.Properties, but over an arbitrary
-- Setoid.  Specialize

map-id : ∀ {a n} {A : Set a} (xs : Vec A n) → mapV id xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = cong (_∷_ x) (map-id xs)

map-++-commute : ∀ {a b m n} {A : Set a} {B : Set b}
                 (f : B → A) (xs : Vec B m) {ys : Vec B n} →
                 mapV f (xs ++V ys) ≡ mapV f xs ++V mapV f ys
map-++-commute f []       = refl
map-++-commute f (x ∷ xs) = cong (λ z → f x ∷ z) (map-++-commute f  xs)

-- this is too, but is done "point free", this version is more convenient

map-∘ : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c}
        (f : B → C) (g : A → B) → (xs : Vec A n) →
        mapV (f ∘ g) xs ≡ (mapV f ∘ mapV g) xs
map-∘ f g [] = refl
map-∘ f g (x ∷ xs) = cong (_∷_ (f (g x))) (map-∘ f g xs)

-- this looks trivial, why can't I find it?

lookup-map : ∀ {a b} {n : ℕ} {A : Set a} {B : Set b} → 
  (i : Fin n) → (f : A → B) → 
  (v : Vec A n) → lookup i (mapV f v) ≡ f (lookup i v)
lookup-map {n = 0} () _ _
lookup-map {n = suc n} zero f (x ∷ v) = refl
lookup-map {n = suc n} (suc i) f (x ∷ v) = lookup-map i f v

-- These are 'generalized' lookup into left/right parts of a Vector which 
-- does not depend on the values in the Vector at all.

look-left : ∀ {m n} {a b c : Level} {A : Set a} {B : Set b} {C : Set c} →
  (i : Fin m) → (f : A → C) → (g : B → C) → (vm : Vec A m) → (vn : Vec B n) → 
  lookup (inject+ n i) (mapV f vm ++V mapV g vn) ≡ f (lookup i vm)
look-left {0} () _ _ _ _
look-left {suc _} zero f g (x ∷ vm) vn = refl
look-left {suc _} (suc i) f g (x ∷ vm) vn = look-left i f g vm vn

look-right : ∀ {m n} {a b c : Level} {A : Set a} {B : Set b} {C : Set c} →
  (i : Fin n) → (f : A → C) → (g : B → C) → (vm : Vec A m) → (vn : Vec B n) → 
  lookup (raise m i) (mapV f vm ++V mapV g vn) ≡ g (lookup i vn)
look-right {0} i f g vn vm = lookup-map i g vm
look-right {suc m} {0} () _ _ _ _
look-right {suc m} {suc n} i f g (x ∷ vn) vm = look-right i f g vn vm

-- similar to lookup-++-inject+ from library

lookup-++-raise : ∀ {m n} {a : Level} {A : Set a} →
  (vm : Vec A m) (vn : Vec A n) (i : Fin n) → 
  lookup (raise m i) (vm ++V vn) ≡ lookup i vn
lookup-++-raise {0} vn vm i = 
  begin (lookup i (vn ++V vm)
           ≡⟨ lookup-++-≥ vn vm i z≤n ⟩ 
         lookup (reduce≥ i z≤n) vm
            ≡⟨ refl ⟩ 
         lookup i vm ∎)
  where open ≡-Reasoning -- 
lookup-++-raise {suc m} {0} _ _ () 
lookup-++-raise {suc m} {suc n} (x ∷ vn) vm i = lookup-++-raise vn vm i

-- concat (map (map f) xs) = map f (concat xs)
concat-map : ∀ {a b m n} {A : Set a} {B : Set b} → 
  (xs : Vec (Vec A n) m) → (f : A → B) → 
  concatV (mapV (mapV f) xs) ≡ mapV f (concatV xs)
concat-map [] f = refl
concat-map (xs ∷ xss) f = 
  begin (concatV (mapV (mapV f) (xs ∷ xss))
           ≡⟨ refl ⟩
         concatV (mapV f xs ∷ mapV (mapV f) xss)
           ≡⟨  refl ⟩
         mapV f xs ++V concatV (mapV (mapV f) xss)
           ≡⟨ cong (_++V_ (mapV f xs)) (concat-map xss f) ⟩
         mapV f xs ++V mapV f (concatV xss)
           ≡⟨ sym (map-++-commute f xs) ⟩
         mapV f (xs ++V concatV xss)
           ≡⟨ refl ⟩
         mapV f (concatV (xs ∷ xss)) ∎)
  where open ≡-Reasoning

splitV+ : ∀ {m n} {a : Level} {A : Set a} {f : Fin (m + n) → A} → Vec A (m + n)
splitV+ {m} {n} {f = f} = tabulate {m} (f ∘ inject+ n) ++V tabulate {n} (f ∘ raise m)

splitVOp+ : ∀ {m} {n} {a : Level} {A : Set a} {f : Fin (n + m) → A} → Vec A (m + n)
splitVOp+ {m} {n} {f = f} = tabulate {m} (f ∘ raise n) ++V tabulate {n} (f ∘ inject+ m)

-- f can be implicit since this is mostly used in equational reasoning, where it can be inferred!
tabulate-split : ∀ {m n} {a : Level} {A : Set a} → {f : Fin (m + n) → A} → 
  tabulate {m + n} f ≡ splitV+ {m} {n} {f = f}
tabulate-split {0} = refl
tabulate-split {suc m} {f = f} = cong (_∷_ (f zero)) (tabulate-split {m} {f = f ∘ suc})

lookup-subst : ∀ {m m' n} 
  (i : Fin n) (xs : Vec (Fin m) n) (eq : m ≡ m') → 
  lookup i (subst (λ s → Vec (Fin s) n) eq xs) ≡ 
  subst Fin eq (lookup i xs)
lookup-subst i xs refl = refl 

lookup-subst-index : ∀ {m n n'} (j : Fin n) (xs : Vec (Fin m) n') (eq : n ≡ n') →
  lookup (subst Fin eq j) xs ≡ lookup j (subst (Vec (Fin m)) (sym eq) xs)
lookup-subst-index j xs refl = refl

-- lookup is associative on Fin vectors
lookupassoc : ∀ {n} → (π₁ π₂ π₃ : Vec (Fin n) n) (i : Fin n) → 
  lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃)) ≡
  lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃
lookupassoc π₁ π₂ π₃ i = 
  begin (lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃))
           ≡⟨ lookup∘tabulate (λ j → lookup (lookup j π₂) π₃) (lookup i π₁) ⟩ 
         lookup (lookup (lookup i π₁) π₂) π₃
           ≡⟨ cong 
                (λ x → lookup x π₃) 
                (sym (lookup∘tabulate (λ j → lookup (lookup j π₁) π₂) i)) ⟩ 
         lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃ ∎)
  where open ≡-Reasoning

-- This should generalize a lot, but that can be done later
subst-lookup-tabulate-raise : ∀ {m n : ℕ} → (z : Fin n) → 
  subst Fin (+-comm n m) (lookup z (tabulate (λ i → subst Fin (+-comm m n) (raise m i)))) ≡
  raise m z
subst-lookup-tabulate-raise {m} {n} z = 
 begin (subst Fin (+-comm n m) (lookup z (tabulate (λ i → subst Fin (+-comm m n) (raise m i))))
      ≡⟨ cong (subst Fin (+-comm n m))
             (lookup∘tabulate (λ i → subst Fin (+-comm m n) (raise m i)) z) ⟩
    subst Fin (+-comm n m) (subst Fin (+-comm m n) (raise m z))
      ≡⟨ subst-subst (+-comm n m) (+-comm m n) 
                 (proof-irrelevance (sym (+-comm n m)) (+-comm m n)) (raise m z) ⟩
    raise m z
     ∎)
  where open ≡-Reasoning

subst-lookup-tabulate-inject+ : ∀ {m n : ℕ} → (z : Fin m) → 
  subst Fin (+-comm n m) (lookup z (tabulate (λ i → subst Fin (+-comm m n) (inject+ n i)))) ≡
  inject+ n z
subst-lookup-tabulate-inject+ {m} {n} z = 
 begin (subst Fin (+-comm n m) (lookup z (tabulate (λ i → subst Fin (+-comm m n) (inject+ n i))))
      ≡⟨ cong (subst Fin (+-comm n m))
             (lookup∘tabulate (λ i → subst Fin (+-comm m n) (inject+ n i)) z) ⟩
    subst Fin (+-comm n m) (subst Fin (+-comm m n) (inject+ n z))
      ≡⟨ subst-subst (+-comm n m) (+-comm m n) 
                 (proof-irrelevance (sym (+-comm n m)) (+-comm m n)) (inject+ n z) ⟩
    inject+ n z
     ∎)
  where open ≡-Reasoning

-- a kind of inverse for splitAt
unSplit : {m n : ℕ} {A : Set} → (f : Fin (m + n) → A) → 
  tabulate {m} (f ∘ (inject+ n)) ++V tabulate {n} (f ∘ (raise m)) ≡ tabulate f
unSplit {0} {n} f = refl
unSplit {suc m} f = cong (λ x → (f zero) ∷ x) (unSplit {m} (f ∘ suc))
