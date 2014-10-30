{-# OPTIONS --without-K #-}

module Cauchy where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+)
open import Data.Nat.DivMod using (_mod_)
open import Relation.Binary using (Rel; Decidable; Setoid)
open import Relation.Binary.Core using (Transitive)

open import Data.String using (String)
  renaming (_++_ to _++S_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  z≤n; s≤s; _≟_; _≤?_; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; _ℕ-_; _≺_;
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties using (bounded; inject+-lemma)
open import Data.Vec.Properties 
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin; tabulate-∘; 
         tabulate-allFin; map-id; allFin-map)
open import Data.Product using (Σ)

open import Data.List 
  using (List; []; _∷_; _∷ʳ_; foldl; replicate; reverse; downFrom; 
         concatMap; gfilter; initLast; InitLast; _∷ʳ'_) 
  renaming (_++_ to _++L_; map to mapL; concat to concatL; zip to zipL)
open import Data.List.NonEmpty 
  using (List⁺; [_]; _∷⁺_; head; last; _⁺++_)
  renaming (toList to nonEmptyListtoList; _∷ʳ_ to _n∷ʳ_; tail to ntail)
open import Data.List.Any using (Any; here; there; any; module Membership)
open import Data.Maybe using (Maybe; nothing; just; maybe′)
open import Data.Vec 
  using (Vec; tabulate; []; _∷_; tail; lookup; zip; zipWith; splitAt;
         _[_]≔_; allFin; toList)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import Function using (id; _∘_; _$_)

open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Groupoid

------------------------------------------------------------------------------
-- Proofs and definitions about natural numbers

_<?_ : Decidable _<_
i <? j = suc i ≤? j

trans< : Transitive _<_
trans< (s≤s z≤n) (s≤s _) = s≤s z≤n
trans< (s≤s (s≤s i≤j)) (s≤s sj<k) = s≤s (trans< (s≤s i≤j) sj<k) 

i*1≡i : (i : ℕ) → (i * 1 ≡ i)
i*1≡i i = begin (i * 1
                   ≡⟨ *-comm i 1 ⟩ 
                 1 * i
                   ≡⟨ refl ⟩ 
                 i + 0
                   ≡⟨ +-right-identity i ⟩
                 i ∎)
  where open ≡-Reasoning

i≤i : (i : ℕ) → i ≤ i
i≤i 0 = z≤n
i≤i (suc i) = s≤s (i≤i i)

i≤si : (i : ℕ) → i ≤ suc i
i≤si 0       = z≤n
i≤si (suc i) = s≤s (i≤si i)

i≤j+i : ∀ {i j} → i ≤ j + i
i≤j+i {i} {0} = i≤i i
i≤j+i {i} {suc j} = 
  begin (i 
           ≤⟨ i≤j+i {i} {j} ⟩
         j + i 
           ≤⟨ i≤si (j + i) ⟩
         suc j + i ∎)
  where open ≤-Reasoning

cong+r≤ : ∀ {i j} → i ≤ j → (k : ℕ) → i + k ≤ j + k
cong+r≤ {0}     {j}     z≤n       k = i≤j+i {k} {j}
cong+r≤ {suc i} {0}     ()        k -- absurd
cong+r≤ {suc i} {suc j} (s≤s i≤j) k = s≤s (cong+r≤ {i} {j} i≤j k)

cong+l≤ : ∀ {i j} → i ≤ j → (k : ℕ) → k + i ≤ k + j
cong+l≤ {i} {j} i≤j k =
  begin (k + i
           ≡⟨ +-comm k i ⟩ 
         i + k
           ≤⟨ cong+r≤ i≤j k ⟩ 
         j + k
           ≡⟨ +-comm j k ⟩ 
         k + j ∎)
  where open ≤-Reasoning

cong*r≤ : ∀ {i j} → i ≤ j → (k : ℕ) → i * k ≤ j * k
cong*r≤ {0}     {j}     z≤n       k = z≤n
cong*r≤ {suc i} {0}     ()        k -- absurd
cong*r≤ {suc i} {suc j} (s≤s i≤j) k = cong+l≤ (cong*r≤ i≤j k) k 

sinj≤ : ∀ {i j} → suc i ≤ suc j → i ≤ j
sinj≤ {0}     {j}     _        = z≤n
sinj≤ {suc i} {0}     (s≤s ()) -- absurd
sinj≤ {suc i} {suc j} (s≤s p)  = p

i*n+k≤m*n : ∀ {m n} → (i : Fin m) → (k : Fin n) → 
            (suc (toℕ i * n + toℕ k) ≤ m * n)
i*n+k≤m*n {0} {_} () _
i*n+k≤m*n {_} {0} _ ()
i*n+k≤m*n {suc m} {suc n} i k = 
  begin (suc (toℕ i * suc n + toℕ k) 
           ≡⟨  cong suc (+-comm (toℕ i * suc n) (toℕ k))  ⟩
         suc (toℕ k + toℕ i * suc n)
           ≡⟨ refl ⟩
         suc (toℕ k) + (toℕ i * suc n)
           ≤⟨ cong+r≤ (bounded k) (toℕ i * suc n) ⟩ 
         suc n + (toℕ i * suc n)
           ≤⟨ cong+l≤ (cong*r≤ (sinj≤ (bounded i)) (suc n)) (suc n) ⟩
         suc n + (m * suc n) 
           ≡⟨ refl ⟩
         suc m * suc n ∎)
  where open ≤-Reasoning

{- -- these are all true, but not actually used!  And they cause termination issues in
    -- my older Agda, so I'll just comment them out for now.  JC

i≰j→j≤i : (i j : ℕ) → (i ≰ j) → (j ≤ i) 
i≰j→j≤i i 0 p = z≤n 
i≰j→j≤i 0 (suc j) p with p z≤n
i≰j→j≤i 0 (suc j) p | ()
i≰j→j≤i (suc i) (suc j) p with i ≤? j
i≰j→j≤i (suc i) (suc j) p | yes p' with p (s≤s p')
i≰j→j≤i (suc i) (suc j) p | yes p' | ()
i≰j→j≤i (suc i) (suc j) p | no p' = s≤s (i≰j→j≤i i j p')

i≠j∧i≤j→i<j : (i j : ℕ) → (¬ i ≡ j) → (i ≤ j) → (i < j)
i≠j∧i≤j→i<j 0 0 p≠ p≤ with p≠ refl
i≠j∧i≤j→i<j 0 0 p≠ p≤ | ()
i≠j∧i≤j→i<j 0 (suc j) p≠ p≤ = s≤s z≤n
i≠j∧i≤j→i<j (suc i) 0 p≠ ()
i≠j∧i≤j→i<j (suc i) (suc j) p≠ (s≤s p≤) with i ≟ j
i≠j∧i≤j→i<j (suc i) (suc j) p≠ (s≤s p≤) | yes p' with p≠ (cong suc p')
i≠j∧i≤j→i<j (suc i) (suc j) p≠ (s≤s p≤) | yes p' | ()
i≠j∧i≤j→i<j (suc i) (suc j) p≠ (s≤s p≤) | no p' = s≤s (i≠j∧i≤j→i<j i j p' p≤)
     
i<j→i≠j : {i j : ℕ} → (i < j) → (¬ i ≡ j)
i<j→i≠j {0} (s≤s p) ()
i<j→i≠j {suc i} (s≤s p) refl = i<j→i≠j {i} p refl

i<j→j≮i : {i j : ℕ} → (i < j) → (j ≮ i) 
i<j→j≮i {0} (s≤s p) ()
i<j→j≮i {suc i} (s≤s p) (s≤s q) = i<j→j≮i {i} p q

i≰j∧j≠i→j<i : (i j : ℕ) → (i ≰ j) → (¬ j ≡ i) → j < i
i≰j∧j≠i→j<i i j i≰j ¬j≡i = i≠j∧i≤j→i<j j i ¬j≡i (i≰j→j≤i i j i≰j)

i≠j→j≠i : (i j : ℕ) → (¬ i ≡ j) → (¬ j ≡ i)
i≠j→j≠i i j i≠j j≡i = i≠j (sym j≡i)

si≠sj→i≠j : (i j : ℕ) → (¬ Data.Nat.suc i ≡ Data.Nat.suc j) → (¬ i ≡ j)
si≠sj→i≠j i j ¬si≡sj i≡j = ¬si≡sj (cong suc i≡j)

si≮sj→i≮j : (i j : ℕ) → (¬ Data.Nat.suc i < Data.Nat.suc j) → (¬ i < j)
si≮sj→i≮j i j si≮sj i<j = si≮sj (s≤s i<j)

i≮j∧i≠j→i≰j : (i j : ℕ) → (i ≮ j) → (¬ i ≡ j) → (i ≰ j)
i≮j∧i≠j→i≰j 0 0 i≮j ¬i≡j i≤j = ¬i≡j refl
i≮j∧i≠j→i≰j 0 (suc j) i≮j ¬i≡j i≤j = i≮j (s≤s z≤n)
i≮j∧i≠j→i≰j (suc i) 0 i≮j ¬i≡j () 
i≮j∧i≠j→i≰j (suc i) (suc j) si≮sj ¬si≡sj (s≤s i≤j) = 
  i≮j∧i≠j→i≰j i j (si≮sj→i≮j i j si≮sj) (si≠sj→i≠j i j ¬si≡sj) i≤j
-}

------------------------------------------------------------------------------
-- Semantic representations of permutations

-- One possibility of course is to represent them as functions but
-- this is a poor representation and eventually requires function
-- extensionality. 

-- Representation III
-- This is the 2 line Cauchy representation. The first line is in
-- canonical order and implicit in the indices of the vector

Cauchy : ℕ → Set
Cauchy n = Vec (Fin n) n

-- What JC thinks will actually work
-- we need injectivity.  surjectivity ought to be provable.
Permutation : ℕ → Set
Permutation n = Σ (Cauchy n) (λ v → ∀ {i j} → lookup i v ≡ lookup j v → i ≡ j)

showCauchy : ∀ {n} → Cauchy n → Vec String n
showCauchy {n} = 
  zipWith (λ i j → show (toℕ i) ++S " → " ++S show (toℕ j)) (allFin n)

-- Ex:

cauchyEx1 cauchyEx2 : Cauchy 6
-- cauchyEx1 (0 1 2 3 4 5)
--           (2 0 4 3 1 5)
cauchyEx1 = 
  (inject+ 3 (fromℕ 2)) ∷
  (inject+ 5 (fromℕ 0)) ∷
  (inject+ 1 (fromℕ 4)) ∷
  (inject+ 2 (fromℕ 3)) ∷
  (inject+ 4 (fromℕ 1)) ∷
  (inject+ 0 (fromℕ 5)) ∷ []
-- cauchyEx2 (0 1 2 3 4 5)
--           (3 2 1 0 5 4)
cauchyEx2 = 
  (inject+ 2 (fromℕ 3)) ∷
  (inject+ 3 (fromℕ 2)) ∷
  (inject+ 4 (fromℕ 1)) ∷
  (inject+ 5 (fromℕ 0)) ∷
  (inject+ 0 (fromℕ 5)) ∷
  (inject+ 1 (fromℕ 4)) ∷ []

------------------------------------------------------------------------------
-- Lemmas

-- Important: Extensionality for finite functions

finext : {n : ℕ} {A : Set} → (f g : Fin n → A) → ((i : Fin n) → f i ≡ g i) → 
         (tabulate f ≡ tabulate g)
finext {0} f g fi≡gi = refl
finext {suc n} f g fi≡gi = 
  begin (tabulate {suc n} f 
           ≡⟨ refl ⟩
         f zero ∷ tabulate {n} (f ∘ suc)
           ≡⟨ cong (λ x → x ∷ tabulate {n} (f ∘ suc)) (fi≡gi zero) ⟩ 
         g zero ∷ tabulate {n} (f ∘ suc)
           ≡⟨ cong 
                (λ x → g zero ∷ x) 
                (finext (f ∘ suc) (g ∘ suc) (fi≡gi ∘ suc)) ⟩ 
         g zero ∷ tabulate {n} (g ∘ suc)
           ≡⟨ refl ⟩
         tabulate g ∎)
  where open ≡-Reasoning

-- Lemmas about map

-- this is actually in Data.Vec.Properties, but over an arbitrary
-- Setoid.  Specialize

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

-- Lemmas about allFin

allFin+ : (m n : ℕ) → allFin (m + n) ≡ 
          mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
allFin+ 0 n = 
  begin (allFin n
           ≡⟨ refl ⟩ 
         tabulate {n} (id ∘ id)
           ≡⟨ tabulate-∘ id id ⟩ 
         mapV id (allFin n) ∎)
  where open ≡-Reasoning
allFin+ (suc m) n = 
  begin (allFin (suc (m + n))
           ≡⟨ allFin-map (m + n) ⟩ 
         zero ∷ mapV suc (allFin (m + n))
           ≡⟨ cong (λ x → zero ∷ mapV suc x) (allFin+ m n) ⟩ 
         zero ∷ 
           mapV suc (mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n))
           ≡⟨ cong 
                (_∷_ zero) 
                (map-++-commute suc (mapV (inject+ n) (allFin m))) ⟩
         zero ∷ (mapV suc (mapV (λ i → (inject+ {m} n i)) (allFin m))) ++V
                  mapV suc (mapV (λ i → (raise {n} m i)) (allFin n))
           ≡⟨ cong 
                (_∷_ zero) 
                (cong₂ _++V_ 
                  (sym (map-∘ suc (inject+ n) (allFin m))) 
                  (sym (map-∘ suc (raise m) (allFin n)))) ⟩ 
         zero ∷ (mapV (λ i → suc (inject+ {m} n i)) (allFin m) ++V 
                 mapV (λ i → suc (raise {n} m i)) (allFin n))
           ≡⟨ refl ⟩ 
         (zero ∷ mapV (λ i → inject+ n (suc i)) (allFin m)) ++V 
         mapV (raise (suc m)) (allFin n)
           ≡⟨ cong 
                (λ x → (zero ∷ x) ++V mapV (raise (suc m)) (allFin n))
                (map-∘ (inject+ n) suc (allFin m)) ⟩ 
         (zero ∷ mapV (inject+ n) (mapV suc (allFin m))) ++V 
         mapV (raise (suc m)) (allFin n)
           ≡⟨ refl ⟩ 
         mapV (inject+ n) (zero ∷ mapV suc (allFin m)) ++V
         mapV (raise (suc m)) (allFin n) 
           ≡⟨ cong 
                 (λ x → mapV (inject+ n) (zero ∷ x) ++V 
                        mapV (raise (suc m)) (allFin n))
                 (sym (tabulate-allFin {m} suc)) ⟩ 
         mapV (inject+ n) (zero ∷ tabulate {m} suc) ++V
         mapV (raise (suc m)) (allFin n) 
           ≡⟨ refl ⟩ 
         mapV (inject+ n) (allFin (suc m)) ++V 
         mapV (raise (suc m)) (allFin n) ∎)
  where open ≡-Reasoning

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
look-right {Data.Nat.zero} i f g vn vm = lookup-map i g vm
look-right {suc m} {Data.Nat.zero} () _ _ _ _
look-right {suc m} {suc n} i f g (x ∷ vn) vm = look-right i f g vn vm

-- a direct proof is hard, but this is really a statement about vectors

lookup-left : ∀ {m n} → (i : Fin m) → (pm : Cauchy m) → (pn : Cauchy n) → 
  lookup (inject+ n i) (mapV (inject+ n) pm ++V mapV (raise m) pn) 
  ≡ inject+ n (lookup i pm)
lookup-left {m} {n} i pm pn = look-left i (inject+ n) (raise m) pm pn

-- as is this

lookup-right : ∀ {m n} → (i : Fin n) → (pm : Cauchy m) → (pn : Cauchy n) → 
  lookup (raise m i) (mapV (inject+ n) pm ++V mapV (raise m) pn) 
  ≡ raise m (lookup i pn)
lookup-right {m} {n} i pm pn = look-right i (inject+ n) (raise m) pm pn

-- A few proof techniques for dealing with subst

congD! : {a b : Level} {A : Set a} {B : A → Set b}
         (f : (x : A) → B x) → {x₁ x₂ : A} → (x₂≡x₁ : x₂ ≡ x₁) → 
         subst B x₂≡x₁ (f x₂) ≡ f x₁
congD! f refl = refl

subst-dist : 
  {a b : Level} {A : Set a} {B : A → Set b} 
  (f : {x : A} → B x → B x → B x) → 
  {x₁ x₂ : A} → (x₂≡x₁ : x₂ ≡ x₁) → (v₁ v₂ : B x₂) → 
  subst B x₂≡x₁ (f v₁ v₂) ≡ f (subst B x₂≡x₁ v₁) (subst B x₂≡x₁ v₂)
subst-dist f refl v₁ v₂ = refl 

subst-trans : 
  {a b : Level} {A : Set a} {B : A → Set b} {x₁ x₂ x₃ : A} → 
  (x₂≡x₁ : x₂ ≡ x₁) → (x₃≡x₂ : x₃ ≡ x₂) → (v : B x₃) →  
  subst B x₂≡x₁ (subst B x₃≡x₂ v) ≡ subst B (trans x₃≡x₂ x₂≡x₁) v
subst-trans refl refl v = refl

subst₂+ : {b : Level} {B : ℕ → Set b} {x₁ x₂ x₃ x₄ : ℕ} → 
  (x₂≡x₁ : x₂ ≡ x₁) → (x₄≡x₃ : x₄ ≡ x₃) → (v₁ : B x₂) → (v₂ : B x₄) → 
  (f : {x₁ x₂ : ℕ} → B x₁ → B x₂ → B (x₁ + x₂)) → 
  subst B (cong₂ _+_ x₂≡x₁ x₄≡x₃) (f v₁ v₂) ≡ 
  f (subst B x₂≡x₁ v₁) (subst B x₄≡x₃ v₂)
subst₂+ refl refl v₁ v₂ f = refl

subst₂* : {b : Level} {B : ℕ → Set b} {x₁ x₂ x₃ x₄ : ℕ} → 
  (x₂≡x₁ : x₂ ≡ x₁) → (x₄≡x₃ : x₄ ≡ x₃) → (v₁ : B x₂) → (v₂ : B x₄) → 
  (f : {x₁ x₂ : ℕ} → B x₁ → B x₂ → B (x₁ * x₂)) → 
  subst B (cong₂ _*_ x₂≡x₁ x₄≡x₃) (f v₁ v₂) ≡ 
  f (subst B x₂≡x₁ v₁) (subst B x₄≡x₃ v₂)
subst₂* refl refl v₁ v₂ f = refl

trans-syml : {A : Set} {x y : A} → (p : x ≡ y) → trans (sym p) p ≡ refl
trans-syml refl = refl

trans-symr : {A : Set} {x y : A} → (p : x ≡ y) → trans p (sym p) ≡ refl
trans-symr refl = refl

------------------------------------------------------------------------------
-- Elementary permutations in the Cauchy representation and their properties

idcauchy : (n : ℕ) → Cauchy n
idcauchy = allFin 

idperm : (n : ℕ) → Permutation n
idperm n = (idcauchy n , λ {i} {j} p → 
  (begin i 
           ≡⟨ sym (lookup∘tabulate id i) ⟩ 
         lookup i (idcauchy n)
           ≡⟨ p ⟩ 
         lookup j (idcauchy n)
           ≡⟨ lookup∘tabulate id j ⟩ 
         j ∎))
  where open ≡-Reasoning

-- a kind of inverse for splitAt

unSplit : {m n : ℕ} {A : Set} → (f : Fin (m + n) → A) → 
  tabulate {m} (f ∘ (inject+ n)) ++V tabulate {n} (f ∘ (raise m)) ≡ tabulate f
unSplit {Data.Nat.zero} {n} f = refl
unSplit {suc m} f = cong (λ x → (f zero) ∷ x) (unSplit {m} (f ∘ suc))

-- swap the first m elements with the last n elements
-- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
-- ==> 
-- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

swap+cauchy : (m n : ℕ) → Cauchy (m + n)
swap+cauchy m n with splitAt n (allFin (n + m))
... | (zeron , (nsum , _)) = 
    (subst (λ s → Vec (Fin s) m) (+-comm n m) nsum) ++V 
    (subst (λ s → Vec (Fin s) n) (+-comm n m) zeron)

-- Sequential composition

scompcauchy : ∀ {n} → Cauchy n → Cauchy n → Cauchy n
scompcauchy {n} perm₁ perm₂ = 
  tabulate (λ i → lookup (lookup i perm₁) perm₂)

-- this was not entirely straightforward!
scompperm : ∀ {n} → Permutation n → Permutation n → Permutation n
scompperm {n} (p₁ , i₁) (p₂ , i₂) =
  (scompcauchy p₁ p₂ , λ {i} {j} p → 
    let g = λ i → lookup (lookup i p₁) p₂ in
    let q = trans (sym (lookup∘tabulate g i)) (trans p (lookup∘tabulate g j)) in
    i₁ (i₂ q))

-- sequential composition with id on the right is identity

scomprid : ∀ {n} → (perm : Cauchy n) → scompcauchy perm (idcauchy n) ≡ perm
scomprid {n} perm = 
  begin (scompcauchy perm (idcauchy n)
           ≡⟨ refl ⟩ 
         tabulate (λ i → lookup (lookup i perm) (allFin n))
           ≡⟨ finext 
                (λ i → lookup (lookup i perm) (allFin n))
                (λ i → lookup i perm)
                (λ i → lookup-allFin (lookup i perm)) ⟩ 
         tabulate (λ i → lookup i perm)
           ≡⟨ tabulate∘lookup perm ⟩ 
         perm ∎)
  where open ≡-Reasoning

-- sequential composition with id on the left is identity

scomplid : ∀ {n} → (perm : Cauchy n) → scompcauchy (idcauchy n) perm ≡ perm
scomplid {n} perm = 
  begin (scompcauchy (idcauchy n) perm 
           ≡⟨ refl ⟩ 
         tabulate (λ i → lookup (lookup i (allFin n)) perm)
           ≡⟨ finext 
                (λ i → lookup (lookup i (allFin n)) perm) 
                (λ i → lookup i perm) 
                (λ i → cong (λ x → lookup x perm) (lookup-allFin i)) ⟩ 
         tabulate (λ i → lookup i perm)
           ≡⟨ tabulate∘lookup perm ⟩ 
         perm ∎)
  where open ≡-Reasoning

-- swap+ is idempotent

-- outline of swap+idemp proof

-- allFin (m + n) ≡ mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
-- zero-m : Vec (Fin (m + n)) m ≡ mapV (inject+ n) (allFin m) 
-- m-sum  : Vec (Fin (m + n)) n ≡ mapV (raise m) (allFin n)
-- allFin (n + m) ≡ mapV (inject+ m) (allFin n) ++V mapV (raise n) (allFin m)
-- zero-n : Vec (Fin (n + m)) n ≡ mapV (inject+ m) (allFin n) 
-- n-sum  : Vec (Fin (n + m)) m ≡ mapV (raise n) (allFin m)
-- 
-- first swap re-arranges allFin (n + m) to n-sum ++V zero-n
-- second swap re-arranges allfin (m + n) to m-sum ++V zero-m
-- 
-- for i = 0, ..., m-1, we have inject+ n i : Fin (m + n)
-- lookup (lookup (inject+ n i) (n-sum ++V zero-n)) (m-sum ++V zero-m) ==> 
-- lookup (lookup i n-sum) (m-sum ++V zero-m) ==>
-- lookup (raise n i) (m-sum ++V zero-m) ==> 
-- lookup i zero-m ==>
-- inject+ n i
-- 
-- for i = m, ..., m+n-1, we have raise m i : Fin (m + n)
-- lookup (lookup (raise m i) (n-sum ++V zero-n)) (m-sum ++V zero-m) ==> 
-- lookup (lookup i zero-n) (m-sum ++V zero-m) ==> 
-- lookup (inject+ m i) (m-sum ++V zero-m) ==> 
-- lookup i m-sum ==> 
-- raise m i

tabulate-++ : ∀ {m n a} {A : Set a} → (f : Fin (m + n) → A) → 
  tabulate {m + n} f ≡ 
  tabulate {m} (f ∘ inject+ n) ++V tabulate {n} (f ∘ raise m)
tabulate-++ {m} {n} {a} f = 
  begin (tabulate {m + n} f 
           ≡⟨ tabulate-allFin f ⟩ 
         mapV f (allFin (m + n))
           ≡⟨ cong (mapV f) (allFin+ m n) ⟩ 
         mapV f (mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n))
           ≡⟨ map-++-commute f (mapV (inject+ n) (allFin m)) ⟩ 
         mapV f (mapV (inject+ n) (allFin m)) ++V 
         mapV f (mapV (raise m) (allFin n))
           ≡⟨ cong₂ _++V_ 
                (sym (map-∘ f (inject+ n) (allFin m)))
                (sym (map-∘ f (raise m) (allFin n))) ⟩ 
         mapV (f ∘ inject+ n) (allFin m) ++V 
         mapV (f ∘ raise m) (allFin n)
           ≡⟨ cong₂ _++V_
                (sym (tabulate-allFin {m} (f ∘ inject+ n)))
                (sym (tabulate-allFin {n} (f ∘ raise m))) ⟩ 
         tabulate {m} (f ∘ inject+ n) ++V 
         tabulate {n} (f ∘ raise m) ∎)
  where open ≡-Reasoning

swap+idemp : (m n : ℕ) → 
  scompcauchy 
    (swap+cauchy m n) 
    (subst Cauchy (+-comm n m) (swap+cauchy n m))
  ≡ 
  allFin (m + n)
swap+idemp m n with splitAt n (allFin (n + m)) | splitAt m (allFin (m + n)) 
... | (zero-n , (n-sum , pr₁)) | (zero-m , (m-sum , pr₂)) = 
  begin (tabulate (λ i → 
           lookup 
             (lookup i 
               (subst (λ s → Vec (Fin s) m) (+-comm n m) n-sum ++V
                subst (λ s → Vec (Fin s) n) (+-comm n m) zero-n))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum ++V
                subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m)))
         ≡⟨ tabulate-++ {m} {n} 
            (λ i → 
             lookup 
             (lookup i 
               (subst (λ s → Vec (Fin s) m) (+-comm n m) n-sum ++V
                subst (λ s → Vec (Fin s) n) (+-comm n m) zero-n))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum ++V
                subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m))) ⟩ 
         tabulate {m} (λ i → 
           lookup 
             (lookup (inject+ n i)
               (subst (λ s → Vec (Fin s) m) (+-comm n m) n-sum ++V
                subst (λ s → Vec (Fin s) n) (+-comm n m) zero-n))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum ++V
                subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m)))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (lookup (raise m i)
               (subst (λ s → Vec (Fin s) m) (+-comm n m) n-sum ++V
                subst (λ s → Vec (Fin s) n) (+-comm n m) zero-n))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum ++V
                subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m)))
           ≡⟨ {!!} ⟩ 
         tabulate {m} (λ i → 
           lookup 
             (subst Fin (+-comm n m) (lookup i n-sum))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum ++V
                subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m)))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (subst Fin (+-comm n m) (lookup i zero-n))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum ++V
                subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m)))
           ≡⟨ {!!} ⟩ 
         tabulate {m} (λ i → 
           lookup 
             (subst Fin (+-comm n m) (raise n i))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum ++V
                subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m)))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (subst Fin (+-comm n m) (inject+ m i))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum ++V
                subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m)))
           ≡⟨ {!!} ⟩ 
         scompcauchy 
           (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) (n-sum ++V zero-n))
           (subst Cauchy (+-comm n m) 
             (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) (m-sum ++V zero-m)))
-- subst (λ s → Vec (Fin s) n) (+-comm m n) m-sum    : Vec (Fin (n + m)) n
-- subst (λ s → Vec (Fin s) m) (+-comm m n) zero-m)) : Vec (Fin (n + m)) m
-- _++V_ : Vec (Fin (n + m)) (n + m) which is Cauchy (n + m)
-- then outer subst maps to : Cauchy (m + n)
-- n-sum ++V zero-n : Vec (Fin (n + m)) (m + n)
-- subst : Vec (Fin (m + n)) (m + n)
-- m-sum ++V zero-m : Vec (Fin (m + n)) (n + m)
-- inner subst : Vec (Fin (n + m)) (n + m)
-- outer subst : Vec (Fin (m + n)) (m + n)
           ≡⟨ {!!} ⟩ 
         allFin (m + n) ∎)
  where open ≡-Reasoning

{--

Ex: size t₁ = 3, size t₂ = 2

allFin (3 + 2) = allFin (2 + 3) = [ 0, 1, 2, 3, 4 ]

scompcauchy 
  (swap+cauchy 3 2)
  (subst Cauchy (+-comm 2 3) (swap+cauchy 2 3))

≡

scompcauchy
  ([ 2, 3, 4 ] ++V [ 0, 1 ])
  ([ 3, 4 ] ++V [ 0, 1, 2 ])

≡

tabulate (λ i → 
  lookup 
    (lookup i ([ 2, 3, 4 ] ++V [ 0, 1 ])) 
    ([ 3, 4 ] ++V [ 0, 1, 2 ]))

0 ==> 2 ==> 0
1 ==> 3 ==> 1 
2 ==> 4 ==> 2
--
3 ==> 0 ==> 3
4 ==> 1 ==> 4

--}

-- sequential composition is associative

lookupassoc : ∀ {n} → (π₁ π₂ π₃ : Cauchy n) (i : Fin n) → 
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

scompassoc : ∀ {n} → (π₁ π₂ π₃ : Cauchy n) → 
  scompcauchy π₁ (scompcauchy π₂ π₃) ≡ scompcauchy (scompcauchy π₁ π₂) π₃
scompassoc π₁ π₂ π₃ = 
  begin (scompcauchy π₁ (scompcauchy π₂ π₃)
           ≡⟨ refl ⟩
         tabulate (λ i → 
           lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃)))
           ≡⟨ finext
              (λ i → 
                lookup (lookup i π₁) (tabulate (λ j → lookup (lookup j π₂) π₃)))
              (λ i → 
                lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃)
              (λ i → lookupassoc π₁ π₂ π₃ i) ⟩
         tabulate (λ i → 
           lookup (lookup i (tabulate (λ j → lookup (lookup j π₁) π₂))) π₃)
           ≡⟨ refl ⟩
         scompcauchy (scompcauchy π₁ π₂) π₃ ∎)
  where open ≡-Reasoning

-- Parallel additive composition 
-- append both permutations but adjust the indices in the second
-- permutation by the size of the first type so that it acts on the
-- second part of the vector

pcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m + n)
pcompcauchy {m} {n} α β = mapV (inject+ n) α ++V mapV (raise m) β

-- Behaviour of parallel additive composition wrt sequential

pcomp-dist : ∀ {m n} → (pm qm : Cauchy m) → (pn qn : Cauchy n) → 
    scompcauchy (pcompcauchy pm pn) (pcompcauchy qm qn) ≡
    pcompcauchy (scompcauchy pm qm) (scompcauchy pn qn)
pcomp-dist {m} {n} pm qm pn qn =
  begin (scompcauchy (pcompcauchy pm pn) (pcompcauchy qm qn)
           ≡⟨ refl ⟩
         tabulate (λ i → 
           lookup 
             (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
             (mapV (inject+ n) qm ++V mapV (raise m) qn))
            ≡⟨ tabulate-allFin (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn)) ⟩
         mapV (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (allFin (m + n))
            ≡⟨ cong 
                 (λ x → 
                   mapV (λ i → 
                     lookup 
                       (lookup i 
                         (mapV (inject+ n) pm ++V mapV (raise m) pn))
                       (mapV (inject+ n) qm ++V mapV (raise m) qn)) 
                     x) 
                 (allFin+ m n) ⟩
         mapV (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n))
            ≡⟨ map-++-commute 
                 (λ i → 
                   lookup 
                     (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn)) 
                 (mapV (inject+ n) (allFin m)) ⟩
         mapV (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (mapV (inject+ n) (allFin m)) 
         ++V 
         mapV (λ i → 
                lookup 
                  (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (mapV (raise m) (allFin n))
            ≡⟨ cong₂ _++V_ 
                 (sym (map-∘ 
                   (λ i → lookup 
                     (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn))
                   (inject+ n) 
                   (allFin m)))
                 (sym (map-∘ 
                   (λ i → lookup 
                     (lookup i (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn)) 
                   (raise m) 
                   (allFin n))) ⟩ 
         mapV (λ i → 
                lookup 
                  (lookup (inject+ n i) 
                    (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (allFin  m)
         ++V 
         mapV (λ i → 
                lookup 
                  (lookup (raise m i) 
                    (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
              (allFin n)
            ≡⟨ cong₂ _++V_ 
                 (sym (tabulate-allFin {m} (λ i → 
                   lookup 
                     (lookup (inject+ n i) 
                       (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn))))
                 (sym (tabulate-allFin {n} (λ i → 
                   lookup 
                     (lookup (raise m i) 
                       (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn))))  ⟩ 
         tabulate {m} (λ i → 
                lookup 
                  (lookup (inject+ n i) 
                    (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
         ++V 
         tabulate {n} (λ i → 
                lookup 
                  (lookup (raise m i) 
                    (mapV (inject+ n) pm ++V mapV (raise m) pn))
                  (mapV (inject+ n) qm ++V mapV (raise m) qn))
            ≡⟨ cong₂ _++V_
                 (finext 
                   (λ i → 
                    lookup 
                      (lookup (inject+ n i) 
                        (mapV (inject+ n) pm ++V mapV (raise m) pn))
                     (mapV (inject+ n) qm ++V mapV (raise m) qn))
                   (λ i → 
                    lookup 
                      (inject+ n (lookup i pm))
                      (mapV (inject+ n) qm ++V mapV (raise m) qn))
                   (λ i → cong 
                            (λ x → 
                              lookup x 
                                (mapV (inject+ n) qm ++V mapV (raise m) qn))
                            (lookup-left i pm pn)))
                 (finext 
                   (λ i → 
                     lookup 
                       (lookup (raise m i) 
                         (mapV (inject+ n) pm ++V mapV (raise m) pn))
                       (mapV (inject+ n) qm ++V mapV (raise m) qn))
                   (λ i → 
                     lookup 
                       (raise m (lookup i pn))
                       (mapV (inject+ n) qm ++V mapV (raise m) qn))
                   (λ i → cong
                            (λ x → 
                              lookup x 
                                (mapV (inject+ n) qm ++V mapV (raise m) qn))
                            (lookup-right i pm pn))) ⟩
         tabulate (λ i → lookup (inject+ n (lookup i pm))
                           (mapV (inject+ n) qm ++V mapV (raise m) qn)) ++V
         tabulate (λ i → lookup (raise m (lookup i pn))
                           (mapV (inject+ n) qm ++V mapV (raise m) qn))
           ≡⟨ cong₂ _++V_
                 (finext 
                   (λ i → lookup (inject+ n (lookup i pm))
                            (mapV (inject+ n) qm ++V mapV (raise m) qn))
                   (λ i → (inject+ n) (lookup (lookup i pm) qm))
                   (λ i → lookup-left (lookup i pm) qm qn))
                 (finext 
                   (λ i → lookup (raise m (lookup i pn))
                            (mapV (inject+ n) qm ++V mapV (raise m) qn))
                   (λ i → (raise m) (lookup (lookup i pn) qn))
                   (λ i → lookup-right (lookup i pn) qm qn))
                   ⟩ 
         tabulate (λ i → (inject+ n) (lookup (lookup i pm) qm)) ++V
         tabulate (λ i → (raise m) (lookup (lookup i pn) qn))
            ≡⟨ cong₂ _++V_ 
               (tabulate-∘ (inject+ n) (λ i → lookup (lookup i pm) qm)) 
               (tabulate-∘ (raise m) (λ i → lookup (lookup i pn) qn)) ⟩ 
         mapV (inject+ n) (tabulate (λ i → lookup (lookup i pm) qm)) ++V 
         mapV (raise m) (tabulate (λ i → lookup (lookup i pn) qn))
            ≡⟨ refl ⟩
         pcompcauchy (scompcauchy pm qm) (scompcauchy pn qn) ∎)
  where open ≡-Reasoning

pcomp-id : ∀ {m n} → pcompcauchy (idcauchy m) (idcauchy n) ≡ idcauchy (m + n)
pcomp-id {m} {n} = 
  begin (mapV (inject+ n) (idcauchy m) ++V (mapV (raise m) (idcauchy n))
    ≡⟨ refl ⟩
  mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
    ≡⟨ cong₂ _++V_ 
       (sym (tabulate-allFin {m} (inject+ n))) 
       (sym (tabulate-allFin (raise m))) ⟩
  tabulate {m} (inject+ n) ++V tabulate {n} (raise m)
    ≡⟨ unSplit {m} {n} id ⟩
  idcauchy (m + n) ∎)
  where open ≡-Reasoning

-- Tensor multiplicative composition
-- Transpositions in α correspond to swapping entire rows
-- Transpositions in β correspond to swapping entire columns

tcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m * n)
tcompcauchy {m} {n} α β = 
  concatV 
    (mapV 
      (λ b → 
         mapV (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)) β)
      α)

-- swap⋆ 
-- 
-- This is essentially the classical problem of in-place matrix transpose:
-- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
-- Given m and n, the desired permutation in Cauchy representation is:
-- P(i) = m*n-1 if i=m*n-1
--      = m*i mod m*n-1 otherwise

transposeIndex : (m n : ℕ) → 
                 (b : Fin (suc (suc m))) → (d : Fin (suc (suc n))) → 
                 Fin (suc (suc m) * suc (suc n))
transposeIndex m n b d with toℕ b * suc (suc n) + toℕ d
transposeIndex m n b d | i with suc i ≟ suc (suc m) * suc (suc n)
transposeIndex m n b d | i | yes _ = 
  fromℕ (suc (n + suc (suc (n + m * suc (suc n))))) 
transposeIndex m n b d | i | no _ = 
  inject≤ 
    ((i * (suc (suc m))) mod (suc (n + suc (suc (n + m * suc (suc n))))))
    (i≤si (suc (n + suc (suc (n + m * suc (suc n))))))

swap⋆cauchy : (m n : ℕ) → Cauchy (m * n)
swap⋆cauchy 0 n = []
swap⋆cauchy 1 n = subst Cauchy (sym (+-right-identity n)) (idcauchy n)
swap⋆cauchy (suc (suc m)) 0 = 
  subst Cauchy (sym (*-right-zero (suc (suc m)))) []
swap⋆cauchy (suc (suc m)) 1 = 
  subst Cauchy (sym (i*1≡i (suc (suc m)))) (idcauchy (suc (suc m)))
swap⋆cauchy (suc (suc m)) (suc (suc n)) = 
  concatV 
    (mapV 
      (λ b → mapV (λ d → transposeIndex m n b d) (allFin (suc (suc n))))
      (allFin (suc (suc m))))

------------------------------------------------------------------------------
