{-# OPTIONS --without-K #-}

module Proofs where

-- Various general lemmas

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Data.Nat.Properties
  using (m≤m+n; n≤m+n; n≤1+n)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)
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
  using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤; _ℕ-_; _≺_; reduce≥; 
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties using (bounded; inject+-lemma)
open import Data.Vec.Properties 
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin; tabulate-∘; 
         tabulate-allFin; allFin-map; lookup-++-inject+; lookup-++-≥)
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
open import Function using (id; _∘_; _$_; _∋_)

open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------------
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

------------------------------------------------------------------------------
-- Lemmas about map

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

------------------------------------------------------------------------------
-- Lemmas about subst

congD! : {a b : Level} {A : Set a} {B : A → Set b}
         (f : (x : A) → B x) → {x₁ x₂ : A} → (x₂≡x₁ : x₂ ≡ x₁) → 
         subst B x₂≡x₁ (f x₂) ≡ f x₁
congD! f refl = refl

-- Courtesy of Wolfram Kahl, a dependent cong₂                                  

cong₂D! : {a b c : Level} {A : Set a} {B : A → Set b} {C : Set c} 
         (f : (x : A) → B x → C)
       → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
       → (x₂≡x₁ : x₂ ≡ x₁) → subst B x₂≡x₁ y₂ ≡ y₁ → f x₁ y₁ ≡ f x₂ y₂
cong₂D! f refl refl = refl

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

lookup-subst : ∀ {m m' n} 
  (i : Fin n) (xs : Vec (Fin m) n) (eq : m ≡ m') → 
  lookup i (subst (λ s → Vec (Fin s) n) eq xs) ≡ 
  subst Fin eq (lookup i xs)
lookup-subst i xs refl = refl 

trans-syml : {A : Set} {x y : A} → (p : x ≡ y) → trans (sym p) p ≡ refl
trans-syml refl = refl

trans-symr : {A : Set} {x y : A} → (p : x ≡ y) → trans p (sym p) ≡ refl
trans-symr refl = refl

≤-proof-irrelevance : {m n : ℕ} → (p q : m ≤ n) → p ≡ q
≤-proof-irrelevance z≤n z≤n = refl
≤-proof-irrelevance (s≤s p) (s≤s q) = cong s≤s (≤-proof-irrelevance p q)

simplify-≤ : {m n m' n' : ℕ} → (m ≤ n) → (m ≡ m') → (n ≡ n') → (m' ≤ n') 
simplify-≤ leq refl refl = leq

leq-lem-0 : (m n : ℕ) → suc n ≤ n + suc m
leq-lem-0 m n =
  begin (suc n
           ≤⟨ m≤m+n (suc n) m ⟩ 
         suc (n + m)
           ≡⟨ cong suc (+-comm n m) ⟩ 
         suc m + n
           ≡⟨ +-comm (suc m) n ⟩ 
         n + suc m ∎)
  where open ≤-Reasoning

leq-lem-1 : (m n : ℕ) → (j : Fin (suc m)) → (d : Fin (suc n)) → 
  suc (toℕ j * suc n + toℕ d) ≤ suc m * suc n
leq-lem-1 0 0 zero zero = {!!}
leq-lem-1 0 0 zero (suc d) = {!!}
leq-lem-1 0 0 (suc j) zero = {!!}
leq-lem-1 0 0 (suc j) (suc d) = {!!}
leq-lem-1 0 (suc n) zero zero = {!!}
leq-lem-1 0 (suc n) zero (suc d) = {!!}
leq-lem-1 0 (suc n) (suc j) zero = {!!}
leq-lem-1 0 (suc n) (suc j) (suc d) = {!!}
leq-lem-1 (suc m) 0 zero zero = {!!}
leq-lem-1 (suc m) 0 zero (suc d) = {!!}
leq-lem-1 (suc m) 0 (suc j) zero = {!!}
leq-lem-1 (suc m) 0 (suc j) (suc d) = {!!}
leq-lem-1 (suc m) (suc n) zero zero = {!!}
leq-lem-1 (suc m) (suc n) zero (suc d) = {!!}
leq-lem-1 (suc m) (suc n) (suc j) zero = {!!}
leq-lem-1 (suc m) (suc n) (suc j) (suc d) = {!!} 

leq-lem-2 : (m n : ℕ) → (j : Fin (suc m)) → (d : Fin (suc n)) → 
  suc (suc (toℕ j) * suc n + toℕ d) ≤ suc (suc m) * suc n
leq-lem-2 0 0 zero zero = {!!}
leq-lem-2 0 0 zero (suc d) = {!!}
leq-lem-2 0 0 (suc j) zero = {!!}
leq-lem-2 0 0 (suc j) (suc d) = {!!}
leq-lem-2 0 (suc n) zero zero = {!!}
leq-lem-2 0 (suc n) zero (suc d) = {!!}
leq-lem-2 0 (suc n) (suc j) zero = {!!}
leq-lem-2 0 (suc n) (suc j) (suc d) = {!!}
leq-lem-2 (suc m) 0 zero zero = {!!}
leq-lem-2 (suc m) 0 zero (suc d) = {!!}
leq-lem-2 (suc m) 0 (suc j) zero = {!!}
leq-lem-2 (suc m) 0 (suc j) (suc d) = {!!}
leq-lem-2 (suc m) (suc n) zero zero = {!!}
leq-lem-2 (suc m) (suc n) zero (suc d) = {!!}
leq-lem-2 (suc m) (suc n) (suc j) zero = {!!}
leq-lem-2 (suc m) (suc n) (suc j) (suc d) = {!!} 

inject-id : (m : ℕ) (j : Fin (suc m)) (leq : toℕ j ≤ m) → 
  j ≡ inject≤ (fromℕ (toℕ j)) (s≤s leq)
inject-id 0 zero z≤n = refl
inject-id 0 (suc j) ()
inject-id (suc m) zero z≤n = refl
inject-id (suc m) (suc j) (s≤s leq) = cong suc (inject-id m j leq) 

raise-lem-0 : (m n : ℕ) → (leq : suc n ≤ n + suc m) →
              raise n zero ≡ inject≤ (fromℕ n) leq
raise-lem-0 m 0 (s≤s leq) = refl
raise-lem-0 m (suc n) (s≤s leq) = cong suc (raise-lem-0 m n leq)

raise-lem-0' : (m n : ℕ) (j : Fin (suc m)) →
  (leq : suc (n + toℕ j) ≤ n + (suc m)) →
  raise n j ≡ inject≤ (fromℕ (n + toℕ j)) leq
raise-lem-0' m 0 j (s≤s leq) = inject-id m j leq
raise-lem-0' m (suc n) j (s≤s leq) = cong suc (raise-lem-0' m n j leq)

raise-lem-1 : (n : ℕ) → (d : Fin (suc n)) → 
  (leq : toℕ d ≤ n) → 
  (leq' : suc (n + suc (toℕ d)) ≤ n + suc (suc n)) → 
  raise n (inject≤ (fromℕ (toℕ (suc d))) (s≤s (s≤s leq)))
  ≡ inject≤ (fromℕ (n + toℕ (suc d))) leq'
raise-lem-1 0 zero z≤n (s≤s (s≤s z≤n)) = refl
raise-lem-1 0 (suc d) () leq'
raise-lem-1 (suc n) zero z≤n (s≤s leq') =
  begin (suc (raise n (suc zero))
           ≡⟨ cong suc (raise-lem-0' (suc (suc n)) n (suc zero) leq') ⟩
         suc (inject≤ (fromℕ (n + 1)) leq') ∎)
  where open ≡-Reasoning
raise-lem-1 (suc n) (suc d) (s≤s leq) (s≤s leq') = cong suc (
  begin (raise n (suc (suc _)))
               ≡⟨ cong (λ x → raise n (suc (suc x))) (sym (inject-id n d leq)) ⟩
            raise n (suc (suc d))
               ≡⟨ raise-lem-0' (suc (suc n)) n (suc (suc d)) leq' ⟩
            inject≤ (fromℕ (n + suc (suc (toℕ d)))) leq' ∎)
  where open ≡-Reasoning

n+0+0≡n : (n : ℕ) → n + 0 + 0 ≡ n
n+0+0≡n n =  trans (+-right-identity (n + 0)) (+-right-identity n)

raise-suc : (m n : ℕ) (j : Fin (suc m)) (d : Fin (suc n))
  (leq : suc (toℕ j * suc n + toℕ d) ≤ suc m * suc n) → 
  (leq' : suc (toℕ (suc j) * suc n + toℕ d) ≤ suc (suc m) * suc n) →
  raise (suc n) (inject≤ (fromℕ (toℕ j * suc n + toℕ d)) leq) ≡
  inject≤ (fromℕ (toℕ (suc j) * suc n + toℕ d)) leq'
raise-suc 0 0 zero zero (s≤s leq) (s≤s (s≤s leq')) = refl
raise-suc 0 0 zero (suc ()) _ _
raise-suc 0 0 (suc ()) zero _ _
raise-suc 0 0 (suc ()) (suc ()) _ _
raise-suc 0 (suc n) zero zero (s≤s z≤n) (s≤s (s≤s leq')) =
  cong (λ x → suc (suc x))
  (begin (raise n zero
           ≡⟨ raise-lem-0 (suc n + 0) n (leq-lem-0 (suc (n + 0)) n) ⟩ 
         inject≤ (fromℕ n) (leq-lem-0 (suc (n + 0)) n)
           ≡⟨ cong₂D! 
                (λ x y → inject≤ (fromℕ x) y)
                (n+0+0≡n n)
                (≤-proof-irrelevance 
                  (subst
                    (λ x → suc x ≤ n + suc (suc (n + 0)))
                    (n+0+0≡n n)
                    leq')
                  (leq-lem-0 (suc (n + 0)) n)) ⟩ 
         inject≤ (fromℕ ((n + 0) + 0)) leq' ∎))
  where open ≡-Reasoning
raise-suc 0 (suc n) zero (suc d) (s≤s (s≤s leq)) (s≤s (s≤s leq')) = 
  cong 
    (λ x → suc (suc x))
    (begin (raise n (inject≤ (fromℕ (toℕ (suc d))) (s≤s (s≤s leq))))
              ≡⟨ {!!} ⟩ 
            raise n (inject≤
                      (fromℕ (toℕ (suc d)))
                      (leq-lem-1 0 (suc n) zero (suc d)))
              ≡⟨ {!!} ⟩ 
            inject≤ (fromℕ ((n + 0) + toℕ (suc d))) leq' ∎)
  where open ≡-Reasoning
raise-suc 0 (suc n) (suc ()) zero _ _
raise-suc 0 (suc n) (suc ()) (suc d) _ _
raise-suc (suc m) 0 zero zero (s≤s leq) (s≤s (s≤s leq')) = refl
raise-suc (suc m) 0 zero (suc ()) _ _
raise-suc (suc m) 0 (suc j) zero (s≤s leq) (s≤s (s≤s leq')) = 
  cong 
    (λ x → suc (suc (inject≤ (fromℕ (toℕ j * suc 0 + 0)) x))) 
    (≤-proof-irrelevance leq leq') 
raise-suc (suc m) 0 (suc j) (suc ()) _ _
raise-suc (suc m) (suc n) zero zero (s≤s leq) (s≤s (s≤s leq')) = 
  cong
    (λ x → suc (suc x))
    (trans
      (raise-lem-0
        (suc (n + suc m * suc (suc n)))
        n
        (simplify-≤ leq' (cong suc (n+0+0≡n n)) refl)) 
      {! !} )
raise-suc (suc m) (suc n) zero (suc d) (s≤s (s≤s leq)) (s≤s (s≤s leq')) = 
  cong (λ x → suc (suc x)) {!!}
raise-suc (suc m) (suc n) (suc j) zero (s≤s leq) (s≤s (s≤s leq')) = 
  cong (λ x → suc (suc x)) {!!}
raise-suc (suc m) (suc n) (suc j) (suc d) (s≤s (s≤s leq)) (s≤s (s≤s leq')) =
  cong (λ x → suc (suc x)) {!!}

------------------------------------------------------------------------------

