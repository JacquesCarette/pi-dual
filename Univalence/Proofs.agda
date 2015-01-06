{-# OPTIONS --without-K #-}

module Proofs where

-- Various general lemmas

open import Level using (Level)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Data.Nat.Properties
  using (cancel-+-left; n∸n≡0; +-∸-assoc; m+n∸n≡m; 1+n≰n; m≤m+n;
         n≤m+n; n≤1+n; cancel-*-right-≤; ≰⇒>; ¬i+1+j≤i; cancel-+-left-≤)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+; +-*-suc)
open import Relation.Binary using (Rel; Decidable; Setoid)
open import Relation.Binary.Core using (Transitive; _⇒_)

open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  z≤n; s≤s; _≟_; _≤?_; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤; _ℕ-_; _≺_; reduce≥; 
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties
  using (bounded; inject+-lemma; to-from; toℕ-injective; toℕ-raise; toℕ-fromℕ≤)
open import Data.Vec.Properties 
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin; tabulate-∘; 
         tabulate-allFin; allFin-map; lookup-++-inject+; lookup-++-≥)

open import Data.Vec 
  using (Vec; tabulate; []; _∷_; tail; lookup; zip; zipWith; splitAt;
         _[_]≔_; allFin; toList)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import Function using (id; _∘_; _$_; _∋_)

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
           ≡⟨ cong (_∷_ (g zero))
                (finext (f ∘ suc) (g ∘ suc) (fi≡gi ∘ suc)) ⟩ 
         g zero ∷ tabulate {n} (g ∘ suc)
           ≡⟨ refl ⟩
         tabulate g ∎)
  where open ≡-Reasoning

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

tabulate-split : ∀ {m n} {a : Level} {A : Set a} → (f : Fin (m + n) → A) → 
  tabulate {m + n} f ≡
  tabulate {m} (f ∘ inject+ n) ++V tabulate {n} (f ∘ raise m)
tabulate-split {0} f = refl
tabulate-split {suc m} f = cong (_∷_ (f zero)) (tabulate-split {m} (f ∘ suc))

------------------------------------------------------------------------------
-- Lemmas about subst

-- From Alan Jeffrey's post to Agda list

_⊨_⇒_≡_ : ∀ {I : Set} (F : I → Set) {i j} →
  (i ≡ j) → (F i) → (F j) → Set
(F ⊨ refl ⇒ x ≡ y) = (x ≡ y)

xcong : ∀ {I J F G} (f : I → J) (g : ∀ {i} → F i → G (f i)) →
  ∀ {i j} (i≡j : i ≡ j) {x y} →
    (F ⊨ i≡j ⇒ x ≡ y) → (G ⊨ cong f i≡j ⇒ g x ≡ g y)
xcong f g refl refl = refl

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

------------------------------------------------------------------------------
-- Proofs and definitions about natural numbers

_<?_ : Decidable _<_
i <? j = suc i ≤? j

-- buried in Data.Nat

refl′ : _≡_ ⇒ _≤_
refl′ {0} refl = z≤n
refl′ {suc m} refl = s≤s (refl′ refl)

trans< : Transitive _<_
trans< (s≤s z≤n) (s≤s _) = s≤s z≤n
trans< (s≤s (s≤s i≤j)) (s≤s sj<k) = s≤s (trans< (s≤s i≤j) sj<k) 

trans≤ : Transitive _≤_
trans≤ z≤n x = z≤n
trans≤ (s≤s m≤n) (s≤s n≤o) = s≤s (trans≤ m≤n n≤o)

i*1≡i : (i : ℕ) → i * 1 ≡ i
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

sinj : ∀ {i j} → suc i ≡ suc j → i ≡ j
sinj = cong (λ { 0 → 0 ; (suc x) → x })

sinj≤ : ∀ {i j} → suc i ≤ suc j → i ≤ j
sinj≤ {0}     {j}     _        = z≤n
sinj≤ {suc i} {0}     (s≤s ()) -- absurd
sinj≤ {suc i} {suc j} (s≤s p)  = p

i*n+n≤sucm*n : ∀ {m n} → (i : Fin (suc m)) → toℕ i * n + n ≤ suc m * n
i*n+n≤sucm*n {0} {n} zero =
  begin (n
           ≡⟨ sym (+-right-identity n) ⟩
         n + 0
           ≤⟨ i≤i (n + 0) ⟩ 
         n + 0 ∎)
  where open ≤-Reasoning
i*n+n≤sucm*n {0} {n} (suc ())
i*n+n≤sucm*n {suc m} {n} i = 
  begin (toℕ i * n + n
           ≡⟨ +-comm (toℕ i * n) n ⟩
         n + toℕ i * n
           ≡⟨ refl ⟩
         suc (toℕ i) * n
           ≤⟨ cong*r≤ (bounded i) n ⟩ 
         suc (suc m) * n ∎)
  where open ≤-Reasoning

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

bounded' : (m : ℕ) → (j : Fin (suc m)) → (toℕ j ≤ m)
bounded' m j with bounded j
... | s≤s pr = pr

simplify-≤ : {m n m' n' : ℕ} → (m ≤ n) → (m ≡ m') → (n ≡ n') → (m' ≤ n') 
simplify-≤ leq refl refl = leq

cancel-Fin : ∀ (n y z : ℕ) → ((x : Fin (suc n)) → toℕ x + y ≤ n + z) → y ≤ z
cancel-Fin 0 y z pf = pf zero
cancel-Fin (suc n) y z pf =
  cancel-+-left-≤ n (trans≤ leq (sinj≤ (pf (fromℕ (suc n)))))
  where leq : n + y ≤ toℕ (fromℕ n) + y
        leq = begin (n + y
                       ≡⟨ cong (λ x → x + y) (sym (to-from n)) ⟩
                     toℕ (fromℕ n) + y ∎)
              where open ≤-Reasoning

≤-proof-irrelevance : {m n : ℕ} → (p q : m ≤ n) → p ≡ q
≤-proof-irrelevance z≤n z≤n = refl
≤-proof-irrelevance (s≤s p) (s≤s q) = cong s≤s (≤-proof-irrelevance p q)

raise-suc' : (n a b n+a : ℕ) (n+a≡ : n+a ≡ n + a) → 
  (leq : suc a ≤ b) → 
  (leq' : suc n+a ≤ n + b) → 
  raise n (inject≤ (fromℕ a) leq) ≡ inject≤ (fromℕ n+a) leq'
raise-suc' 0 a b .a refl leq leq' =
  cong (inject≤ (fromℕ a)) (≤-proof-irrelevance leq leq')
raise-suc' (suc n) a b .(suc (n + a)) refl leq (s≤s leq') =
  cong suc (raise-suc' n a b (n + a) refl leq leq') 

raise-suc : (m n : ℕ) (j : Fin (suc m)) (d : Fin (suc n))
  (leq : suc (toℕ j * suc n + toℕ d) ≤ suc m * suc n) → 
  (leq' : suc (toℕ (suc j) * suc n + toℕ d) ≤ suc (suc m) * suc n) →
  raise (suc n) (inject≤ (fromℕ (toℕ j * suc n + toℕ d)) leq) ≡
  inject≤ (fromℕ (toℕ (suc j) * suc n + toℕ d)) leq'
raise-suc m n j d leq leq' =
  raise-suc'
    (suc n)
    (toℕ j * suc n + toℕ d)
    (suc m * suc n)
    (toℕ (suc j) * suc n + toℕ d)
    (begin (toℕ (suc j) * suc n + toℕ d
              ≡⟨ refl ⟩
            (suc n + toℕ j * suc n) + toℕ d
              ≡⟨ +-assoc (suc n) (toℕ j * suc n) (toℕ d) ⟩
            suc n + (toℕ j * suc n + toℕ d) ∎))
    leq
    leq'
  where open ≡-Reasoning

------------------------------------------------------------------------------
-- Fin and Nat lemmas

toℕ-fin : (m n : ℕ) → (eq : m ≡ n) (fin : Fin m) →
  toℕ (subst Fin eq fin) ≡ toℕ fin
toℕ-fin m .m refl fin = refl

∸≡ : (m n : ℕ) (i j : Fin (m + n)) (i≥ : m ≤ toℕ i) (j≥ : m ≤ toℕ j) →
  toℕ i ∸ m ≡ toℕ j ∸ m → i ≡ j
∸≡ m n i j i≥ j≥ p = toℕ-injective pr
  where pr = begin (toℕ i
                    ≡⟨ sym (m+n∸n≡m (toℕ i) m) ⟩
                    (toℕ i + m) ∸ m
                    ≡⟨ cong (λ x → x ∸ m) (+-comm (toℕ i) m) ⟩ 
                    (m + toℕ i) ∸ m
                    ≡⟨ +-∸-assoc m i≥ ⟩
                    m + (toℕ i ∸ m)
                    ≡⟨ cong (λ x → m + x) p ⟩
                    m + (toℕ j ∸ m)
                    ≡⟨ sym (+-∸-assoc m j≥) ⟩
                    (m + toℕ j) ∸ m
                    ≡⟨ cong (λ x → x ∸ m) (+-comm m (toℕ j)) ⟩
                    (toℕ j + m) ∸ m
                    ≡⟨ m+n∸n≡m (toℕ j) m ⟩
                    toℕ j ∎)
             where open ≡-Reasoning

cancel-right∸ : (m n k : ℕ) (k≤m : k ≤ m) (k≤n : k ≤ n) →
  (m ∸ k ≡ n ∸ k) → m ≡ n
cancel-right∸ m n k k≤m k≤n mk≡nk =
  begin (m
         ≡⟨ sym (m+n∸n≡m m k) ⟩
         (m + k) ∸ k
         ≡⟨ cong (λ x → x ∸ k) (+-comm m k) ⟩
         (k + m) ∸ k
         ≡⟨ +-∸-assoc k k≤m ⟩
         k + (m ∸ k)
         ≡⟨ cong (λ x → k + x) mk≡nk ⟩
         k + (n ∸ k)
         ≡⟨ sym (+-∸-assoc k k≤n) ⟩
         (k + n) ∸ k
         ≡⟨ cong (λ x → x ∸ k) (+-comm k n) ⟩
         (n + k) ∸ k
         ≡⟨ m+n∸n≡m n k ⟩
         n ∎)
  where open ≡-Reasoning

raise< : (m n : ℕ) (i : Fin (m + n)) (i< : toℕ i < m) → 
         toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<))) ≡ n + toℕ i
raise< m n i i< =
  begin (toℕ (subst Fin (+-comm n m) (raise n (fromℕ≤ i<)))
         ≡⟨ toℕ-fin (n + m) (m + n) (+-comm n m) (raise n (fromℕ≤ i<)) ⟩
         toℕ (raise n (fromℕ≤ i<))
         ≡⟨ toℕ-raise n (fromℕ≤ i<) ⟩
         n + toℕ (fromℕ≤ i<)
         ≡⟨ cong (λ x → n + x) (toℕ-fromℕ≤ i<) ⟩ 
         n + toℕ i ∎)
  where open ≡-Reasoning

toℕ-reduce≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) →
               toℕ (reduce≥ i i≥) ≡ toℕ i ∸ m
toℕ-reduce≥ 0 n i _ = refl 
toℕ-reduce≥ (suc m) n zero ()
toℕ-reduce≥ (suc m) n (suc i) (s≤s i≥) = toℕ-reduce≥ m n i i≥

inject≥ : (m n : ℕ) (i : Fin (m + n)) (i≥ : m ≤ toℕ i) →
        toℕ (subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥))) ≡ toℕ i ∸ m
inject≥ m n i i≥ =
  begin (toℕ (subst Fin (+-comm n m) (inject+ m (reduce≥ i i≥)))
         ≡⟨ toℕ-fin (n + m) (m + n) (+-comm n m) (inject+ m (reduce≥ i i≥)) ⟩
         toℕ (inject+ m (reduce≥ i i≥))
         ≡⟨ sym (inject+-lemma m (reduce≥ i i≥)) ⟩
         toℕ (reduce≥ i i≥) 
         ≡⟨ toℕ-reduce≥ m n i i≥ ⟩ 
         toℕ i ∸ m ∎)
  where open ≡-Reasoning

fromℕ≤-inj : (m n : ℕ) (i j : Fin n) (i< : toℕ i < m) (j< : toℕ j < m) → 
  fromℕ≤ i< ≡ fromℕ≤ j< → i ≡ j
fromℕ≤-inj m n i j i< j< fi≡fj =
  toℕ-injective
    (trans (sym (toℕ-fromℕ≤ i<)) (trans (cong toℕ fi≡fj) (toℕ-fromℕ≤ j<)))

reduce≥-inj : (m n : ℕ) (i j : Fin (m + n)) (i≥ : m ≤ toℕ i) (j≥ : m ≤ toℕ j) →
  reduce≥ i i≥ ≡ reduce≥ j j≥ → i ≡ j
reduce≥-inj m n i j i≥ j≥ ri≡rj =
  toℕ-injective
    (cancel-right∸ (toℕ i) (toℕ j) m i≥ j≥
      (trans (sym (toℕ-reduce≥ m n i i≥))
      (trans (cong toℕ ri≡rj) (toℕ-reduce≥ m n j j≥))))

------------------------------------------------------------------------------
