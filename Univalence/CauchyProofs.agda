{-# OPTIONS --without-K #-}

module CauchyProofs where

-- Proofs about permutations defined in module Cauchy

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
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

open import Cauchy

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

lookup-subst' : ∀ {m m'} 
  (i : Fin m) (xs : Vec (Fin m') m) (eq : m ≡ m') (eq' : m' ≡ m)
  (irr : sym eq ≡ eq') → 
  lookup 
    (subst Fin eq i) 
    (subst Cauchy eq (subst (λ s → Vec (Fin s) m) eq' xs)) ≡
  lookup i xs
lookup-subst' i xs refl .refl refl = refl

trans-syml : {A : Set} {x y : A} → (p : x ≡ y) → trans (sym p) p ≡ refl
trans-syml refl = refl

trans-symr : {A : Set} {x y : A} → (p : x ≡ y) → trans p (sym p) ≡ refl
trans-symr refl = refl

------------------------------------------------------------------------------
-- Proofs about sequential composition

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

------------------------------------------------------------------------------
-- proofs about additive permutations

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

-- swap+ is idempotent
--
-- outline of swap+idemp proof
--
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
swap+idemp m n =
  begin (tabulate (λ i → 
           lookup 
             (lookup i 
               (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ≡⟨ tabulate-++ {m} {n} 
              (λ i → 
                lookup 
                  (lookup i 
                    (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                      (mapV (raise n) (allFin m) ++V 
                       mapV (inject+ m) (allFin n))))
                  (subst Cauchy (+-comm n m) 
                    (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                      (mapV (raise m) (allFin n) ++V 
                       mapV (inject+ n) (allFin m))))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (lookup (inject+ n i)
               (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (lookup (raise m i)
               (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ≡⟨ cong₂ _++V_
              (finext {m}
                (λ i → 
                  lookup
                    (lookup (inject+ n i)
                      (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                        (mapV (raise n) (allFin m) ++V 
                         mapV (inject+ m) (allFin n))))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                        (mapV (raise m) (allFin n) ++V 
                         mapV (inject+ n) (allFin m)))))
                (λ i → 
                  lookup
                    (subst Fin (+-comm n m) 
                      (lookup (inject+ n i)
                        (mapV (raise n) (allFin m) ++V 
                         mapV (inject+ m) (allFin n))))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                        (mapV (raise m) (allFin n) ++V 
                         mapV (inject+ n) (allFin m))))) 
                (λ i → 
                  cong 
                    (λ x →
                      lookup x
                        (subst Cauchy (+-comm n m) 
                          (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                            (mapV (raise m) (allFin n) ++V 
                             mapV (inject+ n) (allFin m)))))
                    (lookup-subst 
                       (inject+ n i)
                       (mapV (raise n) (allFin m) ++V 
                        mapV (inject+ m) (allFin n))
                       (+-comm n m))))
              (finext {n}
                (λ i → 
                  lookup 
                    (lookup (raise m i)
                      (subst (λ s → Vec (Fin s) (m + n)) (+-comm n m) 
                        (mapV (raise n) (allFin m) ++V 
                         mapV (inject+ m) (allFin n))))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                        (mapV (raise m) (allFin n) ++V 
                         mapV (inject+ n) (allFin m)))))
                (λ i → 
                   lookup 
                     (subst Fin (+-comm n m)
                       (lookup (raise m i)
                         (mapV (raise n) (allFin m) ++V 
                          mapV (inject+ m) (allFin n))))
                     (subst Cauchy (+-comm n m) 
                       (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                         (mapV (raise m) (allFin n) ++V 
                          mapV (inject+ n) (allFin m))))) 
                (λ i → 
                 cong
                    (λ x → 
                      lookup x
                      (subst Cauchy (+-comm n m) 
                        (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                          (mapV (raise m) (allFin n) ++V 
                           mapV (inject+ n) (allFin m)))))
                    (lookup-subst 
                       (raise m i)
                       (mapV (raise n) (allFin m) ++V 
                        mapV (inject+ m) (allFin n))
                       (+-comm n m)))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (subst Fin (+-comm n m) 
               (lookup (inject+ n i)
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (subst Fin (+-comm n m)
               (lookup (raise m i)
                 (mapV (raise n) (allFin m) ++V mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))

         ≡⟨ cong₂ _++V_
              (finext {m}
                (λ i → 
                  lookup
                    (subst Fin (+-comm n m) 
                      (lookup (inject+ n i)
                        (mapV (raise n) (allFin m) ++V 
                         mapV (inject+ m) (allFin n))))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                        (mapV (raise m) (allFin n) ++V 
                         mapV (inject+ n) (allFin m)))))
                (λ i → 
                  lookup
                    (subst Fin (+-comm n m) 
                      (lookup i (mapV (raise n) (allFin m))))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                      (mapV (raise m) (allFin n) ++V 
                       mapV (inject+ n) (allFin m)))))
                (λ i → cong 
                          (λ x → 
                            lookup
                              (subst Fin (+-comm n m) x)
                              (subst Cauchy (+-comm n m) 
                                (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                                  (mapV (raise m) (allFin n) ++V 
                                   mapV (inject+ n) (allFin m)))))
                          (lookup-++-inject+ 
                            (mapV (raise n) (allFin m))
                            (mapV (inject+ m) (allFin n))
                            i)))
              (finext {n}
                (λ i → 
                  lookup 
                    (subst Fin (+-comm n m)
                      (lookup (raise m i)
                      (mapV (raise n) (allFin m) ++V 
                       mapV (inject+ m) (allFin n))))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                      (mapV (raise m) (allFin n) ++V 
                       mapV (inject+ n) (allFin m)))))
                (λ i → 
                  lookup 
                    (subst Fin (+-comm n m)
                      (lookup i (mapV (inject+ m) (allFin n))))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                      (mapV (raise m) (allFin n) ++V 
                       mapV (inject+ n) (allFin m)))))
                (λ i → cong
                          (λ x → 
                            lookup
                              (subst Fin (+-comm n m) x)
                              (subst Cauchy (+-comm n m) 
                                (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                                  (mapV (raise m) (allFin n) ++V 
                                   mapV (inject+ n) (allFin m)))))
                          (lookup-++-raise
                            (mapV (raise n) (allFin m))
                            (mapV (inject+ m) (allFin n))
                            i))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (subst Fin (+-comm n m) 
               (lookup i (mapV (raise n) (allFin m))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (subst Fin (+-comm n m)
               (lookup i (mapV (inject+ m) (allFin n))))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ≡⟨ cong₂ _++V_
              (finext {m}
                (λ i → 
                  lookup
                    (subst Fin (+-comm n m) 
                      (lookup i (mapV (raise n) (allFin m))))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                        (mapV (raise m) (allFin n) ++V 
                         mapV (inject+ n) (allFin m)))))
                (λ i → 
                  lookup
                    (subst Fin (+-comm n m) (raise n i))
                    (subst Cauchy (+-comm n m) 
                      (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                        (mapV (raise m) (allFin n) ++V 
                         mapV (inject+ n) (allFin m)))))
                (λ i → 
                  cong
                     (λ x → 
                       lookup (subst Fin (+-comm n m) x)
                       (subst Cauchy (+-comm n m) 
                         (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                           (mapV (raise m) (allFin n) ++V 
                            mapV (inject+ n) (allFin m)))))
                     (trans 
                       (lookup-map i (raise n) (allFin m))
                       (cong (raise n) (lookup-allFin i)))))
              (finext {n}
                (λ i → 
                 lookup 
                   (subst Fin (+-comm n m)
                     (lookup i (mapV (inject+ m) (allFin n))))
                   (subst Cauchy (+-comm n m) 
                     (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                     (mapV (raise m) (allFin n) ++V 
                      mapV (inject+ n) (allFin m)))))
                (λ i → 
                 lookup 
                   (subst Fin (+-comm n m) (inject+ m i))
                   (subst Cauchy (+-comm n m) 
                     (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                       (mapV (raise m) (allFin n) ++V 
                        mapV (inject+ n) (allFin m)))))
                (λ i → 
                  cong
                    (λ x → 
                       lookup (subst Fin (+-comm n m) x)
                       (subst Cauchy (+-comm n m) 
                         (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                           (mapV (raise m) (allFin n) ++V 
                            mapV (inject+ n) (allFin m)))))
                     (trans 
                       (lookup-map i (inject+ m) (allFin n))
                       (cong (inject+ m) (lookup-allFin i))))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (subst Fin (+-comm n m) (raise n i))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (subst Fin (+-comm n m) (inject+ m i))
             (subst Cauchy (+-comm n m) 
               (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                 (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))))
         ≡⟨ cong₂ _++V_
             (finext {m}
               (λ i → 
                 lookup
                   (subst Fin (+-comm n m) (raise n i))
                   (subst Cauchy (+-comm n m) 
                     (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                       (mapV (raise m) (allFin n) ++V 
                        mapV (inject+ n) (allFin m)))))
               (λ i → 
                 lookup
                   (raise n i)
                   (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))
               (λ i → 
                 lookup-subst' 
                    (raise n i)
                    (mapV (raise m) (allFin n) ++V 
                     mapV (inject+ n) (allFin m))
                     (+-comm n m)
                     (+-comm m n)
                     (proof-irrelevance (sym (+-comm n m)) (+-comm m n))))
             (finext {n}
               (λ i → 
                 lookup 
                   (subst Fin (+-comm n m) (inject+ m i))
                   (subst Cauchy (+-comm n m) 
                     (subst (λ s → Vec (Fin s) (n + m)) (+-comm m n) 
                       (mapV (raise m) (allFin n) ++V 
                        mapV (inject+ n) (allFin m)))))
               (λ i → 
                 lookup 
                   (inject+ m i)
                   (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))
               (λ i → 
                 lookup-subst'
                    (inject+ m i)
                    (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m))
                    (+-comm n m)
                    (+-comm m n)
                    (proof-irrelevance (sym (+-comm n m)) (+-comm m n)))) ⟩ 
         tabulate {m} (λ i → 
           lookup
             (raise n i)
             (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))
         ++V
         tabulate {n} (λ i → 
           lookup 
             (inject+ m i)
             (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))
         ≡⟨ cong₂ _++V_
              (finext 
                (λ i → 
                  lookup
                    (raise n i)
                    (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))
                (λ i → lookup i (mapV (inject+ n) (allFin m)))
                (lookup-++-raise
                   (mapV (raise m) (allFin n))
                   (mapV (inject+ n) (allFin m))))
              (finext 
                (λ i → 
                  lookup 
                    (inject+ m i)
                    (mapV (raise m) (allFin n) ++V mapV (inject+ n) (allFin m)))
                 (λ i → lookup i (mapV (raise m) (allFin n)))
                 (lookup-++-inject+ 
                    (mapV (raise m) (allFin n)) 
                    (mapV (inject+ n) (allFin m)))) ⟩ 
         tabulate {m} (λ i → lookup i (mapV (inject+ n) (allFin m)))
         ++V
         tabulate {n} (λ i → lookup i (mapV (raise m) (allFin n)))
         ≡⟨ cong₂ _++V_ 
              (tabulate∘lookup (mapV (inject+ n) (allFin m)))
              (tabulate∘lookup (mapV (raise m) (allFin n))) ⟩ 
         mapV (inject+ n) (allFin m) ++V mapV (raise m) (allFin n)
         ≡⟨ sym (allFin+ m n) ⟩
         allFin (m + n) ∎)
  where open ≡-Reasoning

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

-- a kind of inverse for splitAt

unSplit : {m n : ℕ} {A : Set} → (f : Fin (m + n) → A) → 
  tabulate {m} (f ∘ (inject+ n)) ++V tabulate {n} (f ∘ (raise m)) ≡ tabulate f
unSplit {0} {n} f = refl
unSplit {suc m} f = cong (λ x → (f zero) ∷ x) (unSplit {m} (f ∘ suc))

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

------------------------------------------------------------------------------
-- Proofs about multiplicative permutations

-- need to prove tcomp-id and tcomp-dist
-- tcomp-id requires allFin*

concat-nil : ∀ {m} → 
  concatV (tabulate {m} (λ b → [])) ≡ subst Cauchy (sym (*-right-zero m)) []
concat-nil {0} = refl
concat-nil {suc m} = concat-nil {m}

empty-vec : ∀ {m} → (eq : m ≡ 0) → allFin m ≡ subst Cauchy (sym eq) []
empty-vec {0} refl = refl 
empty-vec {suc m} ()

-- two different ways of injecting d : Fin (suc n) into 
-- Fin (suc m * suc n)

inject+0 : ∀ {m} → (i : Fin m) → 
  inject+ 0 i ≡ subst Fin (sym (+-right-identity m)) i
inject+0 {0} () 
inject+0 {suc m} zero =
  begin (inject+ 0 (Fin (suc m) ∋ zero)
           ≡⟨ refl ⟩
         (Fin (suc m + 0) ∋ zero)
           ≡⟨ sym (congD!
                    (λ m → {!!} )
                    {suc m + 0} {suc m}
                    (sym (+-right-identity (suc m)))) ⟩
         subst Fin (sym (+-right-identity (suc m))) (Fin (suc m) ∋ zero) ∎)
  where open ≡-Reasoning
inject+0 {suc m} (suc i) = {!!} 

--congD! : {a b : Level} {A : Set a} {B : A → Set b}
--         (f : (x : A) → B x) → {x₁ x₂ : A} → (x₂≡x₁ : x₂ ≡ x₁) → 
--         subst B x₂≡x₁ (f x₂) ≡ f x₁
--congD! f refl = refl


inj-lemma : ∀ {m n} → (d : Fin (suc n)) (p : suc (toℕ d) ≤ suc m * suc n) →
  inject+ (m * suc n) d ≡ inject≤ (fromℕ (toℕ d)) p 
inj-lemma {m} {n} zero (s≤s m≤n) = refl
inj-lemma {m} {0} (suc ()) (s≤s m≤n) 
inj-lemma {0} {suc n} (suc d) (s≤s (s≤s d≤n)) = {!!}
inj-lemma {suc m} {suc n} (suc d) (s≤s m≤n) = {!!}

-- ?0 : inject+ 0 (suc d) ≡ suc d ≡ 
-- suc (inject≤ (fromℕ (toℕ d)) (s≤s d≤n))

-- ?1 : inject+ (suc m * suc (suc n)) (suc d) ≡
--      inject≤ (fromℕ (toℕ (suc d))) (s≤s m≤n)




{--
inj-lemma {m} {0} zero = {!refl!}
-- ?0 : zero ≡ inject≤ 0 (i*n+k≤m*n 0 0)
-- i*n+k≤m*n 0 0 does not normalize to (s≤s _) which is necessary to pattern
-- match the definition of inject≤
inj-lemma {m} {0} (suc ())
inj-lemma {0} {suc n} zero = {!!}
inj-lemma {0} {suc n} (suc d) = {!!}
inj-lemma {suc m} {suc n} zero = {!!}
inj-lemma {suc m} {suc n} (suc d) = {!!}
--}

{--


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



map-tabulate-suc : ∀ {m n} →
 (f : Fin (suc m → Fin (suc n) → Fin (suc m * suc n)) → 
  mapV 
    (λ b → mapV (f b) (idcauchy (suc n)))
    (tabulate {m} suc) ≡
  mapV
    (λ b → mapV
             (raise (suc n))
             (mapV (f b) (idcauchy (suc n))))
    (tabulate {m} id)
map-tabulate-suc = {!!} 
                   (λ d → inject≤
                            (fromℕ (toℕ b * suc n + toℕ d))
                            (i*n+k≤m*n b d))
--}

allFin* : (m n : ℕ) → allFin (m * n) ≡ 
          concatV 
            (mapV 
              (λ b → 
                mapV
                  (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                  (idcauchy n))
            (idcauchy m))
allFin* 0 _ = refl 
allFin* (suc m) 0 =
  begin (allFin (suc m * 0)
           ≡⟨ empty-vec {suc m * 0} (*-right-zero (suc m)) ⟩ 
         subst Cauchy (sym (*-right-zero (suc m))) []
           ≡⟨ sym (concat-nil {suc m}) ⟩ 
         concatV (tabulate {suc m} (λ b → []))
           ≡⟨ cong concatV (tabulate-allFin {suc m} (λ b → [])) ⟩
         concatV (mapV (λ b → []) (idcauchy (suc m))) ∎)
  where open ≡-Reasoning
allFin* (suc m) (suc n) =
  begin (allFin (suc n + m * suc n)
           ≡⟨ allFin+ (suc n) (m * suc n) ⟩
         mapV (inject+ (m * suc n)) (allFin (suc n)) ++V
         mapV (raise (suc n)) (allFin (m * suc n))
           ≡⟨ cong
                (λ x →
                  mapV (inject+ (m * suc n)) (allFin (suc n)) ++V
                  mapV (raise (suc n)) x)
                (allFin* m (suc n)) ⟩
         mapV (inject+ (m * suc n)) (allFin (suc n)) ++V
         mapV
           (raise (suc n))
           (concatV 
             (mapV 
               (λ b → 
                 mapV
                   (λ d → inject≤
                            (fromℕ (toℕ b * suc n + toℕ d))
                            (i*n+k≤m*n b d))
                   (idcauchy (suc n)))
               (idcauchy m)))
           ≡⟨ cong
                (_++V_ (mapV (inject+ (m * suc n)) (allFin (suc n))))
                (sym (concat-map
                       (mapV 
                         (λ b → 
                           mapV
                             (λ d → inject≤
                                      (fromℕ (toℕ b * suc n + toℕ d))
                                      (i*n+k≤m*n b d))
                             (idcauchy (suc n)))
                         (idcauchy m))
                       (raise (suc n)))) ⟩ 
         mapV (inject+ (m * suc n)) (allFin (suc n)) ++V
         concatV
           (mapV
             (mapV (raise (suc n)))
             (mapV 
               (λ b → 
                 mapV
                   (λ d → inject≤
                            (fromℕ (toℕ b * suc n + toℕ d))
                            (i*n+k≤m*n b d))
                   (idcauchy (suc n)))
               (idcauchy m)))
           ≡⟨ refl ⟩  
         concatV
           ((mapV (inject+ (m * suc n)) (allFin (suc n))) ∷ 
            (mapV
              (mapV (raise (suc n)))
              (mapV 
                (λ b → 
                  mapV
                    (λ d → inject≤
                             (fromℕ (toℕ b * suc n + toℕ d))
                             (i*n+k≤m*n b d))
                    (idcauchy (suc n)))
                (idcauchy m))))
           ≡⟨ cong
                 (λ x →
                   concatV
                     ((mapV (inject+ (m * suc n)) (allFin (suc n))) ∷ x))
                 (sym (map-∘
                        (mapV (raise (suc n)))
                        (λ b → 
                          mapV
                            (λ d → inject≤
                                     (fromℕ (toℕ b * suc n + toℕ d))
                                     (i*n+k≤m*n b d))
                            (idcauchy (suc n)))
                        (idcauchy m))) ⟩  
         concatV
           ((mapV (inject+ (m * suc n)) (allFin (suc n))) ∷ 
            (mapV
              (λ b → mapV
                       (raise (suc n))
                       (mapV
                         (λ d → inject≤
                                  (fromℕ (toℕ b * suc n + toℕ d))
                                  (i*n+k≤m*n b d))
                         (idcauchy (suc n))))
              (idcauchy m)))
           ≡⟨ {!!} ⟩ 
         concatV 
           ((mapV
              (λ d → inject≤
                       (fromℕ (toℕ d))
                       (i*n+k≤m*n {suc m} {suc n} zero d))
              (idcauchy (suc n))) ∷ 
            (mapV 
               (λ b → 
                 mapV
                   (λ d → inject≤
                            (fromℕ (toℕ b * suc n + toℕ d))
                            (i*n+k≤m*n b d))
                   (idcauchy (suc n)))
               (tabulate {m} suc)))
           ≡⟨ refl ⟩ 
         concatV 
           (mapV 
             (λ b → 
               mapV
                 (λ d → inject≤
                          (fromℕ (toℕ b * suc n + toℕ d))
                          (i*n+k≤m*n b d))
                 (idcauchy (suc n)))
             (idcauchy (suc m))) ∎)
  where open ≡-Reasoning

{-- 
map-∘ : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c}
        (f : B → C) (g : A → B) → (xs : Vec A n) →
        mapV (f ∘ g) xs ≡ (mapV f ∘ mapV g) xs

--

  mapV (mapV f) (mapV g xs)
= mapV (mapV f ∘ g) xs


map g (f x1) , map g (f x2) , map g (f x3)
--

f = (λ b → 
      mapV
        (λ d → inject≤
                 (fromℕ (toℕ b * suc n + toℕ d))
                 (i*n+k≤m*n b d))
        (idcauchy (suc n)))

f zero = idcauchy (suc n)

Need to show that:

(mapV (inject+ (m * suc n)) (allFin (suc n))) ∷ 
(mapV (mapV (raise (suc n))) (mapV f (tabulate {m} id)))

≡

f zero ∷ mapV f (tabulate {m} suc)

  mapV (mapV (raise (suc n))) (mapV f (tabulate {m} id))
≡ mapV f (tabulate {m} suc)

f i = [a, b, c]

[map (raise (suc n)) (f 0), 
 map (raise (suc n)) (f 1), 
 map (raise (suc n)) (f 2), 
 map (raise (suc n)) (f 3), 
 map (raise (suc n)) (f 4)]


--}






{--
allFin* : (m n : ℕ) → allFin (m * n) ≡ 
          concatV 
            (mapV 
              (λ b → 
                mapV
                  (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                  (allFin n))
              (allFin m))
allFin* 0 _ = refl
allFin* (suc m) n =
  begin (allFin (suc m * n)
           ≡⟨ refl ⟩
         allFin (n + m * n)
           ≡⟨ allFin+ n (m * n) ⟩
         mapV (inject+ (m * n)) (allFin n) ++V mapV (raise n) (allFin (m * n))
           ≡⟨ cong
                (λ x →
                  mapV (inject+ (m * n)) (allFin n) ++V mapV (raise n) x)
                (allFin* m n) ⟩ 
         mapV (inject+ (m * n)) (allFin n) ++V
         mapV
           (raise n)
           (concatV 
             (mapV 
               (λ b → 
                 mapV
                   (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                   (allFin n))
               (allFin m)))
           ≡⟨ {!!} ⟩ 
         concatV 
           ((mapV
              (λ d → inject≤
                       {suc (toℕ d)}
                       {suc m * n}
                       (fromℕ (toℕ d))
                       (i*n+k≤m*n {suc m} {n} zero d))
              (allFin n))
            ∷ 
            (mapV 
              (λ b → 
                mapV
                  (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                  (allFin n))
              (mapV suc (allFin m))))



-- suc (toℕ zero * n + toℕ d) ≤ suc m * n
-- suc (0 * n + toℕ d) ≤ suc m * n
-- suc (toℕ d) ≤ suc m * n

-- inject< : Fin (suc (toℕ d)) → ... → Fin (suc m * n)


-- i*n+k≤m*n : ∀ {m n} → (i : Fin m) → (k : Fin n) → 
--             (suc (toℕ i * n + toℕ k) ≤ m * n)



           ≡⟨ {!!} ⟩ 
         concatV 
           (mapV 
             (λ b → 
               mapV
                 (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                 (allFin n))
             (zero ∷ mapV suc (allFin m)))
           ≡⟨ {!!} ⟩ 
         concatV 
           (mapV 
             (λ b → 
               mapV
                 (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
                 (allFin n))
             (allFin (suc m))) ∎)
  where open ≡-Reasoning
--}

tcomp-id : ∀ {m n} → tcompcauchy (idcauchy m) (idcauchy n) ≡ idcauchy (m * n)
tcomp-id {m} {n} = sym (allFin* m n)
{--
tcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m * n)
tcompcauchy {m} {n} α β = 
  concatV 
    (mapV 
      (λ b → 
         mapV (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d)) β)
      α)


tcomp-id : ∀ {m n} → tcompcauchy2 (idcauchy m) (idcauchy n) ≡ idcauchy (m * n)
tcomp-id {0} {n} = refl
tcomp-id {suc m} {n} = 
  begin (mapV (raise∘inject {suc m} {n} zero) (idcauchy n) ++V
         tcompcauchy' {m} {suc m} {n} (tabulate suc) (idcauchy n)
          ≡⟨ refl ⟩ 
         mapV (λ d → inject≤ d (i*n+n≤sucm*n {m} {n} zero)) (idcauchy n) ++V
         tcompcauchy' {m} {suc m} {n} (tabulate suc) (idcauchy n)
          ≡⟨ {!!} ⟩ 
         idcauchy (n + m * n) ∎)
  where open ≡-Reasoning

tcompcauchy' : ∀ {i m n} → Vec (Fin m) i → Cauchy n → Vec (Fin (m * n)) (i * n)
tcompcauchy' {0} {m} {n} [] β = []
tcompcauchy' {suc i} {m} {n} (b ∷ α) β = 
  mapV (raise∘inject {m} {n} b) β ++V tcompcauchy' {i} {m} {n} α β

i*n+n≤sucm*n : ∀ {m n} → (i : Fin (suc m)) → (toℕ i * n + n ≤ suc m * n)
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

raise∘inject : ∀ {m n} → (b : Fin m) (d : Fin n) → Fin (m * n)
raise∘inject {0} {n} () d
raise∘inject {suc m} {n} b d =
  inject≤ (raise (toℕ b * n) d) (i*n+n≤sucm*n {m} {n} b)

λ d → inject≤ d (pr : n ≤ suc m * n)

 

xx : Cauchy 3
xx = fromℕ 2 ∷ zero ∷ inject+ 1 (fromℕ 1) ∷ []
-- xx = 2 ∷ 0 ∷ 1 ∷ []

yy : Cauchy 2
yy = fromℕ 1 ∷ zero ∷ []
-- yy = 1 ∷ 0 ∷ []

-- tcompcauchy xx yy = 5 ∷ 4  ∷  1 ∷ 0  ∷  3 ∷ 2  ∷  []
-- tcompcauchy' xx yy = 5 ∷ 4  ∷  1 ∷ 0  ∷  3 ∷ 2  ∷  []
-- yy (+2*2) ++ yy (+0*2) ++ yy (+1*2)

-- i = 3, m = 3, n = 2, b = 2, α = [0,1], β = [1,0] ==> yy (+ 2*2)
-- i = 2, m = 3, n = 2, b = 0, α = [1],   β = [1,0] ==> yy (+ 0*2)
-- i = 1, m = 3, n = 2, b = 1, α = [],    β = [1,0] ==> yy (+ 1*2)
-- i = 0, m = 3, n = 2                              ==> []

-- b : Fin m, d : Fin n
-- α : Vec (Fin m) i
-- tcom... : Vec (Fin (m * n)) (i * n)
-- xxx : Vec (Fin (m * n)) n

-- i*n+k≤m*n : ∀ {m n} → (i : Fin m) → (k : Fin n) → 
--             (suc (toℕ i * n + toℕ k) ≤ m * n)

-- suc (b * n + d)

-- tcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m * n)
-- tcompcauchy {m} {n} α β = 
--   concatV 
--     (mapV 
--       (λ b → 
--         mapV
--           (λ d → inject≤ (fromℕ (toℕ b * n + toℕ d)) (i*n+k≤m*n b d))
--           β)
--      α)

-- tcompcauchy {m} {n} α β
-- = 
-- concatV [ 
--   mapV ((raise n)^{0}   ∘ inject+ (m-1 * n)) β , 
--   mapV ((raise n)^{1}   ∘ inject+ (m-2 * n)) β , 
--   mapV ((raise n)^{2}   ∘ inject+ (m-3 * n)) β , 
--   ...
--   mapV ((raise n)^{m-1} ∘ inject+ (0   * n)) β , 
--   [] 
-- ]

-- allFin (m * n) 
-- = 
-- concatV [ 
--   mapV ((raise n)^{0}   ∘ inject+ (m-1 * n)) (allFin n) , 
--   mapV ((raise n)^{1}   ∘ inject+ (m-2 * n)) (allFin n) , 
--   mapV ((raise n)^{2}   ∘ inject+ (m-3 * n)) (allFin n) , 
--   ...
--   mapV ((raise n)^{m-1} ∘ inject+ (0   * n)) (allFin n) , 
--   [] 
-- ]

-- Cauchy n = Vec (Fin n) n
-- (x ∷ α) : Cauchy (suc m) = Vec (Fin (suc m)) (suc m)
-- x : Fin (suc m)
-- α : Vec (Fin (suc m)) m

tcompcauchy (a ∷ b ∷ c ∷ []) (x ∷ y ∷ [])
=
[ a*2 + x, a*2 + y, b*2 + x , b*2 + y, c*2 + x, c*2 + y ]

tcompcauchy (b ∷ c ∷ []) (x ∷ y ∷ [])
=
[ b*2 + x , b*2 + y, c*2 + x, c*2 + y ]

allFin (suc m * n)
= 
allFin (n + (m * n))
= 
mapV (inject+ (m * n)) (allFin n) ++V 
mapV (raise n) (allFin (m * n))

allFin (4 * 2)
= 
mapV (inject+ (3 * 2)) (allFin 2) ++V 
mapV (raise 2) (mapV (inject+ (2 * 2)) (allFin 2) ++V 
                mapV (raise 2) (mapV (inject+ (1 * 2)) (allFin 2) ++V 
                                mapV (raise 2) (mapV (inject+ 0) (allFin 2) ++V 
                                                mapV (raise 2) [])))
= 
mapV (inject+ (3 * 2)) (allFin 2) ++V 
mapV (raise 2 ∘ inject+ (2 * 2)) (allFin 2) ++V 
mapV (raise 2 ∘ raise 2 ∘ inject+ (1 * 2)) (allFin 2) ++V 
mapV (raise 2 ∘ raise 2 ∘ raise 2 ∘ inject+ 0) (allFin 2) ++V 
mapV (raise 2 ∘ raise 2 ∘ raise 2 ∘ raise 2) []

= 
concatV [ 
  mapV (inject+ (3 * 2)) (allFin 2) , 
  mapV (raise 2 ∘ inject+ (2 * 2)) (allFin 2) , 
  mapV (raise 2 ∘ raise 2 ∘ inject+ (1 * 2)) (allFin 2) , 
  mapV (raise 2 ∘ raise 2 ∘ raise 2 ∘ inject+ 0) (allFin 2) , 
  mapV (raise 2 ∘ raise 2 ∘ raise 2 ∘ raise 2) [] ]

allFin (m * n) 
= 
concatV [ 
  mapV ((raise n)^{0}   ∘ inject+ (m-1 * n)) (allFin n) , 
  mapV ((raise n)^{1}   ∘ inject+ (m-2 * n)) (allFin n) , 
  mapV ((raise n)^{2}   ∘ inject+ (m-3 * n)) (allFin n) , 
  ...
  mapV ((raise n)^{m-1} ∘ inject+ (0   * n)) (allFin n) , 
  [] 
]

allFin (4 * 2)
= 
allFin (2 + (3 * 2))
= 
mapV (inject+ (3 * 2)) (allFin 2) ++V 
mapV (raise 2) (allFin (3 * 2))

allFin (3 * 2)
= 
allFin (2 + (2 * 2))
= 
mapV (inject+ (2 * 2)) (allFin 2) ++V 
mapV (raise 2) (allFin (2 * 2))

allFin (2 * 2)
= 
allFin (2 + (1 * 2))
= 
mapV (inject+ (1 * 2)) (allFin 2) ++V 
mapV (raise 2) (allFin (1 * 2))

allFin (1 * 2)
= 
allFin (2 + (0 * 2))
= 
mapV (inject+ (0 * 2)) (allFin 2) ++V 
mapV (raise 2) (allFin (0 * 2))

allFin (0 * 2)
= 
[] 

postulate
  a b c : Fin 3
  x y : Fin 2

tcompcauchy (a ∷ b ∷ c ∷ []) (x ∷ y ∷ [])
=
[ a*2 + x, a*2 + y, b*2 + x , b*2 + y, c*2 + x, c*2 + y ]

inject≤ (fromℕ (toℕ a * 2 + toℕ x))
(.Data.Nat._.trans
 (.Data.Nat._.refl′ (cong suc (+-comm (toℕ a * 2) (toℕ x))))
 (.Data.Nat._.trans (s≤s (.Data.Nat._.refl′ refl))
  (.Data.Nat._.trans (cong+r≤ (bounded x) (toℕ a * 2))
   (.Data.Nat._.trans
    (.Data.Nat._.trans
     (.Data.Nat._.refl′
      (trans
       (cong suc
        (trans (cong suc (sym (+-right-identity (toℕ a * 2))))
         (trans (sym (+-suc (toℕ a * 2) 0)) refl)))
       (trans (sym (+-suc (toℕ a * 2) 1)) refl)))
     (.Data.Nat._.trans (cong+r≤ (cong*r≤ (sinj≤ (bounded a)) 2) 2)
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
∷
inject≤ (fromℕ (toℕ a * 2 + toℕ y))
(.Data.Nat._.trans
 (.Data.Nat._.refl′ (cong suc (+-comm (toℕ a * 2) (toℕ y))))
 (.Data.Nat._.trans (s≤s (.Data.Nat._.refl′ refl))
  (.Data.Nat._.trans (cong+r≤ (bounded y) (toℕ a * 2))
   (.Data.Nat._.trans
    (.Data.Nat._.trans
     (.Data.Nat._.refl′
      (trans
       (cong suc
        (trans (cong suc (sym (+-right-identity (toℕ a * 2))))
         (trans (sym (+-suc (toℕ a * 2) 0)) refl)))
       (trans (sym (+-suc (toℕ a * 2) 1)) refl)))
     (.Data.Nat._.trans (cong+r≤ (cong*r≤ (sinj≤ (bounded a)) 2) 2)
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
∷
inject≤ (fromℕ (toℕ b * 2 + toℕ x))
(.Data.Nat._.trans
 (.Data.Nat._.refl′ (cong suc (+-comm (toℕ b * 2) (toℕ x))))
 (.Data.Nat._.trans (s≤s (.Data.Nat._.refl′ refl))
  (.Data.Nat._.trans (cong+r≤ (bounded x) (toℕ b * 2))
   (.Data.Nat._.trans
    (.Data.Nat._.trans
     (.Data.Nat._.refl′
      (trans
       (cong suc
        (trans (cong suc (sym (+-right-identity (toℕ b * 2))))
         (trans (sym (+-suc (toℕ b * 2) 0)) refl)))
       (trans (sym (+-suc (toℕ b * 2) 1)) refl)))
     (.Data.Nat._.trans (cong+r≤ (cong*r≤ (sinj≤ (bounded b)) 2) 2)
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
∷
inject≤ (fromℕ (toℕ b * 2 + toℕ y))
(.Data.Nat._.trans
 (.Data.Nat._.refl′ (cong suc (+-comm (toℕ b * 2) (toℕ y))))
 (.Data.Nat._.trans (s≤s (.Data.Nat._.refl′ refl))
  (.Data.Nat._.trans (cong+r≤ (bounded y) (toℕ b * 2))
   (.Data.Nat._.trans
    (.Data.Nat._.trans
     (.Data.Nat._.refl′
      (trans
       (cong suc
        (trans (cong suc (sym (+-right-identity (toℕ b * 2))))
         (trans (sym (+-suc (toℕ b * 2) 0)) refl)))
       (trans (sym (+-suc (toℕ b * 2) 1)) refl)))
     (.Data.Nat._.trans (cong+r≤ (cong*r≤ (sinj≤ (bounded b)) 2) 2)
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
∷
inject≤ (fromℕ (toℕ c * 2 + toℕ x))
(.Data.Nat._.trans
 (.Data.Nat._.refl′ (cong suc (+-comm (toℕ c * 2) (toℕ x))))
 (.Data.Nat._.trans (s≤s (.Data.Nat._.refl′ refl))
  (.Data.Nat._.trans (cong+r≤ (bounded x) (toℕ c * 2))
   (.Data.Nat._.trans
    (.Data.Nat._.trans
     (.Data.Nat._.refl′
      (trans
       (cong suc
        (trans (cong suc (sym (+-right-identity (toℕ c * 2))))
         (trans (sym (+-suc (toℕ c * 2) 0)) refl)))
       (trans (sym (+-suc (toℕ c * 2) 1)) refl)))
     (.Data.Nat._.trans (cong+r≤ (cong*r≤ (sinj≤ (bounded c)) 2) 2)
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
∷
inject≤ (fromℕ (toℕ c * 2 + toℕ y))
(.Data.Nat._.trans
 (.Data.Nat._.refl′ (cong suc (+-comm (toℕ c * 2) (toℕ y))))
 (.Data.Nat._.trans (s≤s (.Data.Nat._.refl′ refl))
  (.Data.Nat._.trans (cong+r≤ (bounded y) (toℕ c * 2))
   (.Data.Nat._.trans
    (.Data.Nat._.trans
     (.Data.Nat._.refl′
      (trans
       (cong suc
        (trans (cong suc (sym (+-right-identity (toℕ c * 2))))
         (trans (sym (+-suc (toℕ c * 2) 0)) refl)))
       (trans (sym (+-suc (toℕ c * 2) 1)) refl)))
     (.Data.Nat._.trans (cong+r≤ (cong*r≤ (sinj≤ (bounded c)) 2) 2)
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
∷ []
--}

tcomp-dist : ∀ {m n} → (pm qm : Cauchy m) → (pn qn : Cauchy n) →
  scompcauchy (tcompcauchy pm pn) (tcompcauchy qm qn) ≡
  tcompcauchy (scompcauchy pm qm) (scompcauchy pn qn)
tcomp-dist {m} {n} pm qm pn qn =
  begin (scompcauchy (tcompcauchy pm pn) (tcompcauchy qm qn)
           ≡⟨ refl ⟩
         tabulate (λ i →
           lookup
             (lookup i (concatV 
                         (mapV 
                           (λ b → 
                             mapV (λ d →
                               inject≤
                                 (fromℕ (toℕ b * n + toℕ d))
                                 (i*n+k≤m*n b d)) pn)
                           pm)))
             (concatV 
               (mapV 
                 (λ b → 
                   mapV (λ d →
                     inject≤
                       (fromℕ (toℕ b * n + toℕ d))
                       (i*n+k≤m*n b d)) qn)
                 qm)))
           ≡⟨  {!!} ⟩
         tcompcauchy (scompcauchy pm qm) (scompcauchy pn qn) ∎)
  where open ≡-Reasoning
              
------------------------------------------------------------------------------
