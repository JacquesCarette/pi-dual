{-# OPTIONS --without-K #-}

module Pif where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
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
  using (lookup∘tabulate; tabulate∘lookup; lookup-allFin)

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
open import Function using (id; _∘_)

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

------------------------------------------------------------------------------
-- Level 0 of Pi
--
-- ZERO is a type with no elements
-- ONE is a type with one element 'tt'
-- PLUS ONE ONE is a type with elements 'false' and 'true'
-- and so on for all finite types built from ZERO, ONE, PLUS, and TIMES
-- 
-- We also have that U is a type with elements ZERO, ONE, PLUS ONE ONE, 
--   TIMES BOOL BOOL, etc.

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U
  BOOL  : U          -- for testing

⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ BOOL ⟧        = Bool

-- Abbreviations for examples

-- BOOL : U
-- BOOL  = PLUS ONE ONE 

BOOL² : U
BOOL² = TIMES BOOL BOOL

-- false⟷ true⟷ : ⟦ BOOL ⟧
-- false⟷ = inj₁ tt
-- true⟷  = inj₂ tt

-- For any finite type (t : U) there is no non-trivial path structure
-- between the elements of t. All such finite types are discrete
-- groupoids
--
-- For U, there are non-trivial paths between its points. In the
-- conventional HoTT presentation, a path between t₁ and t₂ is
-- postulated by univalence for each equivalence between t₁ and t₂. In
-- the context of finite types, an equivalence corresponds to a
-- permutation as each permutation has a unique inverse
-- permutation. Thus instead of the detour using univalence, we can
-- give an inductive definition of all possible permutations between
-- finite types which naturally induces paths between the points of U,
-- i.e., the finite types. More precisely, two types t₁ and t₂ have a
-- path between them if there is a permutation (c : t₁ ⟷ t₂). The fact
-- that c is a permutation guarantees, by construction, that (c ◎ ! c
-- ∼ id⟷) and (! c ◎ c ∼ id⟷). A complete set of generators for all
-- possible permutations between finite types is given by the
-- following definition. Note that these permutations do not reach
-- inside the types and hence do not generate paths between the points
-- within the types. The paths are just between the types themselves.

infix  30 _⟷_
infixr 50 _◎_

data _⟷_ : U → U → Set where
  unite₊  : {t : U} → PLUS ZERO t ⟷ t
  uniti₊  : {t : U} → t ⟷ PLUS ZERO t
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆  : {t : U} → t ⟷ TIMES ONE t
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  distz   : {t : U} → TIMES ZERO t ⟷ ZERO
  factorz : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → 
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) 
  factor  : {t₁ t₂ t₃ : U} → 
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)
  -- for testing
  foldBool   : PLUS ONE ONE ⟷ BOOL
  unfoldBool : BOOL ⟷ PLUS ONE ONE

-- Extensional evaluator for testing: serves as a specification

eval  :{ t₁ t₂ : U } → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
eval unite₊ (inj₁ ())
eval unite₊ (inj₂ v) = v
eval uniti₊ v = inj₂ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆ (tt , v) = v
eval uniti⋆ v = (tt , v)
eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval distz (() , _)
eval factorz ()
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval id⟷ v = v
eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)
eval foldBool (inj₁ tt) = false
eval foldBool (inj₂ tt) = true
eval unfoldBool false = inj₁ tt
eval unfoldBool true = inj₂ tt

-- A canonical representation of each type as a vector of values. This
-- fixes a canonical order for the elements of the types: each value
-- has a canonical index.

size : U → ℕ
size ZERO          = 0
size ONE           = 1
size (PLUS t₁ t₂)  = size t₁ + size t₂
size (TIMES t₁ t₂) = size t₁ * size t₂
size BOOL          = 2

utoVec : (t : U) → Vec ⟦ t ⟧ (size t)
utoVec ZERO          = []
utoVec ONE           = tt ∷ []
utoVec (PLUS t₁ t₂)  = mapV inj₁ (utoVec t₁) ++V mapV inj₂ (utoVec t₂)
utoVec (TIMES t₁ t₂) = 
  concatV (mapV (λ v₁ → mapV (λ v₂ → (v₁ , v₂)) (utoVec t₂)) (utoVec t₁))
utoVec BOOL          = false ∷ true ∷ []

-- Combinators are always between types of the same size

size≡ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (size t₁ ≡ size t₂)
size≡ {PLUS ZERO t} {.t} unite₊ = refl
size≡ {t} {PLUS ZERO .t} uniti₊ = refl
size≡ {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ = +-comm (size t₁) (size t₂)
size≡ {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} assocl₊ = 
  sym (+-assoc (size t₁) (size t₂) (size t₃))
size≡ {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} assocr₊ = 
  +-assoc (size t₁) (size t₂) (size t₃)
size≡ {TIMES ONE t} {.t} unite⋆ = +-right-identity (size t)
size≡ {t} {TIMES ONE .t} uniti⋆ = sym (+-right-identity (size t))
size≡ {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = *-comm (size t₁) (size t₂)
size≡ {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} assocl⋆ = 
  sym (*-assoc (size t₁) (size t₂) (size t₃))
size≡ {TIMES (TIMES t₁ t₂) t₃} {TIMES .t₁ (TIMES .t₂ .t₃)} assocr⋆ = 
  *-assoc (size t₁) (size t₂) (size t₃)
size≡ {TIMES .ZERO t} {ZERO} distz = refl
size≡ {ZERO} {TIMES ZERO t} factorz = refl
size≡ {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} dist = 
  distribʳ-*-+ (size t₃) (size t₁) (size t₂)
size≡ {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} {TIMES (PLUS .t₁ .t₂) .t₃} factor = 
  sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂))
size≡ {t} {.t} id⟷ = refl
size≡ (c₁ ◎ c₂) = trans (size≡ c₁) (size≡ c₂)
size≡ {PLUS t₁ t₂} {PLUS t₃ t₄} (c₁ ⊕ c₂) = cong₂ _+_ (size≡ c₁) (size≡ c₂)
size≡ {TIMES t₁ t₂} {TIMES t₃ t₄} (c₁ ⊗ c₂) = cong₂ _*_ (size≡ c₁) (size≡ c₂)
size≡ {PLUS ONE ONE} {BOOL} foldBool = refl
size≡ {BOOL} {PLUS ONE ONE} unfoldBool = refl

-- All proofs about sizes are "the same"

size∼ : {t₁ t₂ : U} → (c₁ c₂ : t₁ ⟷ t₂) → (size≡ c₁ ≡ size≡ c₂)
size∼ c₁ c₂ = proof-irrelevance (size≡ c₁) (size≡ c₂)

------------------------------------------------------------------------------
-- Examples of Pi programs

-- Nicer syntax that shows intermediate values instead of the above
-- point-free notation of permutations

infixr 2  _⟷⟨_⟩_   
infix  2  _□       

_⟷⟨_⟩_ : (t₁ : U) {t₂ : U} {t₃ : U} → 
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃) 
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U) → {t : U} → (t ⟷ t)
_□ t = id⟷

-- calculate and print specification of a combinator

spec : {t₁ t₂ : U} → (t₁ ⟷ t₂) → Vec (⟦ t₁ ⟧ × ⟦ t₂ ⟧) (size t₁)
spec {t₁} {t₂} c = mapV (λ v₁ → (v₁ , eval c v₁)) (utoVec t₁)

-- Many ways of negating a BOOL. Again, it is absolutely critical that there
-- is NO path between false⟷ and true⟷. These permutations instead are based
-- on paths between x and neg (neg x) which are the trivial paths on each of
-- the two points in BOOL.

NOT : BOOL ⟷ BOOL
NOT = unfoldBool ◎ swap₊ ◎ foldBool
-- spec: (false , true) ∷ (true , false) ∷ []

NEG1 NEG2 NEG3 NEG4 NEG5 : BOOL ⟷ BOOL
NEG1 = unfoldBool ◎ swap₊ ◎ foldBool
-- spec: (false , true) ∷ (true , false) ∷ []
NEG2 = id⟷ ◎ NOT 
-- spec: (false , true) ∷ (true , false) ∷ []
NEG3 = NOT ◎ NOT ◎ NOT 
-- spec: (false , true) ∷ (true , false) ∷ []
NEG4 = NOT ◎ id⟷
-- spec: (false , true) ∷ (true , false) ∷ []
NEG5 = uniti⋆ ◎ swap⋆ ◎ (NOT ⊗ id⟷) ◎ swap⋆ ◎ unite⋆
-- spec: (false , true) ∷ (true , false) ∷ []

-- CNOT

CNOT : BOOL² ⟷ BOOL²
CNOT = TIMES BOOL BOOL
         ⟷⟨ unfoldBool ⊗ id⟷ ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ dist ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT) ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ factor ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ foldBool ⊗ id⟷ ⟩
       TIMES BOOL BOOL □
  where x = ONE; y = ONE
-- spec: 
-- ((false , false) , false , false) ∷
-- ((false , true)  , false , true)  ∷
-- ((true  , false) , true  , true)  ∷
-- ((true  , true)  , true  , false) ∷ []

-- TOFFOLI

TOFFOLI : TIMES BOOL BOOL² ⟷ TIMES BOOL BOOL²
TOFFOLI = TIMES BOOL BOOL² 
            ⟷⟨ unfoldBool ⊗ id⟷ ⟩
          TIMES (PLUS x y) BOOL² 
            ⟷⟨ dist ⟩
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩ 
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ factor ⟩
          TIMES (PLUS x y) BOOL²
            ⟷⟨ foldBool ⊗ id⟷ ⟩
         TIMES BOOL BOOL² □
  where x = ONE; y = ONE
-- spec:
-- ((false , false , false) , false , false , false) ∷
-- ((false , false , true)  , false , false , true)  ∷
-- ((false , true  , false) , false , true  , false) ∷
-- ((false , true  , true)  , false , true  , true)  ∷
-- ((true  , false , false) , true  , false , false) ∷
-- ((true  , false , true)  , true  , false , true)  ∷
-- ((true  , true  , false) , true  , true  , true)  ∷
-- ((true  , true  , true)  , true  , true  , false) ∷ []

-- Swaps for the type 1+(1+1)
-- We have three values in the type 1+(1+1) 
-- Let's call them a, b, and c
-- There 6 permutations. Using the swaps below we can express every permutation:
-- a b c id⟷
-- a c b SWAP23
-- b a c SWAP12
-- b c a ROTL
-- c a b ROTR
-- c b a SWAP13

SWAP12 SWAP23 SWAP13 ROTL ROTR : 
  PLUS ONE (PLUS ONE ONE) ⟷ PLUS ONE (PLUS ONE ONE)
SWAP12 = assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊
-- spec: 
-- (inj₁ tt        , inj₂ (inj₁ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₁ tt)        ∷ 
-- (inj₂ (inj₂ tt) , inj₂ (inj₂ tt)) ∷ []
SWAP23 = id⟷ ⊕ swap₊
-- spec: 
-- (inj₁ tt        , inj₁ tt)        ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₂ tt)) ∷
-- (inj₂ (inj₂ tt) , inj₂ (inj₁ tt)) ∷ []
SWAP13 = SWAP23 ◎ SWAP12 ◎ SWAP23 
-- spec: 
-- (inj₁ tt        , inj₂ (inj₂ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₁ tt)) ∷ 
-- (inj₂ (inj₂ tt) , inj₁ tt)        ∷ []
ROTR   = SWAP12 ◎ SWAP23
-- spec: 
-- (inj₁ tt        , inj₂ (inj₂ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₁ tt)        ∷ 
-- (inj₂ (inj₂ tt) , inj₂ (inj₁ tt)) ∷ []
ROTL   = SWAP13 ◎ SWAP23
-- spec: 
-- (inj₁ tt        , inj₂ (inj₁ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₂ tt)) ∷ 
-- (inj₂ (inj₂ tt) , inj₁ tt)        ∷ []

-- The Peres gate is a universal gate: it takes three inputs a, b, and c, and
-- produces a, a xor b, (a and b) xor c

PERES : TIMES (TIMES BOOL BOOL) BOOL ⟷ TIMES (TIMES BOOL BOOL) BOOL
PERES = (id⟷ ⊗ NOT) ◎ assocr⋆ ◎ (id⟷ ⊗ swap⋆) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ (NOT ⊗ id⟷)) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ swap⋆) ◎ (id⟷ ⊗ (NOT ⊗ id⟷)) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ (NOT ⊗ id⟷)) ◎ assocl⋆
-- spec:
-- (((false , false) , false) , (false , false) , false) ∷
-- (((false , false) , true)  , (false , false) , true)  ∷
-- (((false , true)  , false) , (false , true)  , false) ∷
-- (((false , true)  , true)  , (false , true)  , true)  ∷
-- (((true  , false) , false) , (true  , true)  , false) ∷
-- (((true  , false) , true)  , (true  , true)  , true)  ∷
-- (((true  , true)  , false) , (true  , false) , true)  ∷
-- (((true  , true)  , true)  , (true  , false) , false) ∷ []

-- A reversible full adder: See http://arxiv.org/pdf/1008.3533.pdf
-- Input: (z, ((n1, n2), cin)))
-- Output (g1, (g2, (sum, cout)))
-- where sum = n1 xor n2 xor cin
-- and cout = ((n1 xor n2) and cin) xor (n1 and n2) xor z
FULLADDER : TIMES BOOL (TIMES (TIMES BOOL BOOL) BOOL) ⟷
            TIMES BOOL (TIMES BOOL (TIMES BOOL BOOL))
FULLADDER = 
  -- (z,((n1,n2),cin))
  swap⋆ ◎ 
  -- (((n1,n2),cin),z)
  (swap⋆ ⊗ id⟷) ◎ 
  -- ((cin,(n1,n2)),z)
  assocr⋆ ◎ 
  -- (cin,((n1,n2),z))
  swap⋆ ◎ 
  -- (((n1,n2),z),cin)
  (PERES ⊗ id⟷) ◎     
  -- (((n1,n1 xor n2),(n1 and n2) xor z),cin) 
  assocr⋆ ◎ 
  -- ((n1,n1 xor n2),((n1 and n2) xor z,cin))
  (id⟷ ⊗ swap⋆) ◎ 
  -- ((n1,n1 xor n2),(cin,(n1 and n2) xor z))
  assocr⋆ ◎ 
  -- (n1,(n1 xor n2,(cin,(n1 and n2) xor z)))
  (id⟷ ⊗ assocl⋆) ◎ 
  -- (n1,((n1 xor n2,cin),(n1 and n2) xor z))
  (id⟷ ⊗ PERES) ◎ 
  -- (n1,((n1 xor n2,n1 xor n2 xor cin),
  --      ((n1 xor n2) and cin) xor (n1 and n2) xor z))
  (id⟷ ⊗ assocr⋆)
  -- (n1,(n1 xor n2,
  --      (n1 xor n2 xor cin,((n1 xor n2) and cin) xor (n1 and n2) xor z)))
-- spec: 
-- ((false , (false , false) , false) , false , false , false , false) ∷
-- ((false , (false , false) , true)  , false , false , true  , false) ∷
-- ((false , (false , true)  , false) , false , true  , true  , false) ∷
-- ((false , (false , true)  , true)  , false , true  , false , true)  ∷
-- ((false , (true  , false) , false) , true  , true  , true  , false) ∷
-- ((false , (true  , false) , true)  , true  , true  , false , true)  ∷
-- ((false , (true  , true)  , false) , true  , false , false , true)  ∷
-- ((false , (true  , true)  , true)  , true  , false , true  , true)  ∷
-- ((true  , (false , false) , false) , false , false , false , true)  ∷
-- ((true  , (false , false) , true)  , false , false , true  , true)  ∷
-- ((true  , (false , true)  , false) , false , true  , true  , true)  ∷
-- ((true  , (false , true)  , true)  , false , true  , false , false) ∷
-- ((true  , (true  , false) , false) , true  , true  , true  , true)  ∷
-- ((true  , (true  , false) , true)  , true  , true  , false , false) ∷
-- ((true  , (true  , true)  , false) , true  , false , false , false) ∷
-- ((true  , (true  , true)  , true)  , true  , false , true  , false) ∷ []

------------------------------------------------------------------------------
-- Every permutation has an inverse. There are actually many syntactically
-- different inverses but they are all equivalent.

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊    = uniti₊
! uniti₊    = unite₊
! swap₊     = swap₊
! assocl₊   = assocr₊
! assocr₊   = assocl₊
! unite⋆    = uniti⋆
! uniti⋆    = unite⋆
! swap⋆     = swap⋆
! assocl⋆   = assocr⋆
! assocr⋆   = assocl⋆
! distz     = factorz
! factorz   = distz
! dist      = factor 
! factor    = dist
! id⟷      = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁ 
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)
! unfoldBool = foldBool
! foldBool   = unfoldBool

!! : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! (! c) ≡ c
!! {c = unite₊}  = refl
!! {c = uniti₊}  = refl
!! {c = swap₊}   = refl
!! {c = assocl₊} = refl
!! {c = assocr₊} = refl
!! {c = unite⋆}  = refl
!! {c = uniti⋆}  = refl
!! {c = swap⋆}   = refl
!! {c = assocl⋆} = refl
!! {c = assocr⋆} = refl
!! {c = distz}   = refl
!! {c = factorz} = refl
!! {c = dist}    = refl
!! {c = factor}  = refl
!! {c = id⟷}    = refl
!! {c = c₁ ◎ c₂} = 
  begin (! (! (c₁ ◎ c₂))
           ≡⟨ refl ⟩
         ! (! c₂ ◎ ! c₁)
           ≡⟨ refl ⟩ 
         ! (! c₁) ◎ ! (! c₂)
           ≡⟨ cong₂ _◎_ (!! {c = c₁}) (!! {c = c₂}) ⟩ 
         c₁ ◎ c₂ ∎)
  where open ≡-Reasoning
!! {c = c₁ ⊕ c₂} = 
  begin (! (! (c₁ ⊕ c₂))
           ≡⟨ refl ⟩
         ! (! c₁) ⊕ ! (! c₂)
           ≡⟨ cong₂ _⊕_ (!! {c = c₁}) (!! {c = c₂}) ⟩ 
         c₁ ⊕ c₂ ∎)
  where open ≡-Reasoning
!! {c = c₁ ⊗ c₂} = 
  begin (! (! (c₁ ⊗ c₂))
           ≡⟨ refl ⟩
         ! (! c₁) ⊗ ! (! c₂)
           ≡⟨ cong₂ _⊗_ (!! {c = c₁}) (!! {c = c₂}) ⟩ 
         c₁ ⊗ c₂ ∎)
  where open ≡-Reasoning
!! {c = unfoldBool} = refl
!! {c = foldBool}   = refl

------------------------------------------------------------------------------
-- Semantic representations of permutations

-- One possibility of course is to represent them as functions but
-- this is a poor representation and eventually requires function
-- extensionality. 

-- Representation I:
-- Our first representation of a permutation is as a product of
-- "transpositions." This product is not commutative; we apply it from
-- left to right. Because we eventually want to normalize permutations
-- to some canonical representation, we insist that the first
-- component of a transposition is always ≤ than the second

infix 90 _X_

data Transposition (n : ℕ) : Set where
  _X_ : (i j : Fin n) → {p : toℕ i ≤ toℕ j} → Transposition n

mkTransposition : {n : ℕ} → (i j : Fin n) → Transposition n
mkTransposition {n} i j with toℕ i ≤? toℕ j 
... | yes p = _X_ i j {p}
... | no p  = _X_ j i {i≰j→j≤i (toℕ i) (toℕ j) p}

Transposition* : ℕ → Set
Transposition* n = List (Transposition n) 

showTransposition* : ∀ {n} → Transposition* n → List String
showTransposition* = 
  mapL (λ { (i X j) → show (toℕ i) ++S " X " ++S show (toℕ j) })

actionπ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Transposition* n → Vec A n → Vec A n
actionπ π vs = foldl swapX vs π
  where 
    swapX : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vec A n → Transposition n → Vec A n  
    swapX vs (i X j) = (vs [ i ]≔ lookup j vs) [ j ]≔ lookup i vs

-- Representation II:
-- This is also a product of transpositions but the transpositions are such
-- that the first component is always < the second, i.e., we got rid of trivial
-- transpositions that swap an element with itself

data Transposition< (n : ℕ) : Set where
  _X!_ : (i j : Fin n) → {p : toℕ i < toℕ j} → Transposition< n

Transposition<* : ℕ → Set
Transposition<* n = List (Transposition< n) 

showTransposition<* : ∀ {n} → Transposition<* n → List String
showTransposition<* = 
  mapL (λ { (i X! j) → show (toℕ i) ++S " X! " ++S show (toℕ j) })

filter= : {n : ℕ} → Transposition* n → Transposition<* n
filter= [] = []
filter= (_X_ i j {p≤} ∷ π) with toℕ i ≟ toℕ j
... | yes p= = filter= π 
... | no p≠ = _X!_ i j {i≠j∧i≤j→i<j (toℕ i) (toℕ j) p≠ p≤}  ∷ filter= π 

-- Representation III
-- This is the 2 line Cauchy representation. The first line is in
-- canonical order and implicit in the indices of the vector

Cauchy : ℕ → Set
Cauchy n = Vec (Fin n) n

-- Representation IV
-- A product of cycles where each cycle is a non-empty sequence of indices

Cycle : ℕ → Set
Cycle n = List⁺ (Fin n)

Cycle* : ℕ → Set
Cycle* n = List (Cycle n)

-- convert a cycle to a product of transpositions

cycle→transposition* : ∀ {n} → Cycle n → Transposition* n
cycle→transposition* (i , []) = []
cycle→transposition* (i , (j ∷ ns)) = 
  mkTransposition i j ∷ cycle→transposition* (i , ns)

cycle*→transposition* : ∀ {n} → Cycle* n → Transposition* n
cycle*→transposition* cs = concatMap cycle→transposition* cs

-- Ex:

cycleEx1 cycleEx2 : Cycle 5
-- cycleEx1 (0 1 2 3 4) which rotates right
cycleEx1 = inject+ 4 (fromℕ 0) , 
           inject+ 3 (fromℕ 1) ∷
           inject+ 2 (fromℕ 2) ∷
           inject+ 1 (fromℕ 3) ∷
           inject+ 0 (fromℕ 4) ∷ []
-- cycleEx1 (0 4 3 2 1) which rotates left
cycleEx2 = inject+ 4 (fromℕ 0) , 
           inject+ 0 (fromℕ 4) ∷
           inject+ 1 (fromℕ 3) ∷
           inject+ 2 (fromℕ 2) ∷
           inject+ 3 (fromℕ 1) ∷ []
cycleEx1→transposition* cycleEx2→transposition* : List String
cycleEx1→transposition* = showTransposition* (cycle→transposition* cycleEx1)
-- 0 X 1 ∷ 0 X 2 ∷ 0 X 3 ∷ 0 X 4 ∷ []
-- actionπ (cycle→transposition* cycleEx1) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
-- 4 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
cycleEx2→transposition* = showTransposition* (cycle→transposition* cycleEx2)
-- 0 X 4 ∷ 0 X 3 ∷ 0 X 2 ∷ 0 X 1 ∷ []
-- actionπ (cycle→transposition* cycleEx2) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
-- 1 ∷ 2 ∷ 3 ∷ 4 ∷ 0 ∷ []

-- Convert from Cauchy 2 line representation to product of cycles

-- Helper that checks if there is a cycle that starts at i
-- Returns the cycle containing i and the rest of the permutation
-- without that cycle

findCycle : ∀ {n} → Fin n → Cycle* n →  Maybe (Cycle n × Cycle* n)
findCycle i [] = nothing
findCycle i (c ∷ cs) with toℕ i ≟ toℕ (head c)
findCycle i (c ∷ cs) | yes _ = just (c , cs)
findCycle i (c ∷ cs) | no _ = 
  maybe′ (λ { (c' , cs') → just (c' , c ∷ cs') }) nothing (findCycle i cs)

-- Another helper that repeatedly tries to merge smaller cycles

{-# NO_TERMINATION_CHECK #-}
mergeCycles : ∀ {n} → Cycle* n → Cycle* n
mergeCycles [] = []
mergeCycles (c ∷ cs) with findCycle (last c) cs
mergeCycles (c ∷ cs) | nothing = c ∷ mergeCycles cs
mergeCycles (c ∷ cs) | just (c' , cs') = mergeCycles ((c ⁺++ ntail c') ∷ cs')

-- To convert a Cauchy representation to a product of cycles, just create 
-- a cycle of size 2 for each entry and then merge the cycles

cauchy→cycle* : ∀ {n} → Cauchy n → Cycle* n
cauchy→cycle* {n} perm = 
  mergeCycles (toList (zipWith (λ i j → i ∷⁺ [ j ]) (allFin n) perm))

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
cauchyEx1→transposition* cauchyEx2→transposition* : List String
cauchyEx1→transposition* = 
  showTransposition* (cycle*→transposition* (cauchy→cycle* cauchyEx1))
-- 0 X 2 ∷ 0 X 4 ∷ 0 X 1 ∷ 0 X 0 ∷ 3 X 3 ∷ 5 X 5 ∷ []
-- actionπ (cycle*→transposition* (cauchy→cycle* cauchyEx1)) 
--   (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
-- 1 ∷ 4 ∷ 0 ∷ 3 ∷ 2 ∷ 5 ∷ []
cauchyEx2→transposition* = 
  showTransposition* (cycle*→transposition* (cauchy→cycle* cauchyEx2))
-- 0 X 3 ∷ 0 X 0 ∷ 1 X 2 ∷ 1 X 1 ∷ 4 X 5 ∷ 4 X 4 ∷ []
-- actionπ (cycle*→transposition* (cauchy→cycle* cauchyEx2)) 
--   (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
-- 3 ∷ 2 ∷ 1 ∷ 0 ∷ 5 ∷ 4 ∷ []

-- Cauchy to product of transpostions

cauchy→transposition* : ∀ {n} → Cauchy n → Transposition* n
cauchy→transposition* = cycle*→transposition* ∘ cauchy→cycle*

------------------------------------------------------------------------------
-- Elementary permutations in the Cauchy representation

idcauchy : (n : ℕ) → Cauchy n
idcauchy = allFin 

-- swap the first m elements with the last n elements
-- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
-- ==> 
-- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

swap+cauchy : (m n : ℕ) → Cauchy (m + n)
swap+cauchy m n with splitAt n (allFin (n + m)) | splitAt m (allFin (m + n))
... | (zeron , (nsum , _)) | (zerom , (msum , _)) = 
    (subst (λ s → Vec (Fin s) m) (+-comm n m) nsum) ++V 
    (subst (λ s → Vec (Fin s) n) (+-comm n m) zeron)

-- Ex: 

swap+π : (m n : ℕ) → Transposition* (m + n)
swap+π m n = cauchy→transposition* (swap+cauchy m n)
swap11 swap21 swap32 : List String
swap11 = showTransposition* (swap+π 1 1)
-- 0 X 1 ∷ 0 X 0 ∷ []
-- actionπ (swap+π 1 1) ("a" ∷ "b" ∷ [])
-- "b" ∷ "a" ∷ []
swap21 = showTransposition* (swap+π 2 1)
-- 0 X 1 ∷ 0 X 2 ∷ 0 X 0 ∷ []
-- actionπ (swap+π 2 1) ("a" ∷ "b" ∷ "c" ∷ [])
-- "c" ∷ "a" ∷ "b" ∷ []
swap32 = showTransposition* (swap+π 3 2)
-- 0 X 2 ∷ 0 X 4 ∷ 0 X 1 ∷ 0 X 3 ∷ 0 X 0 ∷ []
-- actionπ (swap+π 3 2) ("a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ [])
-- "d" ∷ "e" ∷ "a" ∷ "b" ∷ "c" ∷ []

-- Sequential composition

scompcauchy : ∀ {n} → Cauchy n → Cauchy n → Cauchy n
scompcauchy {n} perm₁ perm₂ = 
  tabulate (λ i → lookup (lookup i perm₁) perm₂)

scompid : ∀ {n} → (f : Cauchy n) → scompcauchy f (idcauchy n) ≡ f
scompid {n} perm = 
  begin (scompcauchy perm (idcauchy n)
           ≡⟨ refl ⟩ 
         tabulate (λ i → lookup (lookup i perm) (allFin n))
           ≡⟨ {!cong tabulate (EXT (lookup-allFin i)!} ⟩ 
         tabulate (λ i → lookup i perm)
           ≡⟨ tabulate∘lookup perm ⟩ 
         perm ∎)
  where open ≡-Reasoning

-- Parallel additive composition 
-- append both permutations but adjust the indices in the second
-- permutation by the size of the first type so that it acts on the
-- second part of the vector

pcompcauchy : ∀ {m n} → Cauchy m → Cauchy n → Cauchy (m + n)
pcompcauchy {m} {n} α β = mapV (inject+ n) α ++V mapV (raise m) β

-- Ex: 

pcompπ : ∀ {m n} → Cauchy m → Cauchy n → Transposition* (m + n)
pcompπ α β = cauchy→transposition* (pcompcauchy α β)
swap11+21 swap21+11 : List String
swap11+21 = showTransposition* (pcompπ (swap+cauchy 1 1) (swap+cauchy 2 1))
-- 0 X 1 ∷ 0 X 0 ∷ 2 X 3 ∷ 2 X 4 ∷ 2 X 2 ∷ []
-- actionπ (pcompπ (swap+cauchy 1 1) (swap+cauchy 2 1)) 
--   ("a" ∷ "b" ∷ "1" ∷ "2" ∷ "3" ∷ [])
-- "b" ∷ "a" ∷ "3" ∷ "1" ∷ "2" ∷ []
swap21+11 = showTransposition* (pcompπ (swap+cauchy 2 1) (swap+cauchy 1 1))
-- 0 X 1 ∷ 0 X 2 ∷ 0 X 0 ∷ 3 X 4 ∷ 3 X 3 ∷ []
-- actionπ (pcompπ (swap+cauchy 2 1) (swap+cauchy 1 1)) 
--   ("1" ∷ "2" ∷ "3" ∷ "a" ∷ "b" ∷ [])
-- "3" ∷ "1" ∷ "2" ∷ "b" ∷ "a" ∷ []

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

-- Ex:

tcompπ : ∀ {m n} → Cauchy m → Cauchy n → Transposition* (m * n)
tcompπ α β = cauchy→transposition* (tcompcauchy α β)
swap21*swap11 : List String
swap21*swap11 = showTransposition* (tcompπ (swap+cauchy 2 1) (swap+cauchy 1 1))
-- 0 X 3 ∷ 0 X 4 ∷ 0 X 1 ∷ 0 X 2 ∷ 0 X 5 ∷ 0 X 0 ∷ []
-- Recall (swap+π 2 1)
-- 0 X 1 ∷ 0 X 2 ∷ 0 X 0 ∷ []                                                   
-- actionπ (swap+π 2 1) ("a" ∷ "b" ∷ "c" ∷ [])
-- "c" ∷ "a" ∷ "b" ∷ []
-- Recall (swap+π 1 1)
-- 0 X 1 ∷ 0 X 0 ∷ []
-- actionπ (swap+π 1 1) ("1" ∷ "2" ∷ [])
-- "2" ∷ "1" ∷ []
-- Tensor tensorvs 
-- ("a" , "1") ∷ ("a" , "2") ∷
-- ("b" , "1") ∷ ("b" , "2") ∷ 
-- ("c" , "1") ∷ ("c" , "2") ∷ []
-- actionπ (tcompπ (swap+cauchy 2 1) (swap+cauchy 1 1)) tensorvs
-- ("c" , "2") ∷ ("c" , "1") ∷
-- ("a" , "2") ∷ ("a" , "1") ∷ 
-- ("b" , "2") ∷ ("b" , "1") ∷ []

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

-- Ex:

swap⋆π : (m n : ℕ) → Transposition* (m * n) 
swap⋆π m n = cauchy→transposition* (swap⋆cauchy m n)
swap3x2→2x3 : List String
swap3x2→2x3 = showTransposition* (swap⋆π 3 2)
-- 0 X 0 ∷ 1 X 3 ∷ 1 X 4 ∷ 1 X 2 ∷ 1 X 1 ∷ 5 X 5 ∷ []
-- Let vs3x2 = 
-- ("a" , 1) ∷ ("a" , 2) ∷ 
-- ("b" , 1) ∷ ("b" , 2) ∷ 
-- ("c" , 1) ∷ ("c" , 2) ∷ []
-- actionπ (swap⋆π 3 2) vs3x2
-- ("a" , 1) ∷ ("b" , 1) ∷ ("c" , 1) ∷ 
-- ("a" , 2) ∷ ("b" , 2) ∷ ("c" , 2) ∷ []

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes a permutation.

c2cauchy : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Cauchy (size t₁)
c2cauchy {PLUS ZERO t} unite₊ = idcauchy (size t)
c2cauchy {t} uniti₊ = idcauchy (size t)
c2cauchy {PLUS t₁ t₂} swap₊ = swap+cauchy (size t₁) (size t₂)
c2cauchy {PLUS t₁ (PLUS t₂ t₃)} assocl₊ = 
  idcauchy (size t₁ + (size t₂ + size t₃))
c2cauchy {PLUS (PLUS t₁ t₂) t₃} assocr₊ = 
  idcauchy ((size t₁ + size t₂) + size t₃)
c2cauchy {TIMES ONE t} unite⋆ = 
  subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t))
c2cauchy {t} uniti⋆ = idcauchy (size t)
c2cauchy {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = swap⋆cauchy (size t₁) (size t₂)
c2cauchy {TIMES t₁ (TIMES t₂ t₃)} assocl⋆ = 
  idcauchy (size t₁ * (size t₂ * size t₃))
c2cauchy {TIMES (TIMES t₁ t₂) t₃} assocr⋆ = 
  idcauchy ((size t₁ * size t₂) * size t₃)
c2cauchy {TIMES ZERO t} distz = []
c2cauchy factorz = []
c2cauchy {TIMES (PLUS t₁ t₂) t₃} dist = 
  idcauchy ((size t₁ + size t₂) * size t₃)
c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} factor = 
  idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))
c2cauchy {t} id⟷  = idcauchy (size t)
c2cauchy (c₁ ◎ c₂) = 
  scompcauchy 
    (c2cauchy c₁) 
    (subst Cauchy (sym (size≡ c₁)) (c2cauchy c₂)) 
c2cauchy (c₁ ⊕ c₂) = pcompcauchy (c2cauchy c₁) (c2cauchy c₂) 
c2cauchy (c₁ ⊗ c₂) = tcompcauchy (c2cauchy c₁) (c2cauchy c₂)  
c2cauchy unfoldBool = idcauchy 2
c2cauchy foldBool   = idcauchy 2

c2π : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Transposition* (size t₁)
c2π = cauchy→transposition* ∘ c2cauchy

-- Convenient way of seeing c : t₁ ⟷ t₂ as a permutation

showπ : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Vec (⟦ t₁ ⟧ × ⟦ t₂ ⟧) (size t₁) 
showπ {t₁} {t₂} c = 
  let vs₁ = utoVec t₁
      vs₂ = utoVec t₂
  in zip (actionπ (c2π c) vs₁) (subst (Vec ⟦ t₂ ⟧) (sym (size≡ c)) vs₂)

-- Examples

NEG1π NEG2π NEG3π NEG4π NEG5π : Vec (⟦ BOOL ⟧ × ⟦ BOOL ⟧) 2
NEG1π = showπ NEG1
-- (true , false) ∷ (false , true) ∷ []
NEG2π = showπ NEG2  
-- (true , false) ∷ (false , true) ∷ []
NEG3π = showπ NEG3  
-- (true , false) ∷ (false , true) ∷ []
NEG4π = showπ NEG4
-- (true , false) ∷ (false , true) ∷ []
NEG5π = showπ NEG5 
-- (true , false) ∷ (false , true) ∷ []

cnotπ : Vec (⟦ BOOL² ⟧ × ⟦ BOOL² ⟧) 4 
cnotπ = showπ {BOOL²} {BOOL²} CNOT
-- ((false , false) , (false , false)) ∷
-- ((false , true)  , (false , true))  ∷
-- ((true  , true)  , (true  , false)) ∷
-- ((true  , false) , (true  , true))  ∷ []

toffoliπ : Vec (⟦ TIMES BOOL BOOL² ⟧ × ⟦ TIMES BOOL BOOL² ⟧) 8  
toffoliπ = showπ {TIMES BOOL BOOL²} {TIMES BOOL BOOL²} TOFFOLI
-- ((false , false , false) , (false , false , false)) ∷
-- ((false , false , true)  , (false , false , true))  ∷
-- ((false , true  , false) , (false , true  , false)) ∷
-- ((false , true  , true)  , (false , true  , true))  ∷
-- ((true  , false , false) , (true  , false , false)  ∷
-- ((true  , false , true)  , (true  , false , true))  ∷
-- ((true  , true  , true)  , (true  , true  , false)) ∷
-- ((true  , true  , false) , (true  , true  , true))  ∷ []

-- The elements of PLUS ONE (PLUS ONE ONE) in canonical order are:
-- inj₁ tt
-- inj₂ (inj₁ tt)
-- inj₂ (inj₂ tt)

id3π swap12π swap23π swap13π rotlπ rotrπ : 
  Vec (⟦ PLUS ONE (PLUS ONE ONE) ⟧ × ⟦ PLUS ONE (PLUS ONE ONE) ⟧) 3
id3π    = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} id⟷
-- (inj₁ tt , inj₁ tt) ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₁ tt)) ∷
-- (inj₂ (inj₂ tt) , inj₂ (inj₂ tt)) ∷ []
swap12π = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} SWAP12
-- (inj₂ (inj₁ tt) , inj₁ tt) ∷
-- (inj₁ tt , inj₂ (inj₁ tt)) ∷ 
-- (inj₂ (inj₂ tt) , inj₂ (inj₂ tt)) ∷ []
swap23π = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} SWAP23
-- (inj₁ tt , inj₁ tt) ∷
-- (inj₂ (inj₂ tt) , inj₂ (inj₁ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₂ tt)) ∷ []
swap13π = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} SWAP13
-- (inj₂ (inj₂ tt) , inj₁ tt) ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₁ tt)) ∷ 
-- (inj₁ tt , inj₂ (inj₂ tt)) ∷ []
rotrπ   = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} ROTR
-- (inj₂ (inj₁ tt) , inj₁ tt) ∷
-- (inj₂ (inj₂ tt) , inj₂ (inj₁ tt)) ∷ 
-- (inj₁ tt , inj₂ (inj₂ tt)) ∷ []
rotlπ   = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} ROTL
-- (inj₂ (inj₂ tt) , inj₁ tt) ∷
-- (inj₁ tt , inj₂ (inj₁ tt)) ∷ 
-- (inj₂ (inj₁ tt) , inj₂ (inj₂ tt)) ∷ []

peresπ : Vec (((Bool × Bool) × Bool) × ((Bool × Bool) × Bool)) 8
peresπ = showπ PERES
-- (((false , false) , false) , (false , false) , false) ∷
-- (((false , false) , true)  , (false , false) , true)  ∷
-- (((false , true)  , false) , (false , true)  , false) ∷
-- (((false , true)  , true)  , (false , true)  , true)  ∷
-- (((true  , true)  , true)  , (true  , false) , false) ∷
-- (((true  , true)  , false) , (true  , false) , true)  ∷
-- (((true  , false) , false) , (true  , true)  , false) ∷
-- (((true  , false) , true)  , (true  , true)  , true)  ∷ []

fulladderπ : 
  Vec ((Bool × ((Bool × Bool) × Bool)) × (Bool × (Bool × (Bool × Bool)))) 16
fulladderπ = showπ FULLADDER
-- ((false , (false , false) , false) , false , false , false , false) ∷
-- ((true  , (false , false) , false) , false , false , false , true)  ∷
-- ((false , (false , false) , true)  , false , false , true  , false) ∷
-- ((true  , (false , false) , true)  , false , false , true  , true)  ∷
-- ((false , (false , true)  , false) , false , true  , true  , false) ∷
-- ((false , (false , true)  , true)  , false , true  , false , true)  ∷
-- ((true  , (false , true)  , true)  , false , true  , false , false) ∷
-- ((true  , (false , true)  , false) , false , true  , true  , true)  ∷
-- ((true  , (true  , true)  , false) , true  , false , false , false) ∷
-- ((false , (true  , true)  , false) , true  , false , false , true)  ∷
-- ((true  , (true  , true)  , true)  , true  , false , true  , false) ∷ 
-- ((false , (true  , true)  , true)  , true  , false , true  , true)  ∷
-- ((true  , (true  , false) , true)  , true  , true  , false , false) ∷
-- ((false , (true  , false) , true)  , true  , true  , false , true)  ∷
-- ((false , (true  , false) , false) , true  , true  , true  , false) ∷
-- ((true  , (true  , false) , false) , true  , true  , true  , true)  ∷ []
-- which agrees with spec.

------------------------------------------------------------------------------
-- Normalization

-- We sort the list of transpositions using a variation of bubble
-- sort. Like in the conventional bubble sort we look at pairs of
-- transpositions and swap them if they are out of order but if we
-- encounter (i X j) followed by (i X j) we remove both. 

-- one pass of bubble sort
-- goal is to reach a sorted sequene with no repeats in the first position
-- Ex: (0 X 2) ∷ (3 X 4) ∷ (4 X 6) ∷ (5 X 6)

-- There is probably lots of room for improvement. Here is the idea.
-- We take a list of transpositions (a_i X b_i) where a_i < b_i and keep
-- looking at adjacent pairs doing the following transformations:
-- 
-- A.  (a X b) (a X b) => id
-- B.  (a X b) (c X d) => (c X d) (a X b) if c < a
-- C.  (a X b) (c X b) => (c X a) (a X b) if c < a
-- D.  (a X b) (c X a) => (c X b) (a X b) 
-- E.  (a X b) (a X d) => (a X d) (b X d) if b < d
-- F.  (a X b) (a X d) => (a X d) (d X b) if d < b
-- 
-- The point is that we get closer and closer to the following
-- invariant. For any two adjacent transpositions (a X b) (c X d) we have
-- that a < c. Transformations B, C, and D rewrite anything in which a > c.
-- Transformations A, E, and F rewrite anything in which a = c. Termination 
-- is subtle clearly.
-- 
-- New strategy to implement: So could we index things so that a first set of
-- (up to) n passes 'bubble down' (0 X a) until there is only one left at the
-- root, then recurse on the tail to 'bubble down' (1 X b)'s [if any]? That
-- would certainly ensure termination.

{-# NO_TERMINATION_CHECK #-}
bubble : ∀ {n} → Transposition<* n → Transposition<* n
bubble [] = []
bubble (x ∷ []) = x ∷ []
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π) 
--
-- check every possible equality between the indices
--
  with toℕ i ≟ toℕ k | toℕ i ≟ toℕ l | toℕ j ≟ toℕ k | toℕ j ≟ toℕ l
--
-- get rid of a bunch of impossible cases given that i < j and k < l
--
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | _ | yes j≡k | yes j≡l 
  with trans (sym j≡k) (j≡l) | i<j→i≠j {toℕ k} {toℕ l} k<l
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | _ | yes j≡k | yes j≡l
  | k≡l | ¬k≡l with ¬k≡l k≡l
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | _ | yes j≡k | yes j≡l
  | k≡l | ¬k≡l | ()
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | yes i≡l | _ | yes j≡l 
  with trans i≡l (sym j≡l) | i<j→i≠j {toℕ i} {toℕ j} i<j
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | yes i≡l | _ | yes j≡l 
  | i≡j | ¬i≡j with ¬i≡j i≡j
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | yes i≡l | _ | yes j≡l 
  | i≡j | ¬i≡j | ()
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | _ | yes j≡k | _
  with trans i≡k (sym j≡k) | i<j→i≠j {toℕ i} {toℕ j} i<j 
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | _ | yes j≡k | _
  | i≡j | ¬i≡j with ¬i≡j i≡j
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | _ | yes j≡k | _
  | i≡j | ¬i≡j | ()
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | yes i≡l | _ | _
  with trans (sym i≡k) i≡l | i<j→i≠j {toℕ k} {toℕ l} k<l 
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | yes i≡l | _ | _
  | k≡l | ¬k≡l with ¬k≡l k≡l
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | yes i≡l | _ | _
  | k≡l | ¬k≡l | ()
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | yes i≡l | yes j≡k | _
  with subst₂ _<_ (sym j≡k) (sym i≡l) k<l | i<j→j≮i {toℕ i} {toℕ j} i<j
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | yes i≡l | yes j≡k | _
  | j<i | j≮i with j≮i j<i
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | _ | yes i≡l | yes j≡k | _
  | j<i | j≮i | ()
--
-- end of impossible cases
--
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l with toℕ i <? toℕ k
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l | yes i<k = 
  -- already sorted; no repeat in first position; skip and recur
  -- Ex: 2 X! 5 , 3 X! 4
    _X!_ i j {i<j} ∷ bubble (_X!_ k l {k<l} ∷ π)
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l | no i≮k = 
  -- Case B. 
  -- not sorted; no repeat in first position; no interference
  -- just slide one transposition past the other
  -- Ex: 2 X! 5 , 1 X! 4
  -- becomes 1 X! 4 , 2 X! 5
    _X!_ k l {k<l} ∷  bubble (_X!_ i j {i<j} ∷ π)
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | no ¬i≡l | no ¬j≡k | yes j≡l = 
  -- Case A. 
  -- transposition followed by its inverse; simplify by removing both
  -- Ex: 2 X! 5 , 2 X! 5
  -- becomes id and is deleted
  bubble π 
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l with toℕ i <? toℕ k 
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l | yes i<k = 
  -- already sorted; no repeat in first position; skip and recur
  -- Ex: 2 X! 5 , 3 X! 5 
    _X!_ i j {i<j} ∷ bubble (_X!_ k l {k<l} ∷ π)
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l | no i≮k = 
  _X!_ k i 
    {i≰j∧j≠i→j<i (toℕ i) (toℕ k) (i≮j∧i≠j→i≰j (toℕ i) (toℕ k) i≮k ¬i≡k) 
       (i≠j→j≠i (toℕ i) (toℕ k) ¬i≡k)} ∷
  bubble (_X!_ i j {i<j} ∷ π)
  -- Case C. 
  -- Ex: 2 X! 5 , 1 X! 5 
  -- becomes 1 X! 2 , 2 X! 5
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | yes j≡k | no ¬j≡l = 
  -- already sorted; no repeat in first position; skip and recur
  -- Ex: 2 X! 5 , 5 X! 6 
   _X!_ i j {i<j} ∷ bubble (_X!_ k l {k<l} ∷ π)
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | no ¬i≡k | yes i≡l | no ¬j≡k | no ¬j≡l = 
  -- Case D. 
  -- Ex: 2 X! 5 , 1 X! 2 
  -- becomes 1 X! 5 , 2 X! 5
  _X!_ k j {trans< (subst ((λ l → toℕ k < l)) (sym i≡l) k<l) i<j} ∷
  bubble (_X!_ i j {i<j} ∷ π)
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l with toℕ j <? toℕ l
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l | yes j<l =
  -- Case E. 
  -- Ex: 2 X! 5 , 2 X! 6
  -- becomes 2 X! 6 , 5 X! 6
  _X!_ k l {k<l} ∷ bubble (_X!_ j l {j<l} ∷ π)
bubble (_X!_ i j {i<j} ∷ _X!_ k l {k<l} ∷ π)
  | yes i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l | no j≮l = 
  -- Case F. 
  -- Ex: 2 X! 5 , 2 X! 3
  -- becomes 2 X! 3 , 3 X! 5 
  _X!_ k l {k<l} ∷ 
  bubble (_X!_ l j {i≰j∧j≠i→j<i (toℕ j) (toℕ l) 
                    (i≮j∧i≠j→i≰j (toℕ j) (toℕ l) j≮l ¬j≡l)
                    (i≠j→j≠i (toℕ j) (toℕ l) ¬j≡l)} ∷ π)

-- sorted and no repeats in first position

{-# NO_TERMINATION_CHECK #-}
canonical? : ∀ {n} → Transposition<* n → Bool
canonical? [] = true
canonical? (x ∷ []) = true
canonical? (i X! j ∷ k X! l ∷ π) with toℕ i <? toℕ k
canonical? (i X! j ∷ _X!_ k l {k<l}  ∷ π) | yes i<k = 
  canonical? (_X!_ k l {k<l} ∷ π)
canonical? (i X! j ∷ _X!_ k l {k<l} ∷ π) | no i≮k = false

{-# NO_TERMINATION_CHECK #-}
sort : ∀ {n} → Transposition<* n → Transposition<* n
sort π with canonical? π 
sort π | true = π 
sort π | false = sort (bubble π)

-- Examples

snn₁ snn₂ snn₃ snn₄ snn₅ : List String
snn₁ = showTransposition<* (sort (filter= (c2π NEG1)))
   -- 0 X! 1 ∷ []
snn₂ = showTransposition<* (sort (filter= (c2π NEG2)))
   -- 0 X! 1 ∷ []
snn₃ = showTransposition<* (sort (filter= (c2π NEG3)))
   -- 0 X! 1 ∷ []
snn₄ = showTransposition<* (sort (filter= (c2π NEG4)))
   -- 0 X! 1 ∷ []
snn₅ = showTransposition<* (sort (filter= (c2π NEG5)))
   -- 0 X! 1 ∷ []

sncnot sntoffoli : List String
sncnot = showTransposition<* (sort (filter= (c2π CNOT)))
   -- 2 X! 3 ∷ []
sntoffoli = showTransposition<* (sort (filter= (c2π TOFFOLI)))
   -- 6 X! 7 ∷ []

snswap12 snswap23 snswap13 snrotl snrotr : List String
snswap12 = showTransposition<* (sort (filter= (c2π SWAP12)))
   -- 0 X! 1 ∷ []
snswap23 = showTransposition<* (sort (filter= (c2π SWAP23)))
   -- 1 X! 2 ∷ []
snswap13 = showTransposition<* (sort (filter= (c2π SWAP13)))
   -- 0 X! 2 ∷ []
snrotl   = showTransposition<* (sort (filter= (c2π ROTL)))
   -- 0 X! 2 ∷ 1 X! 2 ∷ []
snrotr   = showTransposition<* (sort (filter= (c2π ROTR)))
   -- 0 X! 1 ∷ 1 X! 2 ∷ []

snperes snfulladder : List String
snperes = showTransposition<* (sort (filter= (c2π PERES)))
   -- 4 X! 7 ∷ 5 X! 6 ∷ 6 X! 7 ∷ []

snfulladder = showTransposition<* (sort (filter= (c2π FULLADDER)))
   -- ? 

-- Normalization

normalizeπ : {t₁ t₂ : U} → (c : t₁ ⟷  t₂) → Transposition<* (size t₁)
normalizeπ = sort ∘ filter= ∘ c2π

------------------------------------------------------------------------------
-- Extensional equivalence of combinators: two combinators are
-- equivalent if they denote the same permutation. Generally we would
-- require that the two permutations map the same value x to values y
-- and z that have a path between them, but because the internals of each
-- type are discrete groupoids, this reduces to saying that y and z
-- are identical, and hence that the permutations are identical.

infix  10  _∼_  

_∼_ : ∀ {t₁ t₂} → (c₁ c₂ : t₁ ⟷ t₂) → Set
c₁ ∼ c₂ = (normalizeπ c₁ ≡ normalizeπ c₂)

-- The relation ~ is an equivalence relation

refl∼ : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → (c ∼ c)
refl∼ = refl 

sym∼ : ∀ {t₁ t₂} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₁)
sym∼ = sym

trans∼ : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₃) → (c₁ ∼ c₃)
trans∼ = trans

-- The relation ~ validates the groupoid laws

c◎id∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ id⟷ ∼ c
c◎id∼c {t₁} {t₂} {c} = 
  begin (sort 
          (filter= 
            (cauchy→transposition* 
              (c2cauchy (c ◎ id⟷))))
           ≡⟨ {!!} ⟩ 
         sort 
          (filter= 
            (cauchy→transposition* 
              (scompcauchy 
                (c2cauchy c) 
                (subst Cauchy (sym (size≡ c)) (idcauchy (size t₂))))))
           ≡⟨ {!!} ⟩
         sort 
          (filter= 
            (cauchy→transposition* 
              (scompcauchy 
                (c2cauchy c) 
                (allFin (size t₁)))))
           ≡⟨ cong (λ x → sort (filter= (cauchy→transposition* x)))
                   (scompid (c2cauchy c)) ⟩
         sort (filter= (cauchy→transposition* (c2cauchy c))) ∎)
  where open ≡-Reasoning

{--
id◎c∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ◎ c ∼ c
id◎c∼c = {!!} 

assoc∼ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
         c₁ ◎ (c₂ ◎ c₃) ∼ (c₁ ◎ c₂) ◎ c₃
assoc∼ = {!!} 

linv∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ ! c ∼ id⟷
linv∼ = {!!} 

rinv∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! c ◎ c ∼ id⟷
rinv∼ = {!!} 

resp∼ : {t₁ t₂ t₃ : U} {c₁ c₂ : t₁ ⟷ t₂} {c₃ c₄ : t₂ ⟷ t₃} → 
        (c₁ ∼ c₂) → (c₃ ∼ c₄) → (c₁ ◎ c₃ ∼ c₂ ◎ c₄)
resp∼ = {!!} 

-- The equivalence ∼ of paths makes U a 1groupoid: the points are
-- types (t : U); the 1paths are ⟷; and the 2paths between them are
-- based on extensional equivalence ∼

G : 1Groupoid
G = record
        { set = U
        ; _↝_ = _⟷_
        ; _≈_ = _∼_
        ; id  = id⟷
        ; _∘_ = λ p q → q ◎ p
        ; _⁻¹ = !
        ; lneutr = λ c → c◎id∼c {c = c}
        ; rneutr = λ c → id◎c∼c {c = c}
        ; assoc  = λ c₃ c₂ c₁ → assoc∼ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}  
        ; equiv = record { 
            refl  = λ {c} → refl∼ {c = c}
          ; sym   = λ {c₁} {c₂} → sym∼ {c₁ = c₁} {c₂ = c₂}
          ; trans = λ {c₁} {c₂} {c₃} → trans∼ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} 
          }
        ; linv = λ c → linv∼ {c = c} 
        ; rinv = λ c → rinv∼ {c = c} 
        ; ∘-resp-≈ = λ α β → resp∼ β α 
        }

-- And there are additional laws

assoc⊕∼ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          c₁ ⊕ (c₂ ⊕ c₃) ∼ assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊
assoc⊕∼ = {!!} 

assoc⊗∼ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          c₁ ⊗ (c₂ ⊗ c₃) ∼ assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆
assoc⊗∼ = {!!} 

------------------------------------------------------------------------------
-- Picture so far:
--
--           path p
--   =====================
--  ||   ||             ||
--  ||   ||2path        ||
--  ||   ||             ||
--  ||   ||  path q     ||
--  t₁ =================t₂
--  ||   ...            ||
--   =====================
--
-- The types t₁, t₂, etc are discrete groupoids. The paths between
-- them correspond to permutations. Each syntactically different
-- permutation corresponds to a path but equivalent permutations are
-- connected by 2paths.  But now we want an alternative definition of
-- 2paths that is structural, i.e., that looks at the actual
-- construction of the path t₁ ⟷ t₂ in terms of combinators... The
-- theorem we want is that α ∼ β iff we can rewrite α to β using
-- various syntactic structural rules. We start with a collection of
-- simplication rules and then try to show they are complete.

-- Simplification rules

infix  30 _⇔_

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
          (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
          ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  assoc⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (c₁ ⊕ (c₂ ⊕ c₃)) ⇔ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  assoc⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⇔ (c₁ ⊕ (c₂ ⊕ c₃))
  assoc⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (c₁ ⊗ (c₂ ⊗ c₃)) ⇔ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assoc⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⇔ (c₁ ⊗ (c₂ ⊗ c₃))
  dist⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          ((c₁ ⊕ c₂) ⊗ c₃) ⇔ (dist ◎ ((c₁ ⊗ c₃) ⊕ (c₂ ⊗ c₃)) ◎ factor)
  factor⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (dist ◎ ((c₁ ⊗ c₃) ⊕ (c₂ ⊗ c₃)) ◎ factor) ⇔ ((c₁ ⊕ c₂) ⊗ c₃)
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ id⟷ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ id⟷) 
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c) 
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c) 
  unitel₊⇔ : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (unite₊ ◎ c₂) ⇔ ((c₁ ⊕ c₂) ◎ unite₊)
  uniter₊⇔ : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          ((c₁ ⊕ c₂) ◎ unite₊) ⇔ (unite₊ ◎ c₂)
  unitil₊⇔ : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (uniti₊ ◎ (c₁ ⊕ c₂)) ⇔ (c₂ ◎ uniti₊)
  unitir₊⇔ : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti₊) ⇔ (uniti₊ ◎ (c₁ ⊕ c₂))
  unitial₊⇔ : {t₁ t₂ : U} → (uniti₊ {PLUS t₁ t₂} ◎ assocl₊) ⇔ (uniti₊ ⊕ id⟷)
  unitiar₊⇔ : {t₁ t₂ : U} → (uniti₊ {t₁} ⊕ id⟷ {t₂}) ⇔ (uniti₊ ◎ assocl₊)
  swapl₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          (swap₊ ◎ (c₁ ⊕ c₂)) ⇔ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          ((c₂ ⊕ c₁) ◎ swap₊) ⇔ (swap₊ ◎ (c₁ ⊕ c₂))
  unitel⋆⇔ : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (unite⋆ ◎ c₂) ⇔ ((c₁ ⊗ c₂) ◎ unite⋆)
  uniter⋆⇔ : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          ((c₁ ⊗ c₂) ◎ unite⋆) ⇔ (unite⋆ ◎ c₂)
  unitil⋆⇔ : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (uniti⋆ ◎ (c₁ ⊗ c₂)) ⇔ (c₂ ◎ uniti⋆)
  unitir⋆⇔ : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti⋆) ⇔ (uniti⋆ ◎ (c₁ ⊗ c₂))
  unitial⋆⇔ : {t₁ t₂ : U} → (uniti⋆ {TIMES t₁ t₂} ◎ assocl⋆) ⇔ (uniti⋆ ⊗ id⟷)
  unitiar⋆⇔ : {t₁ t₂ : U} → (uniti⋆ {t₁} ⊗ id⟷ {t₂}) ⇔ (uniti⋆ ◎ assocl⋆)
  swapl⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          (swap⋆ ◎ (c₁ ⊗ c₂)) ⇔ ((c₂ ⊗ c₁) ◎ swap⋆)
  swapr⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          ((c₂ ⊗ c₁) ◎ swap⋆) ⇔ (swap⋆ ◎ (c₁ ⊗ c₂))
  swapfl⋆⇔ : {t₁ t₂ t₃ : U} → 
          (swap₊ {TIMES t₂ t₃} {TIMES t₁ t₃} ◎ factor) ⇔ 
          (factor ◎ (swap₊ {t₂} {t₁} ⊗ id⟷))
  swapfr⋆⇔ : {t₁ t₂ t₃ : U} → 
          (factor ◎ (swap₊ {t₂} {t₁} ⊗ id⟷)) ⇔ 
         (swap₊ {TIMES t₂ t₃} {TIMES t₁ t₃} ◎ factor)
  id⇔     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ c
  trans⇔  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  resp◎⇔  : {t₁ t₂ t₃ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)

-- better syntax for writing 2paths

infix  2  _▤       
infixr 2  _⇔⟨_⟩_   

_⇔⟨_⟩_ : {t₁ t₂ : U} (c₁ : t₁ ⟷ t₂) {c₂ : t₁ ⟷ t₂} {c₃ : t₁ ⟷ t₂} → 
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
_ ⇔⟨ α ⟩ β = trans⇔ α β 

_▤ : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → (c ⇔ c)
_▤ c = id⇔ 

-- Inverses for 2paths

2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l = assoc◎r
2! assoc◎r = assoc◎l
2! assoc⊕l = assoc⊕r
2! assoc⊕r = assoc⊕l
2! assoc⊗l = assoc⊗r
2! assoc⊗r = assoc⊗l
2! dist⇔ = factor⇔ 
2! factor⇔ = dist⇔
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! idr◎l = idr◎r
2! idr◎r = idr◎l
2! linv◎l = linv◎r
2! linv◎r = linv◎l
2! rinv◎l = rinv◎r
2! rinv◎r = rinv◎l
2! unitel₊⇔ = uniter₊⇔
2! uniter₊⇔ = unitel₊⇔
2! unitil₊⇔ = unitir₊⇔
2! unitir₊⇔ = unitil₊⇔
2! swapl₊⇔ = swapr₊⇔
2! swapr₊⇔ = swapl₊⇔
2! unitial₊⇔ = unitiar₊⇔ 
2! unitiar₊⇔ = unitial₊⇔ 
2! unitel⋆⇔ = uniter⋆⇔
2! uniter⋆⇔ = unitel⋆⇔
2! unitil⋆⇔ = unitir⋆⇔
2! unitir⋆⇔ = unitil⋆⇔
2! unitial⋆⇔ = unitiar⋆⇔ 
2! unitiar⋆⇔ = unitial⋆⇔ 
2! swapl⋆⇔ = swapr⋆⇔
2! swapr⋆⇔ = swapl⋆⇔
2! swapfl⋆⇔ = swapfr⋆⇔
2! swapfr⋆⇔ = swapfl⋆⇔
2! id⇔ = id⇔
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)
2! (resp◎⇔ α β) = resp◎⇔ (2! α) (2! β)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β) 

-- a nice example of 2 paths

negEx : neg₅ ⇔ neg₁
negEx = uniti⋆ ◎ (swap⋆ ◎ ((swap₊ ⊗ id⟷) ◎ (swap⋆ ◎ unite⋆)))
          ⇔⟨ resp◎⇔ id⇔ assoc◎l ⟩
        uniti⋆ ◎ ((swap⋆ ◎ (swap₊ ⊗ id⟷)) ◎ (swap⋆ ◎ unite⋆))
          ⇔⟨ resp◎⇔ id⇔ (resp◎⇔ swapl⋆⇔ id⇔) ⟩
        uniti⋆ ◎ (((id⟷ ⊗ swap₊) ◎ swap⋆) ◎ (swap⋆ ◎ unite⋆))
          ⇔⟨ resp◎⇔ id⇔ assoc◎r ⟩
        uniti⋆ ◎ ((id⟷ ⊗ swap₊) ◎ (swap⋆ ◎ (swap⋆ ◎ unite⋆)))
          ⇔⟨ resp◎⇔ id⇔ (resp◎⇔ id⇔ assoc◎l) ⟩
        uniti⋆ ◎ ((id⟷ ⊗ swap₊) ◎ ((swap⋆ ◎ swap⋆) ◎ unite⋆))
          ⇔⟨ resp◎⇔ id⇔ (resp◎⇔ id⇔ (resp◎⇔ linv◎l id⇔)) ⟩
        uniti⋆ ◎ ((id⟷ ⊗ swap₊) ◎ (id⟷ ◎ unite⋆))
          ⇔⟨ resp◎⇔ id⇔ (resp◎⇔ id⇔ idl◎l) ⟩
        uniti⋆ ◎ ((id⟷ ⊗ swap₊) ◎ unite⋆)
          ⇔⟨ assoc◎l ⟩
        (uniti⋆ ◎ (id⟷ ⊗ swap₊)) ◎ unite⋆
          ⇔⟨ resp◎⇔ unitil⋆⇔ id⇔ ⟩
        (swap₊ ◎ uniti⋆) ◎ unite⋆
          ⇔⟨ assoc◎r ⟩
        swap₊ ◎ (uniti⋆ ◎ unite⋆)
          ⇔⟨ resp◎⇔ id⇔ linv◎l ⟩
        swap₊ ◎ id⟷
          ⇔⟨ idr◎l ⟩
        swap₊ ▤

-- The equivalence ⇔ of paths is rich enough to make U a 1groupoid:
-- the points are types (t : U); the 1paths are ⟷; and the 2paths
-- between them are based on the simplification rules ⇔ 

G' : 1Groupoid
G' = record
        { set = U
        ; _↝_ = _⟷_
        ; _≈_ = _⇔_
        ; id  = id⟷
        ; _∘_ = λ p q → q ◎ p
        ; _⁻¹ = !
        ; lneutr = λ _ → idr◎l
        ; rneutr = λ _ → idl◎l
        ; assoc  = λ _ _ _ → assoc◎l
        ; equiv = record { 
            refl  = id⇔
          ; sym   = 2!
          ; trans = trans⇔
          }
        ; linv = λ {t₁} {t₂} α → linv◎l
        ; rinv = λ {t₁} {t₂} α → rinv◎l
        ; ∘-resp-≈ = λ p∼q r∼s → resp◎⇔ r∼s p∼q 
        }

------------------------------------------------------------------------------
-- Inverting permutations to syntactic combinators

perm2comb : {t₁ t₂ : U} → (size t₁ ≡ size t₂) → Perm (size t₁) → (t₁ ⟷ t₂)
perm2comb {ZERO} {t₂} sp [] = {!!} 
perm2comb {ONE} {t₂} sp p = {!!} 
perm2comb {PLUS t₁ t₂} {t₃} sp p = {!!} 
perm2comb {TIMES t₁ t₂} {t₃} sp p = {!!} 

------------------------------------------------------------------------------
-- Soundness and completeness
-- 
-- Proof of soundness and completeness: now we want to verify that ⇔
-- is sound and complete with respect to ∼. The statement to prove is
-- that for all c₁ and c₂, we have c₁ ∼ c₂ iff c₁ ⇔ c₂

soundness : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₁ ∼ c₂)
soundness assoc◎l      = assoc∼
soundness assoc◎r      = sym∼ assoc∼
soundness assoc⊕l      = assoc⊕∼
soundness assoc⊕r      = sym∼ assoc⊕∼
soundness assoc⊗l      = assoc⊗∼
soundness assoc⊗r      = sym∼ assoc⊗∼
soundness dist⇔        = {!!}
soundness factor⇔      = {!!}
soundness idl◎l        = id◎c∼c
soundness idl◎r        = sym∼ id◎c∼c
soundness idr◎l        = c◎id∼c
soundness idr◎r        = sym∼ c◎id∼c
soundness linv◎l       = linv∼
soundness linv◎r       = sym∼ linv∼
soundness rinv◎l       = rinv∼
soundness rinv◎r       = sym∼ rinv∼
soundness unitel₊⇔     = {!!}
soundness uniter₊⇔     = {!!}
soundness unitil₊⇔     = {!!}
soundness unitir₊⇔     = {!!}
soundness unitial₊⇔    = {!!}
soundness unitiar₊⇔    = {!!}
soundness swapl₊⇔      = {!!}
soundness swapr₊⇔      = {!!}
soundness unitel⋆⇔     = {!!}
soundness uniter⋆⇔     = {!!}
soundness unitil⋆⇔     = {!!}
soundness unitir⋆⇔     = {!!}
soundness unitial⋆⇔    = {!!}
soundness unitiar⋆⇔    = {!!}
soundness swapl⋆⇔      = {!!}
soundness swapr⋆⇔      = {!!}
soundness swapfl⋆⇔     = {!!}
soundness swapfr⋆⇔     = {!!}
soundness id⇔          = refl∼
soundness (trans⇔ α β) = trans∼ (soundness α) (soundness β)
soundness (resp◎⇔ α β) = resp∼ (soundness α) (soundness β)
soundness (resp⊕⇔ α β) = {!!}
soundness (resp⊗⇔ α β) = {!!} 

-- The idea is to invert evaluation and use that to extract from each
-- extensional representation of a combinator, a canonical syntactic
-- representative

canonical : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂)
canonical c = perm2comb (size≡ c) (comb2perm c)

-- Note that if c₁ ⇔ c₂, then by soundness c₁ ∼ c₂ and hence their
-- canonical representatives are identical. 

canonicalWellDefined : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → 
  (c₁ ⇔ c₂) → (canonical c₁ ≡ canonical c₂)
canonicalWellDefined {t₁} {t₂} {c₁} {c₂} α = 
  cong₂ perm2comb (size∼ c₁ c₂) (soundness α) 

-- If we can prove that every combinator is equal to its normal form
-- then we can prove completeness.

inversion : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ canonical c
inversion = {!!} 

resp≡⇔ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ≡ c₂) → (c₁ ⇔ c₂)
resp≡⇔ {t₁} {t₂} {c₁} {c₂} p rewrite p = id⇔ 

completeness : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₁ ⇔ c₂)
completeness {t₁} {t₂} {c₁} {c₂} c₁∼c₂ = 
  c₁
    ⇔⟨ inversion ⟩
  canonical c₁
    ⇔⟨  resp≡⇔ (cong₂ perm2comb (size∼ c₁ c₂) c₁∼c₂) ⟩ 
  canonical c₂
    ⇔⟨ 2! inversion ⟩ 
  c₂ ▤

------------------------------------------------------------------------------
--}
