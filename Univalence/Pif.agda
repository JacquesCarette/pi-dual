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

open import Data.List 
  using (List; []; _∷_; _∷ʳ_; foldl; replicate; reverse; downFrom; 
         concatMap; gfilter; initLast; InitLast; _∷ʳ'_) 
  renaming (_++_ to _++L_; map to mapL; concat to concatL)
open import Data.List.NonEmpty 
  using (List⁺; [_]; _∷⁺_; head; last; _⁺++_)
  renaming (toList to nonEmptyListtoList; _∷ʳ_ to _n∷ʳ_; tail to ntail)
open import Data.List.Any using (Any; here; there; any; module Membership)
open import Data.Maybe using (Maybe; nothing; just; maybe′)
open import Data.Vec 
  using (Vec; tabulate; []; _∷_; tail; lookup; zip; zipWith; 
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

not⟷ : BOOL ⟷ BOOL
not⟷ = unfoldBool ◎ swap₊ ◎ foldBool
-- spec: (false , true) ∷ (true , false) ∷ []

neg₁ neg₂ neg₃ neg₄ neg₅ : BOOL ⟷ BOOL
neg₁ = unfoldBool ◎ swap₊ ◎ foldBool
-- spec: (false , true) ∷ (true , false) ∷ []
neg₂ = id⟷ ◎ not⟷ 
-- spec: (false , true) ∷ (true , false) ∷ []
neg₃ = not⟷ ◎ not⟷ ◎ not⟷ 
-- spec: (false , true) ∷ (true , false) ∷ []
neg₄ = not⟷ ◎ id⟷
-- spec: (false , true) ∷ (true , false) ∷ []
neg₅ = uniti⋆ ◎ swap⋆ ◎ (not⟷ ⊗ id⟷) ◎ swap⋆ ◎ unite⋆
-- spec: (false , true) ∷ (true , false) ∷ []

-- CNOT

CNOT : BOOL² ⟷ BOOL²
CNOT = TIMES BOOL BOOL
         ⟷⟨ unfoldBool ⊗ id⟷ ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ dist ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ id⟷ ⊕ (id⟷ ⊗ not⟷) ⟩
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
PERES = (id⟷ ⊗ not⟷) ◎ assocr⋆ ◎ (id⟷ ⊗ swap⋆) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ (not⟷ ⊗ id⟷)) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ swap⋆) ◎ (id⟷ ⊗ (not⟷ ⊗ id⟷)) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ (not⟷ ⊗ id⟷)) ◎ assocl⋆
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
-- Semantic representation of permutations

-- One possibility of course is to represent them as functions but
-- this is a poor representation and eventually requires function
-- extensionality. 

-- A permutation is a represented as a product of
-- "transpositions". This product is not commutative; we apply it from
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

Perm : ℕ → Set
Perm n = List (Transposition n) 

showTransposition : ∀ {n} → Transposition n → String
showTransposition (i X j) = show (toℕ i) ++S " X " ++S show (toℕ j)

-- A permutation with indices less than n can act on a vector of size
-- n by applying the swaps, one by one, from left to right.

actionπ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Perm n → Vec A n → Vec A n
actionπ π vs = foldl swapX vs π
  where 
    swapX : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vec A n → Transposition n → Vec A n  
    swapX vs (i X j) = (vs [ i ]≔ lookup j vs) [ j ]≔ lookup i vs

-- swap the first i elements with the last j elements
-- [ v₁   , v₂   , ... , vᵢ   || vᵢ₊₁ , vᵢ₊₂ , ... , vᵢ₊ⱼ ]
-- ==> 
-- [ vᵢ₊₁ , vᵢ₊₂ , ... , vᵢ₊ⱼ || v₁   , v₂   , ... , vᵢ   ]
-- idea: move each of the first i elements to the end by successive swaps

swap+π : (m n : ℕ) → Perm (m + n)
swap+π 0 n = []
swap+π (suc m) n = 
  concatL 
    (replicate (suc m)
      (toList 
        (zipWith mkTransposition
          (mapV inject₁ (allFin (m + n))) 
          (tail (allFin (suc m + n))))))

-- Ex:

swap11 swap21 swap32 : List String
swap11 = mapL showTransposition (swap+π 1 1)
--
-- 0 X 1 ∷ []
-- Action on [a, b]
--           [b, a]
swap21 = mapL showTransposition (swap+π 2 1)
--
-- 0 X 1 ∷ 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ []
-- Action on [a, b, c]
--           [c, a, b]
-- Once normalized we get:
-- 0 X 2 ∷ 1 X 2 ∷ []
swap32 = mapL showTransposition (swap+π 3 2)
--
-- 0 X 1 ∷ 1 X 2 ∷ 2 X 3 ∷ 3 X 4 ∷
-- 0 X 1 ∷ 1 X 2 ∷ 2 X 3 ∷ 3 X 4 ∷ 
-- 0 X 1 ∷ 1 X 2 ∷ 2 X 3 ∷ 3 X 4 ∷ []
-- Action on [ a, b, c, d, e ]
--           [ b, c, d, e, a ]
--           [ c, d, e, a, b ]
--           [ d, e, a, b, c ]
-- Once normalized we get:
-- 0 X 3 ∷ 1 X 4 ∷ 2 X 3 ∷ 3 X 4 ∷ []
-- Action on [ a, b, c, d, e ]
--           [ d, e, a, b, c ]

-- Sequential composition is just append

scompπ : ∀ {n} → Perm n → Perm n → Perm n
scompπ = _++L_

-- Parallel additive composition 
-- append both permutations but shift the second permutation by the size
-- of the first type so that it acts on the second part of the vector
-- Let α = [ m₀ X n₀ , m₁ X n₁ , ... m₇ X n₇ ]
--     β = [ k₀ X l₀ , k₁ X l₁ , ... ]
-- pcompπ α β is:
--  [ m₀ X n₀ , m₁ X n₁ , ... , m₇ X n₇ , k₀+8 X l₀+8 , k₁+8 X l₁+8 , ... ]

injectπ : ∀ {m} → Perm m → (n : ℕ) → Perm (m + n)
injectπ π n = mapL (λ { (i X j) → 
                      mkTransposition (inject+ n i) (inject+ n j)})
                   π 

raiseπ : ∀ {n} → Perm n → (m : ℕ) → Perm (m + n)
raiseπ π m = mapL (λ { (i X j) → 
                    mkTransposition (raise m i) (raise m j)})
                  π 

pcompπ : ∀ {m n} → Perm m → Perm n → Perm (m + n)
pcompπ {m} {n} α β = (injectπ α n) ++L (raiseπ β m)

-- Ex: 

swap11+21 swap21+11 : List String
swap11+21 = mapL showTransposition (pcompπ (swap+π 1 1) (swap+π 2 1))
--
-- 0 X 1 ∷ 2 X 3 ∷ 3 X 4 ∷ 2 X 3 ∷ 3 X 4 ∷ []
-- Once normalized we get:
-- 0 X 1 ∷ 2 X 4 ∷ 3 X 4 ∷ []
swap21+11 = mapL showTransposition (pcompπ (swap+π 2 1) (swap+π 1 1))
--
-- 0 X 1 ∷ 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ 3 X 4 ∷ []
-- Once normalized we get:
-- 0 X 2 ∷ 1 X 2 ∷ 3 X 4 ∷ []

-- Tensor multiplicative composition

idπ : (n : ℕ) → Perm n
idπ n = toList (zipWith mkTransposition (allFin n) (allFin n))

-- Ex:

idπ5 = mapL showTransposition (idπ 5)
-- 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ []

-- Transpositions in α correspond to swapping entire rows
-- Transpositions in β correspond to swapping entire columns
-- Need to make sure neither α nor β is empty; otherwise composition annhilates
-- So explicitly represent identity permutations using a product of 
-- self-transpositions

delete : ∀ {n} → List (Fin n) → Fin n → List (Fin n)
delete [] _ = []
delete (j ∷ js) i with toℕ i ≟ toℕ j 
delete (j ∷ js) i | yes _ = js
delete (j ∷ js) i | no _ = j ∷ delete js i

extendπ : ∀ {n} → Perm n → Perm n
extendπ {n} π = 
  let existing = mapL (λ { (i X j) → i }) π
      all = toList (allFin n)
      diff = foldl delete all existing
  in π ++L mapL (λ i → _X_ i i {i≤i (toℕ i)}) diff

tcompπ : ∀ {m n} → Perm m → Perm n → Perm (m * n)
tcompπ {m} {n} α β = 
  concatMap
    (λ { (i X j) → 
      mapL (λ { (k X l) → 
             mkTransposition
               (inject≤ (fromℕ (toℕ i * n + toℕ k)) (i*n+k≤m*n i k))
               (inject≤ (fromℕ (toℕ j * n + toℕ l)) (i*n+k≤m*n j l))})
           (extendπ β)})
    (extendπ α)

-- Ex:

swap21*id : List String
swap21*id = mapL showTransposition (tcompπ (swap+π 2 1) (idπ 2))
--
-- 0 X 2 ∷ 1 X 3 ∷ 2 X 4 ∷ 3 X 5 ∷ 
-- 0 X 2 ∷ 1 X 3 ∷ 2 X 4 ∷ 3 X 5 ∷ 
-- 4 X 4 ∷ 5 X 5 ∷ []
-- swap21 takes [a, b, c] to [c, a, b]
-- id2    takes [d, e] to [d, e]
-- tensor is [ (a,d), (a,e), (b,d), (b,e), (c,d), (c,e) ]
-- action on tensor is:
-- [ (a,d), (a,e), (b,d), (b,e), (c,d), (c,e) ]
-- [ (c,d), (c,e), (a,d), (a,e), (b,d), (b,e) ]
-- which is correct

-- swap⋆ 
-- 
-- This is essentially the classical problem of in-place matrix transpose:
-- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
-- 
-- Given m and n, first calculate the desired permutation:
-- P(i) = m*n-1 if i=m*n-1
--      = m*i mod m*n-1 otherwise
-- Then find all the cycles
-- Then express each cycle as a product of transpositions

-- desired permutation expressed in Cauchy's two-line notation:

transpose : (m mn-2 : ℕ) → List (Fin (suc (suc mn-2)) × Fin (suc (suc mn-2)))
transpose m mn-2 = 
  toList 
    (tabulate {suc mn-2}
      (λ x → (subst Fin (+-comm (suc mn-2) 1) (inject+ 1 x) , 
              subst Fin (+-comm (suc mn-2) 1)
                (inject+ 1 ((toℕ x * m) mod (suc mn-2))))))

-- Ex:

v3x2 = concatV 
         (mapV (λ v₁ → mapV (λ v₂ → (v₁ , v₂)) (1 ∷ 2 ∷ []))
         ("a" ∷ "b" ∷ "c" ∷ []))
--
-- [ a1 a2 ]
-- [ b1 b2 ]
-- [ c1 c2 ]

moves3x2→2x3 = transpose 3 4
--
-- (0 , 0) ∷
-- (1 , 3) ∷ 
-- (2 , 1) ∷ 
-- (3 , 4) ∷ 
-- (4 , 2) ∷ []
-- 
-- which transforms our 3x2 set of values above:
-- 
--   0  1  2  3  4  5
-- [ a1 a2 b1 b2 c1 c2 ]
-- [ a1 b1 c1 a2 b2 c2 ]
-- 
-- i.e.
-- [ a1 b1 c1 ]
-- [ a2 b2 c2 ]
-- 

-- find cycles

link : ∀ {n} → Fin n → List (List⁺ (Fin n)) → 
       Maybe (List⁺ (Fin n) × List (List⁺ (Fin n)))
link i [] = nothing
link i (c ∷ cs) with toℕ i ≟ toℕ (head c)
link i (c ∷ cs) | yes _ = just (c , cs)
link i (c ∷ cs) | no _ = 
  maybe′ (λ { (c' , cs') → just (c' , c ∷ cs') }) nothing (link i cs)

{-# NO_TERMINATION_CHECK #-}
connectCycles : ∀ {n} → List (List⁺ (Fin n)) → List (List⁺ (Fin n))
connectCycles [] = []
connectCycles (c ∷ cs) with link (last c) cs
connectCycles (c ∷ cs) | nothing = c ∷ connectCycles cs
connectCycles (c ∷ cs) | just (c' , cs') = 
  connectCycles ((c ⁺++ ntail c') ∷ cs')

-- Simpler still might be to:
-- 1. make the transposition act on an AllFin vector
-- 2. trace out the orbit of each number
-- to make that more efficient, you can of course skip numbers (in step 2)
-- which are already in an orbit.

findCycles : ∀ {n} → List (Fin n × Fin n) → List (List (Fin n))
findCycles perm = 
  mapL nonEmptyListtoList 
    (connectCycles (mapL (λ { (i , j) → i ∷⁺ [ j ]}) perm))

-- Ex:

cycles3x2→2x3 = findCycles moves3x2→2x3
--
-- [ 0 , 0 ] ∷
-- [ 1 , 3 , 4 , 2 , 1 ] ∷

-- convert each cycle to a product of transpositions

cycle→perm : ∀ {n} → List (Fin n) → Perm n
cycle→perm [] = []
cycle→perm (i ∷ []) = []
cycle→perm (i ∷ j ∷ ns) = mkTransposition i j ∷ cycle→perm (i ∷ ns)

-- concatenate all cycles to build final product of transpositions

swap⋆π : (m n : ℕ) → Perm (m * n) 
swap⋆π 0 n = []
swap⋆π 1 n = []
swap⋆π (suc (suc m)) 0 = []
swap⋆π (suc (suc m)) 1 = []
swap⋆π (suc (suc m)) (suc (suc n)) = 
  concatMap cycle→perm 
    (findCycles (transpose (suc (suc m)) (n + suc m * suc (suc n))))

-- Ex:

perm3x2→2x3 : List String
perm3x2→2x3 = mapL showTransposition (swap⋆π 3 2)
-- 0 X 0 ∷ 1 X 3 ∷ 1 X 4 ∷ 1 X 2 ∷ 1 X 1 ∷ []

v2x3 = actionπ (swap⋆π 3 2) v3x2
-- ("a" , 1) ∷ ("b" , 1) ∷ ("c" , 1) ∷ 
-- ("a" , 2) ∷ ("b" , 2) ∷ ("c" , 2) ∷ []

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes a permutation.

c2π : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Perm (size t₁)
c2π unite₊    = []
c2π uniti₊    = []
c2π {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ = swap+π (size t₁) (size t₂)
c2π assocl₊   = []
c2π assocr₊   = []
c2π unite⋆    = []
c2π uniti⋆    = []
c2π {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = swap⋆π (size t₁) (size t₂)
c2π assocl⋆   = []  
c2π assocr⋆   = []  
c2π distz     = []  
c2π factorz   = []  
c2π dist      = []  
c2π factor    = []  
c2π id⟷       = []  
c2π (c₁ ◎ c₂) = scompπ (c2π c₁) (subst Perm (sym (size≡ c₁)) (c2π c₂))
c2π (c₁ ⊕ c₂) = pcompπ (c2π c₁) (c2π c₂) 
c2π (c₁ ⊗ c₂) = tcompπ (c2π c₁) (c2π c₂) 
c2π unfoldBool = []
c2π foldBool   = []

-- Convenient way of seeing the result of applying a c : t₁ ⟷ t₂ 

showπ : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Vec (⟦ t₁ ⟧ × ⟦ t₂ ⟧) (size t₁) 
showπ {t₁} {t₂} c = 
  let vs₁ = utoVec t₁
      vs₂ = utoVec t₂
  in zip (actionπ (c2π c) vs₁) (subst (Vec ⟦ t₂ ⟧) (sym (size≡ c)) vs₂)

-- Examples

neg₁π neg₂π neg₃π neg₄π neg₅π : Vec (⟦ BOOL ⟧ × ⟦ BOOL ⟧) 2
neg₁π = showπ {BOOL} {BOOL} neg₁  
--      (true , false) ∷ (false , true) ∷ []
neg₂π = showπ {BOOL} {BOOL} neg₂  
--      (true , false) ∷ (false , true) ∷ []
neg₃π = showπ {BOOL} {BOOL} neg₃  
--      (true , false) ∷ (false , true) ∷ []
neg₄π = showπ {BOOL} {BOOL} neg₄
--      (true , false) ∷ (false , true) ∷ []
neg₅π = showπ {BOOL} {BOOL} neg₅ 
--      (true , false) ∷ (false , true) ∷ []

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
rotlπ   = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} ROTL
-- (inj₂ (inj₁ tt) , inj₁ tt) ∷
-- (inj₂ (inj₂ tt) , inj₂ (inj₁ tt)) ∷ 
-- (inj₁ tt , inj₂ (inj₂ tt)) ∷ []
rotrπ   = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} ROTR
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
-- fulladderπ = showπ FULLADDER
fulladderπ = showπ FULLADDER
-- ((false , (false , false) , false) , false , false , false , false) ∷
-- ((true , (false , false) , false) , false , false , false , true) ∷
-- ((false , (false , false) , true) , false , false , true , false) ∷
-- ((true , (false , false) , true) , false , false , true , true) ∷
-- ((true , (false , true) , true) , false , true , false , false) ∷
-- ((false , (false , true) , true) , false , true , false , true) ∷
-- ((false , (false , true) , false) , false , true , true , false) ∷
-- ((true , (false , true) , false) , false , true , true , true) ∷
-- ((true , (true , true) , false) , true , false , false , false) ∷
-- ((false , (true , true) , false) , true , false , false , true) ∷
-- ((true , (true , true) , true) , true , false , true , false) ∷
-- ((false , (true , true) , true) , true , false , true , true) ∷
-- ((true , (true , false) , true) , true , true , false , false) ∷
-- ((false , (true , false) , true) , true , true , false , true) ∷
-- ((false , (true , false) , false) , true , true , true , false) ∷
-- ((true , (true , false) , false) , true , true , true , true) ∷ []
-- ... which matches the specification:
-- 0000 0000
-- 1000 0001
-- 0001 0010
-- 1001 0011
-- 1011 0100
-- 0011 0101
-- 0010 0110
-- 1010 0111
-- 1110 1000
-- 0110 1001
-- 1111 1010
-- 0111 1011
-- 1101 1100
-- 0101 1101
-- 0100 1110
-- 1100 1111

-- The various realizations of negation are equivalent but they give
-- different products of transpositions:

n₁ n₂ n₃ n₄ n₅ : List String
n₁ = mapL showTransposition (c2π neg₁)
   -- 0 X 1 ∷ []
n₂ = mapL showTransposition (c2π neg₂)
   -- 0 X 1 ∷ []
n₃ = mapL showTransposition (c2π neg₃)
   -- 0 X 1 ∷ 0 X 1 ∷ 0 X 1 ∷ []
n₄ = mapL showTransposition (c2π neg₄)
   -- 0 X 1 ∷ []
n₅ = mapL showTransposition (c2π neg₅)
   -- 0 X 1 ∷ 0 X 0 ∷ 1 X 1 ∷ []

cnot toffoli : List String
cnot = mapL showTransposition (c2π CNOT)
   -- 0 X 0 ∷
   -- 1 X 1 ∷
   -- 2 X 2 ∷
   -- 3 X 3 ∷
   -- 2 X 3 ∷
   -- 2 X 2 ∷ 
   -- 3 X 3 ∷ 
   -- 0 X 0 ∷ 
   -- 1 X 1 ∷ 
   -- 2 X 2 ∷ 
   -- 3 X 3 ∷ []
toffoli = mapL showTransposition (c2π TOFFOLI)
   -- 0 X 0 ∷
   -- 1 X 1 ∷
   -- 2 X 2 ∷
   -- 3 X 3 ∷
   -- 4 X 4 ∷
   -- 5 X 5 ∷
   -- 6 X 6 ∷
   -- 7 X 7 ∷
   -- 4 X 4 ∷
   -- 5 X 5 ∷
   -- 6 X 6 ∷
   -- 7 X 7 ∷
   -- 6 X 7 ∷
   -- 6 X 6 ∷
   -- 7 X 7 ∷
   -- 4 X 4 ∷
   -- 5 X 5 ∷
   -- 6 X 6 ∷
   -- 7 X 7 ∷
   -- 4 X 4 ∷
   -- 5 X 5 ∷
   -- 6 X 6 ∷
   -- 7 X 7 ∷
   -- 0 X 0 ∷
   -- 1 X 1 ∷
   -- 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7"∷ []

swap12 swap23 swap13 rotl rotr : List String
swap12 = mapL showTransposition (c2π SWAP12)
   -- 0 X 1 ∷ []
swap23 = mapL showTransposition (c2π SWAP23)
   -- 1 X 2 ∷ []
swap13 = mapL showTransposition (c2π SWAP13)
   -- 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ []
rotl   = mapL showTransposition (c2π ROTL)
   -- 0 X 1 ∷ 1 X 2 ∷ []
rotr   = mapL showTransposition (c2π ROTR)
   -- 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ 1 X 2 ∷ []

peres fulladder : List String
peres = mapL showTransposition (c2π PERES)
-- 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷
-- 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 6 X 7 ∷ 6 X 6 ∷ 7 X 7 ∷ 4 X 4 ∷
-- 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 0 X 0 ∷
-- 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 0 X 0 ∷
-- 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 4 X 6 ∷
-- 5 X 7 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷
-- 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷ 
-- 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ []
fulladder = mapL showTransposition (c2π FULLADDER)
-- 0 X 0 ∷ 1 X 2 ∷ 1 X 4 ∷ 1 X 8 ∷ 1 X 1 ∷ 3 X 6 ∷ 3 X 12 ∷ 3 X 9 ∷
-- 3 X 3 ∷ 5 X 10 ∷ 5 X 5 ∷ 7 X 14 ∷ 7 X 13 ∷ 7 X 11 ∷ 7 X 7 ∷ 0 X 0 ∷
-- 1 X 1 ∷ 2 X 8 ∷ 3 X 9 ∷ 2 X 4 ∷ 3 X 5 ∷ 2 X 2 ∷ 3 X 3 ∷ 6 X 10 ∷ 7 X 11 ∷
-- 6 X 12 ∷ 7 X 13 ∷ 6 X 6 ∷ 7 X 7 ∷ 4 X 4 ∷ 5 X 5 ∷ 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷
-- 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 0 X 0 ∷ 1 X 2 ∷ 1 X 4 ∷
-- 1 X 8 ∷ 1 X 1 ∷ 3 X 6 ∷ 3 X 12 ∷ 3 X 9 ∷ 3 X 3 ∷ 5 X 10 ∷ 5 X 5 ∷ 7 X 14 ∷
-- 7 X 13 ∷ 7 X 11 ∷ 7 X 7 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 8 ∷ 3 X 9 ∷ 2 X 4 ∷ 3 X 5 ∷
-- 2 X 2 ∷ 3 X 3 ∷ 6 X 10 ∷ 7 X 11 ∷ 6 X 12 ∷ 7 X 13 ∷ 6 X 6 ∷ 7 X 7 ∷ 0 X 0 ∷
-- 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 8 X 8 ∷ 9 X 9 ∷
-- 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 8 X 8 ∷ 9 X 9 ∷
-- 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 12 X 14 ∷ 
-- 13 X 15 ∷ 14 X 14 ∷ 15 X 15 ∷ 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷
-- 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷
-- 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷
-- 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 4 ∷ 3 X 5 ∷ 2 X 8 ∷
-- 3 X 9 ∷ 2 X 2 ∷ 3 X 3 ∷ 6 X 12 ∷ 7 X 13 ∷ 6 X 10 ∷ 7 X 11 ∷ 6 X 6 ∷
-- 7 X 7 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷
-- 7 X 7 ∷ 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷
-- 15 X 15 ∷ 8 X 12 ∷ 9 X 13 ∷ 10 X 14 ∷ 11 X 15 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷
-- 15 X 15 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷
-- 7 X 7 ∷ 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷
-- 15 X 15 ∷ 0 X 0 ∷ 1 X 2 ∷ 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 6 ∷
-- 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 8 X 8 ∷ 9 X 10 ∷ 9 X 9 ∷ 10 X 10 ∷ 11 X 11 ∷
-- 12 X 12 ∷ 13 X 14 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷
-- 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷
-- 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 0 X 0 ∷ 1 X 4 ∷ 1 X 2 ∷
-- 1 X 1 ∷ 3 X 5 ∷ 3 X 6 ∷ 3 X 3 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷
-- 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷
-- 6 X 7 ∷ 7 X 7 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 0 X 0 ∷ 1 X 1 ∷
-- 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 0 X 0 ∷ 1 X 2 ∷
-- 1 X 4 ∷ 1 X 1 ∷ 3 X 6 ∷ 3 X 5 ∷ 3 X 3 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷
-- 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 4 X 6 ∷ 5 X 7 ∷ 6 X 6 ∷
-- 7 X 7 ∷ 0 X 0 ∷ 1 X 1 ∷ 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷
-- 7 X 7 ∷ 8 X 8 ∷ 9 X 12 ∷ 9 X 10 ∷ 9 X 9 ∷ 11 X 13 ∷ 11 X 14 ∷ 11 X 11 ∷
-- 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷
-- 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 14 X 15 ∷ 15 X 15 ∷ 12 X 12 ∷ 
-- 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷
-- 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 8 X 8 ∷ 9 X 10 ∷ 9 X 12 ∷ 9 X 9 ∷ 11 X 14 ∷
-- 11 X 13 ∷ 11 X 11 ∷ 8 X 8 ∷ 9 X 9 ∷ 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷
-- 14 X 14 ∷ 15 X 15 ∷ 12 X 14 ∷ 13 X 15 ∷ 14 X 14 ∷ 15 X 15 ∷ 8 X 8 ∷ 9 X 9 ∷
-- 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ 0 X 0 ∷ 1 X 1 ∷
-- 2 X 2 ∷ 3 X 3 ∷ 4 X 4 ∷ 5 X 5 ∷ 6 X 6 ∷ 7 X 7 ∷ 8 X 8 ∷ 9 X 9 ∷
-- 10 X 10 ∷ 11 X 11 ∷ 12 X 12 ∷ 13 X 13 ∷ 14 X 14 ∷ 15 X 15 ∷ []

------------------------------------------------------------------------------
-- Normalization

-- First, remove all trivial transpositions (i X i)

data Transposition< (n : ℕ) : Set where
  _X_ : (i j : Fin n) → {p : toℕ i < toℕ j} → Transposition< n

showTransposition< : ∀ {n} → Transposition< n → String
showTransposition< (i X j) = show (toℕ i) ++S " X " ++S show (toℕ j)

Perm< : ℕ → Set
Perm< n = List (Transposition< n) 

filter= : {n : ℕ} → Perm n → Perm< n
filter= [] = []
filter= (_X_ i j {p≤} ∷ π) with toℕ i ≟ toℕ j
... | yes p= = filter= π 
... | no p≠ = _X_ i j {i≠j∧i≤j→i<j (toℕ i) (toℕ j) p≠ p≤}  ∷ filter= π 

-- Examples

nn₁ nn₂ nn₃ nn₄ nn₅ : List String
nn₁ = mapL showTransposition< (filter= (c2π neg₁))
   -- 0 X 1 ∷ []
nn₂ = mapL showTransposition< (filter= (c2π neg₂))
   -- 0 X 1 ∷ []
nn₃ = mapL showTransposition< (filter= (c2π neg₃))
   -- 0 X 1 ∷ 0 X 1 ∷ 0 X 1 ∷ []
nn₄ = mapL showTransposition< (filter= (c2π neg₄))
   -- 0 X 1 ∷ []
nn₅ = mapL showTransposition< (filter= (c2π neg₅))
   -- 0 X 1 ∷ []

ncnot ntoffoli : List String
ncnot = mapL showTransposition< (filter= (c2π CNOT))
   -- 2 X 3 ∷ []
ntoffoli = mapL showTransposition< (filter= (c2π TOFFOLI))
   -- 6 X 7 ∷ []

nswap12 nswap23 nswap13 nrotl nrotr : List String
nswap12 = mapL showTransposition< (filter= (c2π SWAP12))
   -- 0 X 1 ∷ []
nswap23 = mapL showTransposition< (filter= (c2π SWAP23))
   -- 1 X 2 ∷ []
nswap13 = mapL showTransposition< (filter= (c2π SWAP13))
   -- 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ []
nrotl   = mapL showTransposition< (filter= (c2π ROTL))
   -- 0 X 1 ∷ 1 X 2 ∷ []
nrotr   = mapL showTransposition< (filter= (c2π ROTR))
   -- 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ 1 X 2 ∷ []

nperes nfulladder : List String
nperes = mapL showTransposition< (filter= (c2π PERES))
   -- 6 X 7 ∷ 4 X 6 ∷ 5 X 7 ∷ []
nfulladder = mapL showTransposition< (filter= (c2π FULLADDER))
   -- 1 X 2 ∷ 1 X 4 ∷ 1 X 8 ∷  X 6 ∷ 3 X 12 ∷ 3 X 9 ∷ 5 X 10 ∷ 7 X 14 ∷
   -- 7 X 13 ∷ 7 X 11 ∷ 2 X 8 ∷ 3 X 9 ∷ 2 X 4 ∷ 3 X 5 ∷ 6 X 10 ∷ 7 X 11 ∷
   -- 6 X 12 ∷ 7 X 13 ∷ 1 X 2 ∷ 1 X 4 ∷ 1 X 8 ∷ 3 X 6 ∷ 3 X 12 ∷ 3 X 9 ∷
   -- 5 X 10 ∷ 7 X 14 ∷ 7 X 13 ∷ 7 X 11 ∷ 2 X 8 ∷ 3 X 9 ∷ 2 X 4 ∷ 3 X 5 ∷
   -- 6 X 10 ∷ 7 X 11 ∷ 6 X 12 ∷ 7 X 13 ∷ 12 X 14 ∷ 13 X 15 ∷ 2 X 4 ∷
   -- 3 X 5 ∷ 2 X 8 ∷ 3 X 9 ∷ 6 X 12 ∷ 7 X 13 ∷ 6 X 10 ∷ 7 X 11 ∷ 8 X 12 ∷
   -- 9 X 13 ∷ 10 X 14 ∷ 11 X 15 ∷ 1 X 2 ∷ 5 X 6 ∷ 9 X 10 ∷ 13 X 14 ∷
   -- 1 X 4 ∷ 1 X 2 ∷ 3 X 5 ∷ 3 X 6 ∷ 6 X 7 ∷1 X 2 ∷ 1 X 4 ∷ 3 X 6 ∷
   -- 3 X 5 ∷ 4 X 6 ∷ 5 X 7 ∷ 9 X 12 ∷ 9 X 10 ∷ 11 X 13 ∷ 11 X 14 ∷
   -- 14 X 15 ∷ 9 X 10 ∷ 9 X 12 ∷ 11 X 14 ∷ 11 X 13 ∷ 12 X 14 ∷ 13 X 15 ∷ []

-- Next we sort the list of transpositions using a variation of bubble
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
bubble : ∀ {n} → Perm< n → Perm< n
bubble [] = []
bubble (x ∷ []) = x ∷ []
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π) 
--
-- check every possible equality between the indices
--
  with toℕ i ≟ toℕ k | toℕ i ≟ toℕ l | toℕ j ≟ toℕ k | toℕ j ≟ toℕ l
--
-- get rid of a bunch of impossible cases given that i < j and k < l
--
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | _ | yes j≡k | yes j≡l 
  with trans (sym j≡k) (j≡l) | i<j→i≠j {toℕ k} {toℕ l} k<l
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | _ | yes j≡k | yes j≡l
  | k≡l | ¬k≡l with ¬k≡l k≡l
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | _ | yes j≡k | yes j≡l
  | k≡l | ¬k≡l | ()
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | yes i≡l | _ | yes j≡l 
  with trans i≡l (sym j≡l) | i<j→i≠j {toℕ i} {toℕ j} i<j
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | yes i≡l | _ | yes j≡l 
  | i≡j | ¬i≡j with ¬i≡j i≡j
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | yes i≡l | _ | yes j≡l 
  | i≡j | ¬i≡j | ()
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | _ | yes j≡k | _
  with trans i≡k (sym j≡k) | i<j→i≠j {toℕ i} {toℕ j} i<j 
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | _ | yes j≡k | _
  | i≡j | ¬i≡j with ¬i≡j i≡j
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | _ | yes j≡k | _
  | i≡j | ¬i≡j | ()
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | yes i≡l | _ | _
  with trans (sym i≡k) i≡l | i<j→i≠j {toℕ k} {toℕ l} k<l 
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | yes i≡l | _ | _
  | k≡l | ¬k≡l with ¬k≡l k≡l
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | yes i≡l | _ | _
  | k≡l | ¬k≡l | ()
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | yes i≡l | yes j≡k | _
  with subst₂ _<_ (sym j≡k) (sym i≡l) k<l | i<j→j≮i {toℕ i} {toℕ j} i<j
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | yes i≡l | yes j≡k | _
  | j<i | j≮i with j≮i j<i
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | _ | yes i≡l | yes j≡k | _
  | j<i | j≮i | ()
--
-- end of impossible cases
--
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l with toℕ i <? toℕ k
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l | yes i<k = 
  -- already sorted; no repeat in first position; skip and recur
  -- Ex: 2 X 5 , 3 X 4
    _X_ i j {i<j} ∷ bubble (_X_ k l {k<l} ∷ π)
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l | no i≮k = 
  -- Case B. 
  -- not sorted; no repeat in first position; no interference
  -- just slide one transposition past the other
  -- Ex: 2 X 5 , 1 X 4
  -- becomes 1 X 4 , 2 X 5
    _X_ k l {k<l} ∷  bubble (_X_ i j {i<j} ∷ π)
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | no ¬i≡l | no ¬j≡k | yes j≡l = 
  -- Case A. 
  -- transposition followed by its inverse; simplify by removing both
  -- Ex: 2 X 5 , 2 X 5
  -- becomes id and is deleted
  bubble π 
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l with toℕ i <? toℕ k 
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l | yes i<k = 
  -- already sorted; no repeat in first position; skip and recur
  -- Ex: 2 X 5 , 3 X 5 
    _X_ i j {i<j} ∷ bubble (_X_ k l {k<l} ∷ π)
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l | no i≮k = 
  _X_ k i 
    {i≰j∧j≠i→j<i (toℕ i) (toℕ k) (i≮j∧i≠j→i≰j (toℕ i) (toℕ k) i≮k ¬i≡k) 
       (i≠j→j≠i (toℕ i) (toℕ k) ¬i≡k)} ∷
  bubble (_X_ i j {i<j} ∷ π)
  -- Case C. 
  -- Ex: 2 X 5 , 1 X 5 
  -- becomes 1 X 2 , 2 X 5
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | no ¬i≡k | no ¬i≡l | yes j≡k | no ¬j≡l = 
  -- already sorted; no repeat in first position; skip and recur
  -- Ex: 2 X 5 , 5 X 6 
   _X_ i j {i<j} ∷ bubble (_X_ k l {k<l} ∷ π)
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | no ¬i≡k | yes i≡l | no ¬j≡k | no ¬j≡l = 
  -- Case D. 
  -- Ex: 2 X 5 , 1 X 2 
  -- becomes 1 X 5 , 2 X 5
  _X_ k j {trans< (subst ((λ l → toℕ k < l)) (sym i≡l) k<l) i<j} ∷
  bubble (_X_ i j {i<j} ∷ π)
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l with toℕ j <? toℕ l
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l | yes j<l =
  -- Case E. 
  -- Ex: 2 X 5 , 2 X 6
  -- becomes 2 X 6 , 5 X 6
  _X_ k l {k<l} ∷ bubble (_X_ j l {j<l} ∷ π)
bubble (_X_ i j {i<j} ∷ _X_ k l {k<l} ∷ π)
  | yes i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l | no j≮l = 
  -- Case F. 
  -- Ex: 2 X 5 , 2 X 3
  -- becomes 2 X 3 , 3 X 5 
  _X_ k l {k<l} ∷ 
  bubble (_X_ l j {i≰j∧j≠i→j<i (toℕ j) (toℕ l) 
                    (i≮j∧i≠j→i≰j (toℕ j) (toℕ l) j≮l ¬j≡l)
                    (i≠j→j≠i (toℕ j) (toℕ l) ¬j≡l)} ∷ π)

-- sorted and no repeats in first position

{-# NO_TERMINATION_CHECK #-}
canonical? : ∀ {n} → Perm< n → Bool
canonical? [] = true
canonical? (x ∷ []) = true
canonical? (i X j ∷ k X l ∷ π) with toℕ i <? toℕ k
canonical? (i X j ∷ _X_ k l {k<l}  ∷ π) | yes i<k = 
  canonical? (_X_ k l {k<l} ∷ π)
canonical? (i X j ∷ _X_ k l {k<l} ∷ π) | no i≮k = false

{-# NO_TERMINATION_CHECK #-}
sort : ∀ {n} → Perm< n → Perm< n
sort π with canonical? π 
sort π | true = π 
sort π | false = sort (bubble π)

-- Examples

snn₁ snn₂ snn₃ snn₄ snn₅ : List String
snn₁ = mapL showTransposition< (sort (filter= (c2π neg₁)))
   -- 0 X 1 ∷ []
snn₂ = mapL showTransposition< (sort (filter= (c2π neg₂)))
   -- 0 X 1 ∷ []
snn₃ = mapL showTransposition< (sort (filter= (c2π neg₃)))
   -- 0 X 1 ∷ []
snn₄ = mapL showTransposition< (sort (filter= (c2π neg₄)))
   -- 0 X 1 ∷ []
snn₅ = mapL showTransposition< (sort (filter= (c2π neg₅)))
   -- 0 X 1 ∷ []

sncnot sntoffoli : List String
sncnot = mapL showTransposition< (sort (filter= (c2π CNOT)))
   -- 2 X 3 ∷ []
sntoffoli = mapL showTransposition< (sort (filter= (c2π TOFFOLI)))
   -- 6 X 7 ∷ []

snswap12 snswap23 snswap13 snrotl snrotr : List String
snswap12 = mapL showTransposition< (sort (filter= (c2π SWAP12)))
   -- 0 X 1 ∷ []
snswap23 = mapL showTransposition< (sort (filter= (c2π SWAP23)))
   -- 1 X 2 ∷ []
snswap13 = mapL showTransposition< (sort (filter= (c2π SWAP13)))
   -- before sorting: 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ []
   -- after sorting : 0 X 2 ∷ []
snrotl   = mapL showTransposition< (sort (filter= (c2π ROTL)))
   -- 0 X 1 ∷ 1 X 2 ∷ []
snrotr   = mapL showTransposition< (sort (filter= (c2π ROTR)))
   -- before sorting: 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ 1 X 2 ∷ []
   -- after sorting:  0 X 2 ∷ 1 X 2 ∷ []

snperes snfulladder : List String
snperes = mapL showTransposition< (sort (filter= (c2π PERES)))
   -- before sorting: 6 X 7 ∷ 4 X 6 ∷ 5 X 7 ∷ []
   -- after sorting:  4 X 7 ∷ 5 X 6 ∷ 6 X 7 ∷ []
   -- Apply the transpositions:
   -- 000 000
   -- 001 001
   -- 010 010
   -- 011 011
   -- 111 100
   -- 110 101
   -- 100 110
   -- 101 111
   -- for comparison, here is the result of showπ
   -- (((false , false) , false) , (false , false) , false) ∷
   -- (((false , false) , true)  , (false , false) , true)  ∷
   -- (((false , true)  , false) , (false , true)  , false) ∷
   -- (((false , true)  , true)  , (false , true)  , true)  ∷
   -- (((true  , true)  , true)  , (true  , false) , false) ∷
   -- (((true  , true)  , false) , (true  , false) , true)  ∷
   -- (((true  , false) , false) , (true  , true)  , false) ∷
   -- (((true  , false) , true)  , (true  , true)  , true)  ∷ []
   -- Perfect!

snfulladder = mapL showTransposition< (sort (filter= (c2π FULLADDER)))
   -- 1 X 8 ∷ 2 X 8 ∷ 3 X 9 ∷ 4 X 9 ∷ 5 X 10 ∷ 6 X 8 ∷ 7 X 11 ∷
   -- 9 X 12 ∷ 10 X 11 ∷ 11 X 13 ∷ 12 X 13 ∷ 13 X 14 ∷ []

------------------------------------------------------------------------------
