{-# OPTIONS --without-K #-}

module Pif where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+)
open import Relation.Binary using (Rel; Decidable)

open import Data.String using (String)
  renaming (_++_ to _++S_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  z≤n; s≤s; _≟_; _≤?_; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; _ℕ-_; 
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)
open import Data.Fin.Properties using (bounded)              

open import Data.List 
  using (List; []; _∷_; foldl; replicate; reverse; downFrom; gfilter) 
  renaming (_++_ to _++L_; map to mapL; concat to concatL)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Vec 
  using (Vec; tabulate; []; _∷_; [_]; tail; lookup; zip; zipWith; 
         _[_]≔_; allFin; toList)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import Function using (id; _∘_)

open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

open import Groupoid

------------------------------------------------------------------------------
-- Proofs and definitions about natural numbers

_<?_ : Decidable _<_
i <? j = suc i ≤? j

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
  ENUM  : ℕ → U      -- for testing

⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ BOOL ⟧        = Bool
⟦ ENUM n ⟧      = ℕ

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
-- finite types which naturally induces paths between the points. More
-- precisely, two types t₁ and t₂ have a path between them if there is
-- a permutation (c : t₁ ⟷ t₂). The fact that c is a permutation
-- guarantees, by construction, that (c ◎ ! c ∼ id⟷) and (! c ◎ c ∼
-- id⟷). A complete set of generators for all possible permutations
-- between finite types is given by the following definition. Note
-- that these permutations do not reach inside the types and hence do
-- not generate paths between the points within the types. The paths
-- are just between the types themselves.

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

-- Nicer syntax that shows intermediate values instead of the above
-- point-free notation of permutations

infixr 2  _⟷⟨_⟩_   
infix  2  _□       

_⟷⟨_⟩_ : (t₁ : U) {t₂ : U} {t₃ : U} → 
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃) 
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U) → {t : U} → (t ⟷ t)
_□ t = id⟷

-- Many ways of negating a BOOL. Again, it is absolutely critical that there
-- is NO path between false⟷ and true⟷. These permutations instead are based
-- on paths between x and neg (neg x) which are the trivial paths on each of
-- the two points in BOOL.

not⟷ : BOOL ⟷ BOOL
not⟷ = unfoldBool ◎ swap₊ ◎ foldBool

neg₁ neg₂ neg₃ neg₄ neg₅ : BOOL ⟷ BOOL
neg₁ = unfoldBool ◎ swap₊ ◎ foldBool
neg₂ = id⟷ ◎ not⟷ 
neg₃ = not⟷ ◎ not⟷ ◎ not⟷ 
neg₄ = not⟷ ◎ id⟷
neg₅ = uniti⋆ ◎ swap⋆ ◎ (not⟷ ⊗ id⟷) ◎ swap⋆ ◎ unite⋆

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
SWAP23 = id⟷ ⊕ swap₊
SWAP13 = SWAP23 ◎ SWAP12 ◎ SWAP23 
ROTL   = SWAP12 ◎ SWAP23
ROTR   = SWAP13 ◎ SWAP23

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
-- Types as vectors of elements

-- A canonical representation of each type as a vector of values. This
-- fixes a canonical order for the elements of the types: each value
-- has a canonical index.

size : U → ℕ
size ZERO          = 0
size ONE           = 1
size (PLUS t₁ t₂)  = size t₁ + size t₂
size (TIMES t₁ t₂) = size t₁ * size t₂
size BOOL          = 2
size (ENUM n)      = n

utoVec : (t : U) → Vec ⟦ t ⟧ (size t)
utoVec ZERO          = []
utoVec ONE           = [ tt ]
utoVec (PLUS t₁ t₂)  = mapV inj₁ (utoVec t₁) ++V (mapV inj₂ (utoVec t₂))
utoVec (TIMES t₁ t₂) = 
  concatV (mapV (λ v₁ → mapV (λ v₂ → (v₁ , v₂)) (utoVec t₂)) (utoVec t₁))
utoVec BOOL          = false ∷ true ∷ []
utoVec (ENUM n)      = tabulate toℕ

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
-- Semantic representation of permutations

-- One possibility of course is to represent them as functions but
-- this is a poor representation and eventually requires function
-- extensionality. 

-- A permutation is a sequence of "swaps" or "transpositions"; 
-- we allow any sequence of swaps, even "stupid ones"
-- Ex: Perm 4 could have this permutation as an element (1 2) (2 3) (3 1)
-- It could also have (1 2) (1 3) (1 1) (2 1) (2 1) (1 2)
-- to compare two permutations we need to normalize them
-- 
-- For normalization purposes, we insist that the first component of a
-- transposition is always ≤ than the second

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
-- n by applying the swaps, one by one.

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

swapπ : ∀ {m n} → Perm (m + n)
swapπ {0}     {n}     = []
swapπ {suc m} {n}     = 
  concatL 
    (replicate (suc m)
      (toList 
        (zipWith mkTransposition
          (mapV inject₁ (allFin (m + n))) 
          (tail (allFin (suc m + n))))))

-- Sequential composition is just append

scompπ : ∀ {n} → Perm n → Perm n → Perm n
scompπ = _++L_

-- Parallel additive composition 
-- append both permutations but shift the second permutation by the size
-- of the first type so that it acts on the second part of the vector
-- Let α = [ m₀ X n₀ , m₁ X n₁ , ... m₇ X n₇ₛ]
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

-- Tensor multiplicative composition

-- expand id permutation to [ i X i ... ] for all i 

idπ : ∀ {n} → Perm n
idπ {n} = toList (zipWith mkTransposition (allFin n) (allFin n))

-- Swaps in α correspond to swapping entire rows
-- Swaps in β correspond to swapping entire columns
-- Need to make sure neither α nor β is empty; otherwise composition annhilates
-- So explicitly represent identity permutations using a sequence of self-swaps

tcompπ : ∀ {m n} → Perm m → Perm n → Perm (m * n)
tcompπ {m} {n} α β = 
  concatL (mapL 
            (λ { (i X j) → 
                 mapL (λ { (k X l) → 
                        mkTransposition
                          (inject≤ (fromℕ (toℕ i * n + toℕ k)) 
                                   (i*n+k≤m*n i k))
                          (inject≤ (fromℕ (toℕ j * n + toℕ l)) 
                                   (i*n+k≤m*n j l))})
                      (β ++L idπ {n})})
            (α ++L idπ {m}))

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes a permutation.

c2π : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Perm (size t₁)
c2π unite₊    = []
c2π uniti₊    = []
c2π {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ = swapπ {size t₁} {size t₂}
c2π assocl₊   = []
c2π assocr₊   = []
c2π unite⋆    = []
c2π uniti⋆    = []
c2π swap⋆     = [] 
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
neg₂π = showπ {BOOL} {BOOL} neg₂  -- ok
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
swap12π = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} SWAP12
swap23π = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} SWAP23
swap13π = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} SWAP13
rotlπ   = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} ROTL
rotrπ   = showπ {PLUS ONE (PLUS ONE ONE)} {PLUS ONE (PLUS ONE ONE)} ROTR

-- Normalization

-- The various realizations of negation are equivalent but they give
-- different sequences of transpositions:

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
toffoli = mapL showTransposition (c2π TOFFOLI)

swap12 swap23 swap13 rotl rotr : List String
swap12 = mapL showTransposition (c2π SWAP12)
   -- 0 X 1 ∷ []
swap23 = mapL showTransposition (c2π SWAP23)
   -- 1 X 2 ∷ []
swap13 = mapL showTransposition (c2π SWAP13)
   -- 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ []
   -- normalized should be: 0 X 2 ∷ []
rotl   = mapL showTransposition (c2π ROTL)
   -- 0 X 1 ∷ 1 X 2 ∷ []
rotr   = mapL showTransposition (c2π ROTR)
   -- 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ 1 X 2 ∷ []
   -- normalized should be: 1 X 2 ∷ 0 X 1 ∷ []

-- First, remove all trivial transpositions (i X i)

data Transposition< (n : ℕ) : Set where
  _X_ : (i j : Fin n) → {p : toℕ i < toℕ j} → Transposition< n

showTransposition< : ∀ {n} → Transposition< n → String
showTransposition< (i X j) = show (toℕ i) ++S " X " ++S show (toℕ j)

Perm< : ℕ → Set
Perm< n = List (Transposition< n) 

normalize< : {n : ℕ} → Perm n → Perm< n
normalize< [] = []
normalize< (_X_ i j {p≤} ∷ π) with toℕ i ≟ toℕ j
... | yes p= = normalize< π 
... | no p≠ = _X_ i j {i≠j∧i≤j→i<j (toℕ i) (toℕ j) p≠ p≤}  ∷ normalize< π 

-- Examples

nn₁ nn₂ nn₃ nn₄ nn₅ : List String
nn₁ = mapL showTransposition< (normalize< (c2π neg₁))
   -- 0 X 1 ∷ []
nn₂ = mapL showTransposition< (normalize< (c2π neg₂))
   -- 0 X 1 ∷ []
nn₃ = mapL showTransposition< (normalize< (c2π neg₃))
   -- 0 X 1 ∷ 0 X 1 ∷ 0 X 1 ∷ []
nn₄ = mapL showTransposition< (normalize< (c2π neg₄))
   -- 0 X 1 ∷ []
nn₅ = mapL showTransposition< (normalize< (c2π neg₅))
   -- 0 X 1 ∷ []

ncnot ntoffoli : List String
ncnot = mapL showTransposition< (normalize< (c2π CNOT))
   -- 2 X 3 ∷ []
ntoffoli = mapL showTransposition< (normalize< (c2π TOFFOLI))
   -- 6 X 7 ∷ []

nswap12 nswap23 nswap13 nrotl nrotr : List String
nswap12 = mapL showTransposition< (normalize< (c2π SWAP12))
   -- 0 X 1 ∷ []
nswap23 = mapL showTransposition< (normalize< (c2π SWAP23))
   -- 1 X 2 ∷ []
nswap13 = mapL showTransposition< (normalize< (c2π SWAP13))
   -- 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ []
   -- normalized should be: 0 X 2 ∷ []
nrotl   = mapL showTransposition< (normalize< (c2π ROTL))
   -- 0 X 1 ∷ 1 X 2 ∷ []
nrotr   = mapL showTransposition< (normalize< (c2π ROTR))
   -- 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ 1 X 2 ∷ []
   -- normalized should be: 1 X 2 ∷ 0 X 1 ∷ []

-- Next we sort the list of transpositions

module Sort (A : Set) {_<_ : Rel A lzero} ( _<?_ : Decidable _<_) where
  insert : (A × A → A × A) → A → List A → List A
  insert shift x [] = x ∷ []
  insert shift x (y ∷ ys) with x <? y
  ... | yes _ = x ∷ y ∷ ys
  ... | no _ = let (y' , x') = shift (x , y) 
               in y' ∷ insert shift x' ys

  sort : (A × A → A × A) → List A → List A
  sort shift [] = []
  sort shift (x ∷ xs) = insert shift x (sort shift xs)

data _<S_ {n : ℕ} : Rel (Transposition< n) lzero where
   <1 : ∀ {i j k l : Fin n} {p₁ : toℕ i < toℕ j} {p₂ : toℕ k < toℕ l} → 
       (toℕ i < toℕ k) → (_X_ i j {p₁}) <S (_X_ k l {p₂})
   <2 : ∀ {i j k l : Fin n} {p₁ : toℕ i < toℕ j} {p₂ : toℕ k < toℕ l} →  
       (toℕ i ≡ toℕ k) → (toℕ j < toℕ l) → 
       (_X_ i j {p₁}) <S (_X_ k l {p₂})

d<S : {n : ℕ} → Decidable (_<S_ {n})
d<S (_X_ i j {p₁}) (_X_ k l {p₂}) with suc (toℕ i) ≤? toℕ k 
d<S (_X_ i j {p₁}) (_X_ k l {p₂}) | yes p = yes (<1 p)
d<S (_X_ i j {p₁}) (_X_ k l {p₂}) | no p with toℕ i ≟ toℕ k
d<S (_X_ i j {p₁}) (_X_ k l {p₂}) | no p | yes p= with suc (toℕ j) ≤? toℕ l
d<S (_X_ i j {p₁}) (_X_ k l {p₂}) | no p | yes p= | yes p' = yes (<2 p= p')
d<S (_X_ i j {p₁}) (_X_ k l {p₂}) | no p | yes p= | no p' = 
  no (λ { (<1 i<k) → p i<k ;
          (<2 i≡k j<l) → p' j<l})
d<S (_X_ i j {p₁}) (_X_ k l {p₂}) | no p | no p≠ = 
  no (λ { (<1 i<k) → p i<k ;
          (<2 i≡k j<l) → p≠ i≡k })

module TSort (n : ℕ) = Sort (Transposition< n) {_<S_} d<S 

-- If we shift a transposition past another, there is nothing to do if
-- the four indices are different. If however there is a common index,
-- we have to adjust the transpositions.

shift : {n : ℕ} → Transposition< n × Transposition< n → 
                  Transposition< n × Transposition< n
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  with toℕ i ≟ toℕ k | toℕ i ≟ toℕ l | toℕ j ≟ toℕ k | toℕ j ≟ toℕ l
shift {n} (_X_ i j {i<j} , _X_ k l {k<l})  
  | _ | _ | yes j≡k | yes j≡l 
  with trans (sym j≡k) (j≡l) | i<j→i≠j {toℕ k} {toℕ l} k<l
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | _ | _ | yes j≡k | yes j≡l
  | k≡l | ¬k≡l with ¬k≡l k≡l
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | _ | _ | yes j≡k | yes j≡l
  | k≡l | ¬k≡l | ()
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | _ | yes i≡l | _ | yes j≡l 
  with trans i≡l (sym j≡l) | i<j→i≠j {toℕ i} {toℕ j} i<j
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | _ | yes i≡l | _ | yes j≡l 
  | i≡j | ¬i≡j with ¬i≡j i≡j
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | _ | yes i≡l | _ | yes j≡l 
  | i≡j | ¬i≡j | ()
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | yes i≡k | _ | yes j≡k | _
  with trans i≡k (sym j≡k) | i<j→i≠j {toℕ i} {toℕ j} i<j 
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | yes i≡k | _ | yes j≡k | _
  | i≡j | ¬i≡j with ¬i≡j i≡j
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | yes i≡k | _ | yes j≡k | _
  | i≡j | ¬i≡j | ()
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | yes i≡k | yes i≡l | _ | _
  with trans (sym i≡k) i≡l | i<j→i≠j {toℕ k} {toℕ l} k<l 
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | yes i≡k | yes i≡l | _ | _
  | k≡l | ¬k≡l with ¬k≡l k≡l
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | yes i≡k | yes i≡l | _ | _
  | k≡l | ¬k≡l | ()
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | _ | yes i≡l | yes j≡k | _
  with subst₂ _<_ (sym j≡k) (sym i≡l) k<l | i<j→j≮i {toℕ i} {toℕ j} i<j
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | _ | yes i≡l | yes j≡k | _
  | j<i | j≮i with j≮i j<i
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | _ | yes i≡l | yes j≡k | _
  | j<i | j≮i | ()
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l = 
    -- no interference
    (_X_ k l {k<l} , _X_ i j {i<j})  
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | yes i≡k | no ¬i≡l | no ¬j≡k | yes j≡l = 
  -- Ex: 2 X 5 , 2 X 5
  (_X_ k l {k<l} , _X_ i j {i<j})   
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l 
  with toℕ i <? toℕ k 
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l 
  | yes i<k = 
  (_X_ i k {i<k} , _X_ i j {i<j})
  -- Ex: 2 X 5 , 3 X 5 
  -- becomes 2 X 3 , 2 X 5
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | no ¬i≡k | no ¬i≡l | no ¬j≡k | yes j≡l 
  | no i≮k = 
  (_X_ k i 
    {i≰j∧j≠i→j<i (toℕ i) (toℕ k) (i≮j∧i≠j→i≰j (toℕ i) (toℕ k) i≮k ¬i≡k) 
       (i≠j→j≠i (toℕ i) (toℕ k) ¬i≡k)} , 
  _X_ i j {i<j}) 
  -- Ex: 2 X 5 , 1 X 5 
  -- becomes 1 X 2 , 2 X 5
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | no ¬i≡k | no ¬i≡l | yes j≡k | no ¬j≡l = 
    -- Ex: 2 X 5 , 5 X 6 
  {!!} 
shift {n} (_X_ i j {i<j} , _X_ k l {k<l})  
  | no ¬i≡k | yes i≡l | no ¬j≡k | no ¬j≡l = 
  -- Ex: 2 X 5 , 1 X 2 
  {!!} 
shift {n} (_X_ i j {i<j} , _X_ k l {k<l}) 
  | yes i≡k | no ¬i≡l | no ¬j≡k | no ¬j≡l =
  -- Ex: 2 X 5 , 2 X 4
  {!!}

-- Examples

snn₁ snn₂ snn₃ snn₄ snn₅ : List String
snn₁ = mapL showTransposition< (sort shift (normalize< (c2π neg₁)))
  where open TSort 2
   -- 0 X 1 ∷ []
snn₂ = mapL showTransposition< (sort shift (normalize< (c2π neg₂)))
  where open TSort 2
   -- 0 X 1 ∷ []
snn₃ = mapL showTransposition< (sort shift (normalize< (c2π neg₃)))
  where open TSort 2
   -- 0 X 1 ∷ 0 X 1 ∷ 0 X 1 ∷ []
snn₄ = mapL showTransposition< (sort shift (normalize< (c2π neg₄)))
  where open TSort 2
   -- 0 X 1 ∷ []
snn₅ = mapL showTransposition< (sort shift (normalize< (c2π neg₅)))
  where open TSort 2
   -- 0 X 1 ∷ []

sncnot sntoffoli : List String
sncnot = mapL showTransposition< (sort shift (normalize< (c2π CNOT)))
  where open TSort 4
   -- 2 X 3 ∷ []
sntoffoli = mapL showTransposition< (sort shift (normalize< (c2π TOFFOLI)))
  where open TSort 8
   -- 6 X 7 ∷ []

snswap12 snswap23 snswap13 snrotl snrotr : List String
snswap12 = mapL showTransposition< (sort shift (normalize< (c2π SWAP12)))
  where open TSort 3
   -- 0 X 1 ∷ []
snswap23 = mapL showTransposition< (sort shift (normalize< (c2π SWAP23)))
  where open TSort 3
   -- 1 X 2 ∷ []
snswap13 = mapL showTransposition< (sort shift (normalize< (c2π SWAP13)))
  where open TSort 3
   -- before sorting: 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ []
   -- after sorting: 0 X 1 ∷ 1 X 2 ∷ 1 X 2 ∷ []
   -- normalized should be: 0 X 2 ∷ []
   -- soring is WRONG: moving 0 X 1 past 1 X 2 should affect the indices!!!
snrotl   = mapL showTransposition< (sort shift (normalize< (c2π ROTL)))
  where open TSort 3
   -- 0 X 1 ∷ 1 X 2 ∷ []
snrotr   = mapL showTransposition< (sort shift (normalize< (c2π ROTR)))
  where open TSort 3
   -- before sorting: 1 X 2 ∷ 0 X 1 ∷ 1 X 2 ∷ 1 X 2 ∷ []
   -- after sorting:  0 X 1 ∷ 1 X 2 ∷ 1 X 2 ∷ 1 X 2 ∷ []
   -- WRONG again
   -- normalized should be: 1 X 2 ∷ 0 X 1 ∷ []

{--
-- Normalized permutations have exactly one entry for each position

infixr 5 _∷_

data NPerm : ℕ → Set where
  []  : NPerm 0
  _∷_ : {n : ℕ} → Fin (suc n) → NPerm n → NPerm (suc n)

lookupP : ∀ {n} → Fin n → NPerm n → Fin n
lookupP () [] 
lookupP zero (j ∷ _) = j
lookupP {suc n} (suc i) (j ∷ q) = inject₁ (lookupP i q)

insert : ∀ {ℓ n} {A : Set ℓ} → Vec A n → Fin (suc n) → A → Vec A (suc n)
insert vs zero w          = w ∷ vs
insert [] (suc ())        -- absurd
insert (v ∷ vs) (suc i) w = v ∷ insert vs i w

-- A normalized permutation acts on a vector by inserting each element in its
-- new position.

permute : ∀ {ℓ n} {A : Set ℓ} → NPerm n → Vec A n → Vec A n
permute []       []       = []
permute (p ∷ ps) (v ∷ vs) = insert (permute ps vs) p v

-- Convert normalized permutation to a sequence of transpositions

nperm2list : ∀ {n} → NPerm n → Perm< n
nperm2list {0} [] = []
nperm2list {suc n} (p ∷ ps) = {!!} 

-- Aggregate a sequence of transpositions to one insertion in the right
-- position

aggregate : ∀ {n} → Perm< n → NPerm n
aggregate = {!!} 

{--
aggregate [] = []
aggregate (_X_ i j {p₁} ∷ []) = _X_ i j {p₁} ∷ []
aggregate (_X_ i j {p₁} ∷ _X_ k l {p₂} ∷ π) with toℕ i ≟ toℕ k | toℕ j ≟ toℕ l 
aggregate (_X_ i j {p₁} ∷ _X_ k l {p₂} ∷ π) | yes _ | yes _ = 
  aggregate (_X_ k l {p₂} ∷ π)
aggregate (_X_ i j {p₁} ∷ _X_ k l {p₂} ∷ π) | _ | _ = 
  (_X_ i j {p₁}) ∷ aggregate (_X_ k l {p₂} ∷ π)
--}

normalize : ∀ {n} → Perm n → NPerm n
normalize {n} = aggregate ∘ sort ∘ normalize< 
  where open TSort n

-- Examples

nsnn₁ nsnn₂ nsnn₃ nsnn₄ nsnn₅ : List String
nsnn₁ = mapL showTransposition< (nperm2list (normalize (c2π neg₁)))
  where open TSort 2
   -- 0 X 1 ∷ []
nsnn₂ = mapL showTransposition< (nperm2list (normalize (c2π neg₂)))
  where open TSort 2
   -- 0 X 1 ∷ []
nsnn₃ = mapL showTransposition< (nperm2list (normalize (c2π neg₃)))
  where open TSort 2
   -- 0 X 1 ∷ []
nsnn₄ = mapL showTransposition< (nperm2list (normalize (c2π neg₄)))
  where open TSort 2
   -- 0 X 1 ∷ []
nsnn₅ = mapL showTransposition< (nperm2list (normalize (c2π neg₅)))
  where open TSort 2
   -- 0 X 1 ∷ []

nswap₁₂ nswap₂₃ nswap₁₃ : List String
nswap₁₂ = mapL showTransposition< (nperm2list (normalize (c2π SWAP12)))
nswap₂₃ = mapL showTransposition< (nperm2list (normalize (c2π SWAP23)))
nswap₁₃ = mapL showTransposition< (nperm2list (normalize (c2π SWAP13)))

------------------------------------------------------------------------------
-- Extensional equivalence of combinators: two combinators are
-- equivalent if they denote the same permutation. Generally we would
-- require that the two permutations map the same value x to values y
-- and z that have a path between them, but because the internals of each
-- type are discrete groupoids, this reduces to saying that y and z
-- are identical, and hence that the permutations are identical.

infix  10  _∼_  

_∼_ : ∀ {t₁ t₂} → (c₁ c₂ : t₁ ⟷ t₂) → Set
c₁ ∼ c₂ = (normalize (c2π c₁) ≡ normalize (c2π c₂))

-- The relation ~ is an equivalence relation

refl∼ : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → (c ∼ c)
refl∼ = refl 

sym∼ : ∀ {t₁ t₂} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₁)
sym∼ = sym

trans∼ : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₃) → (c₁ ∼ c₃)
trans∼ = trans

-- The relation ~ validates the groupoid laws

c◎id∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ id⟷ ∼ c
c◎id∼c = {!!} 

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
        ; ∘-resp-≈ = {!!} -- λ α β → resp∼ β α 
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

{--
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
--}

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

π2c : {t₁ t₂ : U} → (size t₁ ≡ size t₂) → NPerm (size t₁) → (t₁ ⟷ t₂)
π2c = {!!}

------------------------------------------------------------------------------
-- Soundness and completeness
-- 
-- Proof of soundness and completeness: now we want to verify that ⇔
-- is sound and complete with respect to ∼. The statement to prove is
-- that for all c₁ and c₂, we have c₁ ∼ c₂ iff c₁ ⇔ c₂

soundness : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₁ ∼ c₂)
soundness assoc◎l      = {!!} -- assoc∼
soundness assoc◎r      = {!!} -- sym∼ assoc∼
soundness assoc⊕l      = {!!} -- assoc⊕∼
soundness assoc⊕r      = {!!} -- sym∼ assoc⊕∼
soundness assoc⊗l      = {!!} -- assoc⊗∼
soundness assoc⊗r      = {!!} -- sym∼ assoc⊗∼
soundness dist⇔        = {!!}
soundness factor⇔      = {!!}
soundness idl◎l        = {!!} -- id◎c∼c
soundness idl◎r        = {!!} -- sym∼ id◎c∼c
soundness idr◎l        = {!!} -- c◎id∼c
soundness idr◎r        = {!!} -- sym∼ c◎id∼c
soundness linv◎l       = {!!} -- linv∼
soundness linv◎r       = {!!} -- sym∼ linv∼
soundness rinv◎l       = {!!} -- rinv∼
soundness rinv◎r       = {!!} -- sym∼ rinv∼
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
soundness id⇔          = {!!} -- refl∼
soundness (trans⇔ α β) = {!!} -- trans∼ (soundness α) (soundness β)
soundness (resp◎⇔ α β) = {!!} -- resp∼ (soundness α) (soundness β)
soundness (resp⊕⇔ α β) = {!!}
soundness (resp⊗⇔ α β) = {!!} 

-- The idea is to invert evaluation and use that to extract from each
-- extensional representation of a combinator, a canonical syntactic
-- representative

canonical : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂)
canonical c = π2c (size≡ c) (normalize (c2π c))

-- Note that if c₁ ⇔ c₂, then by soundness c₁ ∼ c₂ and hence their
-- canonical representatives are identical. 

canonicalWellDefined : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → 
  (c₁ ⇔ c₂) → (canonical c₁ ≡ canonical c₂)
canonicalWellDefined {t₁} {t₂} {c₁} {c₂} α = 
  cong₂ π2c (size∼ c₁ c₂) (soundness α) 

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
    ⇔⟨  resp≡⇔ (cong₂ π2c (size∼ c₁ c₂) c₁∼c₂) ⟩ 
  canonical c₂
    ⇔⟨ 2! inversion ⟩ 
  c₂ ▤

------------------------------------------------------------------------------

{--
-- normalize a finite type to (1 + (1 + (1 + ... + (1 + 0) ... )))
-- a bunch of ones ending with zero with left biased + in between

toℕ : U → ℕ
toℕ ZERO          = 0
toℕ ONE           = 1
toℕ (PLUS t₁ t₂)  = toℕ t₁ + toℕ t₂
toℕ (TIMES t₁ t₂) = toℕ t₁ * toℕ t₂

fromℕ : ℕ → U
fromℕ 0       = ZERO
fromℕ (suc n) = PLUS ONE (fromℕ n)

normalℕ : U → U
normalℕ = fromℕ ∘ toℕ

-- invert toℕ: give t and n such that toℕ t = n, return constraints on components of t

reflectPlusZero : {m n : ℕ} → (m + n ≡ 0) → m ≡ 0 × n ≡ 0
reflectPlusZero {0} {0} refl = (refl , refl)
reflectPlusZero {0} {suc n} ()
reflectPlusZero {suc m} {0} ()
reflectPlusZero {suc m} {suc n} ()

-- nbe

nbe : {t₁ t₂ : U} → (p : toℕ t₁ ≡ toℕ t₂) → (⟦ t₁ ⟧ → ⟦ t₂ ⟧) → (t₁ ⟷ t₂)
nbe {ZERO} {ZERO} refl f = id⟷
nbe {ZERO} {ONE} ()
nbe {ZERO} {PLUS t₁ t₂} p f = {!!} 
nbe {ZERO} {TIMES t₂ t₃} p f = {!!}
nbe {ONE} {ZERO} ()
nbe {ONE} {ONE} p f = id⟷
nbe {ONE} {PLUS t₂ t₃} p f = {!!}
nbe {ONE} {TIMES t₂ t₃} p f = {!!}
nbe {PLUS t₁ t₂} {ZERO} p f = {!!}
nbe {PLUS t₁ t₂} {ONE} p f = {!!}
nbe {PLUS t₁ t₂} {PLUS t₃ t₄} p f = {!!}
nbe {PLUS t₁ t₂} {TIMES t₃ t₄} p f = {!!}
nbe {TIMES t₁ t₂} {ZERO} p f = {!!}
nbe {TIMES t₁ t₂} {ONE} p f = {!!}
nbe {TIMES t₁ t₂} {PLUS t₃ t₄} p f = {!!}
nbe {TIMES t₁ t₂} {TIMES t₃ t₄} p f = {!!} 

-- build a combinator that does the normalization

assocrU : {m : ℕ} (n : ℕ) → (PLUS (fromℕ n) (fromℕ m)) ⟷ fromℕ (n + m)
assocrU 0       = unite₊
assocrU (suc n) = assocr₊ ◎ (id⟷ ⊕ assocrU n)

distrU : (m : ℕ) {n : ℕ} → TIMES (fromℕ m) (fromℕ n) ⟷ fromℕ (m * n)
distrU 0           = distz
distrU (suc n) {m} = dist ◎ (unite⋆ ⊕ distrU n) ◎ assocrU m

normalU : (t : U) → t ⟷ normalℕ t
normalU ZERO          = id⟷
normalU ONE           = uniti₊ ◎ swap₊
normalU (PLUS t₁ t₂)  = (normalU t₁ ⊕ normalU t₂) ◎ assocrU (toℕ t₁)
normalU (TIMES t₁ t₂) = (normalU t₁ ⊗ normalU t₂) ◎ distrU (toℕ t₁)

-- a few lemmas

fromℕplus : {m n : ℕ} → fromℕ (m + n) ⟷ PLUS (fromℕ m) (fromℕ n)
fromℕplus {0} {n} = 
  fromℕ n
    ⟷⟨ uniti₊ ⟩
  PLUS ZERO (fromℕ n) □
fromℕplus {suc m} {n} = 
  fromℕ (suc (m + n))
    ⟷⟨ id⟷ ⟩ 
  PLUS ONE (fromℕ (m + n))
    ⟷⟨ id⟷ ⊕ fromℕplus {m} {n} ⟩ 
  PLUS ONE (PLUS (fromℕ m) (fromℕ n))
    ⟷⟨ assocl₊ ⟩ 
  PLUS (PLUS ONE (fromℕ m)) (fromℕ n)
    ⟷⟨ id⟷ ⟩ 
  PLUS (fromℕ (suc m)) (fromℕ n) □

normalℕswap : {t₁ t₂ : U} → normalℕ (PLUS t₁ t₂) ⟷ normalℕ (PLUS t₂ t₁)
normalℕswap {t₁} {t₂} = 
  fromℕ (toℕ t₁ + toℕ t₂) 
    ⟷⟨ fromℕplus {toℕ t₁} {toℕ t₂} ⟩
  PLUS (normalℕ t₁) (normalℕ t₂)
    ⟷⟨ swap₊ ⟩
  PLUS (normalℕ t₂) (normalℕ t₁)
    ⟷⟨ ! (fromℕplus {toℕ t₂} {toℕ t₁}) ⟩
  fromℕ (toℕ t₂ + toℕ t₁) □

assocrUS : {m : ℕ} {t : U} → PLUS t (fromℕ m) ⟷ fromℕ (toℕ t + m)
assocrUS {m} {ZERO} = unite₊
assocrUS {m} {ONE}  = id⟷
assocrUS {m} {t}    = 
  PLUS t (fromℕ m)
    ⟷⟨ normalU t ⊕ id⟷ ⟩
  PLUS (normalℕ t) (fromℕ m)
    ⟷⟨ ! fromℕplus ⟩
  fromℕ (toℕ t + m) □

-- convert each combinator to a normal form

normal⟷ : {t₁ t₂ : U} → (c₁ : t₁ ⟷ t₂) → 
           Σ[ c₂ ∈ normalℕ t₁ ⟷ normalℕ t₂ ] (c₁ ⇔ (normalU t₁ ◎ c₂ ◎ (! (normalU t₂))))
normal⟷ {PLUS ZERO t} {.t} unite₊ = 
  (id⟷ , 
   (unite₊
      ⇔⟨ idr◎r ⟩
    unite₊ ◎ id⟷
      ⇔⟨ resp◎⇔ id⇔ linv◎r ⟩
    unite₊ ◎ (normalU t ◎ (! (normalU t)))
      ⇔⟨ assoc◎l ⟩
    (unite₊ ◎ normalU t) ◎ (! (normalU t))
      ⇔⟨ resp◎⇔ unitel₊⇔ id⇔ ⟩
    ((id⟷ ⊕ normalU t) ◎ unite₊) ◎ (! (normalU t))
      ⇔⟨ resp◎⇔ id⇔ idl◎r ⟩
    ((id⟷ ⊕ normalU t) ◎ unite₊) ◎ (id⟷ ◎ (! (normalU t)))
      ⇔⟨ id⇔ ⟩
    normalU (PLUS ZERO t) ◎ (id⟷ ◎ (! (normalU t))) ▤))
normal⟷ {t} {PLUS ZERO .t} uniti₊ = 
  (id⟷ , 
   (uniti₊ 
      ⇔⟨ idl◎r ⟩ 
    id⟷ ◎ uniti₊
      ⇔⟨ resp◎⇔ linv◎r id⇔ ⟩ 
    (normalU t ◎ (! (normalU t))) ◎ uniti₊
      ⇔⟨ assoc◎r ⟩ 
    normalU t ◎ ((! (normalU t)) ◎ uniti₊)
      ⇔⟨ resp◎⇔ id⇔ unitir₊⇔ ⟩ 
    normalU t ◎ (uniti₊ ◎ (id⟷ ⊕ (! (normalU t))))
      ⇔⟨ resp◎⇔ id⇔ idl◎r ⟩ 
    normalU t ◎ (id⟷ ◎ (uniti₊ ◎ (id⟷ ⊕ (! (normalU t)))))
      ⇔⟨ id⇔ ⟩ 
    normalU t ◎ (id⟷ ◎ (! ((id⟷ ⊕ (normalU t)) ◎ unite₊)))
      ⇔⟨ id⇔ ⟩ 
    normalU t ◎ (id⟷ ◎ (! (normalU (PLUS ZERO t)))) ▤))
normal⟷ {PLUS ZERO t₂} {PLUS .t₂ ZERO} swap₊ = 
  (normalℕswap {ZERO} {t₂} , 
  (swap₊ 
     ⇔⟨ {!!} ⟩
   (unite₊ ◎ normalU t₂) ◎ 
     (normalℕswap {ZERO} {t₂} ◎ ((! (assocrU (toℕ t₂))) ◎ (! (normalU t₂) ⊕ id⟷)))
     ⇔⟨ resp◎⇔ unitel₊⇔ id⇔ ⟩
   ((id⟷ ⊕ normalU t₂) ◎ unite₊) ◎ 
     (normalℕswap {ZERO} {t₂} ◎ ((! (assocrU (toℕ t₂))) ◎ (! (normalU t₂) ⊕ id⟷)))
     ⇔⟨ id⇔ ⟩
   normalU (PLUS ZERO t₂) ◎ (normalℕswap {ZERO} {t₂} ◎ (! (normalU (PLUS t₂ ZERO)))) ▤))
normal⟷ {PLUS ONE t₂} {PLUS .t₂ ONE} swap₊ = 
  (normalℕswap {ONE} {t₂} , 
  (swap₊ 
     ⇔⟨ {!!} ⟩
   ((normalU ONE ⊕ normalU t₂) ◎ assocrU (toℕ ONE)) ◎ 
     (normalℕswap {ONE} {t₂} ◎ ((! (assocrU (toℕ t₂))) ◎ (! (normalU t₂) ⊕ ! (normalU ONE))))
     ⇔⟨ id⇔ ⟩
   normalU (PLUS ONE t₂) ◎ (normalℕswap {ONE} {t₂} ◎ (! (normalU (PLUS t₂ ONE)))) ▤))
normal⟷ {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ = 
  (normalℕswap {t₁} {t₂} , 
  (swap₊ 
     ⇔⟨ {!!} ⟩
   ((normalU t₁ ⊕ normalU t₂) ◎ assocrU (toℕ t₁)) ◎ 
     (normalℕswap {t₁} {t₂} ◎ ((! (assocrU (toℕ t₂))) ◎ (! (normalU t₂) ⊕ ! (normalU t₁))))
     ⇔⟨ id⇔ ⟩
   normalU (PLUS t₁ t₂) ◎ (normalℕswap {t₁} {t₂} ◎ (! (normalU (PLUS t₂ t₁)))) ▤))
normal⟷ {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} assocl₊ = {!!}
normal⟷ {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} assocr₊ = {!!}
normal⟷ {TIMES ONE t} {.t} unite⋆ = {!!} 
normal⟷ {t} {TIMES ONE .t} uniti⋆ = {!!}
normal⟷ {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = {!!}
normal⟷ {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} assocl⋆ = {!!}
normal⟷ {TIMES (TIMES t₁ t₂) t₃} {TIMES .t₁ (TIMES .t₂ .t₃)} assocr⋆ = {!!}
normal⟷ {TIMES ZERO t} {ZERO} distz = {!!}
normal⟷ {ZERO} {TIMES ZERO t} factorz = {!!}
normal⟷ {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} dist = {!!}
normal⟷ {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} {TIMES (PLUS t₁ t₂) t₃} factor = {!!}
normal⟷ {t} {.t} id⟷ = 
  (id⟷ , 
   (id⟷ 
     ⇔⟨ linv◎r ⟩
   normalU t ◎ (! (normalU t))
     ⇔⟨ resp◎⇔ id⇔ idl◎r ⟩
   normalU t ◎ (id⟷ ◎ (! (normalU t))) ▤))
normal⟷ {t₁} {t₃} (_◎_ {t₂ = t₂} c₁ c₂) = {!!}
normal⟷ {PLUS t₁ t₂} {PLUS t₃ t₄} (c₁ ⊕ c₂) = {!!}
normal⟷ {TIMES t₁ t₂} {TIMES t₃ t₄} (c₁ ⊗ c₂) = {!!}

-- if c₁ c₂ : t₁ ⟷ t₂ and c₁ ∼ c₂ then we want a canonical combinator
-- normalℕ t₁ ⟷ normalℕ t₂. If we have that then we should be able to
-- decide whether c₁ ∼ c₂ by normalizing and looking at the canonical
-- combinator.

-- Use ⇔ to normalize a path

{-# NO_TERMINATION_CHECK #-}
normalize : {t₁ t₂ : U} → (c₁ : t₁ ⟷ t₂) → Σ[ c₂ ∈ t₁ ⟷ t₂ ] (c₁ ⇔ c₂)
normalize unite₊     = (unite₊  , id⇔)
normalize uniti₊     = (uniti₊  , id⇔)
normalize swap₊      = (swap₊   , id⇔)
normalize assocl₊    = (assocl₊ , id⇔)
normalize assocr₊    = (assocr₊ , id⇔)
normalize unite⋆     = (unite⋆  , id⇔)
normalize uniti⋆     = (uniti⋆  , id⇔)
normalize swap⋆      = (swap⋆   , id⇔)
normalize assocl⋆    = (assocl⋆ , id⇔)
normalize assocr⋆    = (assocr⋆ , id⇔)
normalize distz      = (distz   , id⇔)
normalize factorz    = (factorz , id⇔)
normalize dist       = (dist    , id⇔)
normalize factor     = (factor  , id⇔)
normalize id⟷        = (id⟷   , id⇔)
normalize (c₁ ◎ c₂)  with normalize c₁ | normalize c₂
... | (c₁' , α) | (c₂' , β) = {!!} 
normalize (c₁ ⊕ c₂)  with normalize c₁ | normalize c₂
... | (c₁' , α) | (c₂₁ ⊕ c₂₂ , β) = 
  (assocl₊ ◎ ((c₁' ⊕ c₂₁) ⊕ c₂₂) ◎ assocr₊ , trans⇔ (resp⊕⇔ α β) assoc⊕l)
... | (c₁' , α) | (c₂' , β)       = (c₁' ⊕ c₂' , resp⊕⇔ α β)
normalize (c₁ ⊗ c₂)  with normalize c₁ | normalize c₂
... | (c₁₁ ⊕ c₁₂ , α) | (c₂' , β) = 
  (dist ◎ ((c₁₁ ⊗ c₂') ⊕ (c₁₂ ⊗ c₂')) ◎ factor , 
   trans⇔ (resp⊗⇔ α β) dist⇔)
... | (c₁' , α) | (c₂₁ ⊗ c₂₂ , β) = 
  (assocl⋆ ◎ ((c₁' ⊗ c₂₁) ⊗ c₂₂) ◎ assocr⋆ , trans⇔ (resp⊗⇔ α β) assoc⊗l)
... | (c₁' , α) | (c₂' , β) = (c₁' ⊗ c₂' , resp⊗⇔ α β)



record Permutation (t t' : U) : Set where
  field
    t₀ : U -- no occurrences of TIMES .. (TIMES .. ..)
    phase₀ : t ⟷ t₀    
    t₁ : U   -- no occurrences of TIMES (PLUS .. ..)
    phase₁ : t₀ ⟷ t₁
    t₂ : U   -- no occurrences of TIMES
    phase₂ : t₁ ⟷ t₂
    t₃ : U   -- no nested left PLUS, all PLUS of form PLUS simple (PLUS ...)
    phase₃ : t₂ ⟷ t₃
    t₄ : U   -- no occurrences PLUS ZERO
    phase₄ : t₃ ⟷ t₄
    t₅ : U   -- do actual permutation using swapij
    phase₅ : t₄ ⟷ t₅
    rest : t₅ ⟷ t' -- blah blah

p◎id∼p : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → (c ◎ id⟷ ∼ c)
p◎id∼p {t₁} {t₂} {c} v = 
  (begin (proj₁ (perm2path (c ◎ id⟷) v))
           ≡⟨ {!!} ⟩
         (proj₁ (perm2path id⟷ (proj₁ (perm2path c v))))
           ≡⟨ {!!} ⟩
         (proj₁ (perm2path c v)) ∎)

-- perm2path {t} id⟷ v = (v , edge •[ t , v ] •[ t , v ])

--perm2path (_◎_ {t₁} {t₂} {t₃} c₁ c₂) v₁ with perm2path c₁ v₁
--... | (v₂ , p) with perm2path c₂ v₂
--... | (v₃ , q) = (v₃ , seq p q) 


-- Equivalences between paths leading to 2path structure
-- Two paths are the same if they go through the same points

_∼_ : ∀ {t₁ t₂ v₁ v₂} → 
      (p : Path •[ t₁ , v₁ ] •[ t₂ , v₂  ]) → 
      (q : Path •[ t₁ , v₁ ] •[ t₂ , v₂ ]) → 
      Set
(edge ._ ._) ∼ (edge ._ ._) = ⊤ 
(edge ._ ._) ∼ (seq p q) = {!!}
(edge ._ ._) ∼ (left p) = {!!}
(edge ._ ._) ∼ (right p) = {!!}
(edge ._ ._) ∼ (par p q) = {!!}
seq p p₁ ∼ edge ._ ._ = {!!}
seq p₁ p ∼ seq q q₁ = {!!}
seq p p₁ ∼ left q = {!!}
seq p p₁ ∼ right q = {!!}
seq p p₁ ∼ par q q₁ = {!!}
left p ∼ edge ._ ._ = {!!}
left p ∼ seq q q₁ = {!!}
left p ∼ left q = {!!}
right p ∼ edge ._ ._ = {!!}
right p ∼ seq q q₁ = {!!}
right p ∼ right q = {!!}
par p p₁ ∼ edge ._ ._ = {!!}
par p p₁ ∼ seq q q₁ = {!!}
par p p₁ ∼ par q q₁ = {!!} 

-- Equivalences between paths leading to 2path structure
-- Following the HoTT approach two paths are considered the same if they
-- map the same points to equal points

infix  4  _∼_  

_∼_ : ∀ {t₁ t₂ v₁ v₂ v₂'} → 
      (p : Path •[ t₁ , v₁ ] •[ t₂ , v₂  ]) → 
      (q : Path •[ t₁ , v₁ ] •[ t₂ , v₂' ]) → 
      Set
_∼_ {t₁} {t₂} {v₁} {v₂} {v₂'} p q = (v₂ ≡ v₂')


-- Lemma 2.4.2

p∼p : {t₁ t₂ : U} {p : Path t₁ t₂} → p ∼ p
p∼p {p = path c} _ = refl

p∼q→q∼p : {t₁ t₂ : U} {p q : Path t₁ t₂} → (p ∼ q) → (q ∼ p)
p∼q→q∼p {p = path c₁} {q = path c₂} α v = sym (α v) 

p∼q∼r→p∼r : {t₁ t₂ : U} {p q r : Path t₁ t₂} → 
                 (p ∼ q) → (q ∼ r) → (p ∼ r) 
p∼q∼r→p∼r {p = path c₁} {q = path c₂} {r = path c₃} α β v = trans (α v) (β v) 

-- lift inverses and compositions to paths

inv : {t₁ t₂ : U} → Path t₁ t₂ → Path t₂ t₁
inv (path c) = path (! c)

infixr 10 _●_

_●_ : {t₁ t₂ t₃ : U} → Path t₁ t₂ → Path t₂ t₃ → Path t₁ t₃
path c₁ ● path c₂ = path (c₁ ◎ c₂)

-- Lemma 2.1.4

p∼p◎id : {t₁ t₂ : U} {p : Path t₁ t₂} → p ∼ p ● path id⟷
p∼p◎id {t₁} {t₂} {path c} v = 
  (begin (perm2path c v)
           ≡⟨ refl ⟩
         (perm2path c (perm2path id⟷ v))
           ≡⟨ refl ⟩
         (perm2path (c ◎ id⟷) v) ∎)

p∼id◎p : {t₁ t₂ : U} {p : Path t₁ t₂} → p ∼ path id⟷ ● p
p∼id◎p {t₁} {t₂} {path c} v = 
  (begin (perm2path c v)
           ≡⟨ refl ⟩
         (perm2path id⟷ (perm2path c v))
           ≡⟨ refl ⟩
         (perm2path (id⟷ ◎ c) v) ∎)

!p◎p∼id : {t₁ t₂ : U} {p : Path t₁ t₂} → (inv p) ● p ∼ path id⟷
!p◎p∼id {t₁} {t₂} {path c} v = 
  (begin (perm2path ((! c) ◎ c) v)
           ≡⟨ refl ⟩
         (perm2path c (perm2path (! c) v))
           ≡⟨ invr {t₁} {t₂} {c} {v} ⟩
         (perm2path id⟷ v) ∎)

p◎!p∼id : {t₁ t₂ : U} {p : Path t₁ t₂} → p ● (inv p) ∼ path id⟷
p◎!p∼id {t₁} {t₂} {path c} v = 
  (begin (perm2path (c ◎ (! c)) v)
           ≡⟨ refl ⟩
         (perm2path (! c) (perm2path c v))
           ≡⟨ invl {t₁} {t₂} {c} {v} ⟩
         (perm2path id⟷ v) ∎)


!!p∼p : {t₁ t₂ : U} {p : Path t₁ t₂} → inv (inv p) ∼ p
!!p∼p {t₁} {t₂} {path c} v = 
  begin (perm2path (! (! c)) v
           ≡⟨ cong (λ x → perm2path x v) (!! {c = c}) ⟩ 
         perm2path c v ∎)

assoc◎ : {t₁ t₂ t₃ t₄ : U} {p : Path t₁ t₂} {q : Path t₂ t₃} {r : Path t₃ t₄} → 
         p ● (q ● r) ∼ (p ● q) ● r
assoc◎ {t₁} {t₂} {t₃} {t₄} {path c₁} {path c₂} {path c₃} v = 
  begin (perm2path (c₁ ◎ (c₂ ◎ c₃)) v 
           ≡⟨ refl ⟩
         perm2path (c₂ ◎ c₃) (perm2path c₁ v)
           ≡⟨ refl ⟩
         perm2path c₃ (perm2path c₂ (perm2path c₁ v))
           ≡⟨ refl ⟩
         perm2path c₃ (perm2path (c₁ ◎ c₂) v)
           ≡⟨ refl ⟩
         perm2path ((c₁ ◎ c₂) ◎ c₃) v ∎)

resp◎ : {t₁ t₂ t₃ : U} {p q : Path t₁ t₂} {r s : Path t₂ t₃} → 
        p ∼ q → r ∼ s → (p ● r) ∼ (q ● s)
resp◎ {t₁} {t₂} {t₃} {path c₁} {path c₂} {path c₃} {path c₄} α β v = 
  begin (perm2path (c₁ ◎ c₃) v 
           ≡⟨ refl ⟩
         perm2path c₃ (perm2path c₁ v)
           ≡⟨ cong (λ x → perm2path c₃ x) (α  v) ⟩
         perm2path c₃ (perm2path c₂ v)
           ≡⟨ β (perm2path c₂ v) ⟩ 
         perm2path c₄ (perm2path c₂ v)
           ≡⟨ refl ⟩ 
         perm2path (c₂ ◎ c₄) v ∎)

-- Recall that two perminators are the same if they denote the same
-- permutation; in that case there is a 2path between them in the relevant
-- path space

data _⇔_ {t₁ t₂ : U} : Path t₁ t₂ → Path t₁ t₂ → Set where
  2path : {p q : Path t₁ t₂} → (p ∼ q) → (p ⇔ q)

-- Examples

p q r : Path BOOL BOOL
p = path id⟷
q = path swap₊
r = path (swap₊ ◎ id⟷)

α : q ⇔ r
α = 2path (p∼p◎id {p = path swap₊})

-- The equivalence of paths makes U a 1groupoid: the points are types t : U;
-- the 1paths are ⟷; and the 2paths between them are ⇔

G : 1Groupoid
G = record
        { set = U
        ; _↝_ = Path
        ; _≈_ = _⇔_ 
        ; id  = path id⟷
        ; _∘_ = λ q p → p ● q
        ; _⁻¹ = inv
        ; lneutr = λ p → 2path (p∼q→q∼p p∼p◎id) 
        ; rneutr = λ p → 2path (p∼q→q∼p p∼id◎p)
        ; assoc  = λ r q p → 2path assoc◎
        ; equiv = record { 
            refl  = 2path p∼p
          ; sym   = λ { (2path α) → 2path (p∼q→q∼p α) }
          ; trans = λ { (2path α) (2path β) → 2path (p∼q∼r→p∼r α β) }
          }
        ; linv = λ p → 2path p◎!p∼id
        ; rinv = λ p → 2path !p◎p∼id
        ; ∘-resp-≈ = λ { (2path β) (2path α) → 2path (resp◎ α β) }
        }

------------------------------------------------------------------------------

data ΩU : Set where
  ΩZERO  : ΩU              -- empty set of paths
  ΩONE   : ΩU              -- a trivial path
  ΩPLUS  : ΩU → ΩU → ΩU      -- disjoint union of paths
  ΩTIMES : ΩU → ΩU → ΩU      -- pairs of paths
  PATH  : (t₁ t₂ : U) → ΩU -- level 0 paths between values

-- values

Ω⟦_⟧ : ΩU → Set
Ω⟦ ΩZERO ⟧             = ⊥
Ω⟦ ΩONE ⟧              = ⊤
Ω⟦ ΩPLUS t₁ t₂ ⟧       = Ω⟦ t₁ ⟧ ⊎ Ω⟦ t₂ ⟧
Ω⟦ ΩTIMES t₁ t₂ ⟧      = Ω⟦ t₁ ⟧ × Ω⟦ t₂ ⟧
Ω⟦ PATH t₁ t₂ ⟧ = Path t₁ t₂

-- two perminators are the same if they denote the same permutation


-- 2paths

data _⇔_ : ΩU → ΩU → Set where
  unite₊  : {t : ΩU} → ΩPLUS ΩZERO t ⇔ t
  uniti₊  : {t : ΩU} → t ⇔ ΩPLUS ΩZERO t
  swap₊   : {t₁ t₂ : ΩU} → ΩPLUS t₁ t₂ ⇔ ΩPLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : ΩU} → ΩPLUS t₁ (ΩPLUS t₂ t₃) ⇔ ΩPLUS (ΩPLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : ΩU} → ΩPLUS (ΩPLUS t₁ t₂) t₃ ⇔ ΩPLUS t₁ (ΩPLUS t₂ t₃)
  unite⋆  : {t : ΩU} → ΩTIMES ΩONE t ⇔ t
  uniti⋆  : {t : ΩU} → t ⇔ ΩTIMES ΩONE t
  swap⋆   : {t₁ t₂ : ΩU} → ΩTIMES t₁ t₂ ⇔ ΩTIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : ΩU} → ΩTIMES t₁ (ΩTIMES t₂ t₃) ⇔ ΩTIMES (ΩTIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : ΩU} → ΩTIMES (ΩTIMES t₁ t₂) t₃ ⇔ ΩTIMES t₁ (ΩTIMES t₂ t₃)
  distz   : {t : ΩU} → ΩTIMES ΩZERO t ⇔ ΩZERO
  factorz : {t : ΩU} → ΩZERO ⇔ ΩTIMES ΩZERO t
  dist    : {t₁ t₂ t₃ : ΩU} → 
            ΩTIMES (ΩPLUS t₁ t₂) t₃ ⇔ ΩPLUS (ΩTIMES t₁ t₃) (ΩTIMES t₂ t₃) 
  factor  : {t₁ t₂ t₃ : ΩU} → 
            ΩPLUS (ΩTIMES t₁ t₃) (ΩTIMES t₂ t₃) ⇔ ΩTIMES (ΩPLUS t₁ t₂) t₃
  id⇔  : {t : ΩU} → t ⇔ t
  _◎_  : {t₁ t₂ t₃ : ΩU} → (t₁ ⇔ t₂) → (t₂ ⇔ t₃) → (t₁ ⇔ t₃)
  _⊕_  : {t₁ t₂ t₃ t₄ : ΩU} → 
         (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (ΩPLUS t₁ t₂ ⇔ ΩPLUS t₃ t₄)
  _⊗_  : {t₁ t₂ t₃ t₄ : ΩU} → 
         (t₁ ⇔ t₃) → (t₂ ⇔ t₄) → (ΩTIMES t₁ t₂ ⇔ ΩTIMES t₃ t₄)
  _∼⇔_ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → 
         PATH t₁ t₂ ⇔ PATH t₁ t₂

-- two spaces are equivalent if there is a path between them; this path
-- automatically has an inverse which is an equivalence. It is a
-- quasi-equivalence but for finite types that's the same as an equivalence.

infix  4  _≃_  

_≃_ : (t₁ t₂ : U) → Set
t₁ ≃ t₂ = (t₁ ⟷ t₂)

-- Univalence says (t₁ ≃ t₂) ≃ (t₁ ⟷ t₂) but as shown above, we actually have
-- this by definition instead of up to ≃

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

another idea is to look at c and massage it as follows: rewrite every 
swap+ ; c
to 
c' ; swaps ; c''

general start with 
 id || id || c
examine c and move anything that's not swap to left. If we get to
 c' || id || id
we are done
if we get to:
 c' || id || swap+;c
then we rewrite
 c';c1 || swaps || c2;c
and we keep going

module Phase₁ where

  -- no occurrences of (TIMES (TIMES t₁ t₂) t₃)

approach that maintains the invariants in proofs

  invariant : (t : U) → Bool
  invariant ZERO = true
  invariant ONE = true
  invariant (PLUS t₁ t₂) = invariant t₁ ∧ invariant t₂ 
  invariant (TIMES ZERO t₂) = invariant t₂
  invariant (TIMES ONE t₂) = invariant t₂
  invariant (TIMES (PLUS t₁ t₂) t₃) = (invariant t₁ ∧ invariant t₂) ∧ invariant t₃
  invariant (TIMES (TIMES t₁ t₂) t₃) = false

  Invariant : (t : U) → Set
  Invariant t = invariant t ≡ true

  invariant? : Decidable Invariant
  invariant? t with invariant t 
  ... | true = yes refl
  ... | false = no (λ ())

  conj : ∀ {b₁ b₂} → (b₁ ≡ true) → (b₂ ≡ true) → (b₁ ∧ b₂ ≡ true)
  conj {true} {true} p q = refl
  conj {true} {false} p ()
  conj {false} {true} ()
  conj {false} {false} ()

  phase₁ : (t₁ : U) → Σ[ t₂ ∈ U ] (True (invariant? t₂) × t₁ ⟷ t₂)
  phase₁ ZERO = (ZERO , (fromWitness {Q = invariant? ZERO} refl , id⟷))
  phase₁ ONE = (ONE , (fromWitness {Q = invariant? ONE} refl , id⟷))
  phase₁ (PLUS t₁ t₂) with phase₁ t₁ | phase₁ t₂
  ... | (t₁' , (p₁ , c₁)) | (t₂' , (p₂ , c₂)) with toWitness p₁ | toWitness p₂
  ... | t₁'ok | t₂'ok = 
    (PLUS t₁' t₂' , 
      (fromWitness {Q = invariant? (PLUS t₁' t₂')} (conj t₁'ok t₂'ok) , 
      c₁ ⊕ c₂))
  phase₁ (TIMES ZERO t) with phase₁ t
  ... | (t' , (p , c)) with toWitness p 
  ... | t'ok = 
    (TIMES ZERO t' , 
      (fromWitness {Q = invariant? (TIMES ZERO t')} t'ok , 
      id⟷ ⊗ c))
  phase₁ (TIMES ONE t) with phase₁ t 
  ... | (t' , (p , c)) with toWitness p
  ... | t'ok = 
    (TIMES ONE t' , 
      (fromWitness {Q = invariant? (TIMES ONE t')} t'ok , 
      id⟷ ⊗ c))
  phase₁ (TIMES (PLUS t₁ t₂) t₃) with phase₁ t₁ | phase₁ t₂ | phase₁ t₃
  ... | (t₁' , (p₁ , c₁)) | (t₂' , (p₂ , c₂)) | (t₃' , (p₃ , c₃)) 
    with toWitness p₁ | toWitness p₂ | toWitness p₃ 
  ... | t₁'ok | t₂'ok | t₃'ok = 
    (TIMES (PLUS t₁' t₂') t₃' , 
      (fromWitness {Q = invariant? (TIMES (PLUS t₁' t₂') t₃')}
        (conj (conj t₁'ok t₂'ok) t₃'ok) , 
      (c₁ ⊕ c₂) ⊗ c₃))
  phase₁ (TIMES (TIMES t₁ t₂) t₃) = {!!} 

  -- invariants are informal
  -- rewrite (TIMES (TIMES t₁ t₂) t₃) to TIMES t₁ (TIMES t₂ t₃)
  invariant : (t : U) → Bool
  invariant ZERO = true
  invariant ONE = true
  invariant (PLUS t₁ t₂) = invariant t₁ ∧ invariant t₂ 
  invariant (TIMES ZERO t₂) = invariant t₂
  invariant (TIMES ONE t₂) = invariant t₂
  invariant (TIMES (PLUS t₁ t₂) t₃) = invariant t₁ ∧ invariant t₂ ∧ invariant t₃
  invariant (TIMES (TIMES t₁ t₂) t₃) = false

  step₁ : (t₁ : U) → Σ[ t₂ ∈ U ] (t₁ ⟷ t₂)
  step₁ ZERO = (ZERO , id⟷)
  step₁ ONE = (ONE , id⟷)
  step₁ (PLUS t₁ t₂) with step₁ t₁ | step₁ t₂
  ... | (t₁' , c₁) | (t₂' , c₂) = (PLUS t₁' t₂' , c₁ ⊕ c₂)
  step₁ (TIMES (TIMES t₁ t₂) t₃) with step₁ t₁ | step₁ t₂ | step₁ t₃
  ... | (t₁' , c₁) | (t₂' , c₂) | (t₃' , c₃) = 
    (TIMES t₁' (TIMES t₂' t₃') , ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  step₁ (TIMES ZERO t₂) with step₁ t₂ 
  ... | (t₂' , c₂) = (TIMES ZERO t₂' , id⟷ ⊗ c₂)
  step₁ (TIMES ONE t₂) with step₁ t₂ 
  ... | (t₂' , c₂) = (TIMES ONE t₂' , id⟷ ⊗ c₂)
  step₁ (TIMES (PLUS t₁ t₂) t₃) with step₁ t₁ | step₁ t₂ | step₁ t₃
  ... | (t₁' , c₁) | (t₂' , c₂) | (t₃' , c₃) = 
    (TIMES (PLUS t₁' t₂') t₃' , (c₁ ⊕ c₂) ⊗ c₃)

  {-# NO_TERMINATION_CHECK #-}
  phase₁ : (t₁ : U) → Σ[ t₂ ∈ U ] (t₁ ⟷ t₂)
  phase₁ t with invariant t
  ... | true = (t , id⟷)
  ... | false with step₁ t
  ... | (t' , c) with phase₁ t'
  ... | (t'' , c') = (t'' , c ◎ c')

  test₁ = phase₁ (TIMES (TIMES (TIMES ONE ONE) (TIMES ONE ONE)) ONE)
  TIMES ONE (TIMES ONE (TIMES ONE (TIMES ONE ONE))) ,
  (((id⟷ ⊗ id⟷) ⊗ (id⟷ ⊗ id⟷)) ⊗ id⟷ ◎ assocr⋆) ◎
  ((id⟷ ⊗ id⟷) ⊗ ((id⟷ ⊗ id⟷) ⊗ id⟷ ◎ assocr⋆) ◎ assocr⋆) ◎ id⟷

  -- Now any perminator (t₁ ⟷ t₂) can be transformed to a canonical
  -- representation in which we first associate all the TIMES to the right
  -- and then do the rest of the perminator

  normalize₁ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → 
               (Σ[ t₁' ∈ U ] (t₁ ⟷ t₁' × t₁' ⟷ t₂))
  normalize₁ {ZERO} {t} c = ZERO , id⟷ , c
  normalize₁ {ONE} c = ONE , id⟷ , c
  normalize₁ {PLUS .ZERO t₂} unite₊ with phase₁ t₂
  ... | (t₂n , cn) = PLUS ZERO t₂n , id⟷ ⊕ cn , unite₊ ◎ ! cn
  normalize₁ {PLUS t₁ t₂} uniti₊ = {!!}
  normalize₁ {PLUS t₁ t₂} swap₊ = {!!}
  normalize₁ {PLUS t₁ ._} assocl₊ = {!!}
  normalize₁ {PLUS ._ t₂} assocr₊ = {!!}
  normalize₁ {PLUS t₁ t₂} uniti⋆ = {!!}
  normalize₁ {PLUS ._ ._} factor = {!!}
  normalize₁ {PLUS t₁ t₂} id⟷ = {!!}
  normalize₁ {PLUS t₁ t₂} (c ◎ c₁) = {!!}
  normalize₁ {PLUS t₁ t₂} (c ⊕ c₁) = {!!} 
  normalize₁ {TIMES t₁ t₂} c = {!!}

record Permutation (t t' : U) : Set where
  field
    t₀ : U -- no occurrences of TIMES .. (TIMES .. ..)
    phase₀ : t ⟷ t₀    
    t₁ : U   -- no occurrences of TIMES (PLUS .. ..)
    phase₁ : t₀ ⟷ t₁
    t₂ : U   -- no occurrences of TIMES
    phase₂ : t₁ ⟷ t₂
    t₃ : U   -- no nested left PLUS, all PLUS of form PLUS simple (PLUS ...)
    phase₃ : t₂ ⟷ t₃
    t₄ : U   -- no occurrences PLUS ZERO
    phase₄ : t₃ ⟷ t₄
    t₅ : U   -- do actual permutation using swapij
    phase₅ : t₄ ⟷ t₅
    rest : t₅ ⟷ t' -- blah blah

canonical : {t₁ t₂ : U} → (t₁ ⟷ t₂) → Permutation t₁ t₂
canonical c = {!!}

------------------------------------------------------------------------------
-- These paths do NOT reach "inside" the finite sets. For example, there is
-- NO PATH between false and true in BOOL even though there is a path between
-- BOOL and BOOL that "twists the space around."
-- 
-- In more detail how do these paths between types relate to the whole
-- discussion about higher groupoid structure of type formers (Sec. 2.5 and
-- on).

-- Then revisit the early parts of Ch. 2 about higher groupoid structure for
-- U, how functions from U to U respect the paths in U, type families and
-- dependent functions, homotopies and equivalences, and then Sec. 2.5 and
-- beyond again.


should this be on the code as done now or on their interpreation
i.e. data _⟷_ : ⟦ U ⟧ → ⟦ U ⟧ → Set where

can add recursive types 
rec : U
⟦_⟧ takes an additional argument X that is passed around
⟦ rec ⟧ X = X
fixpoitn
data μ (t : U) : Set where
 ⟨_⟩ : ⟦ t ⟧ (μ t) → μ t

-- We identify functions with the paths above. Since every function is
-- reversible, every function corresponds to a path and there is no
-- separation between functions and paths and no need to mediate between them
-- using univalence.
--
-- Note that none of the above functions are dependent functions.

------------------------------------------------------------------------------
-- Now we consider homotopies, i.e., paths between functions. Since our
-- functions are identified with the paths ⟷, the homotopies are paths
-- between elements of ⟷

-- First, a sanity check. Our notion of paths matches the notion of
-- equivalences in the conventional HoTT presentation

-- Homotopy between two functions (paths)

-- That makes id ∼ not which is bad. The def. of ∼ should be parametric...

_∼_ : {t₁ t₂ t₃ : U} → (f : t₁ ⟷ t₂) → (g : t₁ ⟷ t₃) → Set
_∼_ {t₁} {t₂} {t₃} f g = t₂ ⟷ t₃

-- Every f and g of the right type are related by ∼

homotopy : {t₁ t₂ t₃ : U} → (f : t₁ ⟷ t₂) → (g : t₁ ⟷ t₃) → (f ∼ g)
homotopy f g = (! f) ◎ g

-- Equivalences 
-- 
-- If f : t₁ ⟷ t₂ has two inverses g₁ g₂ : t₂ ⟷ t₁ then g₁ ∼ g₂. More
-- generally, any two paths of the same type are related by ∼.

equiv : {t₁ t₂ : U} → (f g : t₁ ⟷ t₂) → (f ∼ g) 
equiv f g = id⟷ 

-- It follows that any two types in U are equivalent if there is a path
-- between them

_≃_ : (t₁ t₂ : U) → Set
t₁ ≃ t₂ = t₁ ⟷ t₂ 

-- Now we want to understand the type of paths between paths

------------------------------------------------------------------------------

elems : (t : U) → List ⟦ t ⟧
elems ZERO = []
elems ONE = [ tt ] 
elems (PLUS t₁ t₂) = map inj₁ (elems t₁) ++ map inj₂ (elems t₂)
elems (TIMES t₁ t₂) = concat 
                        (map 
                          (λ v₂ → map (λ v₁ → (v₁ , v₂)) (elems t₁))
                         (elems t₂))

_≟_ : {t : U} → ⟦ t ⟧ → ⟦ t ⟧ → Bool
_≟_ {ZERO} ()
_≟_ {ONE} tt tt = true
_≟_ {PLUS t₁ t₂} (inj₁ v) (inj₁ w) = v ≟ w
_≟_ {PLUS t₁ t₂} (inj₁ v) (inj₂ w) = false
_≟_ {PLUS t₁ t₂} (inj₂ v) (inj₁ w) = false
_≟_ {PLUS t₁ t₂} (inj₂ v) (inj₂ w) = v ≟ w
_≟_ {TIMES t₁ t₂} (v₁ , w₁) (v₂ , w₂) = v₁ ≟ v₂ ∧ w₁ ≟ w₂

  findLoops : {t t₁ t₂ : U} → (PLUS t t₁ ⟷ PLUS t t₂) → List ⟦ t ⟧ → 
               List (Σ[ t ∈ U ] ⟦ t ⟧)
  findLoops c [] = []
  findLoops {t} c (v ∷ vs) = ? with perm2path c (inj₁ v)
  ... | (inj₂ _ , loops) = loops ++ findLoops c vs
  ... | (inj₁ v' , loops) with v ≟ v' 
  ... | true = (t , v) ∷ loops ++ findLoops c vs
  ... | false = loops ++ findLoops c vs

traceLoopsEx : {t : U} → List (Σ[ t ∈ U ] ⟦ t ⟧)
traceLoopsEx {t} = findLoops traceBodyEx (elems (PLUS t (PLUS t t)))
-- traceLoopsEx {ONE} ==> (PLUS ONE (PLUS ONE ONE) , inj₂ (inj₁ tt)) ∷ []

-- Each permutation is a "path" between types. We can think of this path as
-- being indexed by "time" where "time" here is in discrete units
-- corresponding to the sequencing of combinators. A homotopy between paths p
-- and q is a map that, for each "time unit", maps the specified type along p
-- to a corresponding type along q. At each such time unit, the mapping
-- between types is itself a path. So a homotopy is essentially a collection
-- of paths. As an example, given two paths starting at t₁ and ending at t₂
-- and going through different intermediate points:
--   p = t₁ -> t -> t' -> t₂
--   q = t₁ -> u -> u' -> t₂
-- A possible homotopy between these two paths is a path from t to u and 
-- another path from t' to u'. Things get slightly more complicated if the
-- number of intermediate points is not the same etc. but that's the basic idea.
-- The vertical paths must commute with the horizontal ones.
-- 
-- Postulate the groupoid laws and use them to prove commutativity etc.
-- 
-- Bool -id-- Bool -id-- Bool -id-- Bool
--   |          |          |          |
--   |         not        id          | the last square does not commute
--   |          |          |          |
-- Bool -not- Bool -not- Bool -not- Bool
--
-- If the large rectangle commutes then the smaller squares commute. For a
-- proof, let p o q o r o s be the left-bottom path and p' o q' o r' o s' be
-- the top-right path. Let's focus on the square:
--  
--  A-- r'--C
--   |      |
--   ?      s'
--   |      |
--  B-- s --D
-- 
-- We have a path from A to B that is: !q' o !p' o p o q o r. 
-- Now let's see if r' o s' is equivalent to 
-- !q' o !p' o p o q o r o s
-- We know p o q o r o s ⇔ p' o q' o r' o s' 
-- If we know that ⇔ is preserved by composition then:
-- !q' o !p' o p o q o r o s ⇔ !q' o !p' o p' o q' o r' o s' 
-- and of course by inverses and id being unit of composition:
-- !q' o !p' o p o q o r o s ⇔ r' o s' 
-- and we are done.

{-# NO_TERMINATION_CHECK #-}
Path∼ : ∀ {t₁ t₂ t₁' t₂' v₁ v₂ v₁' v₂'} → 
        (p : Path •[ t₁ , v₁ ] •[ t₂ , v₂ ]) → 
        (q : Path •[ t₁' , v₁' ] •[ t₂' , v₂' ]) → 
        Set
-- sequential composition
Path∼ {t₁} {t₃} {t₁'} {t₃'} {v₁} {v₃} {v₁'} {v₃'} 
  (_●_ {t₂ = t₂} {v₂ = v₂} p₁ p₂) (_●_ {t₂ = t₂'} {v₂ = v₂'} q₁ q₂) = 
 (Path∼ p₁ q₁ × Path∼ p₂ q₂) ⊎
 (Path∼ {t₁} {t₂} {t₁'} {t₁'} {v₁} {v₂} {v₁'} {v₁'} p₁ id⟷• × Path∼ p₂ (q₁ ● q₂)) ⊎ 
 (Path∼ p₁ (q₁ ● q₂) × Path∼ {t₂} {t₃} {t₃'} {t₃'} {v₂} {v₃} {v₃'} {v₃'} p₂ id⟷•) ⊎  
 (Path∼ {t₁} {t₁} {t₁'} {t₂'} {v₁} {v₁} {v₁'} {v₂'} id⟷• q₁ × Path∼ (p₁ ● p₂) q₂) ⊎
 (Path∼ (p₁ ● p₂) q₁ × Path∼ {t₃} {t₃} {t₂'} {t₃'} {v₃} {v₃} {v₂'} {v₃'} id⟷• q₂)
Path∼ {t₁} {t₃} {t₁'} {t₃'} {v₁} {v₃} {v₁'} {v₃'} 
  (_●_ {t₂ = t₂} {v₂ = v₂} p q) c = 
    (Path∼ {t₁} {t₂} {t₁'} {t₁'} {v₁} {v₂} {v₁'} {v₁'} p id⟷• × Path∼ q c)
  ⊎ (Path∼ p c × Path∼ {t₂} {t₃} {t₃'} {t₃'} {v₂} {v₃} {v₃'} {v₃'} q id⟷•)
Path∼ {t₁} {t₃} {t₁'} {t₃'} {v₁} {v₃} {v₁'} {v₃'} 
  c (_●_ {t₂ = t₂'} {v₂ = v₂'} p q) = 
    (Path∼ {t₁} {t₁} {t₁'} {t₂'} {v₁} {v₁} {v₁'} {v₂'} id⟷• p × Path∼ c q)
  ⊎ (Path∼ c p × Path∼ {t₃} {t₃} {t₂'} {t₃'} {v₃} {v₃} {v₂'} {v₃'} id⟷• q)
-- choices
Path∼ (⊕1• p) (⊕1• q) = Path∼ p q
Path∼ (⊕1• p) _       = ⊥
Path∼ _       (⊕1• p) = ⊥
Path∼ (⊕2• p) (⊕2• q) = Path∼ p q
Path∼ (⊕2• p) _       = ⊥
Path∼ _       (⊕2• p) = ⊥
-- parallel paths
Path∼ (p₁ ⊗• p₂) (q₁ ⊗• q₂) = Path∼ p₁ q₁ × Path∼ p₂ q₂
Path∼ (p₁ ⊗• p₂) _          = ⊥
Path∼ _          (q₁ ⊗• q₂) = ⊥
-- simple edges connecting two points
Path∼ {t₁} {t₂} {t₁'} {t₂'} {v₁} {v₂} {v₁'} {v₂'} c₁ c₂ = 
  Path •[ t₁ , v₁ ] •[ t₁' , v₁' ] × Path •[ t₂ , v₂ ] •[ t₂' , v₂' ] 

-- In the setting of finite types (in particular with no loops) every pair of
-- paths with related start and end points is equivalent. In other words, we
-- really have no interesting 2-path structure.

allequiv : ∀ {t₁ t₂ t₁' t₂' v₁ v₂ v₁' v₂'} → 
       (p : Path •[ t₁ , v₁ ] •[ t₂ , v₂ ]) → 
       (q : Path •[ t₁' , v₁' ] •[ t₂' , v₂' ]) → 
       (start : Path •[ t₁ , v₁ ] •[ t₁' , v₁' ]) → 
       (end : Path •[ t₂ , v₂ ] •[ t₂' , v₂' ]) → 
       Path∼ p q
allequiv {t₁} {t₃} {t₁'} {t₃'} {v₁} {v₃} {v₁'} {v₃'} 
  (_●_ {t₂ = t₂} {v₂ = v₂} p₁ p₂) (_●_ {t₂ = t₂'} {v₂ = v₂'} q₁ q₂) 
  start end = {!!}
allequiv {t₁} {t₃} {t₁'} {t₃'} {v₁} {v₃} {v₁'} {v₃'} 
  (_●_ {t₂ = t₂} {v₂ = v₂} p q) c start end = {!!}
allequiv {t₁} {t₃} {t₁'} {t₃'} {v₁} {v₃} {v₁'} {v₃'} 
  c (_●_ {t₂ = t₂'} {v₂ = v₂'} p q) start end = {!!}
allequiv (⊕1• p) (⊕1• q) start end = {!!}
allequiv (⊕1• p) _       start end = {!!}
allequiv _       (⊕1• p) start end = {!!}
allequiv (⊕2• p) (⊕2• q) start end = {!!}
allequiv (⊕2• p) _       start end = {!!}
allequiv _       (⊕2• p) start end = {!!}
-- parallel paths
allequiv (p₁ ⊗• p₂) (q₁ ⊗• q₂) start end = {!!}
allequiv (p₁ ⊗• p₂) _          start end = {!!}
allequiv _          (q₁ ⊗• q₂) start end = {!!}
-- simple edges connecting two points
allequiv {t₁} {t₂} {t₁'} {t₂'} {v₁} {v₂} {v₁'} {v₂'} c₁ c₂ start end = {!!}





refl∼ : ∀ {t₁ t₂ v₁ v₂} → (p : Path •[ t₁ , v₁ ] •[ t₂ , v₂ ]) → Path∼ p p 
refl∼ unite•₊   = id⟷• , id⟷• 
refl∼ uniti•₊   = id⟷• , id⟷• 
refl∼ swap1•₊   = id⟷• , id⟷• 
refl∼ swap2•₊   = id⟷• , id⟷• 
refl∼ assocl1•₊ = id⟷• , id⟷• 
refl∼ assocl2•₊ = id⟷• , id⟷• 
refl∼ assocl3•₊ = id⟷• , id⟷• 
refl∼ assocr1•₊ = id⟷• , id⟷• 
refl∼ assocr2•₊ = id⟷• , id⟷• 
refl∼ assocr3•₊ = id⟷• , id⟷• 
refl∼ unite•⋆   = id⟷• , id⟷• 
refl∼ uniti•⋆   = id⟷• , id⟷• 
refl∼ swap•⋆    = id⟷• , id⟷• 
refl∼ assocl•⋆  = id⟷• , id⟷• 
refl∼ assocr•⋆  = id⟷• , id⟷• 
refl∼ distz•    = id⟷• , id⟷• 
refl∼ factorz•  = id⟷• , id⟷• 
refl∼ dist1•    = id⟷• , id⟷• 
refl∼ dist2•    = id⟷• , id⟷• 
refl∼ factor1•  = id⟷• , id⟷• 
refl∼ factor2•  = id⟷• , id⟷• 
refl∼ id⟷•      = id⟷• , id⟷• 
refl∼ (p ● q)   = inj₁ (refl∼ p , refl∼ q)
refl∼ (⊕1• p)   = refl∼ p
refl∼ (⊕2• q)   = refl∼ q
refl∼ (p ⊗• q)  = refl∼ p , refl∼ q 

-- Extensional view

-- First we enumerate all the values of a given finite type

size : U → ℕ
size ZERO          = 0
size ONE           = 1
size (PLUS t₁ t₂)  = size  t₁ + size t₂
size (TIMES t₁ t₂) = size t₁ * size  t₂

enum : (t : U) → ⟦ t ⟧ → Fin (size t)
enum ZERO ()                  -- absurd
enum ONE tt                   = zero
enum (PLUS t₁ t₂) (inj₁ v₁)   = inject+ (size t₂) (enum t₁ v₁)
enum (PLUS t₁ t₂) (inj₂ v₂)   = raise (size t₁) (enum t₂ v₂)
enum (TIMES t₁ t₂) (v₁ , v₂)  = fromℕ≤ (pr {s₁} {s₂} {n₁} {n₂})
  where n₁ = enum t₁ v₁
        n₂ = enum t₂ v₂
        s₁ = size t₁ 
        s₂ = size t₂
        pr : {s₁ s₂ : ℕ} → {n₁ : Fin s₁} {n₂ : Fin s₂} → 
             ((toℕ n₁ * s₂) + toℕ n₂) < (s₁ * s₂)
        pr {0} {_} {()} 
        pr {_} {0} {_} {()}
        pr {suc s₁} {suc s₂} {zero} {zero} = {!z≤n!}
        pr {suc s₁} {suc s₂} {zero} {Fsuc n₂} = {!!}
        pr {suc s₁} {suc s₂} {Fsuc n₁} {zero} = {!!}
        pr {suc s₁} {suc s₂} {Fsuc n₁} {Fsuc n₂} = {!!}

vals3 : Fin 3 × Fin 3 × Fin 3
vals3 = (enum THREE LL , enum THREE LR , enum THREE R)
  where THREE = PLUS (PLUS ONE ONE) ONE
        LL = inj₁ (inj₁ tt)
        LR = inj₁ (inj₂ tt)
        R  = inj₂ tt

xxx : {s₁ s₂ : ℕ} → (i : Fin s₁) → (j : Fin s₂) → 
      suc (toℕ i * s₂ + toℕ j) ≤ s₁ * s₂
xxx {0} {_} ()
xxx {suc s₁} {s₂} i j = {!!} 

-- i  : Fin (suc s₁)
-- j  : Fin s₂
-- ?0 : suc (toℕ i * s₂ + toℕ j)  ≤ suc s₁ * s₂
--      (suc (toℕ i) * s₂ + toℕ j ≤ s₂ + s₁ * s₂
--      (suc (toℕ i) * s₂ + toℕ j ≤ s₁ * s₂ + s₂



utoVecℕ : (t : U) → Vec (Fin (utoℕ t)) (utoℕ t)
utoVecℕ ZERO          = []
utoVecℕ ONE           = [ zero ]
utoVecℕ (PLUS t₁ t₂)  = 
  map (inject+ (utoℕ t₂)) (utoVecℕ t₁) ++ 
  map (raise (utoℕ t₁)) (utoVecℕ t₂)
utoVecℕ (TIMES t₁ t₂) = 
  concat (map (λ i → map (λ j → inject≤ (fromℕ (toℕ i * utoℕ t₂ + toℕ j)) 
                                (xxx i j))
                     (utoVecℕ t₂))
         (utoVecℕ t₁))

-- Vector representation of types so that we can test permutations

utoVec : (t : U) → Vec ⟦ t ⟧ (utoℕ t)
utoVec ZERO          = []
utoVec ONE           = [ tt ]
utoVec (PLUS t₁ t₂)  = map inj₁ (utoVec t₁) ++ map inj₂ (utoVec t₂)
utoVec (TIMES t₁ t₂) = 
  concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) (utoVec t₂)) (utoVec t₁))

-- Examples permutations and their actions on a simple ordered vector

module PermExamples where

  -- ordered vector: position i has value i
  ordered : ∀ {n} → Vec (Fin n) n
  ordered = tabulate id

  -- empty permutation p₀ { }

  p₀ : Perm 0
  p₀ = []

  v₀ = permute p₀ ordered

  -- permutation p₁ { 0 -> 0 }

  p₁ : Perm 1
  p₁ = 0F ∷ p₀
    where 0F = fromℕ 0

  v₁ = permute p₁ ordered

  -- permutations p₂ { 0 -> 0, 1 -> 1 }
  --              q₂ { 0 -> 1, 1 -> 0 }

  p₂ q₂ : Perm 2
  p₂ = 0F ∷ p₁ 
    where 0F = inject+ 1 (fromℕ 0)
  q₂ = 1F ∷ p₁
    where 1F = fromℕ 1

  v₂ = permute p₂ ordered
  w₂ = permute q₂ ordered

  -- permutations p₃ { 0 -> 0, 1 -> 1, 2 -> 2 }
  --              s₃ { 0 -> 0, 1 -> 2, 2 -> 1 }
  --              q₃ { 0 -> 1, 1 -> 0, 2 -> 2 }
  --              r₃ { 0 -> 1, 1 -> 2, 2 -> 0 }
  --              t₃ { 0 -> 2, 1 -> 0, 2 -> 1 }
  --              u₃ { 0 -> 2, 1 -> 1, 2 -> 0 }

  p₃ q₃ r₃ s₃ t₃ u₃ : Perm 3
  p₃ = 0F ∷ p₂
    where 0F = inject+ 2 (fromℕ 0)
  s₃ = 0F ∷ q₂
    where 0F = inject+ 2 (fromℕ 0)
  q₃ = 1F ∷ p₂
    where 1F = inject+ 1 (fromℕ 1)
  r₃ = 2F ∷ p₂
    where 2F = fromℕ 2
  t₃ = 1F ∷ q₂
    where 1F = inject+ 1 (fromℕ 1)
  u₃ = 2F ∷ q₂
    where 2F = fromℕ 2

  v₃ = permute p₃ ordered
  y₃ = permute s₃ ordered
  w₃ = permute q₃ ordered
  x₃ = permute r₃ ordered
  z₃ = permute t₃ ordered
  α₃ = permute u₃ ordered

  -- end module PermExamples

------------------------------------------------------------------------------
-- Testing

t₁  = PLUS ZERO BOOL
t₂  = BOOL
m₁ = matchP {t₁} {t₂} unite₊
-- (inj₂ (inj₁ tt) , inj₁ tt) ∷ (inj₂ (inj₂ tt) , inj₂ tt) ∷ []
m₂ = matchP {t₂} {t₁} uniti₊
-- (inj₁ tt , inj₂ (inj₁ tt)) ∷ (inj₂ tt , inj₂ (inj₂ tt)) ∷ []

t₃ = PLUS BOOL ONE
t₄ = PLUS ONE BOOL
m₃ = matchP {t₃} {t₄} swap₊
-- (inj₂ tt , inj₁ tt) ∷
-- (inj₁ (inj₁ tt) , inj₂ (inj₁ tt)) ∷
-- (inj₁ (inj₂ tt) , inj₂ (inj₂ tt)) ∷ []
m₄ = matchP {t₄} {t₃} swap₊
-- (inj₂ (inj₁ tt) , inj₁ (inj₁ tt)) ∷
-- (inj₂ (inj₂ tt) , inj₁ (inj₂ tt)) ∷ 
-- (inj₁ tt , inj₂ tt) ∷ []

t₅  = PLUS ONE (PLUS BOOL ONE)
t₆  = PLUS (PLUS ONE BOOL) ONE
m₅ = matchP {t₅} {t₆} assocl₊
-- (inj₁ tt , inj₁ (inj₁ tt)) ∷
-- (inj₂ (inj₁ (inj₁ tt)) , inj₁ (inj₂ (inj₁ tt))) ∷
-- (inj₂ (inj₁ (inj₂ tt)) , inj₁ (inj₂ (inj₂ tt))) ∷
-- (inj₂ (inj₂ tt) , inj₂ tt) ∷ []
m₆ = matchP {t₆} {t₅} assocr₊
-- (inj₁ (inj₁ tt) , inj₁ tt) ∷
-- (inj₁ (inj₂ (inj₁ tt)) , inj₂ (inj₁ (inj₁ tt))) ∷
-- (inj₁ (inj₂ (inj₂ tt)) , inj₂ (inj₁ (inj₂ tt))) ∷
-- (inj₂ tt , inj₂ (inj₂ tt)) ∷ []

t₇ = TIMES ONE BOOL
t₈ = BOOL
m₇ = matchP {t₇} {t₈} unite⋆
-- ((tt , inj₁ tt) , inj₁ tt) ∷ ((tt , inj₂ tt) , inj₂ tt) ∷ []
m₈ = matchP {t₈} {t₇} uniti⋆
-- (inj₁ tt , (tt , inj₁ tt)) ∷ (inj₂ tt , (tt , inj₂ tt)) ∷ []

t₉  = TIMES BOOL ONE
t₁₀ = TIMES ONE BOOL
m₉  = matchP {t₉} {t₁₀} swap⋆
-- ((inj₁ tt , tt) , (tt , inj₁ tt)) ∷
-- ((inj₂ tt , tt) , (tt , inj₂ tt)) ∷ []
m₁₀ = matchP {t₁₀} {t₉} swap⋆
-- ((tt , inj₁ tt) , (inj₁ tt , tt)) ∷
-- ((tt , inj₂ tt) , (inj₂ tt , tt)) ∷ []

t₁₁ = TIMES BOOL (TIMES ONE BOOL)
t₁₂ = TIMES (TIMES BOOL ONE) BOOL
m₁₁ = matchP {t₁₁} {t₁₂} assocl⋆
-- ((inj₁ tt , (tt , inj₁ tt)) , ((inj₁ tt , tt) , inj₁ tt)) ∷
-- ((inj₁ tt , (tt , inj₂ tt)) , ((inj₁ tt , tt) , inj₂ tt)) ∷
-- ((inj₂ tt , (tt , inj₁ tt)) , ((inj₂ tt , tt) , inj₁ tt)) ∷
-- ((inj₂ tt , (tt , inj₂ tt)) , ((inj₂ tt , tt) , inj₂ tt)) ∷ []
m₁₂ = matchP {t₁₂} {t₁₁} assocr⋆
-- (((inj₁ tt , tt) , inj₁ tt) , (inj₁ tt , (tt , inj₁ tt)) ∷
-- (((inj₁ tt , tt) , inj₂ tt) , (inj₁ tt , (tt , inj₂ tt)) ∷
-- (((inj₂ tt , tt) , inj₁ tt) , (inj₂ tt , (tt , inj₁ tt)) ∷
-- (((inj₂ tt , tt) , inj₂ tt) , (inj₂ tt , (tt , inj₂ tt)) ∷ []

t₁₃ = TIMES ZERO BOOL
t₁₄ = ZERO
m₁₃ = matchP {t₁₃} {t₁₄} distz
-- []
m₁₄ = matchP {t₁₄} {t₁₃} factorz
-- []

t₁₅ = TIMES (PLUS BOOL ONE) BOOL
t₁₆ = PLUS (TIMES BOOL BOOL) (TIMES ONE BOOL)
m₁₅ = matchP {t₁₅} {t₁₆} dist
-- ((inj₁ (inj₁ tt) , inj₁ tt) , inj₁ (inj₁ tt , inj₁ tt)) ∷
-- ((inj₁ (inj₁ tt) , inj₂ tt) , inj₁ (inj₁ tt , inj₂ tt)) ∷
-- ((inj₁ (inj₂ tt) , inj₁ tt) , inj₁ (inj₂ tt , inj₁ tt)) ∷
-- ((inj₁ (inj₂ tt) , inj₂ tt) , inj₁ (inj₂ tt , inj₂ tt)) ∷
-- ((inj₂ tt , inj₁ tt) , inj₂ (tt , inj₁ tt)) ∷
-- ((inj₂ tt , inj₂ tt) , inj₂ (tt , inj₂ tt)) ∷ []
m₁₆ = matchP {t₁₆} {t₁₅} factor
-- (inj₁ (inj₁ tt , inj₁ tt) , (inj₁ (inj₁ tt) , inj₁ tt)) ∷
-- (inj₁ (inj₁ tt , inj₂ tt) , (inj₁ (inj₁ tt) , inj₂ tt)) ∷
-- (inj₁ (inj₂ tt , inj₁ tt) , (inj₁ (inj₂ tt) , inj₁ tt)) ∷
-- (inj₁ (inj₂ tt , inj₂ tt) , (inj₁ (inj₂ tt) , inj₂ tt)) ∷
-- (inj₂ (tt , inj₁ tt) , (inj₂ tt , inj₁ tt)) ∷
-- (inj₂ (tt , inj₂ tt) , (inj₂ tt , inj₂ tt)) ∷ []

t₁₇ = BOOL 
t₁₈ = BOOL
m₁₇ = matchP {t₁₇} {t₁₈} id⟷
-- (inj₁ tt , inj₁ tt) ∷ (inj₂ tt , inj₂ tt) ∷ []

--◎
--⊕
--⊗

------------------------------------------------------------------------------

mergeS :: SubPerm → SubPerm (suc m * n) (m * n) → SubPerm (suc m * suc n) (m * suc n) 
mergeS = ? 

subP : ∀ {m n} → Fin (suc m) → Perm n → SubPerm (suc m * n) (m * n)
subP {m} {0} i β = {!!}
subP {m} {suc n} i (j ∷ β) = mergeS ? (subP {m} {n} i β)


-- injectP (Perm n) (m * n) 
-- ...
-- SP (suc m * n) (m * n)
-- SP (n + m * n) (m * n)

--SP (suc m * n) (m * n) 
--
--
--==> 
--
--(suc m * suc n) (m * suc n)

--m : ℕ
--n : ℕ
--i : Fin (suc m)
--j : Fin (suc n)
--β : Perm n
--?1 : SubPerm (suc m * suc n) (m * suc n)


tcompperm : ∀ {m n} → Perm m → Perm n → Perm (m * n)
tcompperm []      β = []
tcompperm (i ∷ α) β = merge (subP i β) (tcompperm α β)

-- shift m=3 n=4 i=ax:F3 β=[ay:F4,by:F3,cy:F2,dy:F1] γ=[r4,...,r11]:P8
-- ==> [F12,F11,F10,F9...γ]

-- m = 3
-- n = 4
-- 3 * 4
-- x = [ ax, bx, cx ] : P 3, y : [ay, by, cy, dy] : P 4
-- (shift ax 4 y) || 
--     ( (shift bx 4 y) ||
--          ( (shift cx 4 y) ||
--               [])))
-- 
-- ax : F3, bx : F2, cx : F1
-- ay : F4, by : F3, cy : F2, dy : F1
--
-- suc m = 3, m = 2
--  F12 F11  F10 F9  F8  F7  F6  F5  F4  F3  F2   F1
-- [ r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11 ]
--   ---------------
--  ax : F3 with y=[F4,F3,F2,F1]
--                   --------------
--                       bx : F2
--                                  ------------------
--                                          cx : F1

  -- β should be something like i * n + entry in β

0 * n = 0
(suc m) * n = n + (m * n)

comb2perm (c₁ ⊗ c₂) = tcompperm (comb2perm c₁) (comb2perm c₂) 

c1 = swap+ (f->t,t->f)  [1,0]
c2 = id    (f->f,t->t)  [0,0]

c1xc2 (f,f)->(t,f), (f,t)->(t,t), (t,f)->(f,f), (t,t)->(f,t)
[

ff ft tf tt
 2   2  0  0

index in α * n + index in β

pex qex pqex qpex : Perm 3
pex = inject+ 1 (fromℕ 1) ∷ fromℕ 1 ∷ zero ∷ []
qex = zero ∷ fromℕ 1 ∷ zero ∷ []
pqex = fromℕ 2 ∷ fromℕ 1 ∷ zero ∷ []
qpex = inject+ 1 (fromℕ 1) ∷ zero ∷ zero ∷ []

pqexv  = (permute qex ∘ permute pex) (tabulate id)
pqexv' = permute pqex (tabulate id) 

qpexv  = (permute pex ∘ permute qex) (tabulate id)
qpexv' = permute qpex (tabulate id)

-- [1,1,0]
-- [z] => [z]
-- [y,z] => [z,y]
-- [x,y,z] => [z,x,y] 

-- [0,1,0]
-- [w] => [w]
-- [v,w] => [w,v]
-- [u,v,w] => [u,w,v]

-- R,R,_ ◌ _,R,_
-- R in p1 takes you to middle which also goes R, so first goes RR
-- [a,b,c] ◌ [d,e,f]
-- [a+p2[a], ...]

-- [1,1,0] ◌ [0,1,0] one step [2,1,0]
-- [z] => [z]
-- [y,z] => [z,y]
-- [x,y,z] => [z,y,x]

-- [1,1,0] ◌ [0,1,0]
-- [z] => [z] => [z]
-- [y,z] => 
-- [x,y,z] => 

-- so [1,1,0] ◌ [0,1,0] ==> [2,1,0]
-- so [0,1,0] ◌ [1,1,0] ==> [1,0,0]

-- pex takes [0,1,2] to [2,0,1]
-- qex takes [0,1,2] to [0,2,1]
-- pex ◌ qex takes [0,1,2] to [2,1,0]
-- qex ◌ pex takes [0,1,2] to [1,0,2]

-- seq : ∀ {m n} → (m ≤ n) → Perm m → Perm n → Perm m
-- seq lp [] _ = []
-- seq lp (i ∷ p) q = (lookupP i q) ∷ (seq lp p q)

-- i F+ ...

-- lookupP : ∀ {n} → Fin n → Perm n → Fin n
-- i   : Fin (suc m)
-- p   : Perm m
-- q   : Perm n


-- 
-- (zero ∷ p₁) ◌ (q ∷ q₁) = q ∷ (p₁ ◌ q₁)
-- (suc p ∷ p₁) ◌ (zero ∷ q₁) = {!!}
-- (suc p ∷ p₁) ◌ (suc q ∷ q₁) = {!!}
-- 
-- data Perm : ℕ → Set where
--   []  : Perm 0
--   _∷_ : {n : ℕ} → Fin (suc n) → Perm n → Perm (suc n)

-- Given a vector of (suc n) elements, return one of the elements and
-- the rest. Example: pick (inject+ 1 (fromℕ 1)) (10 ∷ 20 ∷ 30 ∷ 40 ∷ [])

pick : ∀ {ℓ} {n : ℕ} {A : Set ℓ} → Fin n → Vec A (suc n) → (A × Vec A n)
pick {ℓ} {0} {A} ()
pick {ℓ} {suc n} {A} zero (v ∷ vs) = (v , vs)
pick {ℓ} {suc n} {A} (suc i) (v ∷ vs) = 
  let (w , ws) = pick {ℓ} {n} {A} i vs 
  in (w , v ∷ ws)

insertV : ∀ {ℓ} {n : ℕ} {A : Set ℓ} → 
          A → Fin (suc n) → Vec A n → Vec A (suc n) 
insertV {n = 0} v zero [] = [ v ]
insertV {n = 0} v (suc ()) 
insertV {n = suc n} v zero vs = v ∷ vs
insertV {n = suc n} v (suc i) (w ∷ ws) = w ∷ insertV v i ws

-- A permutation takes two vectors of the same size, matches one
-- element from each and returns another permutation

data P {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : 
  (m n : ℕ) → (m ≡ n) → Vec A m → Vec B n → Set (ℓ ⊔ ℓ') where
  nil : P A B 0 0 refl [] []
  cons : {m n : ℕ} {i : Fin (suc m)} {j : Fin (suc n)} → (p : m ≡ n) → 
         (v : A) → (w : B) → (vs : Vec A m) → (ws : Vec B n) →
         P A B m n p vs ws → 
         P A B (suc m) (suc n) (cong suc p) (insertV v i vs) (insertV w j ws)

-- A permutation is a sequence of "insertions".

infixr 5 _∷_

data Perm : ℕ → Set where
  []  : Perm 0
  _∷_ : {n : ℕ} → Fin (suc n) → Perm n → Perm (suc n)

lookupP : ∀ {n} → Fin n → Perm n → Fin n
lookupP () [] 
lookupP zero (j ∷ _) = j
lookupP {suc n} (suc i) (j ∷ q) = inject₁ (lookupP i q)

insert : ∀ {ℓ n} {A : Set ℓ} → Vec A n → Fin (suc n) → A → Vec A (suc n)
insert vs zero w          = w ∷ vs
insert [] (suc ())        -- absurd
insert (v ∷ vs) (suc i) w = v ∷ insert vs i w

-- A permutation acts on a vector by inserting each element in its new
-- position.

permute : ∀ {ℓ n} {A : Set ℓ} → Perm n → Vec A n → Vec A n
permute []       []       = []
permute (p ∷ ps) (v ∷ vs) = insert (permute ps vs) p v

-- Use a permutation to match up the elements in two vectors. See more
-- convenient function matchP below.

match : ∀ {t t'} → (size t ≡ size t') → Perm (size t) → 
        Vec ⟦ t ⟧ (size t) → Vec ⟦ t' ⟧ (size t) → 
        Vec (⟦ t ⟧ × ⟦ t' ⟧) (size t)
match {t} {t'} sp α vs vs' = 
  let js = permute α (tabulate id)
  in zip (tabulate (λ j → lookup (lookup j js) vs)) vs'

-- swap
-- 
-- swapperm produces the permutations that maps:
-- [ a , b || x , y , z ] 
-- to 
-- [ x , y , z || a , b ]
-- Ex. 
-- permute (swapperm {5} (inject+ 2 (fromℕ 2))) ordered=[0,1,2,3,4]
-- produces [2,3,4,0,1]
-- Explicitly:
-- swapex : Perm 5
-- swapex =   inject+ 1 (fromℕ 3) -- :: Fin 5
--          ∷ inject+ 0 (fromℕ 3) -- :: Fin 4
--          ∷ zero
--          ∷ zero
--          ∷ zero
--          ∷ []

swapperm : ∀ {n} → Fin n → Perm n
swapperm {0} ()          -- absurd
swapperm {suc n} zero    = idperm
swapperm {suc n} (suc i) = 
  subst Fin (-+-id n i) 
    (inject+ (toℕ i) (fromℕ (n ∸ toℕ i))) ∷ swapperm {n} i

-- compositions

-- Sequential composition

scompperm : ∀ {n} → Perm n → Perm n → Perm n
scompperm α β = {!!} 

-- Sub-permutations
-- useful for parallel and multiplicative compositions

-- Perm 4 has elements [Fin 4, Fin 3, Fin 2, Fin 1]
-- SubPerm 11 7 has elements [Fin 11, Fin 10, Fin 9, Fin 8]
-- So Perm 4 is a special case SubPerm 4 0

data SubPerm : ℕ → ℕ → Set where
  []s  : {n : ℕ} → SubPerm n n
  _∷s_ : {n m : ℕ} → Fin (suc n) → SubPerm n m → SubPerm (suc n) m

merge : ∀ {m n} → SubPerm m n → Perm n → Perm m
merge []s      β = β
merge (i ∷s α) β = i ∷ merge α β

injectP : ∀ {m} → Perm m → (n : ℕ) → SubPerm (m + n) n
injectP []      n = []s 
injectP (i ∷ α) n = inject+ n i ∷s injectP α n
  
-- Parallel + composition

pcompperm : ∀ {m n} → Perm m → Perm n → Perm (m + n)
pcompperm {m} {n} α β = merge (injectP α n) β

-- Multiplicative * composition

tcompperm : ∀ {m n} → Perm m → Perm n → Perm (m * n)
tcompperm []      β = []
tcompperm (i ∷ α) β = {!!} 

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes a permutation.

comb2perm : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Perm (size t₁)
comb2perm {PLUS ZERO t} {.t} unite₊ = idperm
comb2perm {t} {PLUS ZERO .t} uniti₊ = idperm
comb2perm {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ with size t₂
... | 0     = idperm 
... | suc j = swapperm {size t₁ + suc j} 
               (inject≤ (fromℕ (size t₁)) (suc≤ (size t₁) j))
comb2perm {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} assocl₊ = idperm
comb2perm {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} assocr₊ = idperm
comb2perm {TIMES ONE t} {.t} unite⋆ = idperm
comb2perm {t} {TIMES ONE .t} uniti⋆ = idperm
comb2perm {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = idperm 
comb2perm assocl⋆   = idperm  
comb2perm assocr⋆   = idperm  
comb2perm distz     = idperm  
comb2perm factorz   = idperm  
comb2perm dist      = idperm  
comb2perm factor    = idperm  
comb2perm id⟷      = idperm  
comb2perm (c₁ ◎ c₂) = scompperm 
                        (comb2perm c₁) 
                        (subst Perm (sym (size≡ c₁)) (comb2perm c₂))
comb2perm (c₁ ⊕ c₂) = pcompperm (comb2perm c₁) (comb2perm c₂) 
comb2perm (c₁ ⊗ c₂) = tcompperm (comb2perm c₁) (comb2perm c₂) 

-- Convenient way of "seeing" what the permutation does for each combinator

matchP : ∀ {t t'} → (t ⟷ t') → Vec (⟦ t ⟧ × ⟦ t' ⟧) (size t)
matchP {t} {t'} c = 
  match sp (comb2perm c) (utoVec t) 
    (subst (λ n → Vec ⟦ t' ⟧ n) (sym sp) (utoVec t'))
  where sp = size≡ c

------------------------------------------------------------------------------
-- Extensional equivalence of combinators: two combinators are
-- equivalent if they denote the same permutation. Generally we would
-- require that the two permutations map the same value x to values y
-- and z that have a path between them, but because the internals of each
-- type are discrete groupoids, this reduces to saying that y and z
-- are identical, and hence that the permutations are identical.

infix  10  _∼_  

_∼_ : ∀ {t₁ t₂} → (c₁ c₂ : t₁ ⟷ t₂) → Set
c₁ ∼ c₂ = (comb2perm c₁ ≡ comb2perm c₂)

-- The relation ~ is an equivalence relation

refl∼ : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → (c ∼ c)
refl∼ = refl 

sym∼ : ∀ {t₁ t₂} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₁)
sym∼ = sym

trans∼ : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₃) → (c₁ ∼ c₃)
trans∼ = trans

-- The relation ~ validates the groupoid laws

c◎id∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ id⟷ ∼ c
c◎id∼c = {!!} 

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

------------------------------------------------------------------------------
-- Nat and Fin lemmas

suc≤ : (m n : ℕ) → suc m ≤ m + suc n
suc≤ 0 n       = s≤s z≤n
suc≤ (suc m) n = s≤s (suc≤ m n)

-+-id : (n : ℕ) → (i : Fin n) → suc (n ∸ toℕ i) + toℕ i ≡ suc n
-+-id 0 ()            -- absurd
-+-id (suc n) zero    = +-right-identity (suc (suc n))
-+-id (suc n) (suc i) = begin
  suc (suc n ∸ toℕ (suc i)) + toℕ (suc i) 
    ≡⟨ refl ⟩
  suc (n ∸ toℕ i) + suc (toℕ i) 
    ≡⟨ +-suc (suc (n ∸ toℕ i)) (toℕ i) ⟩
  suc (suc (n ∸ toℕ i) + toℕ i)
    ≡⟨ cong suc (-+-id n i) ⟩
  suc (suc n) ∎

p0 p1 : Perm 4
p0 = idπ
p1 = swap (inject+ 1 (fromℕ 2)) (inject+ 3 (fromℕ 0))
     (swap (fromℕ 3) zero
     (swap zero (inject+ 1 (fromℕ 2))
     idπ))


xx = action p1 (10 ∷ 20 ∷ 30 ∷ 40 ∷ [])

n≤sn : ∀ {x} → x ≤ suc x
n≤sn {0}     = z≤n
n≤sn {suc n} = s≤s (n≤sn {n})

<implies≤ : ∀ {x y} → (x < y) → (x ≤ y)
<implies≤ (s≤s z≤n) = z≤n 
<implies≤ {suc x} {suc y} (s≤s p) = 
  begin (suc x 
           ≤⟨ p ⟩
         y
            ≤⟨ n≤sn {y} ⟩
         suc y ∎)
  where open ≤-Reasoning

bounded≤ : ∀ {n} (i : Fin n) → toℕ i ≤ n
bounded≤ i = <implies≤ (bounded i)
                 
n≤n : (n : ℕ) → n ≤ n
n≤n 0 = z≤n
n≤n (suc n) = s≤s (n≤n n)

-- Convenient way of "seeing" what the permutation does for each combinator

matchP : ∀ {t t'} → (t ⟷ t') → Vec (⟦ t ⟧ × ⟦ t' ⟧) (size t)
matchP {t} {t'} c = 
  match sp (comb2perm c) (utoVec t) 
    (subst (λ n → Vec ⟦ t' ⟧ n) (sym sp) (utoVec t'))
  where sp = size≡ c

infix 90 _X_

data Swap (n : ℕ) : Set where
  _X_ : Fin n → Fin n → Swap n

Perm : ℕ → Set
Perm n = List (Swap n)

showSwap : ∀ {n} → Swap n → String
showSwap (i X j) = show (toℕ i) ++S " X " ++S show (toℕ j)

actionπ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Perm n → Vec A n → Vec A n
actionπ π vs = foldl swapX vs π
  where 
    swapX : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vec A n → Swap n → Vec A n  
    swapX vs (i X j) = (vs [ i ]≔ lookup j vs) [ j ]≔ lookup i vs

swapπ : ∀ {m n} → Perm (m + n)
swapπ {0}     {n}     = []
swapπ {suc m} {n}     = 
  concatL 
    (replicate (suc m)
      (toList 
        (zipWith _X_ 
          (mapV inject₁ (allFin (m + n))) 
          (tail (allFin (suc m + n))))))

scompπ : ∀ {n} → Perm n → Perm n → Perm n
scompπ = _++L_

injectπ : ∀ {m} → Perm m → (n : ℕ) → Perm (m + n)
injectπ π n = mapL (λ { (i X j) → (inject+ n i) X (inject+ n j) }) π 

raiseπ : ∀ {n} → Perm n → (m : ℕ) → Perm (m + n)
raiseπ π m = mapL (λ { (i X j) → (raise m i) X (raise m j) }) π 

pcompπ : ∀ {m n} → Perm m → Perm n → Perm (m + n)
pcompπ {m} {n} α β = (injectπ α n) ++L (raiseπ β m)

idπ : ∀ {n} → Perm n
idπ {n} = toList (zipWith _X_ (allFin n) (allFin n))

tcompπ : ∀ {m n} → Perm m → Perm n → Perm (m * n)
tcompπ {m} {n} α β = 
  concatL (mapL 
            (λ { (i X j) → 
                 mapL (λ { (k X l) → 
                        (inject≤ (fromℕ (toℕ i * n + toℕ k)) 
                                 (i*n+k≤m*n i k))
                        X 
                        (inject≤ (fromℕ (toℕ j * n + toℕ l)) 
                                 (i*n+k≤m*n j l))})
                      (β ++L idπ {n})})
            (α ++L idπ {m}))
--}
--}

