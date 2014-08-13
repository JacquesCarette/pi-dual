{-# OPTIONS --without-K #-}

module Pif where

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat.Properties.Simple using (+-right-identity; +-suc)

open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _≤_; z≤n; s≤s)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; _ℕ-_; raise; inject+; inject≤; _≻toℕ_) 
open import Data.Vec using (Vec; tabulate; []; _∷_; [_]; map; _++_; concat)
open import Function using (id; _∘_)

open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

open import Groupoid

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

⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

-- Abbreviations for examples

BOOL BOOL² : U
BOOL  = PLUS ONE ONE 
BOOL² = TIMES BOOL BOOL

false⟷ true⟷ : ⟦ BOOL ⟧
false⟷ = inj₁ tt
true⟷  = inj₂ tt

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

neg₁ neg₂ neg₃ neg₄ neg₅ : BOOL ⟷ BOOL
neg₁ = swap₊
neg₂ = id⟷ ◎ swap₊
neg₃ = swap₊ ◎ swap₊ ◎ swap₊
neg₄ = swap₊ ◎ id⟷
neg₅ = uniti⋆ ◎ swap⋆ ◎ (swap₊ ⊗ id⟷) ◎ swap⋆ ◎ unite⋆

-- CNOT

CNOT : BOOL² ⟷ BOOL²
CNOT = TIMES (PLUS x y) BOOL
         ⟷⟨ dist ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ id⟷ ⊕ (id⟷ ⊗ swap₊) ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ factor ⟩
       TIMES (PLUS x y) BOOL □
  where x = ONE; y = ONE

-- TOFFOLI

TOFFOLI : TIMES BOOL BOOL² ⟷ TIMES BOOL BOOL²
TOFFOLI = TIMES (PLUS x y) BOOL² 
            ⟷⟨ dist ⟩
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩ 
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ factor ⟩
          TIMES (PLUS x y) BOOL² □
  where x = ONE; y = ONE

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
!! {c = c₁ ⊕ c₂} = 
  begin (! (! (c₁ ⊕ c₂))
           ≡⟨ refl ⟩
         ! (! c₁) ⊕ ! (! c₂)
           ≡⟨ cong₂ _⊕_ (!! {c = c₁}) (!! {c = c₂}) ⟩ 
         c₁ ⊕ c₂ ∎)
!! {c = c₁ ⊗ c₂} = 
  begin (! (! (c₁ ⊗ c₂))
           ≡⟨ refl ⟩
         ! (! c₁) ⊗ ! (! c₂)
           ≡⟨ cong₂ _⊗_ (!! {c = c₁}) (!! {c = c₂}) ⟩ 
         c₁ ⊗ c₂ ∎)

------------------------------------------------------------------------------
-- Fin lemmas

-+-id : (n : ℕ) → (i : Fin n) → suc (n ∸ toℕ i) + toℕ i ≡ suc n
-+-id 0 ()
-+-id (suc n) zero = +-right-identity (suc (suc n))
-+-id (suc n) (suc i) = begin
  suc (suc n ∸ toℕ (suc i)) + toℕ (suc i) 
    ≡⟨ refl ⟩
  suc (n ∸ toℕ i) + suc (toℕ i) 
    ≡⟨ +-suc (suc (n ∸ toℕ i)) (toℕ i) ⟩
  suc (suc (n ∸ toℕ i) + toℕ i)
    ≡⟨ cong suc (-+-id n i) ⟩
  suc (suc n) ∎

simp-+-id : ∀ {n} {i : Fin n} → Fin (suc (n ∸ toℕ i) + toℕ i) → Fin (suc n)
simp-+-id {n} {i} x = help {n} {i} (-+-id n i) x 
  where help : ∀ {n} {i : Fin n} → suc (n ∸ toℕ i) + toℕ i ≡ suc n → 
               Fin (suc (n ∸ toℕ i) + toℕ i) → Fin (suc n)
        help pr x rewrite cong Fin pr = x

suc≤ : (m n : ℕ) → suc m ≤ m + suc n
suc≤ 0 n = s≤s z≤n
suc≤ (suc m) n = s≤s (suc≤ m n)

------------------------------------------------------------------------------
-- Extensional view of permutations. One possibility of course is to
-- represent them as functions but this is a poor representation and
-- eventually requires function extensionality. Instead we represent them as
-- vectors.

infixr 5 _∷_

data Perm : ℕ → Set where
  []  : Perm 0
  _∷_ : {n : ℕ} → (p : Fin (suc n)) → (ps : Perm n) → Perm (suc n)

-- A permutation acts on a vector...

permute : ∀ {ℓ n} {A : Set ℓ} → Perm n → Vec A n → Vec A n 
permute [] [] = []
permute (p ∷ ps) (x ∷ xs) = insert (permute ps xs) p x
  where insert : ∀ {ℓ n} {A : Set ℓ} → 
          Vec A n → Fin (suc n) → A → Vec A (suc n)
        insert xs zero a = a ∷ xs
        insert [] (suc ()) 
        insert (x ∷ xs) (suc i) a = x ∷ insert xs i a

-- Examples permutations and their actions on a simple ordered vector

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

------------------------------------------------------------------------------
-- Library for permutations

-- id

idperm : ∀ {n} → Perm n
idperm {0}     = []
idperm {suc n} = zero ∷ idperm

-- swap
-- 
-- swapperm produces the permutations that maps:
-- [ a , b || x , y , z ] 
-- to 
-- [ x , y , z || a , b ]

swapperm : ∀ {n} → Fin n → Perm n
swapperm {0} ()          -- can't give you an index 
swapperm {suc n} zero    = idperm
swapperm {suc n} (suc i) = 
  simp-+-id {n} {i} (inject+ (toℕ i) (fromℕ (n ∸ toℕ i))) ∷ swapperm {n} i

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

------------------------------------------------------------------------------
-- A type is mapped to its size s; the values of the type are the
-- values of Fin s

utoℕ : U → ℕ
utoℕ ZERO          = 0
utoℕ ONE           = 1
utoℕ (PLUS t₁ t₂)  = utoℕ t₁ + utoℕ t₂
utoℕ (TIMES t₁ t₂) = utoℕ t₁ * utoℕ t₂

ufromℕ : ℕ → U
ufromℕ 0       = ZERO
ufromℕ (suc n) = PLUS ONE (ufromℕ n)

-- Vector representation so that we can test permutations

utoVec : (t : U) → Vec ⟦ t ⟧ (utoℕ t)
utoVec ZERO          = []
utoVec ONE           = [ tt ]
utoVec (PLUS t₁ t₂)  = map inj₁ (utoVec t₁) ++ map inj₂ (utoVec t₂)
utoVec (TIMES t₁ t₂) = 
  concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) (utoVec t₂)) (utoVec t₁))

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

-- normalize a finite type to (1 + (1 + (1 + ... + (1 + 0) ... )))
-- a bunch of ones ending with zero with left biased + in between

normalℕ : U → U
normalℕ = ufromℕ ∘ utoℕ

-- A combinator t₁ ⟷ t₂ is mapped to a permutation of size s = utoℕ t₁
-- = utoℕ t₂. This permutation maps a vector Fin s values to another
-- vector of Fin s values. 

comb2perm : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Perm (utoℕ t₁)
comb2perm {PLUS ZERO t} {.t} unite₊ = idperm
  -- input vector is of the shape [] ++ vs = vs 
  -- output vector is of the shape vs
  -- permutation does need to do anything
comb2perm {t} {PLUS ZERO .t} uniti₊ = idperm
  -- input vector is of the shape vs
  -- output vector is of the shape [] ++ vs = vs 
  -- permutation does need to do anything
comb2perm {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ with utoℕ t₂
... | 0 = idperm 
... | suc j = swapperm {utoℕ t₁ + suc j} 
               (inject≤ (fromℕ (utoℕ t₁)) (suc≤ (utoℕ t₁) j))
  -- input vector is of the shape vs₁ ++ vs₂
  -- output vector is of the shape vs₂ ++ vs₁
  -- e.g. [a , b] ++ [x , y , z] = [a , b , x, y , z] 
  -- permutation needs to produce
  -- e.g. [x , y , z] ++ [a , b] = [x , y , z , a , b] 
comb2perm assocl₊   = idperm
comb2perm assocr₊   = idperm
comb2perm unite⋆    = idperm
comb2perm uniti⋆    = idperm
comb2perm swap⋆     = idperm --
comb2perm assocl⋆   = idperm
comb2perm assocr⋆   = idperm
comb2perm distz     = idperm
comb2perm factorz   = idperm
comb2perm dist      = idperm --
comb2perm factor    = idperm --
comb2perm id⟷      = idperm
comb2perm (c₁ ◎ c₂) = idperm --
comb2perm (c₁ ⊕ c₂) = idperm --
comb2perm (c₁ ⊗ c₂) = idperm  --

------------------------------------------------------------------------------
