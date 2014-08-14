{-# OPTIONS --without-K #-}

module Pif where

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; distribʳ-*-+)

open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _≤_; z≤n; s≤s)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; _ℕ-_; raise; inject+; inject≤; _≻toℕ_) 
open import Data.Vec 
  using (Vec; tabulate; []; _∷_; [_]; lookup; map; _++_; concat; zip)
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

------------------------------------------------------------------------------
-- Semantic representation of permutations

-- One possibility of course is to represent them as functions but
-- this is a poor representation and eventually requires function
-- extensionality. Instead we represent them as vectors of "insert
-- positions".

-- First here is a canonical representation of each type as a vector
-- of values. This fixes a canonical order for the elements of the
-- types: each value has a canonical index. 

size : U → ℕ
size ZERO          = 0
size ONE           = 1
size (PLUS t₁ t₂)  = size t₁ + size t₂
size (TIMES t₁ t₂) = size t₁ * size t₂

utoVec : (t : U) → Vec ⟦ t ⟧ (size t)
utoVec ZERO          = []
utoVec ONE           = [ tt ]
utoVec (PLUS t₁ t₂)  = map inj₁ (utoVec t₁) ++ map inj₂ (utoVec t₂)
utoVec (TIMES t₁ t₂) = 
  concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) (utoVec t₂)) (utoVec t₁))

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

-- A permutation is a sequence of "insertions".

infixr 5 _∷_

data Perm : ℕ → Set where
  []  : Perm 0
  _∷_ : {n : ℕ} → Fin (suc n) → Perm n → Perm (suc n)

-- Insertions are as expected. 

insert : ∀ {ℓ n} {A : Set ℓ} → Vec A n → Fin (suc n) → A → Vec A (suc n)
insert vs zero w = w ∷ vs
insert [] (suc ())
insert (v ∷ vs) (suc i) w = v ∷ insert vs i w

-- A permutation takes a vector and inserts each element into a new
-- position.

permute : ∀ {ℓ n} {A : Set ℓ} → Perm n → Vec A n → Vec A n
permute [] [] = []
permute (p ∷ ps) (v ∷ vs) = insert (permute ps vs) p v

-- Use a permutation to match up the elements in two vectors

match : ∀ {t t'} → (size t ≡ size t') → Perm (size t) → 
        Vec ⟦ t ⟧ (size t) → Vec ⟦ t' ⟧ (size t) → 
        Vec (⟦ t ⟧ × ⟦ t' ⟧) (size t)
match {t} {t'} sp α vs vs' = 
  let js = permute α (tabulate id)
  in zip (tabulate (λ j → lookup (lookup j js) vs)) vs'

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
swapperm {0} ()          -- can't give you an index 
swapperm {suc n} zero    = idperm
swapperm {suc n} (suc i) = 
  subst Fin (-+-id n i) 
    (inject+ (toℕ i) (fromℕ (n ∸ toℕ i))) ∷ swapperm {n} i

-- composition

compperm : ∀ {m n} → (m ≡ n) → Perm m → Perm n → Perm m
compperm sp α β = {!!} 

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ is mapped to a permutation of size s = size t₁
-- = size t₂. This permutation maps a vector Fin s values to another
-- vector of Fin s values. 

comb2perm : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Perm (size t₁)
comb2perm {PLUS ZERO t} {.t} unite₊ = idperm
  -- input vector is of the shape [] ++ vs = vs 
  -- output vector is of the shape vs
  -- permutation does nothing
comb2perm {t} {PLUS ZERO .t} uniti₊ = idperm
  -- input vector is of the shape vs
  -- output vector is of the shape [] ++ vs = vs 
  -- permutation does nothing
comb2perm {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ with size t₂
... | 0     = idperm 
... | suc j = swapperm {size t₁ + suc j} 
               (inject≤ (fromℕ (size t₁)) (suc≤ (size t₁) j))
  -- input vector is of the shape  vs₁ ++ vs₂
  -- output vector is of the shape vs₂ ++ vs₁
  -- e.g. from input [a , b || x, y , z] 
  -- permutation needs to produce
  -- output          [x , y , z || a , b] 
comb2perm {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} assocl₊ = idperm
  -- input vector is of the shape  vs₁ ++ (vs₂ ++ vs₃)
  -- output vector is of the shape (vs₁ ++ vs₂) ++ vs₃
  -- permutation does nothing
comb2perm {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} assocr₊ = idperm
  -- input vector is of the shape  (vs₁ ++ vs₂) ++ vs₃
  -- output vector is of the shape vs₁ ++ (vs₂ ++ vs₃)
  -- permutation does nothing
comb2perm {TIMES ONE t} {.t} unite⋆ = idperm
  -- permutation does nothing
comb2perm {t} {TIMES ONE .t} uniti⋆ = idperm
  -- permutation does nothing
comb2perm {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = idperm 
  -- permutation does nothing
comb2perm assocl⋆   = idperm  
  -- permutation does nothing
comb2perm assocr⋆   = idperm  
  -- permutation does nothing
comb2perm distz     = idperm  
  -- permutation does nothing
comb2perm factorz   = idperm  
  -- permutation does nothing
comb2perm dist      = idperm  
  -- permutation does nothing
comb2perm factor    = idperm  
  -- permutation does nothing
comb2perm id⟷      = idperm  
  -- permutation does nothing
comb2perm (c₁ ◎ c₂) = compperm (size≡ c₁) (comb2perm c₁) (comb2perm c₂) 
comb2perm (c₁ ⊕ c₂) = {!!} 
comb2perm (c₁ ⊗ c₂) = {!!} 

------------------------------------------------------------------------------
-- Testing

t₁  = PLUS ZERO BOOL
t₂  = BOOL
m₁ = match refl (comb2perm {t₁} {t₂} unite₊) (utoVec t₁) (utoVec t₂)
-- (inj₂ (inj₁ tt) , inj₁ tt) ∷ (inj₂ (inj₂ tt) , inj₂ tt) ∷ []
m₂ = match refl (comb2perm {t₂} {t₁} uniti₊) (utoVec t₂) (utoVec t₁)
-- (inj₁ tt , inj₂ (inj₁ tt)) ∷ (inj₂ tt , inj₂ (inj₂ tt)) ∷ []

t₃ = PLUS BOOL ONE
t₄ = PLUS ONE BOOL
m₃ = match refl (comb2perm {t₃} {t₄} swap₊) (utoVec t₃) (utoVec t₄)
-- (inj₂ tt , inj₁ tt) ∷
-- (inj₁ (inj₁ tt) , inj₂ (inj₁ tt)) ∷
-- (inj₁ (inj₂ tt) , inj₂ (inj₂ tt)) ∷ []
m₄ = match refl (comb2perm {t₄} {t₃} swap₊) (utoVec t₄) (utoVec t₃)
-- (inj₂ (inj₁ tt) , inj₁ (inj₁ tt)) ∷
-- (inj₂ (inj₂ tt) , inj₁ (inj₂ tt)) ∷ 
-- (inj₁ tt , inj₂ tt) ∷ []

t₅  = PLUS ONE (PLUS BOOL ONE)
t₆  = PLUS (PLUS ONE BOOL) ONE
m₅ = match refl (comb2perm {t₅} {t₆} assocl₊) (utoVec t₅) (utoVec t₆)
-- (inj₁ tt , inj₁ (inj₁ tt)) ∷
-- (inj₂ (inj₁ (inj₁ tt)) , inj₁ (inj₂ (inj₁ tt))) ∷
-- (inj₂ (inj₁ (inj₂ tt)) , inj₁ (inj₂ (inj₂ tt))) ∷
-- (inj₂ (inj₂ tt) , inj₂ tt) ∷ []
m₆ = match refl (comb2perm {t₆} {t₅} assocr₊) (utoVec t₆) (utoVec t₅)
-- (inj₁ (inj₁ tt) , inj₁ tt) ∷
-- (inj₁ (inj₂ (inj₁ tt)) , inj₂ (inj₁ (inj₁ tt))) ∷
-- (inj₁ (inj₂ (inj₂ tt)) , inj₂ (inj₁ (inj₂ tt))) ∷
-- (inj₂ tt , inj₂ (inj₂ tt)) ∷ []

t₇ = TIMES ONE BOOL
t₈ = BOOL
m₇ = match refl (comb2perm {t₇} {t₈} unite⋆) (utoVec t₇) (utoVec t₈)
-- ((tt , inj₁ tt) , inj₁ tt) ∷ ((tt , inj₂ tt) , inj₂ tt) ∷ []
m₈ = match refl (comb2perm {t₈} {t₇} uniti⋆) (utoVec t₈) (utoVec t₇)
-- (inj₁ tt , (tt , inj₁ tt)) ∷ (inj₂ tt , (tt , inj₂ tt)) ∷ []

t₉  = TIMES BOOL ONE
t₁₀ = TIMES ONE BOOL
m₉  = match refl (comb2perm {t₉} {t₁₀} swap⋆) (utoVec t₉) (utoVec t₁₀)
-- ((inj₁ tt , tt) , (tt , inj₁ tt)) ∷
-- ((inj₂ tt , tt) , (tt , inj₂ tt)) ∷ []
m₁₀ = match refl (comb2perm {t₁₀} {t₉} swap⋆) (utoVec t₁₀) (utoVec t₉)
-- ((tt , inj₁ tt) , (inj₁ tt , tt)) ∷
-- ((tt , inj₂ tt) , (inj₂ tt , tt)) ∷ []

t₁₁ = TIMES BOOL (TIMES ONE BOOL)
t₁₂ = TIMES (TIMES BOOL ONE) BOOL
m₁₁ = match refl (comb2perm {t₁₁} {t₁₂} assocl⋆) (utoVec t₁₁) (utoVec t₁₂)
-- ((inj₁ tt , (tt , inj₁ tt)) , ((inj₁ tt , tt) , inj₁ tt)) ∷
-- ((inj₁ tt , (tt , inj₂ tt)) , ((inj₁ tt , tt) , inj₂ tt)) ∷
-- ((inj₂ tt , (tt , inj₁ tt)) , ((inj₂ tt , tt) , inj₁ tt)) ∷
-- ((inj₂ tt , (tt , inj₂ tt)) , ((inj₂ tt , tt) , inj₂ tt)) ∷ []
m₁₂ = match refl (comb2perm {t₁₂} {t₁₁} assocr⋆) (utoVec t₁₂) (utoVec t₁₁)
-- (((inj₁ tt , tt) , inj₁ tt) , (inj₁ tt , (tt , inj₁ tt)) ∷
-- (((inj₁ tt , tt) , inj₂ tt) , (inj₁ tt , (tt , inj₂ tt)) ∷
-- (((inj₂ tt , tt) , inj₁ tt) , (inj₂ tt , (tt , inj₁ tt)) ∷
-- (((inj₂ tt , tt) , inj₂ tt) , (inj₂ tt , (tt , inj₂ tt)) ∷ []

t₁₃ = TIMES ZERO BOOL
t₁₄ = ZERO
m₁₃ = match refl (comb2perm {t₁₃} {t₁₄} distz) (utoVec t₁₃) (utoVec t₁₄)
-- []
m₁₄ = match refl (comb2perm {t₁₄} {t₁₃} factorz) (utoVec t₁₄) (utoVec t₁₃)
-- []

t₁₅ = TIMES (PLUS BOOL ONE) BOOL
t₁₆ = PLUS (TIMES BOOL BOOL) (TIMES ONE BOOL)
m₁₅ = match refl (comb2perm {t₁₅} {t₁₆} dist) (utoVec t₁₅) (utoVec t₁₆)
-- ((inj₁ (inj₁ tt) , inj₁ tt) , inj₁ (inj₁ tt , inj₁ tt)) ∷
-- ((inj₁ (inj₁ tt) , inj₂ tt) , inj₁ (inj₁ tt , inj₂ tt)) ∷
-- ((inj₁ (inj₂ tt) , inj₁ tt) , inj₁ (inj₂ tt , inj₁ tt)) ∷
-- ((inj₁ (inj₂ tt) , inj₂ tt) , inj₁ (inj₂ tt , inj₂ tt)) ∷
-- ((inj₂ tt , inj₁ tt) , inj₂ (tt , inj₁ tt)) ∷
-- ((inj₂ tt , inj₂ tt) , inj₂ (tt , inj₂ tt)) ∷ []
m₁₆ = match refl (comb2perm {t₁₆} {t₁₅} factor) (utoVec t₁₆) (utoVec t₁₅)
-- (inj₁ (inj₁ tt , inj₁ tt) , (inj₁ (inj₁ tt) , inj₁ tt)) ∷
-- (inj₁ (inj₁ tt , inj₂ tt) , (inj₁ (inj₁ tt) , inj₂ tt)) ∷
-- (inj₁ (inj₂ tt , inj₁ tt) , (inj₁ (inj₂ tt) , inj₁ tt)) ∷
-- (inj₁ (inj₂ tt , inj₂ tt) , (inj₁ (inj₂ tt) , inj₂ tt)) ∷
-- (inj₂ (tt , inj₁ tt) , (inj₂ tt , inj₁ tt)) ∷
-- (inj₂ (tt , inj₂ tt) , (inj₂ tt , inj₂ tt)) ∷ []

t₁₇ = BOOL 
t₁₈ = BOOL
m₁₇ = match refl (comb2perm {t₁₇} {t₁₈} id⟷) (utoVec t₁₇) (utoVec t₁₈)
-- (inj₁ tt , inj₁ tt) ∷ (inj₂ tt , inj₂ tt) ∷ []

--◎
--⊕
--⊗

------------------------------------------------------------------------------
