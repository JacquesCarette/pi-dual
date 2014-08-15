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

-- A permutation is a sequence of "insertions".

infixr 5 _∷_

data Perm : ℕ → Set where
  []  : Perm 0
  _∷_ : {n : ℕ} → Fin (suc n) → Perm n → Perm (suc n)

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
swapperm {0} ()          -- absurd
swapperm {suc n} zero    = idperm
swapperm {suc n} (suc i) = 
  subst Fin (-+-id n i) 
    (inject+ (toℕ i) (fromℕ (n ∸ toℕ i))) ∷ swapperm {n} i

-- compositions

pex qex : Perm 3
pex = inject+ 1 (fromℕ 1) ∷ fromℕ 1 ∷ zero ∷ []
qex = fromℕ 2 ∷ zero ∷ zero ∷ []
cex = permute pex (permute qex (tabulate id))

-- pex takes [0,1,2] to [2,0,1]
-- qex takes [0,1,2] to [1,2,0]
-- pex ◌ qex takes [0,1,2] to [0,1,2]
-- qex ◌ pex takes [0,1,2] to

-- _◌_ : ∀ {n} → Perm n → Perm n → Perm n
-- [] ◌ [] = []
-- (i ∷ p) ◌ (j ∷ q) = {!!} ∷ (p ◌ q) 

-- .n : ℕ
-- i  : Fin (suc .n)
-- p  : Perm .n
-- j  : Fin (suc .n)
-- q  : Perm .n
-- 
-- (zero ∷ p₁) ◌ (q ∷ q₁) = q ∷ (p₁ ◌ q₁)
-- (suc p ∷ p₁) ◌ (zero ∷ q₁) = {!!}
-- (suc p ∷ p₁) ◌ (suc q ∷ q₁) = {!!}
-- 
-- data Perm : ℕ → Set where
--   []  : Perm 0
--   _∷_ : {n : ℕ} → Fin (suc n) → Perm n → Perm (suc n)

-------------

scompperm : ∀ {n} → Perm n → Perm n → Perm n
scompperm α β = {!!} 

pcompperm : ∀ {m n} → Perm m → Perm n → Perm (m + n)
pcompperm α β = {!!} 

tcompperm : ∀ {m n} → Perm m → Perm n → Perm (m * n)
tcompperm α β = {!!} 

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
        ; linv = {!!} 
        ; rinv = {!!} 
        ; ∘-resp-≈ = {!!} 
        }

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
  id⇔ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ c
  trans⇔ : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
           (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)

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
2! id⇔          = id⇔ 
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)

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
        ; lneutr = {!!} 
        ; rneutr = {!!} 
        ; assoc  = {!!} 
        ; equiv = record { 
            refl  = id⇔ 
          ; sym   = 2! 
          ; trans = trans⇔ 
          }
        ; linv = {!!} 
        ; rinv = {!!} 
        ; ∘-resp-≈ = {!!} 
        }

------------------------------------------------------------------------------
-- Inverting permutations to syntactic combinators

perm2comb : {t₁ t₂ : U} → Perm (size t₁) → (t₁ ⟷ t₂)
perm2comb = {!!} 

------------------------------------------------------------------------------
-- Soundness and completeness
-- 
-- Proof of soundness and completeness: now we want to verify that ⇔
-- is sound and complete with respect to ∼. The statement to prove is
-- that for all c₁ and c₂, we have c₁ ∼ c₂ iff c₁ ⇔ c₂

soundness : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₁ ∼ c₂)
soundness = {!!} 

-- The idea is to invert evaluation and use that to extract from each
-- extensional representation of a combinator, a canonical syntactic
-- representative

canonical : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂)
canonical = perm2comb ∘ comb2perm

-- Note that if c₁ ⇔ c₂, then by soundness c₁ ∼ c₂ and hence their
-- canonical representatives are identical. 

canonicalWellDefined : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → 
                       (c₁ ⇔ c₂) → (canonical c₁ ≡ canonical c₂)
canonicalWellDefined α = cong perm2comb (soundness α)

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
    ⇔⟨  resp≡⇔ (cong perm2comb c₁∼c₂) ⟩ 
  canonical c₂
    ⇔⟨ 2! inversion ⟩ 
  c₂ ▤

------------------------------------------------------------------------------
