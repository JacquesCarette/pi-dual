{-# OPTIONS --without-K #-}

module Pif where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Data.Nat.Properties using (m≢1+m+n; i+j≡0⇒i≡0; i+j≡0⇒j≡0)
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

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Cauchy
open import Perm
open import Proofs
open import CauchyProofs
open import CauchyProofsT
open import CauchyProofsS
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

-- Combinators, permutations, or paths depending on the perspective

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

eval : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
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
-- Paths preserve sizes

size≡ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (size t₁ ≡ size t₂)
-- the composition case must be the first one
-- otherwise Agda will not unfold (c ◎ id⟷)
-- See "inconclusive matching" at 
-- http://wiki.portal.chalmers.se/agda/
-- pmwiki.php?n=ReferenceManual.PatternMatching
size≡ (c₁ ◎ c₂) = trans (size≡ c₁) (size≡ c₂)
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

-- Alternative view: this corresponds to Lemma 2.1.1 In our notation,
-- for every path t₁ ⟷ t₂, we have a path t₂ ⟷ t₁ such that (! id⟷)
-- reduces to id⟷. 

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

-- size≡ and !

size≡! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (size t₂ ≡ size t₁)
size≡! (c₁ ◎ c₂) = trans (size≡! c₂) (size≡! c₁)
size≡! {PLUS ZERO t} {.t} unite₊ = refl
size≡! {t} {PLUS ZERO .t} uniti₊ = refl
size≡! {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ = +-comm (size t₂) (size t₁)
size≡! {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} assocl₊ = 
  +-assoc (size t₁) (size t₂) (size t₃)
size≡! {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} assocr₊ = 
  sym (+-assoc (size t₁) (size t₂) (size t₃))
size≡! {TIMES ONE t} {.t} unite⋆ = sym (+-right-identity (size t))
size≡! {t} {TIMES ONE .t} uniti⋆ = +-right-identity (size t)
size≡! {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = *-comm (size t₂) (size t₁) 
size≡! {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} assocl⋆ = 
  *-assoc (size t₁) (size t₂) (size t₃)
size≡! {TIMES (TIMES t₁ t₂) t₃} {TIMES .t₁ (TIMES .t₂ .t₃)} assocr⋆ = 
  sym (*-assoc (size t₁) (size t₂) (size t₃))
size≡! {TIMES .ZERO t} {ZERO} distz = refl
size≡! {ZERO} {TIMES ZERO t} factorz = refl
size≡! {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} dist = 
  sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂))
size≡! {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} {TIMES (PLUS .t₁ .t₂) .t₃} factor = 
  distribʳ-*-+ (size t₃) (size t₁) (size t₂)
size≡! {t} {.t} id⟷ = refl
size≡! {PLUS t₁ t₂} {PLUS t₃ t₄} (c₁ ⊕ c₂) = cong₂ _+_ (size≡! c₁) (size≡! c₂)
size≡! {TIMES t₁ t₂} {TIMES t₃ t₄} (c₁ ⊗ c₂) = cong₂ _*_ (size≡! c₁) (size≡! c₂)
size≡! {PLUS ONE ONE} {BOOL} foldBool = refl
size≡! {BOOL} {PLUS ONE ONE} unfoldBool = refl

size∼! : {t₁ t₂ : U} → (c₁ c₂ : t₁ ⟷ t₂) → (size≡! c₁ ≡ size≡! c₂)
size∼! c₁ c₂ = proof-irrelevance (size≡! c₁) (size≡! c₂)

size≡!! : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → (size≡! (! c) ≡ sym (size≡! c))
size≡!! c = proof-irrelevance (size≡! (! c)) (sym (size≡! c))

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes a permutation.

c2cauchy : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Cauchy (size t₁)
-- the cases that do not inspect t₁ and t₂ should be at the beginning
-- so that Agda would unfold them
c2cauchy (c₁ ◎ c₂) = 
  scompcauchy 
    (c2cauchy c₁) 
    (subst Cauchy (size≡! c₁) (c2cauchy c₂)) 
c2cauchy (c₁ ⊕ c₂) = pcompcauchy (c2cauchy c₁) (c2cauchy c₂) 
c2cauchy (c₁ ⊗ c₂) = tcompcauchy (c2cauchy c₁) (c2cauchy c₂)  
c2cauchy unfoldBool = idcauchy 2
c2cauchy foldBool   = idcauchy 2
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

c2perm : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Permutation (size t₁)
-- the cases that do not inspect t₁ and t₂ should be at the beginning
-- so that Agda would unfold them
c2perm (c₁ ◎ c₂) = 
  scompperm 
    (c2perm c₁) 
    (subst Permutation (size≡! c₁) (c2perm c₂)) 
c2perm (c₁ ⊕ c₂) = pcompperm (c2perm c₁) (c2perm c₂) 
c2perm (c₁ ⊗ c₂) = tcompperm (c2perm c₁) (c2perm c₂)  
c2perm unfoldBool = idperm 2
c2perm foldBool   = idperm 2
c2perm {PLUS ZERO t} unite₊ = idperm (size t)
c2perm {t} uniti₊ = idperm (size t)
c2perm {PLUS t₁ t₂} swap₊ = swap+perm (size t₁) (size t₂)
c2perm {PLUS t₁ (PLUS t₂ t₃)} assocl₊ = 
  idperm (size t₁ + (size t₂ + size t₃))
c2perm {PLUS (PLUS t₁ t₂) t₃} assocr₊ = 
  idperm ((size t₁ + size t₂) + size t₃)
c2perm {TIMES ONE t} unite⋆ = 
  subst Permutation (sym (+-right-identity (size t))) (idperm (size t))
c2perm {t} uniti⋆ = idperm (size t)
c2perm {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = swap⋆perm (size t₁) (size t₂) 
c2perm {TIMES t₁ (TIMES t₂ t₃)} assocl⋆ = 
  idperm (size t₁ * (size t₂ * size t₃))
c2perm {TIMES (TIMES t₁ t₂) t₃} assocr⋆ = 
  idperm ((size t₁ * size t₂) * size t₃)
c2perm {TIMES ZERO t} distz = emptyperm
c2perm factorz = emptyperm
c2perm {TIMES (PLUS t₁ t₂) t₃} dist = 
  idperm ((size t₁ + size t₂) * size t₃)
c2perm {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} factor = 
  idperm ((size t₁ * size t₃) + (size t₂ * size t₃))
c2perm {t} id⟷  = idperm (size t)

-- Looking forward to Sec. 2.2 (Functions are functors). The
-- corresponding statement to Lemma 2.2.1 in our setting would be the
-- following. Given any *size preserving* function f : U → U, it is
-- the case that a combinator (path) c : t₁ ⟷ t₂ maps to a combinator
-- (path) ap_f(c) : f(t₁) ⟷ f(t₂).

------------------------------------------------------------------------------
-- Extensional equivalence of combinators

-- Two combinators are equivalent if they denote the same
-- permutation. Generally we would require that the two permutations
-- map the same value x to values y and z that have a path between
-- them, but because the internals of each type are discrete
-- groupoids, this reduces to saying that y and z are identical, and
-- hence that the permutations are identical.

infix  10  _∼_  

_∼_ : {t₁ t₂ : U} → (c₁ c₂ : t₁ ⟷ t₂) → Set
c₁ ∼ c₂ = (c2cauchy c₁ ≡ c2cauchy c₂)

-- The relation ~ is an equivalence relation

refl∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ∼ c)
refl∼ = refl 

sym∼ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₁)
sym∼ = sym

trans∼ : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₃) → (c₁ ∼ c₃)
trans∼ = trans

assoc∼ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
         c₁ ◎ (c₂ ◎ c₃) ∼ (c₁ ◎ c₂) ◎ c₃
assoc∼ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃} = 
  begin (c2cauchy (c₁ ◎ (c₂ ◎ c₃))
           ≡⟨ refl ⟩ 
         scompcauchy
           (c2cauchy c₁)
           (subst Cauchy (size≡! c₁)
             (scompcauchy
               (c2cauchy c₂)
               (subst Cauchy (size≡! c₂) (c2cauchy c₃))))
           ≡⟨ cong 
                (scompcauchy (c2cauchy c₁))
                (subst-dist 
                  scompcauchy 
                  (size≡! c₁) 
                  (c2cauchy c₂)
                  (subst Cauchy (size≡! c₂) (c2cauchy c₃))) ⟩ 
         scompcauchy
           (c2cauchy c₁)
           (scompcauchy
             (subst Cauchy (size≡! c₁) (c2cauchy c₂))
             (subst Cauchy (size≡! c₁)
               (subst Cauchy (size≡! c₂) (c2cauchy c₃))))
           ≡⟨ cong (λ x → 
                scompcauchy 
                  (c2cauchy c₁)
                  (scompcauchy 
                    (subst Cauchy (size≡! c₁) (c2cauchy c₂))
                    x))
                (subst-trans (size≡! c₁) (size≡! c₂) (c2cauchy c₃)) ⟩ 
         scompcauchy
           (c2cauchy c₁)
           (scompcauchy
             (subst Cauchy (size≡! c₁) (c2cauchy c₂))
             (subst Cauchy (trans (size≡! c₂) (size≡! c₁)) (c2cauchy c₃)))
           ≡⟨ scompassoc 
                (c2cauchy c₁) 
                (subst Cauchy (size≡! c₁) (c2cauchy c₂)) 
                (subst Cauchy (trans (size≡! c₂) (size≡! c₁)) (c2cauchy c₃)) ⟩
         scompcauchy 
           (scompcauchy 
             (c2cauchy c₁)
             (subst Cauchy (size≡! c₁) (c2cauchy c₂)))
           (subst Cauchy (trans (size≡! c₂) (size≡! c₁)) (c2cauchy c₃))
           ≡⟨ refl ⟩ 
         c2cauchy ((c₁ ◎ c₂) ◎ c₃) ∎)
  where open ≡-Reasoning

-- The combinators c : t₁ ⟷ t₂ are paths; we can transport
-- size-preserving properties across c. In particular, for some
-- appropriate P we want P(t₁) to map to P(t₂) via c.

-- The relation ~ validates the groupoid laws

c◎id∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ id⟷ ∼ c
c◎id∼c {t₁} {t₂} {c} = 
  begin (c2cauchy (c ◎ id⟷)
           ≡⟨ refl ⟩ 
        scompcauchy 
          (c2cauchy c)
          (subst Cauchy (size≡! c) (allFin (size t₂)))
           ≡⟨ cong (λ x → scompcauchy (c2cauchy c) x) 
              (congD! {B = Cauchy} allFin (size≡! c)) ⟩ 
        scompcauchy (c2cauchy c) (allFin (size t₁))
           ≡⟨ scomprid (c2cauchy c) ⟩ 
         c2cauchy c ∎)
  where open ≡-Reasoning

id◎c∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ◎ c ∼ c
id◎c∼c {t₁} {t₂} {c} = 
  begin (c2cauchy (id⟷ ◎ c)
           ≡⟨ refl ⟩ 
        scompcauchy 
          (allFin (size t₁))
          (subst Cauchy refl (c2cauchy c))
           ≡⟨ refl ⟩ 
        scompcauchy (allFin (size t₁)) (c2cauchy c)
           ≡⟨ scomplid (c2cauchy c) ⟩ 
         c2cauchy c ∎)
  where open ≡-Reasoning

linv∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ ! c ∼ id⟷
linv∼ {PLUS ZERO t} {.t} {unite₊} = 
  begin (c2cauchy {PLUS ZERO t} (unite₊ ◎ uniti₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {PLUS ZERO t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {t} {PLUS ZERO .t} {uniti₊} = 
  begin (c2cauchy {t} (uniti₊ ◎ unite₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS t₁ t₂} {PLUS .t₂ .t₁} {swap₊} =
  begin (c2cauchy {PLUS t₁ t₂} (swap₊ ◎ swap₊)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (swap+cauchy (size t₁) (size t₂))
           (subst Cauchy (+-comm (size t₂) (size t₁)) 
             (swap+cauchy (size t₂) (size t₁)))
           ≡⟨ swap+idemp (size t₁) (size t₂) ⟩ 
         c2cauchy {PLUS t₁ t₂} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} {assocl₊} = 
  begin (c2cauchy {PLUS t₁ (PLUS t₂ t₃)} (assocl₊ ◎ assocr₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃)))
           (subst Cauchy (+-assoc (size t₁) (size t₂) (size t₃))
             (idcauchy ((size t₁ + size t₂) + size t₃)))
           ≡⟨ cong 
               (scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃))))
               (congD! idcauchy (+-assoc (size t₁) (size t₂) (size t₃))) ⟩ 
         scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃)))
           (idcauchy (size t₁ + (size t₂ + size t₃)))
           ≡⟨ scomplid (idcauchy (size t₁ + (size t₂ + size t₃))) ⟩ 
         c2cauchy {PLUS t₁ (PLUS t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} {assocr₊} = 
  begin (c2cauchy {PLUS (PLUS t₁ t₂) t₃} (assocr₊ ◎ assocl₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃))
           (subst Cauchy (sym (+-assoc (size t₁) (size t₂) (size t₃)))
             (idcauchy (size t₁ + (size t₂ + size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃)))
                (congD! idcauchy (sym (+-assoc (size t₁) (size t₂) (size t₃)))) ⟩
         scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃))
           (idcauchy ((size t₁ + size t₂) + size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ + size t₂) + size t₃)) ⟩ 
         c2cauchy {PLUS (PLUS t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES ONE t} {.t} {unite⋆} = 
  begin (c2cauchy {TIMES ONE t} (unite⋆ ◎ uniti⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t)))
           (subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t)))
           ≡⟨ cong  
                (λ x → scompcauchy x x) 
                (congD! idcauchy (sym (+-right-identity (size t)))) ⟩ 
         scompcauchy (idcauchy (size t + 0)) (idcauchy (size t + 0))
           ≡⟨ scomplid (idcauchy (size t + 0)) ⟩ 
         c2cauchy {TIMES ONE t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {t} {TIMES ONE .t} {uniti⋆} = 
  begin (c2cauchy {t} (uniti⋆ ◎ unite⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy (+-right-identity (size t))
             (subst Cauchy (sym (+-right-identity (size t))) 
               (idcauchy (size t))))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t)))
                (subst-trans 
                  (+-right-identity (size t))
                  (sym (+-right-identity (size t))) 
                  (idcauchy (size t))) ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy (trans (sym (+-right-identity (size t)))
                                (+-right-identity (size t)))
               (idcauchy (size t)))
           ≡⟨ cong 
                 (λ x → scompcauchy 
                          (idcauchy (size t))
                          (subst Cauchy x (idcauchy (size t))))
                 (trans-syml (+-right-identity (size t))) ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy refl (idcauchy (size t)))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES t₁ t₂} {TIMES .t₂ .t₁} {swap⋆} = 
  begin (c2cauchy {TIMES t₁ t₂} (swap⋆ ◎ swap⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (swap⋆cauchy (size t₁) (size t₂))
           (subst Cauchy (*-comm (size t₂) (size t₁)) 
             (swap⋆cauchy (size t₂) (size t₁)))
           ≡⟨ swap⋆idemp (size t₁) (size t₂) ⟩
         c2cauchy {TIMES t₁ t₂} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} {assocl⋆} = 
  begin (c2cauchy {TIMES t₁ (TIMES t₂ t₃)} (assocl⋆ ◎ assocr⋆)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃)))
           (subst Cauchy (*-assoc (size t₁) (size t₂) (size t₃))
             (idcauchy ((size t₁ * size t₂) * size t₃)))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃))))
                (congD! idcauchy (*-assoc (size t₁) (size t₂) (size t₃))) ⟩ 
         scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃)))
           (idcauchy (size t₁ * (size t₂ * size t₃)))
           ≡⟨ scomplid (idcauchy (size t₁ * (size t₂ * size t₃))) ⟩ 
         c2cauchy {TIMES t₁ (TIMES t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES (TIMES t₁ t₂) t₃} {TIMES .t₁ (TIMES .t₂ .t₃)} {assocr⋆} = 
  begin (c2cauchy {TIMES (TIMES t₁ t₂) t₃} (assocr⋆ ◎ assocl⋆)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃))
           (subst Cauchy (sym (*-assoc (size t₁) (size t₂) (size t₃)))
             (idcauchy (size t₁ * (size t₂ * size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃)))
                (congD! idcauchy (sym (*-assoc (size t₁) (size t₂) (size t₃)))) ⟩
         scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃))
           (idcauchy ((size t₁ * size t₂) * size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ * size t₂) * size t₃)) ⟩ 
         c2cauchy {TIMES (TIMES t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES ZERO t} {ZERO} {distz} = refl
linv∼ {ZERO} {TIMES ZERO t} {factorz} = refl
linv∼ {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} {dist} = 
  begin (c2cauchy {TIMES (PLUS t₁ t₂) t₃} (dist ◎ factor)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃))
           (subst Cauchy (sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂)))
             (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃)))
                (congD! idcauchy 
                  (sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂)))) ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃))
           (idcauchy ((size t₁ + size t₂) * size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ + size t₂) * size t₃)) ⟩ 
         c2cauchy {TIMES (PLUS t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} {TIMES (PLUS .t₁ .t₂) .t₃} {factor} = 
  begin (c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)} (factor ◎ dist)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           (subst Cauchy (distribʳ-*-+ (size t₃) (size t₁) (size t₂))
             (idcauchy ((size t₁ + size t₂) * size t₃)))
           ≡⟨ cong 
                (scompcauchy 
                  (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))))
                (congD! idcauchy 
                  (distribʳ-*-+ (size t₃) (size t₁) (size t₂))) ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           ≡⟨ scomplid (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))) ⟩ 
         c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {t} {.t} {id⟷} = 
  begin (c2cauchy {t} (id⟷ ◎ id⟷)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {t₁} {t₃} {_◎_ {t₂ = t₂} c₁ c₂} = 
  begin (c2cauchy {t₁} ((c₁ ◎ c₂) ◎ ((! c₂) ◎ (! c₁)))
           ≡⟨ refl ⟩ 
         scompcauchy 
           (scompcauchy 
              (c2cauchy c₁) 
              (subst Cauchy (size≡! c₁) (c2cauchy c₂)))
           (subst Cauchy (trans (size≡! c₂) (size≡! c₁))
              (scompcauchy 
                (c2cauchy (! c₂)) 
                (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))
           ≡⟨ sym (scompassoc 
                    (c2cauchy c₁)
                    (subst Cauchy (size≡! c₁) (c2cauchy c₂))
                    (subst Cauchy (trans (size≡! c₂) (size≡! c₁))
                      (scompcauchy
                        (c2cauchy (! c₂))
                        (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))))  ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (scompcauchy 
              (subst Cauchy (size≡! c₁) (c2cauchy c₂))
              (subst Cauchy (trans (size≡! c₂) (size≡! c₁))
                (scompcauchy
                  (c2cauchy (! c₂))
                  (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (scompcauchy 
                           (subst Cauchy (size≡! c₁) (c2cauchy c₂))
                           x))
                (sym (subst-trans (size≡! c₁) (size≡! c₂)
                       (scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (scompcauchy 
              (subst Cauchy (size≡! c₁) (c2cauchy c₂))
              (subst Cauchy (size≡! c₁) 
                (subst Cauchy (size≡! c₂)
                  (scompcauchy
                    (c2cauchy (! c₂))
                    (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))))
           ≡⟨ cong 
                (scompcauchy (c2cauchy c₁))
                (sym (subst-dist scompcauchy (size≡! c₁)
                       (c2cauchy c₂)
                       (subst Cauchy (size≡! c₂)
                         (scompcauchy
                           (c2cauchy (! c₂))
                           (subst Cauchy (size≡! (! c₂)) 
                             (c2cauchy (! c₁))))))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (scompcauchy 
               (c2cauchy c₂)
               (subst Cauchy (size≡! c₂)
                 (scompcauchy
                   (c2cauchy (! c₂))
                   (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁)
                           (scompcauchy (c2cauchy c₂) x)))
                (subst-dist scompcauchy (size≡! c₂)
                  (c2cauchy (! c₂))
                  (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (scompcauchy 
               (c2cauchy c₂)
                 (scompcauchy
                   (subst Cauchy (size≡! c₂) (c2cauchy (! c₂)))
                   (subst Cauchy (size≡! c₂) 
                     (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) x))
                (scompassoc 
                  (c2cauchy c₂)
                  (subst Cauchy (size≡! c₂) (c2cauchy (! c₂)))
                  (subst Cauchy (size≡! c₂) 
                    (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (scompcauchy 
               (scompcauchy
                 (c2cauchy c₂)
                 (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
               (subst Cauchy (size≡! c₂) 
                 (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁)
                           (scompcauchy 
                             x
                             (subst Cauchy (size≡! c₂)
                               (subst Cauchy (size≡! (! c₂)) 
                                 (c2cauchy (! c₁)))))))
                (linv∼ {t₂} {t₃} {c₂}) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (scompcauchy 
               (allFin (size t₂))
               (subst Cauchy (size≡! c₂) 
                 (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))))
           ≡⟨ cong 
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) x))
                (scomplid
                  (subst Cauchy (size≡! c₂) 
                    (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (subst Cauchy (size≡! c₂) 
               (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))
           ≡⟨ cong 
                (λ x → scompcauchy 
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) x))
                (subst-trans (size≡! c₂) (size≡! (! c₂))
                  (c2cauchy (! c₁))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (subst Cauchy (trans (size≡! (! c₂)) (size≡! c₂))
               (c2cauchy (! c₁))))
           ≡⟨ cong 
                (λ x → scompcauchy 
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) 
                           (subst Cauchy x (c2cauchy (! c₁)))))
                (trans 
                  (cong (λ y → trans y (size≡! c₂)) (size≡!! c₂)) 
                  (trans-syml (size≡! c₂))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) (c2cauchy (! c₁)))
           ≡⟨ linv∼ {t₁} {t₂} {c₁} ⟩ 
         c2cauchy {t₁} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS t₁ t₂} {PLUS t₃ t₄} {c₁ ⊕ c₂} = 
  begin (c2cauchy {PLUS t₁ t₂} ((c₁ ⊕ c₂) ◎ ((! c₁) ⊕ (! c₂)))
           ≡⟨ refl ⟩ 
         scompcauchy
           (pcompcauchy (c2cauchy c₁) (c2cauchy c₂))
           (subst Cauchy (cong₂ _+_ (size≡! c₁) (size≡! c₂))
             (pcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂))))
           ≡⟨ cong 
                (scompcauchy (pcompcauchy (c2cauchy c₁) (c2cauchy c₂)))
                (subst₂+ 
                  (size≡! c₁) (size≡! c₂) 
                  (c2cauchy (! c₁)) (c2cauchy (! c₂))
                  pcompcauchy) ⟩
         scompcauchy
           (pcompcauchy (c2cauchy c₁) (c2cauchy c₂))
           (pcompcauchy 
             (subst Cauchy (size≡! c₁) (c2cauchy (! c₁)))
             (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
           ≡⟨ pcomp-dist 
               (c2cauchy c₁) 
               (subst Cauchy (size≡! c₁) (c2cauchy (! c₁)))
               (c2cauchy c₂) (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))) ⟩
         pcompcauchy 
           (scompcauchy 
             (c2cauchy c₁) 
             (subst Cauchy (size≡! c₁) (c2cauchy (! c₁))))
           (scompcauchy 
             (c2cauchy c₂) 
             (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
           ≡⟨ cong₂ pcompcauchy (linv∼ {t₁} {t₃} {c₁}) (linv∼ {t₂} {t₄} {c₂}) ⟩
         pcompcauchy (c2cauchy {t₁} id⟷) (c2cauchy {t₂} id⟷)
           ≡⟨ pcomp-id {size t₁} {size t₂} ⟩ 
         c2cauchy {PLUS t₁ t₂} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES t₁ t₂} {TIMES t₃ t₄} {c₁ ⊗ c₂} = 
  begin (c2cauchy {TIMES t₁ t₂} ((c₁ ⊗ c₂) ◎ ((! c₁) ⊗ (! c₂)))
           ≡⟨ refl ⟩ 
         scompcauchy
           (tcompcauchy (c2cauchy c₁) (c2cauchy c₂))
           (subst Cauchy (cong₂ _*_ (size≡! c₁) (size≡! c₂))
             (tcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂))))
           ≡⟨ cong 
                (scompcauchy (tcompcauchy (c2cauchy c₁) (c2cauchy c₂)))
                (subst₂*
                  (size≡! c₁) (size≡! c₂)
                  (c2cauchy (! c₁)) (c2cauchy (! c₂))
                  tcompcauchy) ⟩ 
         scompcauchy 
           (tcompcauchy (c2cauchy c₁) (c2cauchy c₂))
           (tcompcauchy
             (subst Cauchy (size≡! c₁) (c2cauchy (! c₁)))
             (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
           ≡⟨ tcomp-dist
                (c2cauchy c₁)
                (subst Cauchy (size≡! c₁) (c2cauchy (! c₁))) 
                (c2cauchy c₂)
                (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))) ⟩
         tcompcauchy
           (scompcauchy 
             (c2cauchy c₁)
             (subst Cauchy (size≡! c₁) (c2cauchy (! c₁))))
           (scompcauchy 
             (c2cauchy c₂)
             (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
           ≡⟨ cong₂ tcompcauchy (linv∼ {t₁} {t₃} {c₁}) (linv∼ {t₂} {t₄} {c₂}) ⟩ 
         tcompcauchy (c2cauchy {t₁} id⟷) (c2cauchy {t₂} id⟷)
            ≡⟨ tcomp-id {size t₁} {size t₂} ⟩
         c2cauchy {TIMES t₁ t₂} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS ONE ONE} {BOOL} {foldBool} = 
  begin (c2cauchy {PLUS ONE ONE} (foldBool ◎ unfoldBool)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy 2) (idcauchy 2)
           ≡⟨ scomplid (idcauchy 2) ⟩ 
         c2cauchy {PLUS ONE ONE} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {BOOL} {PLUS ONE ONE} {unfoldBool} = 
  begin (c2cauchy {BOOL} (unfoldBool ◎ foldBool)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy 2) (idcauchy 2)
           ≡⟨ scomplid (idcauchy 2) ⟩ 
         c2cauchy {BOOL} id⟷ ∎)
  where open ≡-Reasoning

rinv∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! c ◎ c ∼ id⟷
rinv∼ {PLUS ZERO t} {.t} {unite₊} = 
  begin (c2cauchy {t} (uniti₊ ◎ unite₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {t} {PLUS ZERO .t} {uniti₊} = 
  begin (c2cauchy {PLUS ZERO t} (unite₊ ◎ uniti₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {PLUS ZERO t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS t₁ t₂} {PLUS .t₂ .t₁} {swap₊} =
  begin (c2cauchy {PLUS t₂ t₁} (swap₊ ◎ swap₊)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (swap+cauchy (size t₂) (size t₁))
           (subst Cauchy (+-comm (size t₁) (size t₂)) 
             (swap+cauchy (size t₁) (size t₂)))
           ≡⟨ swap+idemp (size t₂) (size t₁) ⟩ 
         c2cauchy {PLUS t₂ t₁} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} {assocl₊} = 
  begin (c2cauchy {PLUS (PLUS t₁ t₂) t₃} (assocr₊ ◎ assocl₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃))
           (subst Cauchy (sym (+-assoc (size t₁) (size t₂) (size t₃)))
             (idcauchy (size t₁ + (size t₂ + size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃)))
                (congD! idcauchy (sym (+-assoc (size t₁) (size t₂) (size t₃)))) ⟩
         scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃))
           (idcauchy ((size t₁ + size t₂) + size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ + size t₂) + size t₃)) ⟩ 
         c2cauchy {PLUS (PLUS t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} {assocr₊} = 
  begin (c2cauchy {PLUS t₁ (PLUS t₂ t₃)} (assocl₊ ◎ assocr₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃)))
           (subst Cauchy (+-assoc (size t₁) (size t₂) (size t₃))
             (idcauchy ((size t₁ + size t₂) + size t₃)))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃))))
                (congD! idcauchy (+-assoc (size t₁) (size t₂) (size t₃))) ⟩ 
         scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃)))
           (idcauchy (size t₁ + (size t₂ + size t₃)))
           ≡⟨ scomplid (idcauchy (size t₁ + (size t₂ + size t₃))) ⟩ 
         c2cauchy {PLUS t₁ (PLUS t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES ONE t} {.t} {unite⋆} = 
  begin (c2cauchy {t} (uniti⋆ ◎ unite⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy (+-right-identity (size t))
             (subst Cauchy (sym (+-right-identity (size t))) 
               (idcauchy (size t))))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t)))
                (subst-trans 
                  (+-right-identity (size t))
                  (sym (+-right-identity (size t))) 
                  (idcauchy (size t))) ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy (trans (sym (+-right-identity (size t)))
                                (+-right-identity (size t)))
               (idcauchy (size t)))
           ≡⟨ cong 
                 (λ x → scompcauchy 
                          (idcauchy (size t))
                          (subst Cauchy x (idcauchy (size t))))
                 (trans-syml (+-right-identity (size t))) ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy refl (idcauchy (size t)))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {t} {TIMES ONE .t} {uniti⋆} = 
  begin (c2cauchy {TIMES ONE t} (unite⋆ ◎ uniti⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t)))
           (subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t)))
           ≡⟨ cong  
                (λ x → scompcauchy x x) 
                (congD! idcauchy (sym (+-right-identity (size t)))) ⟩ 
         scompcauchy (idcauchy (size t + 0)) (idcauchy (size t + 0))
           ≡⟨ scomplid (idcauchy (size t + 0)) ⟩ 
         c2cauchy {TIMES ONE t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES t₁ t₂} {TIMES .t₂ .t₁} {swap⋆} =
  begin (c2cauchy {TIMES t₂ t₁} (swap⋆ ◎ swap⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (swap⋆cauchy (size t₂) (size t₁))
           (subst Cauchy (*-comm (size t₁) (size t₂)) 
             (swap⋆cauchy (size t₁) (size t₂)))
           ≡⟨ swap⋆idemp (size t₂) (size t₁) ⟩
         c2cauchy {TIMES t₂ t₁} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} {assocl⋆} = 
  begin (c2cauchy {TIMES (TIMES t₁ t₂) t₃} (assocr⋆ ◎ assocl⋆)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃))
           (subst Cauchy (sym (*-assoc (size t₁) (size t₂) (size t₃)))
             (idcauchy (size t₁ * (size t₂ * size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃)))
                (congD! idcauchy (sym (*-assoc (size t₁) (size t₂) (size t₃)))) ⟩
         scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃))
           (idcauchy ((size t₁ * size t₂) * size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ * size t₂) * size t₃)) ⟩ 
         c2cauchy {TIMES (TIMES t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES (TIMES t₁ t₂) t₃} {TIMES .t₁ (TIMES .t₂ .t₃)} {assocr⋆} = 
  begin (c2cauchy {TIMES t₁ (TIMES t₂ t₃)} (assocl⋆ ◎ assocr⋆)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃)))
           (subst Cauchy (*-assoc (size t₁) (size t₂) (size t₃))
             (idcauchy ((size t₁ * size t₂) * size t₃)))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃))))
                (congD! idcauchy (*-assoc (size t₁) (size t₂) (size t₃))) ⟩ 
         scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃)))
           (idcauchy (size t₁ * (size t₂ * size t₃)))
           ≡⟨ scomplid (idcauchy (size t₁ * (size t₂ * size t₃))) ⟩ 
         c2cauchy {TIMES t₁ (TIMES t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES ZERO t} {ZERO} {distz} = refl
rinv∼ {ZERO} {TIMES ZERO t} {factorz} = refl
rinv∼ {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} {dist} = 
  begin (c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)} (factor ◎ dist)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           (subst Cauchy (distribʳ-*-+ (size t₃) (size t₁) (size t₂))
             (idcauchy ((size t₁ + size t₂) * size t₃)))
           ≡⟨ cong 
                (scompcauchy 
                  (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))))
                (congD! idcauchy 
                  (distribʳ-*-+ (size t₃) (size t₁) (size t₂))) ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           ≡⟨ scomplid (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))) ⟩ 
         c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} {TIMES (PLUS .t₁ .t₂) .t₃} {factor} = 
  begin (c2cauchy {TIMES (PLUS t₁ t₂) t₃} (dist ◎ factor)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃))
           (subst Cauchy (sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂)))
             (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃)))
                (congD! idcauchy 
                  (sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂)))) ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃))
           (idcauchy ((size t₁ + size t₂) * size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ + size t₂) * size t₃)) ⟩ 
         c2cauchy {TIMES (PLUS t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {t} {.t} {id⟷} = 
  begin (c2cauchy {t} (id⟷ ◎ id⟷)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {t₁} {t₃} {_◎_ {t₂ = t₂} c₁ c₂} = 
  begin (c2cauchy {t₃} (((! c₂) ◎ (! c₁)) ◎ (c₁ ◎ c₂))
           ≡⟨ refl ⟩ 
         scompcauchy
           (scompcauchy
              (c2cauchy (! c₂))
              (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))
           (subst Cauchy (trans (size≡! (! c₁)) (size≡! (! c₂)))
             (scompcauchy
               (c2cauchy c₁)
               (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))
           ≡⟨ sym (scompassoc
                     (c2cauchy (! c₂))
                     (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))
                     (subst Cauchy (trans (size≡! (! c₁)) (size≡! (! c₂)))
                       (scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (scompcauchy
              (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))
              (subst Cauchy (trans (size≡! (! c₁)) (size≡! (! c₂)))
                (scompcauchy
                  (c2cauchy c₁)
                  (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (scompcauchy
                           (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))
                           x))
                (sym (subst-trans (size≡! (! c₂)) (size≡! (! c₁))
                       (scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (scompcauchy
              (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))
              (subst Cauchy (size≡! (! c₂))
                (subst Cauchy (size≡! (! c₁))
                  (scompcauchy
                    (c2cauchy c₁)
                    (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))))
           ≡⟨ cong
                (scompcauchy (c2cauchy (! c₂)))
                (sym (subst-dist scompcauchy (size≡! (! c₂))
                       (c2cauchy (! c₁))
                       (subst Cauchy (size≡! (! c₁))
                         (scompcauchy
                           (c2cauchy c₁)
                           (subst Cauchy (size≡! c₁) (c2cauchy c₂)))))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (scompcauchy
               (c2cauchy (! c₁))
               (subst Cauchy (size≡! (! c₁))
                 (scompcauchy
                   (c2cauchy c₁)
                   (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))))
           ≡⟨ cong 
                (λ x → scompcauchy 
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂))
                           (scompcauchy (c2cauchy (! c₁)) x)))
                (subst-dist scompcauchy (size≡! (! c₁))
                  (c2cauchy c₁)
                  (subst Cauchy (size≡! c₁) (c2cauchy  c₂))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (scompcauchy
               (c2cauchy (! c₁))
                 (scompcauchy
                   (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
                   (subst Cauchy (size≡! (! c₁))
                     (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))))
           ≡⟨ cong
                (λ x → scompcauchy 
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂)) x))
                (scompassoc
                  (c2cauchy (! c₁))
                  (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
                  (subst Cauchy (size≡! (! c₁))
                    (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))) ⟩
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (scompcauchy
               (scompcauchy
                 (c2cauchy (! c₁))
                 (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁)))
               (subst Cauchy (size≡! (! c₁))
                 (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂))
                           (scompcauchy 
                             x
                             (subst Cauchy (size≡! (! c₁))
                               (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))))
                (rinv∼ {t₁} {t₂} {c₁}) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (scompcauchy
               (allFin (size t₂))
               (subst Cauchy (size≡! (! c₁))
                 (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂)) x))
                (scomplid
                  (subst Cauchy (size≡! (! c₁))
                    (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (subst Cauchy (size≡! (! c₁))
               (subst Cauchy (size≡! c₁) (c2cauchy c₂))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂)) x))
                (subst-trans (size≡! (! c₁)) (size≡! c₁) (c2cauchy c₂)) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (subst Cauchy (trans (size≡! c₁) (size≡! (! c₁))) 
               (c2cauchy c₂)))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂))
                           (subst Cauchy x (c2cauchy c₂))))
                (trans
                  (cong (λ y → trans (size≡! c₁) y) (size≡!! c₁))
                  (trans-symr (size≡! c₁))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂))
           ≡⟨ rinv∼ {t₂} {t₃} {c₂} ⟩ 
         c2cauchy {t₃} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS t₁ t₂} {PLUS t₃ t₄} {c₁ ⊕ c₂} =
  begin (c2cauchy {PLUS t₃ t₄} (((! c₁) ⊕ (! c₂)) ◎ (c₁ ⊕ c₂))
           ≡⟨ refl ⟩ 
         scompcauchy
           (pcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂)))
           (subst Cauchy (cong₂ _+_ (size≡! (! c₁)) (size≡! (! c₂)))
             (pcompcauchy (c2cauchy c₁) (c2cauchy c₂)))
           ≡⟨ cong 
                (scompcauchy (pcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂))))
                (subst₂+ 
                  (size≡! (! c₁)) (size≡! (! c₂))
                  (c2cauchy c₁) (c2cauchy c₂)
                  pcompcauchy) ⟩
         scompcauchy
           (pcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂)))
           (pcompcauchy 
             (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
             (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)))
           ≡⟨ pcomp-dist 
               (c2cauchy (! c₁))
               (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
               (c2cauchy (! c₂)) (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)) ⟩
         pcompcauchy 
           (scompcauchy 
             (c2cauchy (! c₁))
             (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁)))
           (scompcauchy 
             (c2cauchy (! c₂))
             (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)))
           ≡⟨ cong₂ pcompcauchy (rinv∼ {t₁} {t₃} {c₁}) (rinv∼ {t₂} {t₄} {c₂}) ⟩
         pcompcauchy (c2cauchy {t₃} id⟷) (c2cauchy {t₄} id⟷)
           ≡⟨ pcomp-id {size t₃} {size t₄} ⟩ 
         c2cauchy {PLUS t₃ t₄} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES t₁ t₂} {TIMES t₃ t₄} {c₁ ⊗ c₂} =
  begin (c2cauchy {TIMES t₃ t₄} (((! c₁) ⊗ (! c₂)) ◎ (c₁ ⊗ c₂))
           ≡⟨ refl ⟩ 
         scompcauchy
           (tcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂)))
           (subst Cauchy (cong₂ _*_ (size≡! (! c₁)) (size≡! (! c₂)))
             (tcompcauchy (c2cauchy c₁) (c2cauchy c₂)))
           ≡⟨ cong 
                (scompcauchy (tcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂))))
                (subst₂*
                  (size≡! (! c₁)) (size≡! (! c₂))
                  (c2cauchy c₁) (c2cauchy c₂)
                  tcompcauchy) ⟩ 
         scompcauchy 
           (tcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂)))
           (tcompcauchy
             (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
             (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)))
           ≡⟨ tcomp-dist
                (c2cauchy (! c₁))
                (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
                (c2cauchy (! c₂))
                (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)) ⟩
         tcompcauchy
           (scompcauchy 
             (c2cauchy (! c₁))
             (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁)))
           (scompcauchy 
             (c2cauchy (! c₂))
             (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)))
           ≡⟨ cong₂ tcompcauchy (rinv∼ {t₁} {t₃} {c₁}) (rinv∼ {t₂} {t₄} {c₂}) ⟩ 
         tcompcauchy (c2cauchy {t₃} id⟷) (c2cauchy {t₄} id⟷)
            ≡⟨ tcomp-id {size t₃} {size t₄} ⟩
         c2cauchy {TIMES t₃ t₄} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS ONE ONE} {BOOL} {foldBool} = 
  begin (c2cauchy {BOOL} (unfoldBool ◎ foldBool)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy 2) (idcauchy 2)
           ≡⟨ scomplid (idcauchy 2) ⟩ 
         c2cauchy {BOOL} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {BOOL} {PLUS ONE ONE} {unfoldBool} = 
  begin (c2cauchy {PLUS ONE ONE} (foldBool ◎ unfoldBool)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy 2) (idcauchy 2)
           ≡⟨ scomplid (idcauchy 2) ⟩ 
         c2cauchy {PLUS ONE ONE} id⟷ ∎)
  where open ≡-Reasoning

resp∼ : {t₁ t₂ t₃ : U} {c₁ c₂ : t₁ ⟷ t₂} {c₃ c₄ : t₂ ⟷ t₃} → 
        (c₁ ∼ c₂) → (c₃ ∼ c₄) → (c₁ ◎ c₃ ∼ c₂ ◎ c₄)
resp∼ {t₁} {t₂} {t₃} {c₁} {c₂} {c₃} {c₄} c₁∼c₂ c₃∼c₄ = 
  begin (c2cauchy (c₁ ◎ c₃)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (c2cauchy c₁)
           (subst Cauchy (size≡! c₁) (c2cauchy c₃))
           ≡⟨ cong₂ 
                (λ x y → scompcauchy x (subst Cauchy (size≡! c₁) y))
                c₁∼c₂ c₃∼c₄ ⟩ 
         scompcauchy 
           (c2cauchy c₂)
           (subst Cauchy (size≡! c₁) (c2cauchy c₄))
           ≡⟨ cong 
                (λ x → scompcauchy (c2cauchy c₂) (subst Cauchy x (c2cauchy c₄)))
                (size∼! c₁ c₂) ⟩ 
         scompcauchy 
           (c2cauchy c₂)
           (subst Cauchy (size≡! c₂) (c2cauchy c₄))
           ≡⟨ refl ⟩ 
         c2cauchy (c₂ ◎ c₄) ∎)
  where open ≡-Reasoning

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
        ; ∘-resp-≈ = λ {t₁} {t₂} {t₃} {p} {q} {r} {s} p∼q r∼s → 
                    resp∼ {t₁} {t₂} {t₃} {r} {s} {p} {q} r∼s p∼q 
        }

-- There are additional laws that should hold:
-- 
-- assoc⊕∼ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
--           {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
--           c₁ ⊕ (c₂ ⊕ c₃) ∼ assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊
-- 
-- assoc⊗∼ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
--           {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
--           c₁ ⊗ (c₂ ⊗ c₃) ∼ assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆
-- 
-- but we will turn our attention to completeness below (in Pif2) in a more
-- systematic way.

------------------------------------------------------------------------------
