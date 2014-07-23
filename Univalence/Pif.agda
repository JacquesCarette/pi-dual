{-# OPTIONS --without-K #-}

module Pif where

open import Data.Bool
open import Relation.Nullary.Core using (yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

-- infix  4  _∼_  
-- infix  4  _≃_  
infixr 10 _◎_
infix 30 _⟷_

------------------------------------------------------------------------------
-- Level 0: 

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
⟦ ZERO ⟧ = ⊥ 
⟦ ONE ⟧ = ⊤
⟦ PLUS t₁ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

BOOL BOOL² : U
BOOL = PLUS ONE ONE 
BOOL² = TIMES BOOL BOOL

false⟷ true⟷ : ⟦ BOOL ⟧
false⟷ = inj₁ tt
true⟷ = inj₂ tt

-- For any finite type (t : U) there is no non-trivial path structure between
-- the elements of t. All such finite types are discrete groupoids
--
-- For U, there are non-trivial paths between its points. In the conventional
-- HoTT presentation, a path between t₁ and t₂ is postulated by univalence
-- for each equivalence between t₁ and t₂. In the context of finite types, an
-- equivalence is generated by a permutation as each permutation has a unique
-- inverse permutation. Instead of the detour using univalence, we can
-- instead give an inductive definition of all possible permutations between
-- finite types and identify all syntactic definitions that denote the same
-- permutation. A complete set of generators for all possible permutations
-- between finite types is given by the following definition:

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

-- Every permutation has an inverse

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊ = uniti₊
! uniti₊ = unite₊
! swap₊ = swap₊
! assocl₊ = assocr₊
! assocr₊ = assocl₊
! unite⋆ = uniti⋆
! uniti⋆ = unite⋆
! swap⋆ = swap⋆
! assocl⋆ = assocr⋆
! assocr⋆ = assocl⋆
! distz = factorz
! factorz = distz
! dist = factor 
! factor = dist
! id⟷ = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁ 
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)

-- Canonical form of permutations. This is used to decide whether two paths
-- of type t₁ ⟷ t₂ are related by ∼; the answer is yes if they denote the
-- same canonical permutation.

module Phase₀ where

  -- no occurrences of (TIMES (TIMES t₁ t₂) t₃)

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
  phase₁ (TIMES (TIMES t₁ t₂) t₃) = ? 

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

{--

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


{--
should this be on the code as done now or on their interpreation
i.e. data _⟷_ : ⟦ U ⟧ → ⟦ U ⟧ → Set where

can add recursive types 
rec : U
⟦_⟧ takes an additional argument X that is passed around
⟦ rec ⟧ X = X
fixpoitn
data μ (t : U) : Set where
 ⟨_⟩ : ⟦ t ⟧ (μ t) → μ t
--}

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

--}

