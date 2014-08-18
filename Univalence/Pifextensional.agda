{-# OPTIONS --without-K #-}

module Pifextensional where

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

open import Groupoid

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
-- Extensional view of 2paths.
-- 
-- There is a 2path between two permutations p and q if for each x, the
-- result of p(x) and q(x) are identical. 

-- First we define the extensional view of a permutation as a function.

ap : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
ap unite₊ (inj₁ ())         -- absurd
ap unite₊ (inj₂ v)          = v
ap uniti₊ v                 = inj₂ v
ap swap₊ (inj₁ v)           = inj₂ v
ap swap₊ (inj₂ v)           = inj₁ v
ap assocl₊ (inj₁ v)         = inj₁ (inj₁ v)
ap assocl₊ (inj₂ (inj₁ v))  = inj₁ (inj₂ v) 
ap assocl₊ (inj₂ (inj₂ v))  = inj₂ v
ap assocr₊ (inj₁ (inj₁ v))  = inj₁ v
ap assocr₊ (inj₁ (inj₂ v))  = inj₂ (inj₁ v)
ap assocr₊ (inj₂ v)         = inj₂ (inj₂ v)
ap unite⋆ (tt , v)          = v
ap uniti⋆ v                 = (tt , v)
ap swap⋆ (v₁ , v₂)          = (v₂ , v₁)
ap assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
ap assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
ap distz (() , _)           -- absurd
ap factorz ()               -- absurd
ap dist (inj₁ v₁ , v₃)      = inj₁ (v₁ , v₃)
ap dist (inj₂ v₂ , v₃)      = inj₂ (v₂ , v₃)
ap factor (inj₁ (v₁ , v₃))  = (inj₁ v₁ , v₃)
ap factor (inj₂ (v₂ , v₃))  = (inj₂ v₂ , v₃)
ap id⟷ v                   = v
ap (c₁ ◎ c₂) v              = ap c₂ (ap c₁ v)
ap (c₁ ⊕ c₂) (inj₁ v)       = inj₁ (ap c₁ v)
ap (c₁ ⊕ c₂) (inj₂ v)       = inj₂ (ap c₂ v)
ap (c₁ ⊗ c₂) (v₁ , v₂)      = (ap c₁ v₁ , ap c₂ v₂)

α◎!α : {t₁ t₂ : U} {α : t₁ ⟷ t₂} {v : ⟦ t₁ ⟧} → ap (α ◎ ! α) v ≡ v
α◎!α {α = unite₊} {inj₁ ()}
α◎!α {α = unite₊} {inj₂ v} = refl
α◎!α {α = uniti₊} {v} = refl
α◎!α {α = swap₊} {inj₁ v} = refl
α◎!α {α = swap₊} {inj₂ v} = refl
α◎!α {α = assocl₊} {inj₁ v} = refl
α◎!α {α = assocl₊} {inj₂ (inj₁ v)} = refl
α◎!α {α = assocl₊} {inj₂ (inj₂ v)} = refl
α◎!α {α = assocr₊} {inj₁ (inj₁ v)} = refl
α◎!α {α = assocr₊} {inj₁ (inj₂ v)} = refl
α◎!α {α = assocr₊} {inj₂ v} = refl
α◎!α {α = unite⋆} {v} = refl
α◎!α {α = uniti⋆} {v} = refl
α◎!α {α = swap⋆} {v} = refl
α◎!α {α = assocl⋆} {v} = refl
α◎!α {α = assocr⋆} {v} = refl
α◎!α {α = distz} {(() , _)}
α◎!α {α = factorz} {()}
α◎!α {α = dist} {(inj₁ v₁ , v₂)} = refl
α◎!α {α = dist} {(inj₂ v₁ , v₂)} = refl
α◎!α {α = factor} {inj₁ v} = refl
α◎!α {α = factor} {inj₂ v} = refl
α◎!α {α = id⟷} {v} = refl
α◎!α {α = α₁ ◎ α₂} {v} = 
  begin 
    ap ((α₁ ◎ α₂) ◎ ! (α₁ ◎ α₂)) v
      ≡⟨ refl ⟩
    ap (! α₁) (ap (α₂ ◎ ! α₂) (ap α₁ v))
      ≡⟨ cong (λ v' → ap (! α₁) v') (α◎!α {α = α₂} {v = ap α₁ v}) ⟩ 
    ap (! α₁) (ap α₁ v)
      ≡⟨ α◎!α {α = α₁} {v = v} ⟩
    v ∎
α◎!α {α = α₁ ⊕ α₂} {inj₁ v} = 
  begin 
    ap ((α₁ ⊕ α₂) ◎ ! (α₁ ⊕ α₂)) (inj₁ v)
      ≡⟨ refl ⟩
    inj₁ (ap (! α₁) (ap α₁ v))
      ≡⟨ cong inj₁ (α◎!α {α = α₁} {v}) ⟩
    inj₁ v ∎
α◎!α {α = α₁ ⊕ α₂} {inj₂ v} = 
  begin 
    ap ((α₁ ⊕ α₂) ◎ ! (α₁ ⊕ α₂)) (inj₂ v)
      ≡⟨ refl ⟩
    inj₂ (ap (! α₂) (ap α₂ v))
      ≡⟨ cong inj₂ (α◎!α {α = α₂} {v}) ⟩
    inj₂ v ∎
α◎!α {α = α₁ ⊗ α₂} {(v₁ , v₂)} = 
  begin 
    ap ((α₁ ⊗ α₂) ◎ ! (α₁ ⊗ α₂)) (v₁ , v₂) 
      ≡⟨ refl ⟩
    (ap (! α₁) (ap α₁ v₁) , ap (! α₂) (ap α₂ v₂))
      ≡⟨ cong₂ (_,_) (α◎!α {α = α₁} {v = v₁}) (α◎!α {α = α₂} {v = v₂}) ⟩
    (v₁ , v₂) ∎

!α◎α : {t₁ t₂ : U} {α : t₁ ⟷ t₂} {v : ⟦ t₂ ⟧} → ap (! α ◎ α) v ≡ v
!α◎α {α = unite₊} {v} = refl
!α◎α {α = uniti₊} {inj₁ ()} 
!α◎α {α = uniti₊} {inj₂ v} = refl
!α◎α {α = swap₊} {inj₁ v} = refl
!α◎α {α = swap₊} {inj₂ v} = refl
!α◎α {α = assocl₊} {inj₁ (inj₁ v)} = refl
!α◎α {α = assocl₊} {inj₁ (inj₂ v)} = refl
!α◎α {α = assocl₊} {inj₂ v} = refl
!α◎α {α = assocr₊} {inj₁ v} = refl
!α◎α {α = assocr₊} {inj₂ (inj₁ v)} = refl
!α◎α {α = assocr₊} {inj₂ (inj₂ v)} = refl
!α◎α {α = unite⋆} {v} = refl
!α◎α {α = uniti⋆} {v} = refl
!α◎α {α = swap⋆} {v} = refl
!α◎α {α = assocl⋆} {v} = refl
!α◎α {α = assocr⋆} {v} = refl
!α◎α {α = distz} {()}
!α◎α {α = factorz} {(() , _)}
!α◎α {α = dist} {inj₁ v} = refl
!α◎α {α = dist} {inj₂ v} = refl
!α◎α {α = factor} {(inj₁ v₁ , v₂)} = refl
!α◎α {α = factor} {(inj₂ v₁ , v₂)} = refl
!α◎α {α = id⟷} {v} = refl
!α◎α {α = α₁ ◎ α₂} {v} = 
  begin 
    ap (! (α₁ ◎ α₂) ◎ (α₁ ◎ α₂)) v
      ≡⟨ refl ⟩
    ap α₂ (ap (! α₁ ◎ α₁) (ap (! α₂) v))
      ≡⟨ cong (λ v' → ap α₂ v') (!α◎α {α = α₁} {v = ap (! α₂) v}) ⟩ 
    ap α₂ (ap (! α₂) v)
      ≡⟨ !α◎α {α = α₂} {v = v} ⟩
    v ∎
!α◎α {α = α₁ ⊕ α₂} {inj₁ v} = 
  begin 
    ap (! (α₁ ⊕ α₂) ◎ (α₁ ⊕ α₂)) (inj₁ v)
      ≡⟨ refl ⟩
    inj₁ (ap α₁ (ap (! α₁) v))
      ≡⟨ cong inj₁ (!α◎α {α = α₁} {v}) ⟩
    inj₁ v ∎
!α◎α {α = α₁ ⊕ α₂} {inj₂ v} = 
  begin 
    ap (! (α₁ ⊕ α₂) ◎ (α₁ ⊕ α₂)) (inj₂ v)
      ≡⟨ refl ⟩
    inj₂ (ap α₂ (ap (! α₂) v))
      ≡⟨ cong inj₂ (!α◎α {α = α₂} {v}) ⟩
    inj₂ v ∎
!α◎α {α = α₁ ⊗ α₂} {(v₁ , v₂)} = 
  begin 
    ap (! (α₁ ⊗ α₂) ◎ (α₁ ⊗ α₂)) (v₁ , v₂) 
      ≡⟨ refl ⟩
    (ap α₁ (ap (! α₁) v₁) , ap α₂ (ap (! α₂) v₂))
      ≡⟨ cong₂ (_,_) (!α◎α {α = α₁} {v = v₁}) (!α◎α {α = α₂} {v = v₂}) ⟩
    (v₁ , v₂) ∎

-- Two permutations, viewed extensionally, are equivalent if they map
-- each value x to the same value. Generally we would only require
-- that the resulting values y and z have a path between them, but
-- because the internals of each type are discrete groupoids, this
-- reduces to saying that y and z are identical.

infix  10  _∼_  

_∼_ : ∀ {t₁ t₂} → (p q : t₁ ⟷ t₂) → Set
_∼_ {t₁} {t₂} p q = (x : ⟦ t₁ ⟧) → ap p x ≡ ap q x

α◎!α∼id⟷ : {t₁ t₂ : U} {α : t₁ ⟷ t₂} → α ◎ ! α ∼ id⟷ 
α◎!α∼id⟷ {α = α} v = α◎!α {α = α} {v}

!α◎α∼id⟷ : {t₁ t₂ : U} {α : t₁ ⟷ t₂} → ! α ◎ α ∼ id⟷ 
!α◎α∼id⟷ {t₁} {t₂} {α} v = !α◎α {α = α} {v}

resp◎ : {t₁ t₂ t₃ : U} {p q : t₁ ⟷ t₂} {r s : t₂ ⟷ t₃} → 
        (α : p ∼ q) → (β : r ∼ s) → (p ◎ r) ∼ (q ◎ s)
resp◎ {t₁} {t₂} {t₃} {p} {q} {r} {s} α β v = 
  begin 
    ap (p ◎ r) v 
      ≡⟨ refl ⟩
    ap r (ap p v)
      ≡⟨ cong (λ v → ap r v) (α v) ⟩ 
    ap r (ap q v)
      ≡⟨ β (ap q v) ⟩ 
    ap (q ◎ s) v ∎

-- Because we representing combinators semantically as functions (not as
-- permutations), we have to use function extensionality to compare the
-- semantic representation. This need to be changed by making use of a proper
-- representation of permutations instead of plain functions.

postulate
  funExtP : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → (f ≡ g)

-- Two extensionally equivalent combinators are semantically
-- equivalent. Again, if we had a proper representation of permutations, this
-- would reduce to comparing the two representations without involving
-- function extensionality.

ext2id : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → ap c₁ ≡ ap c₂
ext2id {t₁} {t₂} {c₁} {c₂} c₁∼c₂ = 
  funExtP {⟦ t₁ ⟧} {⟦ t₂ ⟧} {ap c₁} {ap c₂} c₁∼c₂
  
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
        ; lneutr = λ _ _ → refl
        ; rneutr = λ _ _ → refl
        ; assoc  = λ _ _ _ _ → refl 
        ; equiv = record { 
            refl  = λ _ → refl
          ; sym   = λ α x → sym (α x)
          ; trans = λ α β x → trans (α x) (β x)
          }
        ; linv = λ {t₁} {t₂} α → α◎!α∼id⟷ {t₁} {t₂} {α}
        ; rinv = λ {t₁} {t₂} α → !α◎α∼id⟷ {t₁} {t₂} {α}
        ; ∘-resp-≈ = λ {t₁} {t₂} {t₃} {p} {q} {r} {s} p∼q r∼s → 
                    resp◎ {t₁} {t₂} {t₃} {r} {s} {p} {q} r∼s p∼q 
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
-- Soundness and completeness
-- 
-- Proof of soundness and completeness: now we want to verify that ⇔
-- is sound and complete with respect to ∼. The statement to prove is
-- that for all c₁ and c₂, we have c₁ ∼ c₂ iff c₁ ⇔ c₂

postulate -- to do eventually but should be fairly easy
  soundnessP : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₁ ∼ c₂)

-- postulate -- proved below
--  completenessP : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₁ ⇔ c₂)

-- The idea is to invert evaluation and use that to extract from each
-- extensional representation of a combinator, a canonical syntactic
-- representative

postulate
  invertP : {t₁ t₂ : U} → (⟦ t₁ ⟧ → ⟦ t₂ ⟧) → (t₁ ⟷ t₂)

canonical : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂)
canonical c = invertP (ap c)

-- Note that if c₁ ⇔ c₂, then by soundness c₁ ∼ c₂ and hence their
-- canonical representatives are identical. 

canonicalWellDefined : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → 
  (c₁ ⇔ c₂) → (canonical c₁ ≡ canonical c₂)
canonicalWellDefined {t₁} {t₂} {c₁} {c₂} α = 
  cong invertP (ext2id {t₁} {t₂} {c₁} {c₂} (soundnessP α))

-- If we can prove that every combinator is equal to its normal form
-- then we can prove completeness.

postulate 
  inversionP : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ canonical c

resp≡⇔ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ≡ c₂) → (c₁ ⇔ c₂)
resp≡⇔ {t₁} {t₂} {c₁} {c₂} p rewrite p = id⇔ 

completeness : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₁ ⇔ c₂)
completeness {t₁} {t₂} {c₁} {c₂} c₁∼c₂ = 
  c₁
    ⇔⟨ inversionP ⟩
  canonical c₁
    ⇔⟨  resp≡⇔ (cong invertP (ext2id {t₁} {t₂} {c₁} {c₂} c₁∼c₂)) ⟩
  canonical c₂
    ⇔⟨ 2! inversionP ⟩
  c₂ ▤

-- To summarize, completeness can be proved if we can define the following
-- two functions:
-- 
-- * a function that extracts a canonical combinator out of the 
--   semantic representation of a permutation:
--     invertP : {t₁ t₂ : U} → (⟦ t₁ ⟧ → ⟦ t₂ ⟧) → (t₁ ⟷ t₂)
-- * a function that proves that every combinator can be rewritten to this
--   canonical form:
--    inversionP : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ canonical c
--
-- This all uses function extensionality. It is possible to get rid of 
-- that if we use an accurate representation of permutations.

------------------------------------------------------------------------------
