{-# OPTIONS --without-K #-}

module Pif where

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Fin renaming (_+_ to _F+_; suc to Fsuc)
  using (Fin; zero; raise; inject+; inject≤; toℕ; fromℕ≤)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≟_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple
open import Function using (_∘_)

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)

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

-- Extensional view of 2paths.
-- 
-- There is a 2path between two permutations p and q if for each x, the
-- result of p(x) and q(x) are identical. 

-- First we define the extensional view of a permutation as a function

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
-- Proof of soundness and completeness: now we want to verify that ⇔
-- is sound and complete with respect to ∼. The statement to prove is
-- that for all c₁ and c₂, we have c₁ ∼ c₂ iff c₁ ⇔ c₂

postulate 
  soundnessP : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₁ ∼ c₂)

-- postulate 
--  completenessP : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₁ ⇔ c₂)

-- The idea is to invert evaluation and use that to extract from each
-- extensional representation of a combinator, a canonical syntactic
-- representative

postulate
  invertP : {t₁ t₂ : U} → (⟦ t₁ ⟧ → ⟦ t₂ ⟧) → (t₁ ⟷ t₂)

canonical : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂)
canonical c = invertP (ap c)

-- If we call invert with two extensionally equivalent permutations,
-- we get back the same combinator.

postulate
  funExtP : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (ap c₁ ≡ ap c₂)

ext2syn : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → 
          (c₁ ∼ c₂) → canonical c₁ ≡ canonical c₂
ext2syn {t₁} {t₂} {c₁} {c₂} c₁∼c₂ = 
  cong invertP (funExtP {t₁} {t₂} {c₁} {c₂} c₁∼c₂)

-- Note that if c₁ ⇔ c₂, then by soundness c₁ ∼ c₂ and hence their
-- canonical representatives are identical. 

canonicalWellDefined : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → 
  (c₁ ⇔ c₂) → (canonical c₁ ≡ canonical c₂)
canonicalWellDefined {t₁} {t₂} {c₁} {c₂} α = 
  ext2syn {t₁} {t₂} {c₁} {c₂} (soundnessP α)

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
    ⇔⟨ id⇔  ⟩
  invertP (ap c₁)
    ⇔⟨  resp≡⇔ (ext2syn {t₁} {t₂} {c₁} {c₂} c₁∼c₂) ⟩
  invertP (ap c₂)
    ⇔⟨ id⇔ ⟩
  canonical c₂
    ⇔⟨ 2! inversionP ⟩
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

--}
