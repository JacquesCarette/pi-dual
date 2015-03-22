{-# OPTIONS --without-K #-}

module PiPerm where


open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
{-
open import Data.Nat.Properties using (m≢1+m+n; i+j≡0⇒i≡0; i+j≡0⇒j≡0)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+)
open import Relation.Binary.Core using (Transitive)

open import Data.String using (String)
  renaming (_++_ to _++S_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; false; true; _∧_; _∨_)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  z≤n; s≤s; _≟_; _≤?_; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; _ℕ-_; _≺_;
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
-}

open ≡-Reasoning

open import CauchyEquiv using (module F)
open F using (_∘̂_)
open import ConcretePermutation
open import PiLevel0
open import Groupoid

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes a permutation.

c2perm : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → CPerm (size t₂) (size t₁)
-- the cases that do not inspect t₁ and t₂ should be at the beginning
-- so that Agda would unfold them
c2perm (_◎_ {t₁} {t₂} {t₃} c₁ c₂) = transp (c2perm c₁) (c2perm c₂)
c2perm (c₁ ⊕ c₂) = (c2perm c₁) ⊎p (c2perm c₂)
c2perm (c₁ ⊗ c₂) = {!!}
c2perm unite₊ = idp -- could use something more 'precise' ?
c2perm uniti₊ = idp -- ditto
c2perm {PLUS t₁ t₂} swap₊ = swap+p {size t₁} {size t₂}
c2perm {PLUS t₁ (PLUS t₂ t₃)} assocl₊ = assocl+p {size t₁} {size t₂} {size t₃}
c2perm {PLUS (PLUS t₁ t₂) t₃} assocr₊ = assocr+p {size t₁} {size t₂} {size t₃}
c2perm {TIMES ONE t₁} unite⋆ = unite*p {size t₁}
c2perm {t₁} uniti⋆ = uniti*p {size t₁}
c2perm {TIMES t₁ t₂} swap⋆ = swap*p {size t₁} {size t₂}
c2perm {TIMES t₁ (TIMES t₂ t₃)} assocl⋆ = assocl*p {size t₁}
c2perm {TIMES (TIMES t₁ t₂) t₃} assocr⋆ = assocr*p {size t₁}
c2perm distz = 0p
c2perm factorz = 0p
c2perm dist = {!!}
c2perm factor = {!!}
c2perm id⟷ = idp

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
c₁ ∼ c₂ = (c2perm c₁ ≡ c2perm c₂)

-- The relation ~ is an equivalence relation

refl∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ∼ c)
refl∼ = refl 

sym∼ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₁)
sym∼ = sym

trans∼ : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₃) → (c₁ ∼ c₃)
trans∼ = trans

assoc∼ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
         c₁ ◎ (c₂ ◎ c₃) ∼ (c₁ ◎ c₂) ◎ c₃
assoc∼ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃} = {!!}

-- The combinators c : t₁ ⟷ t₂ are paths; we can transport
-- size-preserving properties across c. In particular, for some
-- appropriate P we want P(t₁) to map to P(t₂) via c.

-- The relation ~ validates the groupoid laws

c◎id∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ id⟷ ∼ c
c◎id∼c {t₁} {t₂} {c} = 
  begin (
    c2perm (c ◎ id⟷)
      ≡⟨ refl ⟩
    transp (c2perm c) idp
      ≡⟨ {!!} ⟩
    c2perm c ∎)

id◎c∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ◎ c ∼ c
id◎c∼c {t₁} {t₂} {c} = {!!}

linv∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ ! c ∼ id⟷
linv∼ {t₁} {t₂} {c} = {!!}

rinv∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! c ◎ c ∼ id⟷
rinv∼ {t₁} {t₂} {c} = {!!}

resp∼ : {t₁ t₂ t₃ : U} {c₁ c₂ : t₁ ⟷ t₂} {c₃ c₄ : t₂ ⟷ t₃} → 
        (c₁ ∼ c₂) → (c₃ ∼ c₄) → (c₁ ◎ c₃ ∼ c₂ ◎ c₄)
resp∼ {t₁} {t₂} {t₃} {c₁} {c₂} {c₃} {c₄} c₁∼c₂ c₃∼c₄ = {!!}

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

