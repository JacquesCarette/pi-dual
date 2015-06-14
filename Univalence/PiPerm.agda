{-# OPTIONS --without-K #-}

module PiPerm where


open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open ≡-Reasoning

open import ConcretePermutation
open import PiLevel0
open import Groupoid

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes a permutation.

c2perm : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → CPerm (size t₂) (size t₁)
-- the cases that do not inspect t₁ and t₂ should be at the beginning
-- so that Agda would unfold them
c2perm (c₁ ◎ c₂) = transp (c2perm c₁) (c2perm c₂)
c2perm (c₁ ⊕ c₂) = (c2perm c₁) ⊎p (c2perm c₂)
c2perm (c₁ ⊗ c₂) = (c2perm c₁) ×p (c2perm c₂)
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
c2perm absorbr = 0p
c2perm {TIMES t₁ ZERO} absorbl = 0pr {size t₁}
c2perm {ZERO} {TIMES t₁ ZERO} factorzr = 0pl {size t₁}
c2perm factorzl = 0p
c2perm {TIMES (PLUS t₁ t₂) t₃} dist = distp {size t₁} {size t₂} {size t₃}
c2perm {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} factor = factorp {size t₁} {size t₂} {size t₃}
c2perm {TIMES t₁ (PLUS t₂ t₃)} distl = distlp {size t₁} {size t₂} {size t₃}
c2perm {PLUS (TIMES t₁ t₂) (TIMES .t₁ t₃)} factorl = factorlp {size t₁} {size t₂} {size t₃}
c2perm id⟷ = idp

-- Looking forward to Sec. 2.2 (Functions are functors). The
-- corresponding statement to Lemma 2.2.1 in our setting would be the
-- following. Given any *size preserving* function f : U → U, it is
-- the case that a combinator (path) c : t₁ ⟷ t₂ maps to a combinator
-- (path) ap_f(c) : f(t₁) ⟷ f(t₂).

-- the action of ! wrt c2perm.  This is not trivial!  
-- it needs p≡ for most of the cases, but then relies on non-trivial lemmas for 
-- the last 3 cases
!≡symp : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → c2perm (! c) ≡ symp (c2perm c)
!≡symp unite₊ = p≡ refl
!≡symp uniti₊ = p≡ refl
!≡symp swap₊ = p≡ refl
!≡symp assocl₊ = p≡ refl
!≡symp assocr₊ = p≡ refl
!≡symp unite⋆ = p≡ refl
!≡symp uniti⋆ = p≡ refl
!≡symp swap⋆ = p≡ refl
!≡symp assocl⋆ = p≡ refl
!≡symp assocr⋆ = p≡ refl
!≡symp absorbr = p≡ refl
!≡symp absorbl = p≡ refl
!≡symp factorzr = p≡ refl
!≡symp factorzl = p≡ refl
!≡symp dist = p≡ refl
!≡symp factor = p≡ refl
!≡symp distl = p≡ refl
!≡symp factorl = p≡ refl
!≡symp id⟷ = p≡ refl
!≡symp (c ◎ c₁) = p≡ (cong₂ (λ x y → CPerm.π (transp x y)) (!≡symp c₁) (!≡symp c))
!≡symp (c ⊕ c₁) = p≡ (cong₂ (λ x y → CPerm.π (x ⊎p y)) (!≡symp c) (!≡symp c₁))
!≡symp (c ⊗ c₁) = p≡ (cong₂ (λ x y → CPerm.π (x ×p y)) (!≡symp c) (!≡symp c₁))

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
assoc∼ {c₁ = c₁} {c₂} {c₃} = assocp {p₁ = c2perm c₁} {c2perm c₂} {c2perm c₃}

-- The combinators c : t₁ ⟷ t₂ are paths; we can transport
-- size-preserving properties across c. In particular, for some
-- appropriate P we want P(t₁) to map to P(t₂) via c.

-- The relation ~ validates the groupoid laws

c◎id∼c : {t₁ t₂ : U} (c : t₁ ⟷ t₂) → c ◎ id⟷ ∼ c
c◎id∼c c = ridp

id◎c∼c : {t₁ t₂ : U} (c : t₁ ⟷ t₂) → id⟷ ◎ c ∼ c
id◎c∼c c = lidp

linv∼ : {t₁ t₂ : U} (c : t₁ ⟷ t₂) → c ◎ ! c ∼ id⟷ {t₁}
linv∼ c =
  let p = c2perm c in
  trans (cong (transp p) (!≡symp c)) (linv p)

rinv∼ : {t₁ t₂ : U} (c : t₁ ⟷ t₂) → ! c ◎ c ∼ id⟷
rinv∼ c = 
  let p = c2perm c in
  trans (cong (λ x → transp x p) (!≡symp c)) (rinv p)

resp∼ : {t₁ t₂ t₃ : U} {c₁ c₂ : t₁ ⟷ t₂} {c₃ c₄ : t₂ ⟷ t₃} → 
        (c₁ ∼ c₂) → (c₃ ∼ c₄) → (c₁ ◎ c₃ ∼ c₂ ◎ c₄)
resp∼ c₁∼c₂ c₃∼c₄ = cong₂ transp c₁∼c₂ c₃∼c₄

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
        ; lneutr = c◎id∼c
        ; rneutr = id◎c∼c
        ; assoc  = λ c₃ c₂ c₁ → assoc∼ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}  
        ; equiv = record { 
            refl  = λ {c} → refl∼ {c = c}
          ; sym   = λ {c₁} {c₂} → sym∼ {c₁ = c₁} {c₂ = c₂}
          ; trans = λ {c₁} {c₂} {c₃} → trans∼ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} 
          }
        ; linv = linv∼
        ; rinv = rinv∼
        ; ∘-resp-≈ = λ {_} {_} {_} {p} {q} {r} {s} p∼q r∼s → 
                    resp∼ {c₁ = r} {s} {p} {q} r∼s p∼q 
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

