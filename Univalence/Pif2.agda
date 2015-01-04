{-# OPTIONS --without-K #-}

module Pif2 where

{-- 2 paths --} 

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid;
        inspect; Reveal_is_; [_]; proof-irrelevance; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Nullary.Core using (Dec; yes; no; ¬_)
open import Data.Nat.Properties
  using (m≢1+m+n; i+j≡0⇒i≡0; i+j≡0⇒j≡0; n≤m+n)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+)
open import Data.Nat.DivMod using (_mod_)
open import Relation.Binary using (Rel; Decidable; Setoid)
open import Relation.Binary.Core using (Transitive)

open import Data.String using (String)
  renaming (_++_ to _++S_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; false; true; T; _∧_; _∨_)
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
  using (List⁺; module List⁺; [_]; _∷⁺_; head; last; _⁺++_)
  renaming (toList to nonEmptyListtoList; _∷ʳ_ to _n∷ʳ_; tail to ntail)
open List⁺ public  
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
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Cauchy
open import Perm
open import Proofs
open import CauchyProofs
open import CauchyProofsT
open import CauchyProofsS
open import Groupoid
open import Pif
open import Swaps

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

negEx : uniti⋆ ◎ (swap⋆ ◎ ((swap₊ {ONE} {ONE} ⊗ id⟷) ◎ (swap⋆ ◎ unite⋆))) 
        ⇔ swap₊
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

-- The idea is to invert evaluation and use that to extract from each
-- extensional representation of a combinator, a canonical syntactic
-- representative

canonical : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂)
canonical c = perm2c (size≡ c , c2perm c)

-- Check canonical NOT = canonical NEG1 = canonical NEG2 = canonical NEG3
-- = canonical NEG4 = canonical NEG5

canonicalEx : Bool
canonicalEx =
  let x = canonical NOT in 
  comb= x (canonical NEG1) ∧
  comb= x (canonical NEG2) ∧
  comb= x (canonical NEG3) ∧
  comb= x (canonical NEG4) ∧
  comb= x (canonical NEG5)

-- Proof of soundness and completeness: now we want to verify that ⇔
-- is sound and complete with respect to ∼. The statement to prove is
-- that for all c₁ and c₂, we have c₁ ∼ c₂ iff c₁ ⇔ c₂

assoc⊕∼ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} →
  subst Cauchy (+-assoc (size t₁) (size t₃) (size t₅)) (c2cauchy ((c₁ ⊕ c₂) ⊕ c₃))
  ≡ c2cauchy (c₁ ⊕ (c₂ ⊕ c₃)) 
assoc⊕∼ {t₁} {t₂} {t₃} {t₄} {t₅} {t₆} {c₁} {c₂} {c₃} =
  begin (subst Cauchy (+-assoc (size t₁) (size t₃) (size t₅))
           (mapV
             (inject+ (size t₅))
             (mapV (inject+ (size t₃)) (c2cauchy c₁) ++V
              mapV (raise (size t₁)) (c2cauchy c₂))
            ++V mapV (raise (size t₁ + size t₃)) (c2cauchy c₃))
        ≡⟨ cong
             (λ x →
               subst Cauchy (+-assoc (size t₁) (size t₃) (size t₅))
                 (x ++V mapV (raise (size t₁ + size t₃)) (c2cauchy c₃)))
             (map-++-commute
               (inject+ (size t₅))
               (mapV (inject+ (size t₃)) (c2cauchy c₁))) ⟩
         subst Cauchy (+-assoc (size t₁) (size t₃) (size t₅))
           ((mapV (inject+ (size t₅)) (mapV (inject+ (size t₃)) (c2cauchy c₁)) ++V
             mapV (inject+ (size t₅)) (mapV (raise (size t₁)) (c2cauchy c₂)))
            ++V mapV (raise (size t₁ + size t₃)) (c2cauchy c₃))
        ≡⟨ cong
             (λ x →
               subst Cauchy (+-assoc (size t₁) (size t₃) (size t₅))
                 (x ++V mapV (raise (size t₁ + size t₃)) (c2cauchy c₃)))
             (cong₂ _++V_
               (sym (map-∘ (inject+ (size t₅)) (inject+ (size t₃)) (c2cauchy c₁)))
               (sym (map-∘ (inject+ (size t₅)) (raise (size t₁)) (c2cauchy c₂)))) ⟩ 
         subst Cauchy (+-assoc (size t₁) (size t₃) (size t₅))
           ((mapV (inject+ (size t₅) ∘ inject+ (size t₃)) (c2cauchy c₁) ++V
             mapV (inject+ (size t₅) ∘ raise (size t₁)) (c2cauchy c₂))
            ++V mapV (raise (size t₁ + size t₃)) (c2cauchy c₃))
        ≡⟨ {!!} ⟩
         mapV (inject+ (size t₃ + size t₅)) (c2cauchy c₁) ++V
         (mapV (raise (size t₁) ∘ inject+ (size t₅)) (c2cauchy c₂) ++V
          mapV (raise (size t₁) ∘ raise (size t₃)) (c2cauchy c₃))
        ≡⟨ cong
             (λ x → mapV (inject+ (size t₃ + size t₅)) (c2cauchy c₁) ++V x)
             (cong₂ _++V_ 
               (map-∘ (raise (size t₁)) (inject+ (size t₅)) (c2cauchy c₂))
               (map-∘ (raise (size t₁)) (raise (size t₃)) (c2cauchy c₃))) ⟩
         mapV (inject+ (size t₃ + size t₅)) (c2cauchy c₁) ++V
         (mapV (raise (size t₁)) (mapV (inject+ (size t₅)) (c2cauchy c₂)) ++V
          mapV (raise (size t₁)) (mapV (raise (size t₃)) (c2cauchy c₃)))
        ≡⟨ cong
             (λ x → mapV (inject+ (size t₃ + size t₅)) (c2cauchy c₁) ++V x)
             (sym (map-++-commute
                    (raise (size t₁))
                    (mapV (inject+ (size t₅)) (c2cauchy c₂)))) ⟩ 
         mapV (inject+ (size t₃ + size t₅)) (c2cauchy c₁) ++V
         (mapV (raise (size t₁))
           (mapV (inject+ (size t₅)) (c2cauchy c₂) ++V
            mapV (raise (size t₃)) (c2cauchy c₃)))
        ≡⟨ refl ⟩
         pcompcauchy (c2cauchy c₁) (pcompcauchy (c2cauchy c₂) (c2cauchy c₃)) ∎)
  where open ≡-Reasoning

soundness : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₁ ∼ c₂)
soundness (assoc◎l {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃}) =
  assoc∼ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃}
soundness (assoc◎r {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃}) =
  sym (assoc∼ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃})
soundness (assoc⊕l {t₁} {t₂} {t₃} {t₄} {t₅} {t₆} {c₁} {c₂} {c₃}) =
  begin (c2cauchy (c₁ ⊕ (c₂ ⊕ c₃))
       ≡⟨ sym (assoc⊕∼ {t₁} {t₂} {t₃} {t₄} {t₅} {t₆} {c₁} {c₂} {c₃}) ⟩ 
         subst Cauchy (+-assoc (size t₁) (size t₃) (size t₅)) 
           (c2cauchy {PLUS (PLUS t₁ t₃) t₅} {PLUS (PLUS t₂ t₄) t₆} ((c₁ ⊕ c₂) ⊕ c₃))
       ≡⟨ sym (scomprid _) ⟩
       scompcauchy
         (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
           (c2cauchy {PLUS (PLUS t₁ t₃) t₅} {PLUS (PLUS t₂ t₄) t₆} ((c₁ ⊕ c₂) ⊕ c₃)))
         (idcauchy (size t₁ + (size t₃ + size t₅)))
       ≡⟨ cong
            (scompcauchy
              (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
                (c2cauchy
                  {PLUS (PLUS t₁ t₃) t₅}
                  {PLUS (PLUS t₂ t₄) t₆}
                  ((c₁ ⊕ c₂) ⊕ c₃))))
            (sym (congD! idcauchy (size≡! (assocl₊ {t₁} {t₃} {t₅})))) ⟩
       scompcauchy
         (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
           (c2cauchy {PLUS (PLUS t₁ t₃) t₅} {PLUS (PLUS t₂ t₄) t₆} ((c₁ ⊕ c₂) ⊕ c₃)))
         (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
           (idcauchy ((size t₁ + size t₃) + size t₅)))
       ≡⟨ cong
            (λ x →
             scompcauchy
              (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
                (c2cauchy
                  {PLUS (PLUS t₁ t₃) t₅}
                  {PLUS (PLUS t₂ t₄) t₆}
                  ((c₁ ⊕ c₂) ⊕ c₃)))
              (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅})) x))
            (sym (congD! idcauchy (size≡! ((c₁ ⊕ c₂) ⊕ c₃)))) ⟩
       scompcauchy
         (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
           (c2cauchy {PLUS (PLUS t₁ t₃) t₅} {PLUS (PLUS t₂ t₄) t₆} ((c₁ ⊕ c₂) ⊕ c₃)))
         (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
           (subst Cauchy (size≡! ((c₁ ⊕ c₂) ⊕ c₃))
             (idcauchy ((size t₂ + size t₄) + size t₆))))
       ≡⟨ sym (subst-dist scompcauchy (size≡! (assocl₊ {t₁} {t₃} {t₅})) _ _) ⟩
       subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
         (scompcauchy
           (c2cauchy {PLUS (PLUS t₁ t₃) t₅} {PLUS (PLUS t₂ t₄) t₆} ((c₁ ⊕ c₂) ⊕ c₃))
           (subst Cauchy (size≡! ((c₁ ⊕ c₂) ⊕ c₃))
             (idcauchy ((size t₂ + size t₄) + size t₆))))
       ≡⟨ sym (scomplid _) ⟩
         scompcauchy
           (idcauchy (size t₁ + (size t₃ + size t₅)))
           (subst Cauchy (size≡! (assocl₊ {t₁} {t₃} {t₅}))
             (scompcauchy
               (c2cauchy
                  {PLUS (PLUS t₁ t₃) t₅} {PLUS (PLUS t₂ t₄) t₆} ((c₁ ⊕ c₂) ⊕ c₃))
               (subst Cauchy (size≡! ((c₁ ⊕ c₂) ⊕ c₃))
                (idcauchy ((size t₂ + size t₄) + size t₆)))))
       ≡⟨ refl ⟩
         c2cauchy (assocl₊ ◎ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)) ∎)
  where open ≡-Reasoning
soundness (assoc⊕r {t₁} {t₂} {t₃} {t₄} {t₅} {t₆} {c₁} {c₂} {c₃}) = {!!}
soundness (assoc⊗l {t₁} {t₂} {t₃} {t₄} {t₅} {t₆} {c₁} {c₂} {c₃}) = {!!}
soundness (assoc⊗r {t₁} {t₂} {t₃} {t₄} {t₅} {t₆} {c₁} {c₂} {c₃}) = {!!}
soundness (dist⇔ {t₁} {t₂} {t₃} {t₄} {t₅} {t₆} {c₁} {c₂} {c₃}) = {!!}
soundness (factor⇔ {t₁} {t₂} {t₃} {t₄} {t₅} {t₆} {c₁} {c₂} {c₃}) = {!!}
soundness (idl◎l {t₁} {t₂} {c}) = id◎c∼c {t₁} {t₂} {c}
soundness (idl◎r {t₁} {t₂} {c}) = sym (id◎c∼c {t₁} {t₂} {c})
soundness (idr◎l {t₁} {t₂} {c}) = c◎id∼c {t₁} {t₂} {c}
soundness (idr◎r {t₁} {t₂} {c}) = sym (c◎id∼c {t₁} {t₂} {c})
soundness (linv◎l {t₁} {t₂} {c}) = linv∼ {t₁} {t₂} {c}
soundness (linv◎r {t₁} {t₂} {c}) = sym (linv∼ {t₁} {t₂} {c})
soundness (rinv◎l {t₁} {t₂} {c})  = rinv∼ {t₁} {t₂} {c}
soundness (rinv◎r {t₁} {t₂} {c})  = sym (rinv∼ {t₁} {t₂} {c})
soundness (unitel₊⇔ {t₁} {t₂} {c₁} {c₂}) = {!!}
soundness (uniter₊⇔ {t₁} {t₂} {c₁} {c₂}) = {!!}
soundness (unitil₊⇔ {t₁} {t₂} {c₁} {c₂}) = {!!}
soundness (unitir₊⇔ {t₁} {t₂} {c₁} {c₂}) = {!!}
soundness (unitial₊⇔ {t₁} {t₂}) = {!!}
soundness (unitiar₊⇔ {t₁} {t₂}) = {!!}
soundness (swapl₊⇔ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂}) = {!!}
soundness (swapr₊⇔ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂}) = {!!}
soundness (unitel⋆⇔ {t₁} {t₂} {c₁} {c₂}) = {!!}
soundness (uniter⋆⇔ {t₁} {t₂} {c₁} {c₂}) = {!!}
soundness (unitil⋆⇔ {t₁} {t₂} {c₁} {c₂}) = {!!}
soundness (unitir⋆⇔ {t₁} {t₂} {c₁} {c₂}) = {!!}
soundness (unitial⋆⇔ {t₁} {t₂}) = {!!}
soundness (unitiar⋆⇔ {t₁} {t₂}) = {!!}
soundness (swapl⋆⇔ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂}) = {!!}
soundness (swapr⋆⇔ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂}) = {!!}
soundness (swapfl⋆⇔ {t₁} {t₂} {t₃}) = {!!}
soundness (swapfr⋆⇔ {t₁} {t₂} {t₃}) = {!!}
soundness (id⇔ {t₁} {t₂} {c}) = refl∼ {t₁} {t₂} {c}
soundness (trans⇔ {t₁} {t₂} {c₁} {c₂} {c₃} α β) =
  trans∼ {t₁} {t₂} {c₁} {c₂} {c₃} (soundness α) (soundness β)
soundness (resp◎⇔ {t₁} {t₂} {t₃} {c₁} {c₃} {c₂} {c₄} α β) =
  resp∼ {t₁} {t₂} {t₃} {c₁} {c₂} {c₃} {c₄} (soundness α) (soundness β)
soundness (resp⊕⇔ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃} {c₄} α β) = {!!}
soundness (resp⊗⇔ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃} {c₄} α β) = {!!}

-- If we can prove that every combinator is equal to its normal form
-- then we can prove completeness.

inversion : {t₁ t₂ : U} (c : t₁ ⟷ t₂) → c ⇔ canonical c
inversion (c₁ ◎ c₂) = {!!} 
inversion {PLUS ZERO t} {.t} unite₊ = {!!} 
inversion {t} {PLUS ZERO .t} uniti₊ = {!!} 
inversion {PLUS t₁ t₂} {PLUS .t₂ .t₁} swap₊ = {!!} 
inversion {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} assocl₊ = {!!} 
inversion {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} assocr₊ = {!!}
inversion {TIMES ONE t} {.t} unite⋆ = {!!}
inversion {t} {TIMES ONE .t} uniti⋆ = {!!} 
inversion {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = {!!} 
inversion {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} assocl⋆ = {!!}
inversion {TIMES (TIMES t₁ t₂) t₃} {TIMES .t₁ (TIMES .t₂ .t₃)} assocr⋆ = {!!}
inversion {TIMES .ZERO t} {ZERO} distz = {!!} 
inversion {ZERO} {TIMES ZERO t} factorz = {!!} 
inversion {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} dist = {!!}
inversion {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} {TIMES (PLUS .t₁ .t₂) .t₃} factor = {!!}
inversion {t} {.t} id⟷ = {!!} 
inversion {PLUS t₁ t₂} {PLUS t₃ t₄} (c₁ ⊕ c₂) = {!!} 
inversion {TIMES t₁ t₂} {TIMES t₃ t₄} (c₁ ⊗ c₂) = {!!} 
inversion {PLUS ONE ONE} {BOOL} foldBool = {!!} 
inversion {BOOL} {PLUS ONE ONE} unfoldBool = {!!} 

resp≡⇔ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ≡ c₂) → (c₁ ⇔ c₂)
resp≡⇔ {t₁} {t₂} {c₁} {c₂} p rewrite p = id⇔ 

completeness : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₁ ⇔ c₂)
completeness {t₁} {t₂} {c₁} {c₂} c₁∼c₂ = 
  c₁
    ⇔⟨ inversion c₁ ⟩
  canonical c₁
    ⇔⟨ resp≡⇔ {!!} ⟩ 
  canonical c₂
    ⇔⟨ 2! (inversion c₂) ⟩ 
  c₂ ▤

------------------------------------------------------------------------------



