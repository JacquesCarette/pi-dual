{-# OPTIONS --without-K #-}

module Swaps where

-- Intermediate representation of permutations to prove soundness and
-- completeness 

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
open import Data.Bool using (Bool; false; true; T)
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

------------------------------------------------------------------------------
-- The syntactic combinators are rich enough to define the groupoid structure. Now
-- we investigate whether they are complete.

-- A permutation between t₁ and t₂ has three components in the Cauchy
-- representation: the map π of each element to a new position and a
-- proof that the sizes of the domain and range are the same and that
-- the map is injective.

TPermutation : U → U → Set
TPermutation t₁ t₂ = size t₁ ≡ size t₂ × Permutation (size t₁)

-- A view of (t : U) as normalized types.
-- Let size t be n then the normalized version of t is the type
-- (1 + (1 + (1 + (1 + ... 0)))) i.e. Fin n.

fromSize : ℕ → U
fromSize 0 = ZERO
fromSize (suc n) = PLUS ONE (fromSize n)

canonicalU : U → U
canonicalU = fromSize ∘ size

size+ : (n₁ n₂ : ℕ) → PLUS (fromSize n₁) (fromSize n₂) ⟷ fromSize (n₁ + n₂)
size+ 0 n₂ = unite₊
size+ (suc n₁) n₂ = assocr₊ ◎ (id⟷ ⊕ size+ n₁ n₂)

size* : (n₁ n₂ : ℕ) → TIMES (fromSize n₁) (fromSize n₂) ⟷ fromSize (n₁ * n₂)
size* 0 n₂ = distz
size* (suc n₁) n₂ = dist ◎ (unite⋆ ⊕ size* n₁ n₂) ◎ size+ n₂ (n₁ * n₂)

normalizeC : (t : U) → t ⟷ canonicalU t
normalizeC ZERO = id⟷
normalizeC ONE = uniti₊ ◎ swap₊
normalizeC BOOL = unfoldBool ◎
                 ((uniti₊ ◎ swap₊) ⊕ (uniti₊ ◎ swap₊)) ◎
                 (assocr₊ ◎ (id⟷ ⊕ unite₊))
normalizeC (PLUS t₀ t₁) =
  (normalizeC t₀ ⊕ normalizeC t₁) ◎ size+ (size t₀) (size t₁) 
normalizeC (TIMES t₀ t₁) =
  (normalizeC t₀ ⊗ normalizeC t₁) ◎ size* (size t₀) (size t₁) 

-- Given a normalized type Fin n and two indices 'a' and 'b' generate the code
-- to swap the two indices. Ex:
-- swapFin {3} "0" "1" should produce the permutation:
-- assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊ : 
-- PLUS ONE (PLUS ONE (PLUS ONE ZERO)) ⟷ PLUS ONE (PLUS ONE (PLUS ONE ZERO))

swapFin : {n : ℕ} → (a b : Fin n) → (leq : toℕ a ≤ toℕ b) → fromSize n ⟷ fromSize n
swapFin zero zero z≤n = id⟷
swapFin zero (suc zero) z≤n = assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊
swapFin zero (suc (suc b)) z≤n =
  (assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊) ◎
  (id⟷ ⊕ swapFin zero (suc b) z≤n) ◎
  (assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊)
swapFin (suc a) zero ()
swapFin (suc a) (suc b) (s≤s leq) = id⟷ ⊕ swapFin a b leq 

--------------
-- Representation I:
-- Our first representation of a permutation is as a product of
-- "transpositions." This product is not commutative; we apply it from
-- left to right. Because we eventually want to normalize permutations
-- to some canonical representation, we insist that the first
-- component of a transposition is always ≤ than the second

infix 90 _X_

data Transposition (n : ℕ) : Set where
  _X_ : (i j : Fin n) → {p : toℕ i ≤ toℕ j} → Transposition n

i≰j→j≤i : (i j : ℕ) → (i ≰ j) → (j ≤ i) 
i≰j→j≤i i 0 p = z≤n 
i≰j→j≤i 0 (suc j) p with p z≤n
i≰j→j≤i 0 (suc j) p | ()
i≰j→j≤i (suc i) (suc j) p with i ≤? j
i≰j→j≤i (suc i) (suc j) p | yes p' with p (s≤s p')
i≰j→j≤i (suc i) (suc j) p | yes p' | ()
i≰j→j≤i (suc i) (suc j) p | no p' = s≤s (i≰j→j≤i i j p')

mkTransposition : {n : ℕ} → (i j : Fin n) → Transposition n
mkTransposition {n} i j with toℕ i ≤? toℕ j 
... | yes p = _X_ i j {p}
... | no p  = _X_ j i {i≰j→j≤i (toℕ i) (toℕ j) p}

Transposition* : ℕ → Set
Transposition* n = List (Transposition n) 

showTransposition* : ∀ {n} → Transposition* n → List String
showTransposition* = 
  mapL (λ { (i X j) → show (toℕ i) ++S " X " ++S show (toℕ j) })

actionπ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Transposition* n → Vec A n → Vec A n
actionπ π vs = foldl swapX vs π
  where 
    swapX : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vec A n → Transposition n → Vec A n  
    swapX vs (i X j) = (vs [ i ]≔ lookup j vs) [ j ]≔ lookup i vs

-- Representation II:
-- This is also a product of transpositions but the transpositions are such
-- that the first component is always < the second, i.e., we got rid of trivial
-- transpositions that swap an element with itself

data Transposition< (n : ℕ) : Set where
  _X!_ : (i j : Fin n) → {p : toℕ i < toℕ j} → Transposition< n

Transposition<* : ℕ → Set
Transposition<* n = List (Transposition< n) 

showTransposition<* : ∀ {n} → Transposition<* n → List String
showTransposition<* = 
  mapL (λ { (i X! j) → show (toℕ i) ++S " X! " ++S show (toℕ j) })

i≠j∧i≤j→i<j : (i j : ℕ) → (¬ i ≡ j) → (i ≤ j) → (i < j)
i≠j∧i≤j→i<j 0 0 p≠ p≤ with p≠ refl
i≠j∧i≤j→i<j 0 0 p≠ p≤ | ()
i≠j∧i≤j→i<j 0 (suc j) p≠ p≤ = s≤s z≤n
i≠j∧i≤j→i<j (suc i) 0 p≠ ()
i≠j∧i≤j→i<j (suc i) (suc j) p≠ (s≤s p≤) with i ≟ j
i≠j∧i≤j→i<j (suc i) (suc j) p≠ (s≤s p≤) | yes p' with p≠ (cong suc p')
i≠j∧i≤j→i<j (suc i) (suc j) p≠ (s≤s p≤) | yes p' | ()
i≠j∧i≤j→i<j (suc i) (suc j) p≠ (s≤s p≤) | no p' = s≤s (i≠j∧i≤j→i<j i j p' p≤)
     
filter= : {n : ℕ} → Transposition* n → Transposition<* n
filter= [] = []
filter= (_X_ i j {p≤} ∷ π) with toℕ i ≟ toℕ j
... | yes p= = filter= π 
... | no p≠ = _X!_ i j {i≠j∧i≤j→i<j (toℕ i) (toℕ j) p≠ p≤}  ∷ filter= π 

-- Representation IV
-- A product of cycles where each cycle is a non-empty sequence of indices

Cycle : ℕ → Set
Cycle n = List⁺ (Fin n)

Cycle* : ℕ → Set
Cycle* n = List (Cycle n)

-- convert a cycle to a product of transpositions

postulate
  cycle→transposition* : ∀ {n} → Cycle n → Transposition* n

-- cycle→transposition* : ∀ {n} → Cycle n → Transposition* n
-- cycle→transposition* = {!!} 

{--
cycle→transposition* (i , []) = []
cycle→transposition* (i , (j ∷ ns)) = 
  mkTransposition i j ∷ cycle→transposition* (i , ns)
--}
cycle*→transposition* : ∀ {n} → Cycle* n → Transposition* n
cycle*→transposition* cs = concatMap cycle→transposition* cs

-- Convert from Cauchy 2 line representation to product of cycles

-- Helper that checks if there is a cycle that starts at i
-- Returns the cycle containing i and the rest of the permutation
-- without that cycle

findCycle : ∀ {n} → Fin n → Cycle* n →  Maybe (Cycle n × Cycle* n)
findCycle i [] = nothing
findCycle i (c ∷ cs) with toℕ i ≟ toℕ (head c)
findCycle i (c ∷ cs) | yes _ = just (c , cs)
findCycle i (c ∷ cs) | no _ = 
  maybe′ (λ { (c' , cs') → just (c' , c ∷ cs') }) nothing (findCycle i cs)

-- Another helper that repeatedly tries to merge smaller cycles

{-# NO_TERMINATION_CHECK #-}
mergeCycles : ∀ {n} → Cycle* n → Cycle* n
mergeCycles [] = []
mergeCycles (c ∷ cs) with findCycle (last c) cs
mergeCycles (c ∷ cs) | nothing = c ∷ mergeCycles cs
mergeCycles (c ∷ cs) | just (c' , cs') = mergeCycles ((c ⁺++ ntail c') ∷ cs')

-- To convert a Cauchy representation to a product of cycles, just create 
-- a cycle of size 2 for each entry and then merge the cycles

cauchy→cycle* : ∀ {n} → Cauchy n → Cycle* n
cauchy→cycle* {n} perm = 
  mergeCycles (toList (zipWith (λ i j → i ∷⁺ Data.List.NonEmpty.[ j ]) (allFin n) perm))

cauchyEx1→transposition* cauchyEx2→transposition* : List String
cauchyEx1→transposition* = 
  showTransposition* (cycle*→transposition* (cauchy→cycle* cauchyEx1))
-- 0 X 2 ∷ 0 X 4 ∷ 0 X 1 ∷ 0 X 0 ∷ 3 X 3 ∷ 5 X 5 ∷ []
-- actionπ (cycle*→transposition* (cauchy→cycle* cauchyEx1)) 
--   (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
-- 1 ∷ 4 ∷ 0 ∷ 3 ∷ 2 ∷ 5 ∷ []
cauchyEx2→transposition* = 
  showTransposition* (cycle*→transposition* (cauchy→cycle* cauchyEx2))
-- 0 X 3 ∷ 0 X 0 ∷ 1 X 2 ∷ 1 X 1 ∷ 4 X 5 ∷ 4 X 4 ∷ []
-- actionπ (cycle*→transposition* (cauchy→cycle* cauchyEx2)) 
--   (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
-- 3 ∷ 2 ∷ 1 ∷ 0 ∷ 5 ∷ 4 ∷ []

-- Cauchy to product of transpostions

cauchy→transposition* : ∀ {n} → Cauchy n → Transposition* n
cauchy→transposition* = cycle*→transposition* ∘ cauchy→cycle*

--------------

transposition*2c : (m n : ℕ) (m≡n : m ≡ n) → Transposition* m →
                   (fromSize m ⟷ fromSize n)
transposition*2c m n m≡n [] rewrite m≡n = id⟷ 
transposition*2c m n m≡n (_X_ i j {leq} ∷ π) rewrite m≡n =
  swapFin i j leq ◎ transposition*2c n n refl π

perm2c : {t₁ t₂ : U} → TPermutation t₁ t₂ → (t₁ ⟷ t₂)
perm2c {t₁} {t₂} (s₁≡s₂ , (π , inj)) =
  normalizeC t₁ ◎
  transposition*2c (size t₁) (size t₂) s₁≡s₂ (cauchy→transposition* π) ◎
  (! (normalizeC t₂))

------------------------------------------------------------------------------
