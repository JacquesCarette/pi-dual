{-# OPTIONS --without-K #-}

module FinVec where

-- This is the second step in building a representation of
-- permutations. We use permutations expressed as equivalences (in
-- FinVec) to construct one-line notation for permutations. We have
-- enough structure to model a commutative semiring EXCEPT for
-- symmetry. This will be addressed in ConcretePermutation.

import Level using (zero)

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Sum
   using (_⊎_; inj₁; inj₂)
   renaming (map to map⊎)
open import Data.Product using (_×_; proj₁; proj₂; _,′_)

open import Data.Vec
  using (Vec; allFin; tabulate; _>>=_)
  renaming (_++_ to _++V_; map to mapV)

open import Algebra using (CommutativeSemiring)
open import Algebra.Structures using
  (IsSemigroup; IsCommutativeMonoid; IsCommutativeSemiring)

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open import Function using (_∘_; id)

--

open import Equiv using (_∼_; p∘!p≡id; module qinv)
open import TypeEquiv using (swap₊)
open import FinEquiv using (module Plus; module Times; module PlusTimes)

open import Proofs using (
  -- FiniteFunctions
      finext; 
  -- VectorLemmas
      _!!_; tabulate-split
     )

------------------------------------------------------------------------------
-- The main goal is to represent permutations in the one-line notation
-- and to develop all the infrastructure to get a commutative
-- semiring, e.g., we can take unions and products of such one-line
-- notations of permutations, etc.

-- This is the type representing permutations in the one-line
-- notation. We will show that it is a commutative semiring

FinVec : ℕ → ℕ → Set
FinVec m n = Vec (Fin m) n

-- The additive and multiplicative units are trivial

1C : {n : ℕ} → FinVec n n
1C {n} = allFin n

-- corresponds to ⊥ ≃ ⊥ × A and other impossibilities but don't use
-- it, as it is abstract and will confuse external proofs!

abstract

  0C : FinVec 0 0
  0C = 1C {0}

-- sequential composition (transitivity)

_∘̂_ : {n₀ n₁ n₂ : ℕ} → Vec (Fin n₁) n₀ → Vec (Fin n₂) n₁ → Vec (Fin n₂) n₀
π₁ ∘̂ π₂ = tabulate (_!!_ π₂ ∘ _!!_ π₁)

------------------------------------------------------------------------------
-- Additive monoid

private

  _⊎v_ : ∀ {m n} {A B : Set} → Vec A m → Vec B n → Vec (A ⊎ B) (m + n)
  α ⊎v β = tabulate (inj₁ ∘ _!!_ α) ++V tabulate (inj₂ ∘ _!!_ β)

-- Parallel additive composition
-- conceptually, what we want is

_⊎c'_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ →
        FinVec (m₁ + n₁) (m₂ + n₂)
_⊎c'_ α β = mapV Plus.fwd (α ⊎v β)

-- but the above is tedious to work with.  Instead, inline a bit to get

_⊎c_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ →
       FinVec (m₁ + n₁) (m₂ + n₂)
_⊎c_ {m₁} α β = tabulate (Plus.fwd ∘ inj₁ ∘ _!!_ α) ++V
                tabulate (Plus.fwd {m₁} ∘ inj₂ ∘ _!!_ β)

-- see ⊎c≡⊎c' lemma below

_⊎fv_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ →
        FinVec (m₁ + n₁) (m₂ + n₂)
_⊎fv_ {m₁} α β =
  tabulate (λ j → Plus.fwd (map⊎ (_!!_ α) (_!!_ β) (Plus.bwd j)))

⊎-equiv : ∀ {m₁ n₁ m₂ n₂} → (α : FinVec m₁ m₂) → (β : FinVec n₁ n₂) →
          α ⊎c β ≡ α ⊎fv β
⊎-equiv {m₁} {n₁} {m₂} {n₂} α β =
  let mm s = map⊎ (_!!_ α) (_!!_ β) s in
  let g = Plus.fwd ∘ mm ∘ Plus.bwd in
  begin (
  tabulate (λ j → Plus.fwd (inj₁ (α !! j))) ++V
  tabulate (λ j → Plus.fwd {m₁} (inj₂ (β !! j)))
    ≡⟨ refl ⟩ -- map⊎ evaluates on inj₁/inj₂
  tabulate (Plus.fwd ∘ mm ∘ inj₁) ++V tabulate (Plus.fwd ∘ mm ∘ inj₂)
    ≡⟨ cong₂ _++V_
         (finext (λ i → cong (Plus.fwd ∘ mm)
                          (sym (Plus.bwd∘fwd~id (inj₁ i)))))
         (finext (λ i → cong (Plus.fwd ∘ mm)
                          (sym (Plus.bwd∘fwd~id (inj₂ i))))) ⟩
  tabulate {m₂} (g ∘ Plus.fwd ∘ inj₁) ++V
  tabulate {n₂} (g ∘ Plus.fwd {m₂} ∘ inj₂)
    ≡⟨ sym (tabulate-split {m₂} {n₂} {f = g}) ⟩
  tabulate g ∎)
  where
    open ≡-Reasoning
        
-- additive units

unite+ : {m : ℕ} → FinVec m (0 + m)
unite+ {m} = tabulate (proj₁ (Plus.unite+ {m}))

uniti+ : {m : ℕ} → FinVec (0 + m) m
uniti+ {m} = tabulate (proj₁ (Plus.uniti+ {m}))

unite+r : {m : ℕ} → FinVec m (m + 0)
unite+r {m} = tabulate (proj₁ (Plus.unite+r {m}))

unite+r' : {m : ℕ} → FinVec m (m + 0)
unite+r' {m} = tabulate (proj₁ (Plus.unite+r' {m}))

uniti+r : {m : ℕ} → FinVec (m + 0) m
uniti+r {m} = tabulate (proj₁ (Plus.uniti+r {m}))
    
-- commutativity

-- swap the first m elements with the last n elements
-- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
-- ==>
-- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

swap+cauchy : (m n : ℕ) → FinVec (n + m) (m + n)
swap+cauchy m n = tabulate (Plus.swapper m n)

-- associativity

assocl+ : {m n o : ℕ} → FinVec  ((m + n) + o) (m + (n + o))
assocl+ {m} {n} {o} = tabulate (proj₁ (Plus.assocl+ {m} {n} {o}))

assocr+ : {m n o : ℕ} → FinVec  (m + (n + o)) (m + n + o)
assocr+ {m} {n} {o} = tabulate (proj₁ (Plus.assocr+ {m} {n} {o}))

------------------------------------------------------------------------------
-- Multiplicative monoid

private

  _×v_ : ∀ {m n} {A B : Set} → Vec A m → Vec B n → Vec (A × B) (m * n)
  α ×v β = α >>= (λ b → mapV (_,′_ b) β)

-- Tensor multiplicative composition
-- Transpositions in α correspond to swapping entire rows
-- Transpositions in β correspond to swapping entire columns

_×c_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ →
       FinVec (m₁ * n₁) (m₂ * n₂)
α ×c β = mapV Times.fwd (α ×v β)

-- multiplicative units

unite* : {m : ℕ} → FinVec m (1 * m)
unite* {m} = tabulate (proj₁ (Times.unite* {m}))

uniti* : {m : ℕ} → FinVec (1 * m) m
uniti* {m} = tabulate (proj₁ (Times.uniti* {m}))

unite*r : {m : ℕ} → FinVec m (m * 1)
unite*r {m} = tabulate (proj₁ (Times.unite*r {m}))

uniti*r : {m : ℕ} → FinVec (m * 1) m
uniti*r {m} = tabulate (proj₁ (Times.uniti*r {m}))

-- commutativity

-- swap⋆
-- 
-- This is essentially the classical problem of in-place matrix transpose:
-- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
-- Given m and n, the desired permutation in Cauchy representation is:
-- P(i) = m*n-1 if i=m*n-1
--      = m*i mod m*n-1 otherwise

-- transposeIndex : {m n : ℕ} → Fin m × Fin n → Fin (n * m)
-- transposeIndex = Times.fwd ∘ swap
-- inject≤ (fromℕ (toℕ d * m + toℕ b)) (i*n+k≤m*n d b)

swap⋆cauchy : (m n : ℕ) → FinVec (n * m) (m * n)
swap⋆cauchy m n = tabulate (Times.swapper m n)
-- mapV transposeIndex (V.tcomp 1C 1C)

-- associativity

assocl* : {m n o : ℕ} → FinVec  ((m * n) * o) (m * (n * o))
assocl* {m} {n} {o} = tabulate (proj₁ (Times.assocl* {m} {n} {o}))

assocr* : {m n o : ℕ} → FinVec  (m * (n * o)) (m * n * o)
assocr* {m} {n} {o} = tabulate (proj₁ (Times.assocr* {m} {n} {o}))

------------------------------------------------------------------------------
-- Distributivity

dist*+ : ∀ {m n o} → FinVec (m * o + n * o) ((m + n) * o)
dist*+ {m} {n} {o} = tabulate (proj₁ (PlusTimes.dist {m} {n} {o}))

factor*+ : ∀ {m n o} → FinVec ((m + n) * o) (m * o + n * o)
factor*+ {m} {n} {o} = tabulate (proj₁ (PlusTimes.factor {m} {n} {o}))

distl*+ : ∀ {m n o} → FinVec (m * n + m * o) (m * (n + o))
distl*+ {m} {n} {o} = tabulate (proj₁ (PlusTimes.distl {m} {n} {o}))

factorl*+ : ∀ {m n o} → FinVec (m * (n + o)) (m * n + m * o)
factorl*+ {m} {n} {o} = tabulate (proj₁ (PlusTimes.factorl {m} {n} {o}))

right-zero*l : ∀ {m} → FinVec 0 (m * 0)
right-zero*l {m} = tabulate (proj₁ (PlusTimes.distzr {m}))

right-zero*r : ∀ {m} → FinVec (m * 0) 0
right-zero*r {m} = tabulate (proj₁ (PlusTimes.factorzr {m}))
   
------------------------------------------------------------------------------
-- Putting it all together, we have a commutative semiring structure
-- (modulo symmetry)

_cauchy≃_ : (m n : ℕ) → Set
m cauchy≃ n = FinVec m n

id-iso : {m : ℕ} → FinVec m m
id-iso = 1C

-- This is only here to show that we do have everything for a
-- commutative semiring structure EXCEPT for symmetry; this is
-- addressed in ConcretePermutation

postulate sym-iso : {m n : ℕ} → FinVec m n → FinVec n m

trans-iso : {m n o : ℕ} → FinVec m n → FinVec n o → FinVec m o 
trans-iso c₁ c₂ = c₂ ∘̂ c₁

cauchy≃IsEquiv : IsEquivalence {Level.zero} {Level.zero} {ℕ} _cauchy≃_
cauchy≃IsEquiv = record {
  refl = id-iso ; 
  sym = sym-iso ; 
  trans = trans-iso
  }

cauchyPlusIsSG : IsSemigroup {Level.zero} {Level.zero} {ℕ} _cauchy≃_ _+_
cauchyPlusIsSG = record {
  isEquivalence = cauchy≃IsEquiv ; 
  assoc = λ m n o → assocl+ {m} {n} {o} ; 
  ∙-cong = _⊎c_ 
  }

cauchyTimesIsSG : IsSemigroup {Level.zero} {Level.zero} {ℕ} _cauchy≃_ _*_
cauchyTimesIsSG = record {
  isEquivalence = cauchy≃IsEquiv ;
  assoc = λ m n o → assocl* {m} {n} {o} ;
  ∙-cong = _×c_
  }

cauchyPlusIsCM : IsCommutativeMonoid _cauchy≃_ _+_ 0
cauchyPlusIsCM = record {
  isSemigroup = cauchyPlusIsSG ;
  identityˡ = λ m → 1C ;
  comm = λ m n → swap+cauchy n m 
  }

cauchyTimesIsCM : IsCommutativeMonoid _cauchy≃_ _*_ 1
cauchyTimesIsCM = record {
  isSemigroup = cauchyTimesIsSG ;
  identityˡ = λ m → uniti* {m} ;
  comm = λ m n → swap⋆cauchy n m
  }

cauchyIsCSR : IsCommutativeSemiring _cauchy≃_ _+_ _*_ 0 1
cauchyIsCSR = record {
  +-isCommutativeMonoid = cauchyPlusIsCM ;
  *-isCommutativeMonoid = cauchyTimesIsCM ; 
  distribʳ = λ o m n → factor*+ {m} {n} {o} ; 
  zeroˡ = λ m → 0C
  }

cauchyCSR : CommutativeSemiring Level.zero Level.zero
cauchyCSR = record {
  Carrier = ℕ ;
  _≈_ = _cauchy≃_ ;
  _+_ = _+_ ;
  _*_ = _*_ ;
  0# = 0 ;
  1# = 1 ;
  isCommutativeSemiring = cauchyIsCSR
  }

------------------------------------------------------------------------------
