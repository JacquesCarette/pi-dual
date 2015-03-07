-- Definition of the Operations on permutations, based on the Vector representation
-- There are 2 sets of definitions here:
-- 1. pure Vector, in which the contents are arbitrary sets
-- 2. specialized to Fin contents.

-- Some notes:
--   - There are operations (such as sequential composition) which 'lift' more
--     awkwardly.
--   - To avoid a proliferation of bad names, we use sub-modules

module VecOps where

open import Data.Nat
open import Data.Vec renaming (map to mapV; _++_ to _++V_; concat to concatV)
open import Data.Fin using (Fin; inject+; raise)
open import Function using (_∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

open import TypeEquivalences using (swap₊; swap⋆)
open import VectorLemmas using (_!!_)
open import FinEquiv using (module Plus; module Times)

------------------------------------------------------------------------------
-- Pure vector operations
-- Does not involve Fin at all.
-- Note: not exported!
private
  module V where
    _⊎v_ : ∀ {m n} {A B : Set} → Vec A m → Vec B n → Vec (A ⊎ B) (m + n)
    α ⊎v β = tabulate (inj₁ ∘ _!!_ α) ++V tabulate (inj₂ ∘ _!!_ β)

    swap+ : {m n : ℕ} {A B : Set} → Vec (A ⊎ B) (m + n) → Vec (B ⊎ A) (m + n)
    swap+ v = tabulate (swap₊ ∘ _!!_ v)

    _×v_ : ∀ {m n} {A B : Set} → Vec A m → Vec B n → Vec (A × B) (m * n)
    α ×v β = α >>= (λ b → mapV (_,_ b) β)

    0v : {A : Set} → Vec A 0
    0v = []

------------------------------------------------------------------------------
-- Elementary permutations, Fin version

-- We need to define (at least) 0, 1, +, *, ∘, swap+, swap*
module F where
  open V

  -- convenient abbreviation
  Cauchy : ℕ → ℕ → Set
  Cauchy m n = Vec (Fin m) n

  -- principal component of the identity permutation  
  1C : {n : ℕ} → Cauchy n n
  1C {n} = allFin n

  -- corresponds to ⊥ ≃ (⊥ × A) and other impossibilities
  0C : Cauchy 0 0
  0C = 0v

  -- Sequential composition
  _∘̂_ : {n₀ n₁ n₂ : ℕ} → Vec (Fin n₁) n₀ → Vec (Fin n₂) n₁ → Vec (Fin n₂) n₀
  π₁ ∘̂ π₂ = tabulate (_!!_ π₂ ∘ _!!_ π₁)

  -- swap the first m elements with the last n elements
  -- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
  -- ==>
  -- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

  swap+cauchy : (m n : ℕ) → Cauchy (n + m) (m + n)
  swap+cauchy m n = tabulate (Plus.swapper m n)

  -- Parallel additive composition
  -- conceptually, what we want is
  _⊎c'_ : ∀ {m₁ n₁ m₂ n₂} → Cauchy m₁ m₂ → Cauchy n₁ n₂ → Cauchy (m₁ + n₁) (m₂ + n₂)
  _⊎c'_ α β = mapV Plus.fwd (α ⊎v β)
  -- but the above is tedious to work with.  Instead, inline a bit to get
  _⊎c_ : ∀ {m₁ n₁ m₂ n₂} → Cauchy m₁ m₂ → Cauchy n₁ n₂ → Cauchy (m₁ + n₁) (m₂ + n₂)
  _⊎c_ {m₁} {m₂} {_} {n₂} α β = tabulate (inject+ m₂ ∘ _!!_ α) ++V
                                                       tabulate (raise m₁ ∘ _!!_ β)
  -- see ⊎c≡⊎c' lemma below

  -- Tensor multiplicative composition
  -- Transpositions in α correspond to swapping entire rows
  -- Transpositions in β correspond to swapping entire columns
  _×c_ : ∀ {m₁ n₁ m₂ n₂} → Cauchy m₁ m₂ → Cauchy n₁ n₂ → Cauchy (m₁ * n₁) (m₂ * n₂)
  α ×c β = mapV Times.fwd (α ×v β)

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

  swap⋆cauchy : (m n : ℕ) → Cauchy (n * m) (m * n)
  swap⋆cauchy m n = tabulate (Times.swapper m n)
    -- mapV transposeIndex (V.tcomp 1C 1C)

  -------------------------------------------------------------------------------------------
  -- Below here, we start with properties

  open import FiniteFunctions
  open import VectorLemmas using (lookupassoc; map-++-commute; 
    tabulate-split; left!!)
  open import Proofs using (congD!)
  open import Data.Vec.Properties using (lookup-allFin; tabulate∘lookup; 
    lookup∘tabulate; tabulate-∘; lookup-++-inject+)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; 
    cong; cong₂; module ≡-Reasoning)
  open ≡-Reasoning

  -- Useful stuff
  infix 4 _∼p_

  _∼p_ : {n : ℕ} (p₁ p₂ : Vec (Fin n) n) → Set
  _∼p_ {n} p₁ p₂ = (i : Fin n) → p₁ !! i ≡ p₂ !! i

  ∼p⇒≡ : {n : ℕ} {p₁ p₂ : Vec (Fin n) n} → (p₁ ∼p p₂) → p₁ ≡ p₂
  ∼p⇒≡ {n} {p₁} {p₂} eqv = 
    begin (
      p₁                                    ≡⟨ sym (tabulate∘lookup p₁) ⟩
      tabulate (_!!_ p₁)            ≡⟨ finext eqv ⟩
      tabulate (_!!_ p₂)            ≡⟨ tabulate∘lookup p₂ ⟩
      p₂ ∎)
    where open ≡-Reasoning

  -- note the flip!
  ∘̂⇒∘ : {n : ℕ} → (f g : Fin n → Fin n) → tabulate f ∘̂ tabulate g ∼p tabulate (g ∘ f)
  ∘̂⇒∘ f g i = 
    begin (
      (tabulate f ∘̂ tabulate g) !! i
        ≡⟨ lookup∘tabulate _ i ⟩
      (tabulate g) !! (tabulate f !! i)
        ≡⟨ lookup∘tabulate _ (tabulate f !! i) ⟩
      g (tabulate f !! i)
        ≡⟨ cong g (lookup∘tabulate f i) ⟩
      g (f i)
        ≡⟨ sym (lookup∘tabulate (g ∘ f) i) ⟩
      tabulate (g ∘ f) !! i ∎)
    where open ≡-Reasoning

  -- properties of sequential composition
  ∘̂-assoc : {n : ℕ} → (a b c : Vec (Fin n) n) → a ∘̂ (b ∘̂ c) ≡ (a ∘̂ b) ∘̂ c
  ∘̂-assoc a b c = finext (lookupassoc a b c)

  ∘̂-rid : {n : ℕ} → (π : Vec (Fin n) n) → π ∘̂ 1C ≡ π
  ∘̂-rid π = trans (finext (λ i → lookup-allFin (π !! i))) (tabulate∘lookup π)

  ∘̂-lid : {n : ℕ} → (π : Vec (Fin n) n) → 1C ∘̂ π ≡ π
  ∘̂-lid π = trans (finext (λ i → cong (_!!_ π) (lookup-allFin i))) (tabulate∘lookup π)

  !!⇒∘̂ : {n₁ n₂ n₃ : ℕ} → (π₁ : Vec (Fin n₁) n₂) → (π₂ : Vec (Fin n₂) n₃) → (i : Fin n₃) → π₁ !! (π₂ !! i) ≡ (π₂ ∘̂ π₁) !! i
  !!⇒∘̂ π₁ π₂ i = 
    begin (
      π₁ !! (π₂ !! i)
            ≡⟨ sym (lookup∘tabulate (λ j → (π₁ !! (π₂ !! j))) i) ⟩
      tabulate (λ i → π₁ !! (π₂ !! i)) !! i
            ≡⟨ refl ⟩
      (π₂ ∘̂ π₁) !! i ∎)
    where open ≡-Reasoning

  left⊎⊎!! :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → (p₁ : Cauchy m₁ n₁) → (p₂ : Cauchy m₂ n₂)
    → (p₃ : Cauchy m₃ m₁) → (p₄ : Cauchy m₄ m₂) → (i : Fin n₁) → 
    (p₃ ⊎c p₄) !! ( (p₁ ⊎c p₂) !! inject+ n₂ i ) ≡ inject+ m₄ ( (p₁ ∘̂ p₃) !! i) 
  left⊎⊎!! {m₁} {m₂} {_} {m₄} {_} {n₂} p₁ p₂ p₃ p₄ i =
    let pp = p₃ ⊎c p₄ in
    let qq = p₁ ⊎c p₂ in
    begin (
        pp !! (qq !! inject+ n₂ i)
          ≡⟨ cong (_!!_ pp) (lookup-++-inject+ (tabulate (inject+ m₂ ∘ _!!_ p₁) ) 
                                                                     (tabulate (raise m₁ ∘ _!!_ p₂)) i) ⟩ 
       pp !! (tabulate (inject+ m₂ ∘ _!!_ p₁ ) !! i)
          ≡⟨ cong (_!!_ pp) (lookup∘tabulate _ i) ⟩
       pp !! (inject+ m₂ (p₁ !! i))
          ≡⟨ left!! (p₁ !! i) (inject+ m₄ ∘ (_!!_ p₃)) ⟩
        inject+ m₄ (p₃ !! (p₁ !! i))
          ≡⟨ cong (inject+ m₄) (sym (lookup∘tabulate _ i)) ⟩
        inject+ m₄ ((p₁ ∘̂ p₃) !! i) ∎ )

  ⊎c-distrib : ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : Cauchy m₁ n₁} → {p₂ : Cauchy m₂ n₂}
    → {p₃ : Cauchy m₃ m₁} → {p₄ : Cauchy m₄ m₂} →
      (p₁ ⊎c p₂) ∘̂ (p₃ ⊎c p₄) ≡ (p₁ ∘̂ p₃) ⊎c (p₂ ∘̂ p₄)
  ⊎c-distrib {m₁} {m₂} {m₃} {m₄} {n₁} {n₂} {p₁} {p₂} {p₃} {p₄} =
    let p₃₄ = p₃ ⊎c p₄ in let p₁₂ = p₁ ⊎c p₂ in
    let lhs = λ i → p₃₄ !! (p₁₂ !! i) in
    begin (
      tabulate lhs
        ≡⟨ tabulate-split {n₁} {n₂} ⟩
      tabulate {n₁} (lhs ∘ inject+ n₂) ++V tabulate {n₂} (lhs ∘ raise n₁)
        ≡⟨ cong₂ _++V_ (finext (left⊎⊎!! p₁ _ _ _)) (finext {!!}) ⟩
      tabulate {n₁} (λ i → inject+ m₄ ((p₁ ∘̂ p₃) !! i)) ++V 
      tabulate {n₂} (λ i → raise m₃ ((p₂ ∘̂ p₄) !! i))
        ≡⟨ refl ⟩
      (p₁ ∘̂ p₃) ⊎c (p₂ ∘̂ p₄) ∎)
