{-# OPTIONS --without-K #-}

-- FinSet is the category of finite sets and all functions between
-- them: the full subcategory of Set on finite sets. It is easy (and
-- thus common) to make FinSet skeletal; there is one object for each
-- natural number n (including n=0), and a morphism from m to n is an
-- m-tuple (f0,…,fm−1) of numbers satisfying 0≤fi<n. This amounts to
-- identifying n with the set {0,…,n−1}. (Sometimes {1,…,n} is used
-- instead.) This is exactly what we do below

-- Definition of the Operations on permutations, based on the Vector representation
-- There are 2 sets of definitions here:
-- 1. pure Vector, in which the contents are arbitrary sets
-- 2. specialized to Fin contents.

-- Some notes:
--   - There are operations (such as sequential composition) which 'lift' more
--     awkwardly.
--   - To avoid a proliferation of bad names, we use sub-modules

-- Cauchy representation Vec (Fin m) n without checks that m=n or
-- checks of uniqueness and completeness has a commutative semiring
-- structure (modulo a postulate about sym). This is the main building
-- block of ConcretePermutation

module FinVec where

import Level using (zero)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin; zero; suc; inject+; raise)
open import Data.Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
  renaming (map to map⊎)
open import Data.Product using (_×_; proj₁; proj₂; _,′_) 
open import Data.Vec
  using (Vec; _∷_; []; tabulate; _>>=_; allFin)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)
open import Data.Vec.Properties
  using (lookup-allFin; tabulate∘lookup; lookup∘tabulate; lookup-++-inject+;
         tabulate-∘)
open import Function using (_∘_; id)
open import Algebra using (CommutativeSemiring)
open import Algebra.Structures using
  (IsSemigroup; IsCommutativeMonoid; IsCommutativeSemiring)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Equiv using (_∼_; p∘!p≡id)
open import TypeEquiv using (swap₊)
import FinEquiv using (module Plus; module Times; module PlusTimes)
open FinEquiv.Plus using ()
  renaming (fwd-iso to plus-fwd-iso; swapper to plus-swapper;
  unite+ to plus-unite+; uniti+ to plus-uniti+;
  unite+r to plus-unite+r; uniti+r to plus-uniti+r;
  assocl+ to plus-assocl+; assocr+ to plus-assocr+;
  swap-inv to plus-swap-inv)
open FinEquiv.Times using ()
  renaming (fwd to times-fwd; bwd to times-bwd; swapper to times-swapper;
  fwd∘bwd~id to times-fwd∘bwd~id; bwd∘fwd~id to times-bwd∘fwd~id;
  swap-inv to times-swap-inv; 
  unite* to times-unite*; uniti* to times-uniti*;
  unite*r to times-unite*r; uniti*r to times-uniti*r;
  assocl* to times-assocl*; assocr* to times-assocr*;
  distz to times-distz; factorz to times-factorz;
  distzr to times-distzr; factorzr to times-factorzr)
open FinEquiv.PlusTimes using ()
  renaming (dist to plustimes-dist; factor to plustimes-factor;
            distl to plustimes-distl; factorl to plustimes-factorl)
open import Proofs using (
  -- FiniteFunctions
     finext; 
  -- VectorLemmas
     lookup-++-raise; lookupassoc; tabulate-split; _!!_; unSplit;
     concat-map; map-map-map; lookup-map; map-∘;
     left!!; right!!
     )

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
    α ×v β = α >>= (λ b → mapV (_,′_ b) β)

    0v : {A : Set} → Vec A 0
    0v = []

------------------------------------------------------------------------------
-- Elementary permutations, Fin version
-- Cauchy Representation Vec (Fin m) n without checks of uniqueness
-- and completeness

-- We need to define (at least) 0, 1, +, *, ∘, swap+, swap*

module F where

  open V

  -- convenient abbreviations
  FinVec : ℕ → ℕ → Set
  FinVec m n = Vec (Fin m) n

  private
    fwd : {m n : ℕ} → (Fin m ⊎ Fin n) → Fin (m + n)
    fwd = proj₁ plus-fwd-iso

    bwd : {m n : ℕ} → Fin (m + n) → (Fin m ⊎ Fin n)
    bwd = Equiv.qinv.g (proj₂ plus-fwd-iso)

    bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
    bwd∘fwd~id = Equiv.qinv.β (proj₂ plus-fwd-iso)
    
  -- make all the definitions abstract.  Note that the type isn't,
  -- otherwise we could not do anything at all with it!

  abstract
    -- principal component of the identity permutation  
    1C : {n : ℕ} → FinVec n n
    1C {n} = allFin n

    -- corresponds to ⊥ ≃ (⊥ × A) and other impossibilities
    -- but don't use it, as it is abstract and will confuse external proofs!
    0C : FinVec 0 0
    0C = 1C {0}

    -- Sequential composition
    _∘̂_ : {n₀ n₁ n₂ : ℕ} → Vec (Fin n₁) n₀ → Vec (Fin n₂) n₁ → Vec (Fin n₂) n₀
    π₁ ∘̂ π₂ = tabulate (_!!_ π₂ ∘ _!!_ π₁)

    -- swap the first m elements with the last n elements
    -- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
    -- ==>
    -- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

    swap+cauchy : (m n : ℕ) → FinVec (n + m) (m + n)
    swap+cauchy m n = tabulate (plus-swapper m n)

    -- Parallel additive composition
    -- conceptually, what we want is
    _⊎c'_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ + n₁) (m₂ + n₂)
    _⊎c'_ α β = mapV fwd (α ⊎v β)
    -- but the above is tedious to work with.  Instead, inline a bit to get
    _⊎c_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ + n₁) (m₂ + n₂)
    _⊎c_ {m₁} α β = tabulate (fwd ∘ inj₁ ∘ _!!_ α) ++V
                     tabulate (fwd {m₁} ∘ inj₂ ∘ _!!_ β)
    -- see ⊎c≡⊎c' lemma below

    _⊎fv_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ + n₁) (m₂ + n₂)
    _⊎fv_ {m₁} α β = tabulate (λ j → fwd (map⊎ (_!!_ α) (_!!_ β) (bwd j)))

    ⊎-equiv : ∀ {m₁ n₁ m₂ n₂} → (α : FinVec m₁ m₂) → (β : FinVec n₁ n₂) → α ⊎c β ≡ α ⊎fv β
    ⊎-equiv {m₁} {n₁} {m₂} {n₂} α β =
      let mm s = map⊎ (_!!_ α) (_!!_ β) s in
      let g = fwd ∘ mm ∘ bwd in
      begin (
      tabulate (λ j → fwd (inj₁ (α !! j))) ++V tabulate (λ j → fwd {m₁} (inj₂ (β !! j)))
        ≡⟨ refl ⟩ -- map⊎ evaluates on inj₁/inj₂
      tabulate (fwd ∘ mm ∘ inj₁) ++V tabulate (fwd ∘ mm ∘ inj₂)
        ≡⟨ cong₂ _++V_ (finext (λ i → cong (fwd ∘ mm) (sym (bwd∘fwd~id (inj₁ i)))))
                       (finext (λ i → cong (fwd ∘ mm) (sym (bwd∘fwd~id (inj₂ i))))) ⟩
      tabulate {m₂} (g ∘ fwd ∘ inj₁) ++V tabulate {n₂} (g ∘ fwd {m₂} ∘ inj₂)
        ≡⟨ sym (tabulate-split {m₂} {n₂} {f = g}) ⟩
      tabulate g ∎)
      where
        open ≡-Reasoning
        
    -- Tensor multiplicative composition
    -- Transpositions in α correspond to swapping entire rows
    -- Transpositions in β correspond to swapping entire columns
    _×c_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ * n₁) (m₂ * n₂)
    α ×c β = mapV times-fwd (α ×v β)

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
    swap⋆cauchy m n = tabulate (times-swapper m n)
      -- mapV transposeIndex (V.tcomp 1C 1C)

    -------------------------------------------------------------------------------------------
    -- Things which are the foundations of other permutations, but coming
    -- from properties, rather than being operators

    unite+ : {m : ℕ} → FinVec m (0 + m)
    unite+ {m} = tabulate (proj₁ (plus-unite+ {m}))

    uniti+ : {m : ℕ} → FinVec (0 + m) m
    uniti+ {m} = tabulate (proj₁ (plus-uniti+ {m}))

    unite+r : {m : ℕ} → FinVec m (m + 0)
    unite+r {m} = tabulate (proj₁ (plus-unite+r {m}))

    uniti+r : {m : ℕ} → FinVec (m + 0) m
    uniti+r {m} = tabulate (proj₁ (plus-uniti+r {m}))
    
    assocl+ : {m n o : ℕ} → FinVec  ((m + n) + o) (m + (n + o))
    assocl+ {m} {n} {o} = tabulate (proj₁ (plus-assocl+ {m} {n} {o}))

    assocr+ : {m n o : ℕ} → FinVec  (m + (n + o)) (m + n + o)
    assocr+ {m} {n} {o} = tabulate (proj₁ (plus-assocr+ {m} {n} {o}))

    unite* : {m : ℕ} → FinVec m (1 * m)
    unite* {m} = tabulate (proj₁ (times-unite* {m}))

    uniti* : {m : ℕ} → FinVec (1 * m) m
    uniti* {m} = tabulate (proj₁ (times-uniti* {m}))

    unite*r : {m : ℕ} → FinVec m (m * 1)
    unite*r {m} = tabulate (proj₁ (times-unite*r {m}))

    uniti*r : {m : ℕ} → FinVec (m * 1) m
    uniti*r {m} = tabulate (proj₁ (times-uniti*r {m}))

    assocl* : {m n o : ℕ} → FinVec  ((m * n) * o) (m * (n * o))
    assocl* {m} {n} {o} = tabulate (proj₁ (times-assocl* {m} {n} {o}))

    assocr* : {m n o : ℕ} → FinVec  (m * (n * o)) (m * n * o)
    assocr* {m} {n} {o} = tabulate (proj₁ (times-assocr* {m} {n} {o}))

    dist*+ : ∀ {m n o} → FinVec (m * o + n * o) ((m + n) * o)
    dist*+ {m} {n} {o} = tabulate (proj₁ (plustimes-dist {m} {n} {o}))

    factor*+ : ∀ {m n o} → FinVec ((m + n) * o) (m * o + n * o)
    factor*+ {m} {n} {o} = tabulate (proj₁ (plustimes-factor {m} {n} {o}))

    distl*+ : ∀ {m n o} → FinVec (m * n + m * o) (m * (n + o))
    distl*+ {m} {n} {o} = tabulate (proj₁ (plustimes-distl {m} {n} {o}))

    factorl*+ : ∀ {m n o} → FinVec (m * (n + o)) (m * n + m * o)
    factorl*+ {m} {n} {o} = tabulate (proj₁ (plustimes-factorl {m} {n} {o}))

    right-zero*l : ∀ {m} → FinVec 0 (m * 0)
    right-zero*l {m} = tabulate (proj₁ (times-distzr {m}))

    right-zero*r : ∀ {m} → FinVec (m * 0) 0
    right-zero*r {m} = tabulate (proj₁ (times-factorzr {m}))
   
    -------------------------------------------------------------------------------------------
    -- Below here, we start with properties

    -- Useful stuff
    infix 4 _∼p_

    _∼p_ : {n m : ℕ} (p₁ p₂ : Vec (Fin m) n) → Set
    _∼p_ {n} p₁ p₂ = (i : Fin n) → p₁ !! i ≡ p₂ !! i

    ∼p⇒≡ : {n : ℕ} {p₁ p₂ : Vec (Fin n) n} → (p₁ ∼p p₂) → p₁ ≡ p₂
    ∼p⇒≡ {n} {p₁} {p₂} eqv = 
      begin (
        p₁                            ≡⟨ sym (tabulate∘lookup p₁) ⟩
        tabulate (_!!_ p₁)            ≡⟨ finext eqv ⟩
        tabulate (_!!_ p₂)            ≡⟨ tabulate∘lookup p₂ ⟩
        p₂ ∎)
      where open ≡-Reasoning

    -- note the flip!
    ∘̂⇒∘ : {m n o : ℕ} → (f : Fin m → Fin n) → (g : Fin n → Fin o) → 
              tabulate f ∘̂ tabulate g ∼p tabulate (g ∘ f)
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

    -- this is just tabulate∘lookup, but it hides the details; should this be
    -- called 'join' or 'flatten' ?
    cauchyext : {m n : ℕ} (π : FinVec m n) → tabulate (_!!_ π) ≡ π
    cauchyext π = tabulate∘lookup π

    -- we could go through ~p, but this works better in practice
    ~⇒≡ : {m n : ℕ} {f : Fin m → Fin n} {g : Fin n → Fin m} → 
               (f ∘ g ∼ id) → (tabulate g ∘̂ tabulate f ≡ 1C)
    ~⇒≡ {f = f} {g} β = ∼p⇒≡ (λ i → trans (∘̂⇒∘ g f i) (cong (λ x → x !! i) (finext β)))

    -- make a permutation from something lower level, directly
    --  ~⇒≡ {m} {n = m} {o = m} (p∘!p≡id {p = Plus.unite+ {m}})

    -- properties of sequential composition
    ∘̂-assoc : {m₁ m₂ m₃ m₄ : ℕ} →
             (a : Vec (Fin m₂) m₁) (b : Vec (Fin m₃) m₂) (c : Vec (Fin m₄) m₃) → 
             a ∘̂ (b ∘̂ c) ≡ (a ∘̂ b) ∘̂ c
    ∘̂-assoc a b c = finext (lookupassoc a b c)

    ∘̂-rid : {m n : ℕ} → (π : Vec (Fin m) n) → π ∘̂ 1C ≡ π
    ∘̂-rid π = trans (finext (λ i → lookup-allFin (π !! i))) (cauchyext π)

    ∘̂-lid : {m n : ℕ} → (π : Vec (Fin m) n) → 1C ∘̂ π ≡ π
    ∘̂-lid π = trans (finext (λ i → cong (_!!_ π) (lookup-allFin i))) (cauchyext π)

    !!⇒∘̂ : {n₁ n₂ n₃ : ℕ} →
            (π₁ : Vec (Fin n₁) n₂) → (π₂ : Vec (Fin n₂) n₃) → (i : Fin n₃) →
            π₁ !! (π₂ !! i) ≡ (π₂ ∘̂ π₁) !! i
    !!⇒∘̂ π₁ π₂ i = 
      begin (
        π₁ !! (π₂ !! i)
              ≡⟨ sym (lookup∘tabulate (λ j → (π₁ !! (π₂ !! j))) i) ⟩
        tabulate (λ i → π₁ !! (π₂ !! i)) !! i
              ≡⟨ refl ⟩
        (π₂ ∘̂ π₁) !! i ∎)
      where open ≡-Reasoning

    -- properties of sequential composition
    0C∘̂0C≡0C : 1C {0} ∘̂ 1C {0} ≡ 1C {0}
    0C∘̂0C≡0C = refl
    
    -- properties of parallel composition
    -- trivial ones first
    1C₀⊎x≡x : ∀ {m n} {x : FinVec m n} → 1C {0} ⊎c x ≡ x
    1C₀⊎x≡x {x = x} = cauchyext x

    unite+∘[0⊎x]≡x∘unite+ : ∀ {m n} {x : FinVec m n} → unite+ ∘̂ (1C {0} ⊎c x) ≡ x ∘̂ unite+
    unite+∘[0⊎x]≡x∘unite+ {m} {n} {x} = finext pf
      where
        pf : (i : Fin n) → (0C ⊎c x) !! (unite+ !! i) ≡ unite+ !! (x !! i)
        pf i = 
          begin (
            tabulate (λ y → x !! y) !! (tabulate id !! i)
              ≡⟨ cong (λ j → tabulate (λ y → x !! y) !! j) (lookup∘tabulate id i) ⟩
            tabulate (λ y → x !! y) !! i
              ≡⟨ lookup∘tabulate (_!!_ x) i ⟩
            x !! i
              ≡⟨ sym (lookup∘tabulate id (x !! i)) ⟩
            tabulate id !! (x !! i) ∎)
          where open ≡-Reasoning
            
    uniti+∘x≡[0⊎x]∘uniti+ : ∀ {m n} {x : FinVec m n} →
      uniti+ ∘̂ x ≡ (1C {0} ⊎c x) ∘̂ uniti+
    uniti+∘x≡[0⊎x]∘uniti+ {m} {n} {x} = finext pf
      where
        pf : (i : Fin n) → x !! (uniti+ !! i) ≡ uniti+ !! ((0C ⊎c x) !! i)
        pf i = begin (
          x !! (tabulate id !! i)
            ≡⟨ cong (_!!_ x) (lookup∘tabulate id i) ⟩
          x !! i
            ≡⟨ sym (lookup∘tabulate (λ y → x !! y) i) ⟩
          tabulate (λ y → x !! y) !! i
            ≡⟨ sym (lookup∘tabulate id _) ⟩
          tabulate id !! (tabulate (λ y → x !! y) !! i) ∎)
          where open ≡-Reasoning

    1C⊎1C≡1C : ∀ {m n} → 1C {m} ⊎c 1C {n} ≡ 1C
    1C⊎1C≡1C {m} {n} = 
      begin (
         tabulate {m} (inject+ n ∘ _!!_ 1C) ++V tabulate {n} (raise m ∘ _!!_ 1C)
           ≡⟨ cong₂ (_++V_ {m = m}) (finext (λ i → cong (inject+ n) (lookup-allFin i))) 
                                      (finext (λ i → cong (raise m) (lookup-allFin i))) ⟩
         tabulate {m} (inject+ n) ++V tabulate {n} (raise m)
           ≡⟨ unSplit {m} id ⟩
         tabulate {m + n} id ∎)
      where open ≡-Reasoning

    1C!!i≡i : ∀ {m} {i : Fin m} → 1C {m} !! i ≡ i
    1C!!i≡i = lookup∘tabulate id _

    unite+∘̂uniti+~id : ∀ {m} → (unite+ {m}) ∘̂ uniti+ ≡ 1C {m}
    unite+∘̂uniti+~id {m} = ~⇒≡ {m} {n = m} (p∘!p≡id {p = plus-unite+ {m}})

    uniti+∘̂unite+~id : ∀ {m} → (uniti+ {m}) ∘̂ unite+ ≡ 1C {m}
    uniti+∘̂unite+~id {m} = ~⇒≡ {m} {n = m} (p∘!p≡id {p = plus-uniti+})

    unite+r∘̂uniti+r~id : ∀ {m} → (unite+r {m}) ∘̂ uniti+r ≡ 1C {m + 0}
    unite+r∘̂uniti+r~id {m} = ~⇒≡ {m} (p∘!p≡id {p = plus-unite+r {m}})

    uniti+r∘̂unite+r~id : ∀ {m} → (uniti+r {m}) ∘̂ unite+r ≡ 1C {m}
    uniti+r∘̂unite+r~id {m} = ~⇒≡ (p∘!p≡id {p = plus-uniti+r})

    assocl+∘̂assocr+~id : ∀ {m n o} → assocl+ {m} {n} {o} ∘̂ assocr+ {m} ≡ 1C
    assocl+∘̂assocr+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = plus-assocl+ {m}})

    assocr+∘̂assocl+~id : ∀ {m n o} → assocr+ {m} {n} {o} ∘̂ assocl+ {m} ≡ 1C
    assocr+∘̂assocl+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = plus-assocr+ {m}})

    swap+-inv : ∀ {m n} → swap+cauchy m n ∘̂ swap+cauchy n m ≡ 1C
    swap+-inv {m} {n} = ~⇒≡ (plus-swap-inv m n)

    idˡ⊕ : ∀ {m n} {x : FinVec m n} → uniti+ ∘̂ (1C {0} ⊎c x) ≡ x ∘̂ uniti+
    idˡ⊕ {m} {n} {x} = finext pf
      where
        open ≡-Reasoning
        pf : (i : Fin n) → (1C {0} ⊎c x) !! (uniti+ !! i) ≡ (uniti+ !! (x !! i))
        pf i =  begin (
          tabulate (λ y → x !! y) !! (tabulate id !! i)
            ≡⟨ cong (_!!_ (tabulate λ y → x !! y)) (lookup∘tabulate id i) ⟩
          (tabulate (λ y → x !! y)) !! i
            ≡⟨ lookup∘tabulate (λ y → x !! y) i ⟩
          x !! i
            ≡⟨ sym (lookup∘tabulate id (x !! i)) ⟩
          tabulate id !! (x !! i) ∎)

    [,]-commute : {A B C D E : Set} → {f : A → C} → {g : B → C} → {h : C → D} →
      ∀ x → h ([ f , g ]′ x) ≡ [ (h ∘ f) , (h ∘ g) ]′ x
    [,]-commute (inj₁ x) = refl
    [,]-commute (inj₂ y) = refl

    -- properties of multiplicative composition
    unite*∘̂uniti*~id : ∀ {m} → (unite* {m}) ∘̂ uniti* ≡ 1C {1 * m}
    unite*∘̂uniti*~id {m} = ~⇒≡ {m} {n = 1 * m} (p∘!p≡id {p = times-unite* {m}})

    uniti*∘̂unite*~id : ∀ {m} → (uniti* {m}) ∘̂ unite* ≡ 1C {m}
    uniti*∘̂unite*~id {m} = ~⇒≡ {1 * m} {n = m} (p∘!p≡id {p = times-uniti* {m}})

    unite*r∘̂uniti*r~id : ∀ {m} → (unite*r {m}) ∘̂ uniti*r ≡ 1C {m * 1}
    unite*r∘̂uniti*r~id {m} = ~⇒≡ {m} {n = m * 1} (p∘!p≡id {p = times-unite*r {m}})

    uniti*r∘̂unite*r~id : ∀ {m} → (uniti*r {m}) ∘̂ unite*r ≡ 1C {m}
    uniti*r∘̂unite*r~id {m} = ~⇒≡ {m * 1} {n = m} (p∘!p≡id {p = times-uniti*r {m}})

    assocl*∘̂assocr*~id : ∀ {m n o} → assocl* {m} {n} {o} ∘̂ assocr* {m} ≡ 1C
    assocl*∘̂assocr*~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = times-assocl* {m}})

    assocr*∘̂assocl*~id : ∀ {m n o} → assocr* {m} {n} {o} ∘̂ assocl* {m} ≡ 1C
    assocr*∘̂assocl*~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = times-assocr* {m}})

    dist*+∘̂factor*+~id : ∀ {m n o} → dist*+ {m} {n} {o} ∘̂ factor*+ {m} ≡ 1C
    dist*+∘̂factor*+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = plustimes-dist {m}})

    factor*+∘̂dist*+~id : ∀ {m n o} → factor*+ {m} {n} {o} ∘̂ dist*+ {m} ≡ 1C
    factor*+∘̂dist*+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = plustimes-factor {m}})

    distl*+∘̂factorl*+~id : ∀ {m n o} → distl*+ {m} {n} {o} ∘̂ factorl*+ {m} ≡ 1C
    distl*+∘̂factorl*+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = plustimes-distl {m}})

    factorl*+∘̂distl*+~id : ∀ {m n o} → factorl*+ {m} {n} {o} ∘̂ distl*+ {m} ≡ 1C
    factorl*+∘̂distl*+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = plustimes-factorl {m}})

    right-zero*l∘̂right-zero*r~id : ∀ {m} → right-zero*l {m} ∘̂ right-zero*r {m} ≡ 1C {m * 0}
    right-zero*l∘̂right-zero*r~id {m} = ~⇒≡ {f = proj₁ (times-factorzr {m})} (p∘!p≡id {p = times-distzr {m}})

    right-zero*r∘̂right-zero*l~id : ∀ {m} → right-zero*r {m} ∘̂ right-zero*l {m} ≡ 1C
    right-zero*r∘̂right-zero*l~id {m} = ~⇒≡ { f = proj₁ (times-factorz {m})} (p∘!p≡id {p = times-distz {m}})

    private
      left⊎⊎!! :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → (p₁ : FinVec m₁ n₁) → (p₂ : FinVec m₂ n₂)
        → (p₃ : FinVec m₃ m₁) → (p₄ : FinVec m₄ m₂) → (i : Fin n₁) → 
        (p₃ ⊎c p₄) !! ( (p₁ ⊎c p₂) !! inject+ n₂ i ) ≡ inject+ m₄ ( (p₁ ∘̂ p₃) !! i) 
      left⊎⊎!! {m₁} {m₂} {_} {m₄} {_} {n₂} p₁ p₂ p₃ p₄ i =
        let pp = p₃ ⊎c p₄ in
        let qq = p₁ ⊎c p₂ in
        begin (
            pp !! (qq !! inject+ n₂ i)
              ≡⟨ cong
                   (_!!_ pp)
                   (lookup-++-inject+
                     (tabulate (inject+ m₂ ∘ _!!_ p₁)) 
                     (tabulate (raise m₁ ∘ _!!_ p₂))
                     i) ⟩ 
           pp !! (tabulate (inject+ m₂ ∘ _!!_ p₁ ) !! i)
              ≡⟨ cong (_!!_ pp) (lookup∘tabulate _ i) ⟩
           pp !! (inject+ m₂ (p₁ !! i))
              ≡⟨ left!! (p₁ !! i) (inject+ m₄ ∘ (_!!_ p₃)) ⟩
            inject+ m₄ (p₃ !! (p₁ !! i))
              ≡⟨ cong (inject+ m₄) (sym (lookup∘tabulate _ i)) ⟩
            inject+ m₄ ((p₁ ∘̂ p₃) !! i) ∎ )
          where open ≡-Reasoning

      right⊎⊎!! :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → (p₁ : FinVec m₁ n₁) → (p₂ : FinVec m₂ n₂)
        → (p₃ : FinVec m₃ m₁) → (p₄ : FinVec m₄ m₂) → (i : Fin n₂) → 
        (p₃ ⊎c p₄) !! ( (p₁ ⊎c p₂) !! raise n₁ i ) ≡ raise m₃ ( (p₂ ∘̂ p₄) !! i) 
      right⊎⊎!! {m₁} {m₂} {m₃} {_} {n₁} {_} p₁ p₂ p₃ p₄ i =
        let pp = p₃ ⊎c p₄ in
        let qq = p₁ ⊎c p₂ in
        begin (
          pp !! (qq !! raise n₁ i)
            ≡⟨ cong
                 (_!!_ pp)
                 (lookup-++-raise
                   (tabulate (inject+ m₂ ∘ _!!_ p₁))
                   (tabulate (raise m₁ ∘ _!!_ p₂))
                   i) ⟩
          pp !! (tabulate (raise m₁ ∘ _!!_ p₂) !! i)
            ≡⟨ cong (_!!_ pp) (lookup∘tabulate _ i) ⟩
          pp !! raise m₁ (p₂ !! i)
            ≡⟨ right!! {m₁} (p₂ !! i) (raise m₃ ∘ (_!!_ p₄)) ⟩
          raise m₃ (p₄ !! (p₂ !! i))
            ≡⟨ cong (raise m₃) (sym (lookup∘tabulate _ i)) ⟩
          raise m₃ ((p₂ ∘̂ p₄) !! i) ∎ )
          where open ≡-Reasoning

    ⊎c-distrib : ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : FinVec m₁ n₁} → {p₂ : FinVec m₂ n₂}
      → {p₃ : FinVec m₃ m₁} → {p₄ : FinVec m₄ m₂} →
        (p₁ ⊎c p₂) ∘̂ (p₃ ⊎c p₄) ≡ (p₁ ∘̂ p₃) ⊎c (p₂ ∘̂ p₄)
    ⊎c-distrib {m₁} {m₂} {m₃} {m₄} {n₁} {n₂} {p₁} {p₂} {p₃} {p₄} =
      let p₃₄ = p₃ ⊎c p₄ in let p₁₂ = p₁ ⊎c p₂ in
      let lhs = λ i → p₃₄ !! (p₁₂ !! i) in
      begin (
        tabulate lhs
          ≡⟨ tabulate-split {n₁} {n₂} ⟩
        tabulate {n₁} (lhs ∘ inject+ n₂) ++V tabulate {n₂} (lhs ∘ raise n₁)
          ≡⟨ cong₂ _++V_ (finext (left⊎⊎!! p₁ _ _ _)) (finext (right⊎⊎!! p₁ _ _ _)) ⟩
        tabulate {n₁} (λ i → inject+ m₄ ((p₁ ∘̂ p₃) !! i)) ++V 
        tabulate {n₂} (λ i → raise m₃ ((p₂ ∘̂ p₄) !! i))
          ≡⟨ refl ⟩
        (p₁ ∘̂ p₃) ⊎c (p₂ ∘̂ p₄) ∎)
        where open ≡-Reasoning

    ------------------------------------------------------------------------------
    -- properties of ×c
    
    private
      concat!! : {A : Set} {m n : ℕ} → (a : Fin m) → (b : Fin n) → (xss : Vec (Vec A n) m) →
        concatV xss !! (times-fwd (a ,′ b)) ≡ (xss !! a) !! b
      concat!! zero b (xs ∷ xss) = lookup-++-inject+ xs (concatV xss) b
      concat!! (suc a) b (xs ∷ xss) = 
        trans (lookup-++-raise xs (concatV xss) (times-fwd (a ,′ b))) (concat!! a b xss) 

      ×c-equiv : {m₁ m₂ n₁ n₂ : ℕ} (p₁ : FinVec m₁ n₁) (p₂ : FinVec m₂ n₂) →
        (p₁ ×c p₂) ≡ concatV (mapV (λ y → mapV times-fwd (mapV (λ x → y ,′ x) p₂)) p₁)
      ×c-equiv p₁ p₂ =
        let zss = mapV  (λ b → mapV (λ x → b ,′ x) p₂) p₁ in
        begin (
          (p₁ ×c p₂)
            ≡⟨ refl ⟩
          mapV times-fwd (concatV zss)
            ≡⟨ sym (concat-map zss times-fwd) ⟩
          concatV (mapV (mapV times-fwd) zss)
            ≡⟨ cong concatV (map-map-map times-fwd (λ b → mapV (λ x → b ,′ x) p₂) p₁) ⟩
           concatV (mapV (λ y → mapV times-fwd (mapV (λ x → y ,′ x) p₂)) p₁) ∎)
          where open ≡-Reasoning

      lookup-2d : {A : Set} (m n : ℕ) → (k : Fin (m * n)) → {f : Fin m × Fin n → A} →
         concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i ,′ j)))) !! k ≡ f (times-bwd k)
      lookup-2d m n k {f} =
        let lhs =  concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i ,′ j)))) in
        let a = proj₁ (times-bwd {m} {n} k) in
        let b = proj₂ (times-bwd {m} {n} k) in
        begin (
          lhs !! k 
            ≡⟨ cong (_!!_ lhs) (sym (times-fwd∘bwd~id {m} k)) ⟩
          lhs !! (times-fwd (a ,′ b))
            ≡⟨ concat!! a b _ ⟩
          (tabulate {m} (λ i → tabulate {n} (λ j → f (i ,′ j))) !! a) !! b
            ≡⟨ cong (λ x → x !! b) (lookup∘tabulate _ a) ⟩
          tabulate {n} (λ j → f (a ,′ j)) !! b
            ≡⟨ lookup∘tabulate _ b ⟩
          f (a ,′ b)
            ≡⟨ refl ⟩
          f (times-bwd k) ∎)
          where open ≡-Reasoning

      ×c!! : {m₁ m₂ n₁ n₂ : ℕ} (p₁ : FinVec m₁ n₁) (p₂ : FinVec m₂ n₂) (k : Fin (n₁ * n₂)) →
        (p₁ ×c p₂) !! k ≡ times-fwd (p₁ !! proj₁ (times-bwd k) ,′ p₂ !! proj₂ (times-bwd {n₁} k))
      ×c!! {n₁ = n₁} p₁ p₂ k =
        let a = proj₁ (times-bwd {n₁} k) in
        let b = proj₂ (times-bwd {n₁} k) in
        begin (
          (p₁ ×c p₂) !! k
            ≡⟨ cong₂ _!!_ (×c-equiv p₁ p₂) (sym (times-fwd∘bwd~id {n₁} k)) ⟩
          concatV (mapV (λ y → mapV times-fwd (mapV (λ x → y ,′ x) p₂)) p₁) !! times-fwd (a ,′ b)
            ≡⟨ concat!! a b _ ⟩
          ((mapV (λ y → mapV times-fwd (mapV (λ x → y ,′ x) p₂)) p₁) !! a) !! b
            ≡⟨ cong (λ x → x !! b) (lookup-map a _ p₁) ⟩
          mapV times-fwd (mapV (λ x → p₁ !! a ,′ x) p₂) !! b
            ≡⟨ cong (λ x → x !! b) (sym (map-∘ times-fwd _ p₂)) ⟩
          mapV (times-fwd ∘ (λ x → p₁ !! a ,′ x)) p₂ !! b
            ≡⟨ lookup-map b _ p₂ ⟩
          times-fwd (p₁ !! a ,′ p₂ !! b) ∎)
          where open ≡-Reasoning

    ×c-distrib : ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : FinVec m₁ n₁} → {p₂ : FinVec m₂ n₂}
      → {p₃ : FinVec m₃ m₁} → {p₄ : FinVec m₄ m₂} →
        (p₁ ×c p₂) ∘̂ (p₃ ×c p₄) ≡ (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄)
    ×c-distrib {m₁} {m₂} {m₃} {m₄} {n₁} {n₂} {p₁} {p₂} {p₃} {p₄} =
      let p₃₄ = p₃ ×c p₄ in let p₁₂ = p₁ ×c p₂ in
      let p₂₄ = p₂ ∘̂ p₄ in let p₁₃ = p₁ ∘̂ p₃ in
      let lhs = λ i → p₃₄ !! (p₁₂ !! i) in
      let zss = mapV  (λ b → mapV (λ x → b ,′ x) (p₂ ∘̂ p₄)) (p₁ ∘̂ p₃) in
      begin (
         tabulate {n₁ * n₂} (λ i → p₃₄ !! (p₁₂ !! i))
           ≡⟨ finext (λ j → cong (_!!_ p₃₄) (×c!! p₁ p₂ j)) ⟩
         tabulate {n₁ * n₂}
           (λ i → p₃₄ !! times-fwd (p₁ !! proj₁ (times-bwd i) ,′ p₂ !! proj₂ (times-bwd i)))
           ≡⟨ finext (λ j → ×c!! p₃ p₄ _) ⟩
         tabulate (λ i →
           let k = times-fwd (p₁ !! proj₁ (times-bwd i) ,′ p₂ !! proj₂ (times-bwd i)) in
           times-fwd (p₃ !! proj₁ (times-bwd k) ,′ p₄ !! proj₂ (times-bwd k)))
           ≡⟨ finext (λ i → cong₂ (λ x y → times-fwd (p₃ !! proj₁ x ,′ p₄ !! proj₂ y))
                     (times-bwd∘fwd~id {m₁} {m₂} (p₁ !! proj₁ (times-bwd i) ,′ _))
                     (times-bwd∘fwd~id (_ ,′ p₂ !! proj₂ (times-bwd i)))) ⟩
         tabulate (λ i → times-fwd (p₃ !! (p₁ !! proj₁ (times-bwd i)) ,′
                                    (p₄ !! (p₂ !! proj₂ (times-bwd i)))))
           ≡⟨ finext (λ k → sym (lookup-2d n₁ n₂ k)) ⟩
         tabulate (λ k →
           concatV (tabulate {n₁} (λ z →
                    tabulate {n₂} (λ w →
                    times-fwd ((p₃ !! (p₁ !! z)) ,′ (p₄ !! (p₂ !! w))))))
           !! k)

           ≡⟨ tabulate∘lookup _ ⟩
         concatV (tabulate {n₁} (λ z →
                  tabulate {n₂} (λ w →
                  times-fwd ((p₃ !! (p₁ !! z)) ,′ (p₄ !! (p₂ !! w))))))
           ≡⟨ cong
               concatV
               (finext (λ i →
                 tabulate-∘ times-fwd (λ w → ((p₃ !! (p₁ !! i)) ,′ (p₄ !! (p₂ !! w)))) )) ⟩
         concatV (tabulate (λ z →
                  mapV times-fwd (tabulate (λ w → (p₃ !! (p₁ !! z)) ,′ (p₄ !! (p₂ !! w))))))
           ≡⟨ cong
               concatV
               (finext (λ i →
                 cong
                   (mapV times-fwd)
                   (tabulate-∘ (λ x → (p₃ !! (p₁ !! i)) ,′ x) (_!!_ p₄ ∘ _!!_ p₂)))) ⟩
         concatV (tabulate (λ z → mapV times-fwd (mapV (λ x → (p₃ !! (p₁ !! z)) ,′ x) p₂₄)))
           ≡⟨ cong concatV (tabulate-∘ _ (_!!_ p₃ ∘ _!!_ p₁)) ⟩
         concatV (mapV (λ y → mapV times-fwd (mapV (λ x → y ,′ x) p₂₄)) p₁₃)
           ≡⟨ sym (×c-equiv p₁₃ p₂₄) ⟩
         (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄) ∎)
         where open ≡-Reasoning

    -- there might be a simpler proofs of this using tablate∘lookup right
    -- at the start.

    1C×1C≡1C : ∀ {m n} → (1C {m} ×c 1C {n}) ≡ 1C {m * n}
    1C×1C≡1C {m} {n} = 
      begin (
        1C {m} ×c 1C
          ≡⟨ ×c-equiv 1C 1C ⟩
        concatV (mapV (λ y → mapV times-fwd (mapV (_,′_ y) (1C {n}))) (1C {m}))
          ≡⟨ cong (concatV {n = m}) (sym (tabulate-∘ _ id)) ⟩
        concatV {n = m} (tabulate (λ y → mapV times-fwd (mapV (_,′_ y) (1C {n}))))
          ≡⟨ cong (concatV {n = m}) (finext (λ y → sym (map-∘ times-fwd (λ x → y ,′ x) 1C))) ⟩
        concatV (tabulate {n = m} (λ y → mapV (times-fwd ∘ (_,′_ y)) (1C {n})))
          ≡⟨ cong
              (concatV {m = n} {m})
              (finext (λ y → sym (tabulate-∘ (times-fwd ∘ (_,′_ y)) id))) ⟩
        concatV (tabulate {n = m} (λ a → tabulate {n = n} (λ b → times-fwd (a ,′ b))))
          ≡⟨ sym (tabulate∘lookup _) ⟩
        tabulate (λ k →
        concatV (tabulate {n = m} (λ a → tabulate {n = n} (λ b → times-fwd (a ,′ b)))) !! k)
          ≡⟨ finext (λ k → lookup-2d m n k) ⟩
        tabulate (λ k → times-fwd {m} {n} (times-bwd k))
          ≡⟨ finext (times-fwd∘bwd~id {m} {n}) ⟩
        1C {m * n} ∎ )
        where open ≡-Reasoning        

    swap*-inv : ∀ {m n} → swap⋆cauchy m n ∘̂ swap⋆cauchy n m ≡ 1C
    swap*-inv {m} {n} = ~⇒≡ (times-swap-inv m n)

    ------------------------
    -- A few "reveal" functions, to let us peek into the representation
    reveal1C : ∀ {m} → allFin m ≡ 1C
    reveal1C = refl

    reveal0C : [] ≡ 1C {0}
    reveal0C = refl

    reveal⊎c :  ∀ {m₁ n₁ m₂ n₂} → {α : FinVec m₁ m₂} → {β : FinVec n₁ n₂} →
      α ⊎c β ≡
        tabulate (fwd ∘ inj₁ ∘ _!!_ α) ++V
        tabulate (fwd {m₁} ∘ inj₂ ∘ _!!_ β)
    reveal⊎c = refl
    
------------------------------------------------------------------------------
-- Commutative semiring structure

open F

_cauchy≃_ : (m n : ℕ) → Set
m cauchy≃ n = FinVec m n

id-iso : {m : ℕ} → FinVec m m
id-iso = 1C

private
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
{--
-- Groupoid structure

private
  postulate linv : {m n : ℕ} (c : FinVec m n) → (sym-iso c) ∘̂ c ≡ 1C
  postulate rinv : {m n : ℕ} (c : FinVec m n) → c ∘̂ (sym-iso c) ≡ 1C

G : 1Groupoid
G = record {
  set = ℕ ; 
  _↝_ = _cauchy≃_ ; 
  _≈_ = _≡_ ; 
  id  = id-iso ;
  _∘_ = λ c₁ c₂ → trans-iso c₂ c₁ ; 
  _⁻¹ = sym-iso ; 
  lneutr = ∘̂-lid ; 
  rneutr = ∘̂-rid ; 
  assoc  = λ c₁ c₂ c₃ → sym (∘̂-assoc c₁ c₂ c₃) ; 
  equiv = record { 
            refl  = refl ; 
            sym   = sym ; 
            trans = trans 
          } ;
  linv = linv ; 
  rinv = rinv ; 
  ∘-resp-≈ = cong₂ _∘̂_ 
  }
--}
------------------------------------------------------------------------------
