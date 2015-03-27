{-# OPTIONS --without-K #-}

-- From nlab: FinSet is the category of finite sets and all functions
-- between them: the full subcategory of Set on finite sets. It is
-- easy (and thus common) to make FinSet skeletal; there is one object
-- for each natural number n (including n=0), and a morphism from m to
-- n is an m-tuple (f0,…,fm−1) of numbers satisfying 0≤fi<n. This
-- amounts to identifying n with the set {0,…,n−1}. (Sometimes {1,…,n}
-- is used instead.) This is exactly what we do below.

module SkFinSetCategory where

open import Data.Nat
open import Data.Vec renaming (map to mapV; _++_ to _++V_; concat to concatV)
open import Data.Fin using (Fin; inject+; raise; zero; suc)
open import Function using (_∘_; id)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Equiv using (p∘!p≡id)
open import TypeEquiv using (swap₊; swap⋆)
open import VectorLemmas using (_!!_; concat-map; map-map-map; lookup-map; map-∘)
open import FinEquiv using (module Plus; module Times; module PlusTimes)

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
-- Cauchy Representation Vec (Fin m) n without checks of uniqueness
-- and completeness

-- We need to define (at least) 0, 1, +, *, ∘, swap+, swap*

module F where

  open import Data.Vec.Properties
    using (lookup-allFin; tabulate∘lookup; lookup∘tabulate; tabulate-∘; lookup-++-inject+)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
  open ≡-Reasoning

  open import FiniteFunctions
  open import Equiv using (_∼_)
  open import VectorLemmas
    using (lookupassoc; map-++-commute; tabulate-split; left!!; right!!;
           lookup-++-raise; unSplit)
  open import Proofs using (congD!)

  open V

  -- convenient abbreviations
  FinVec : ℕ → ℕ → Set
  FinVec m n = Vec (Fin m) n

  private
    fwd : {m n : ℕ} → (Fin m ⊎ Fin n) → Fin (m + n)
    fwd = proj₁ Plus.fwd-iso

  -- principal component of the identity permutation  
  1C : {n : ℕ} → FinVec n n
  1C {n} = allFin n

  -- corresponds to ⊥ ≃ (⊥ × A) and other impossibilities
  0C : FinVec 0 0
  0C = 0v

  -- Sequential composition
  _∘̂_ : {n₀ n₁ n₂ : ℕ} → Vec (Fin n₁) n₀ → Vec (Fin n₂) n₁ → Vec (Fin n₂) n₀
  π₁ ∘̂ π₂ = tabulate (_!!_ π₂ ∘ _!!_ π₁)

  -- swap the first m elements with the last n elements
  -- [ v₀ , v₁   , v₂   , ... , vm-1 ,     vm , vm₊₁ , ... , vm+n-1 ]
  -- ==>
  -- [ vm , vm₊₁ , ... , vm+n-1 ,     v₀ , v₁   , v₂   , ... , vm-1 ]

  swap+cauchy : (m n : ℕ) → FinVec (n + m) (m + n)
  swap+cauchy m n = tabulate (Plus.swapper m n)

  -- Parallel additive composition
  -- conceptually, what we want is
  _⊎c'_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ + n₁) (m₂ + n₂)
  _⊎c'_ α β = mapV fwd (α ⊎v β)
  -- but the above is tedious to work with.  Instead, inline a bit to get
  _⊎c_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ + n₁) (m₂ + n₂)
  _⊎c_ {m₁} α β = tabulate (fwd ∘ inj₁ ∘ _!!_ α) ++V
                                                       tabulate (fwd {m₁} ∘ inj₂ ∘ _!!_ β)
  -- see ⊎c≡⊎c' lemma below

  -- Tensor multiplicative composition
  -- Transpositions in α correspond to swapping entire rows
  -- Transpositions in β correspond to swapping entire columns
  _×c_ : ∀ {m₁ n₁ m₂ n₂} → FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ * n₁) (m₂ * n₂)
  α ×c β = mapV Times.fwd (α ×v β)

  -- swap⋆
  -- 
  -- This is essentially the classical problem of in-place matrix transpose:
  -- "http://en.wikipedia.org/wiki/In-place_matrix_transposition"
  -- Given m and n, the desired permutation in FinVec representation is:
  -- P(i) = m*n-1 if i=m*n-1
  --      = m*i mod m*n-1 otherwise

  -- transposeIndex : {m n : ℕ} → Fin m × Fin n → Fin (n * m)
  -- transposeIndex = Times.fwd ∘ swap
    -- inject≤ (fromℕ (toℕ d * m + toℕ b)) (i*n+k≤m*n d b)

  swap⋆cauchy : (m n : ℕ) → FinVec (n * m) (m * n)
  swap⋆cauchy m n = tabulate (Times.swapper m n)
    -- mapV transposeIndex (V.tcomp 1C 1C)

  -------------------------------------------------------------------------------------------
  -- Things which are the foundations of other permutations, but coming
  -- from properties, rather than being operators

  unite+ : {m : ℕ} → FinVec m (0 + m) 
  unite+ {m} = 1C

  uniti+ : {m : ℕ} → FinVec (0 + m) m
  uniti+ {m} = 1C

  assocl+ : {m n o : ℕ} → FinVec  ((m + n) + o) (m + (n + o))
  assocl+ {m} {n} {o} = tabulate (proj₁ (Plus.assocl+ {m} {n} {o}))

  assocr+ : {m n o : ℕ} → FinVec  (m + (n + o)) (m + n + o)
  assocr+ {m} {n} {o} = tabulate (proj₁ (Plus.assocr+ {m} {n} {o}))

  unite* : {m : ℕ} → FinVec m (1 * m)
  unite* {m} = tabulate (proj₁ (Times.unite* {m}))

  uniti* : {m : ℕ} → FinVec (1 * m) m
  uniti* {m} = tabulate (proj₁ (Times.uniti* {m}))

  assocl* : {m n o : ℕ} → FinVec  ((m * n) * o) (m * (n * o))
  assocl* {m} {n} {o} = tabulate (proj₁ (Times.assocl* {m} {n} {o}))

  assocr* : {m n o : ℕ} → FinVec  (m * (n * o)) (m * n * o)
  assocr* {m} {n} {o} = tabulate (proj₁ (Times.assocr* {m} {n} {o}))

  dist*+ : ∀ {m n o} → FinVec (m * o + n * o) ((m + n) * o)
  dist*+ {m} {n} {o} = tabulate (proj₁ (PlusTimes.dist {m} {n} {o}))

  factor*+ : ∀ {m n o} → FinVec ((m + n) * o) (m * o + n * o)
  factor*+ {m} {n} {o} = tabulate (proj₁ (PlusTimes.factor {m} {n} {o}))

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

  -- this is just tabulate∘lookup, but it hides the details
  permext : {m n : ℕ} (π : FinVec m n) → tabulate (_!!_ π) ≡ π
  permext π = tabulate∘lookup π

  -- we could go through ~p, but this works better in practice
  ~⇒≡ : {m n o : ℕ} {f : Fin m → Fin n} {g : Fin n → Fin m} → 
             (f ∘ g ∼ id) → (tabulate g ∘̂ tabulate f ≡ 1C)
  ~⇒≡ {f = f} {g} β = ∼p⇒≡ (λ i → trans (∘̂⇒∘ g f i) (cong (λ x → x !! i) (finext β)))

  -- properties of sequential composition
  ∘̂-assoc : {m₁ m₂ m₃ m₄ : ℕ} →
           (a : Vec (Fin m₂) m₁) (b : Vec (Fin m₃) m₂) (c : Vec (Fin m₄) m₃) → 
           a ∘̂ (b ∘̂ c) ≡ (a ∘̂ b) ∘̂ c
  ∘̂-assoc a b c = finext (lookupassoc a b c)

  ∘̂-rid : {m n : ℕ} → (π : Vec (Fin m) n) → π ∘̂ 1C ≡ π
  ∘̂-rid π = trans (finext (λ i → lookup-allFin (π !! i))) (permext π)

  ∘̂-lid : {m n : ℕ} → (π : Vec (Fin m) n) → 1C ∘̂ π ≡ π
  ∘̂-lid π = trans (finext (λ i → cong (_!!_ π) (lookup-allFin i))) (permext π)

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

  -- properties of parallel composition
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

  assocl+∘̂assocr+~id : ∀ {m n o} → assocl+ {m} {n} {o} ∘̂ assocr+ {m} ≡ 1C
  assocl+∘̂assocr+~id {m} {_} {o} = ~⇒≡ {o = o} (p∘!p≡id {p = Plus.assocl+ {m}})
  
  assocr+∘̂assocl+~id : ∀ {m n o} → assocr+ {m} {n} {o} ∘̂ assocl+ {m} ≡ 1C
  assocr+∘̂assocl+~id {m} {_} {o} = ~⇒≡ {o = o} (p∘!p≡id {p = Plus.assocr+ {m}})

  swap+-inv : ∀ {m n} → swap+cauchy m n ∘̂ swap+cauchy n m ≡ 1C
  swap+-inv {m} {n} = ~⇒≡ {o = m + n} (Plus.swap-inv m n)

  unite*∘̂uniti*~id : ∀ {m} → (unite* {m}) ∘̂ uniti* ≡ 1C {1 * m}
  unite*∘̂uniti*~id {m} = ~⇒≡ {m} {n = 1 * m} {o = 1 * m} (p∘!p≡id {p = Times.unite* {m}})
   
  uniti*∘̂unite*~id : ∀ {m} → (uniti* {m}) ∘̂ unite* ≡ 1C {m}
  uniti*∘̂unite*~id {m} = ~⇒≡ {1 * m} {n = m} {o = 1 * m} (p∘!p≡id {p = Times.uniti* {m}})
   
  assocl*∘̂assocr*~id : ∀ {m n o} → assocl* {m} {n} {o} ∘̂ assocr* {m} ≡ 1C
  assocl*∘̂assocr*~id {m} {_} {o} = ~⇒≡ {o = o} (p∘!p≡id {p = Times.assocl* {m}})
  
  assocr*∘̂assocl*~id : ∀ {m n o} → assocr* {m} {n} {o} ∘̂ assocl* {m} ≡ 1C
  assocr*∘̂assocl*~id {m} {_} {o} = ~⇒≡ {o = o} (p∘!p≡id {p = Times.assocr* {m}})

  dist*+∘̂factor*+~id : ∀ {m n o} → dist*+ {m} {n} {o} ∘̂ factor*+ {m} ≡ 1C
  dist*+∘̂factor*+~id {m} {_} {o} = ~⇒≡ {o = o} (p∘!p≡id {p = PlusTimes.dist {m}})

  factor*+∘̂dist*+~id : ∀ {m n o} → factor*+ {m} {n} {o} ∘̂ dist*+ {m} ≡ 1C
  factor*+∘̂dist*+~id {m} {_} {o} = ~⇒≡ {o = o} (p∘!p≡id {p = PlusTimes.factor {m}})

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

  private
    concat!! : {A : Set} {m n : ℕ} → (a : Fin m) → (b : Fin n) → (xss : Vec (Vec A n) m) →
      concatV xss !! (Times.fwd (a , b)) ≡ (xss !! a) !! b
    concat!! zero b (xs ∷ xss) = lookup-++-inject+ xs (concatV xss) b
    concat!! (suc a) b (xs ∷ xss) = 
      trans (lookup-++-raise xs (concatV xss) (Times.fwd (a , b))) (concat!! a b xss) 

    ×c-equiv : {m₁ m₂ n₁ n₂ : ℕ} (p₁ : FinVec m₁ n₁) (p₂ : FinVec m₂ n₂) →
      (p₁ ×c p₂) ≡ concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y , x) p₂)) p₁)
    ×c-equiv p₁ p₂ =
      let zss = mapV  (λ b → mapV (λ x → b , x) p₂) p₁ in
      begin (
        (p₁ ×c p₂)
          ≡⟨ refl ⟩
        mapV Times.fwd (concatV zss)
          ≡⟨ sym (concat-map zss Times.fwd) ⟩
        concatV (mapV (mapV Times.fwd) zss)
          ≡⟨ cong concatV (map-map-map Times.fwd (λ b → mapV (λ x → b , x) p₂) p₁) ⟩
         concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y , x) p₂)) p₁) ∎)

    lookup-2d : {A : Set} (m n : ℕ) → (k : Fin (m * n)) → {f : Fin m × Fin n → A} →
       concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j)))) !! k ≡ f (Times.bwd k)
    lookup-2d m n k {f} =
      let lhs =  concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j)))) in
      let (a , b) = Times.bwd {m} {n} k in
      begin (
        lhs !! k 
          ≡⟨ cong (_!!_ lhs) (sym (Times.fwd∘bwd~id {m} k)) ⟩
        lhs !! (Times.fwd (a , b))
          ≡⟨ concat!! a b _ ⟩
        (tabulate {m} (λ i → tabulate {n} (λ j → f (i , j))) !! a) !! b
          ≡⟨ cong (λ x → x !! b) (lookup∘tabulate _ a) ⟩
        tabulate {n} (λ j → f (a , j)) !! b
          ≡⟨ lookup∘tabulate _ b ⟩
        f (a , b)
          ≡⟨ refl ⟩
        f (Times.bwd k) ∎)
        
    ×c!! : {m₁ m₂ n₁ n₂ : ℕ} (p₁ : FinVec m₁ n₁) (p₂ : FinVec m₂ n₂) (k : Fin (n₁ * n₂)) →
      (p₁ ×c p₂) !! k ≡ Times.fwd (p₁ !! proj₁ (Times.bwd k) , p₂ !! proj₂ (Times.bwd k))
    ×c!! {n₁ = n₁} p₁ p₂ k =
      let (a , b) = Times.bwd {n₁} k in
      begin (
        (p₁ ×c p₂) !! k
          ≡⟨ cong₂ _!!_ (×c-equiv p₁ p₂) (sym (Times.fwd∘bwd~id {n₁} k)) ⟩
        concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y , x) p₂)) p₁) !! Times.fwd (a , b)
          ≡⟨ concat!! a b _ ⟩
        ((mapV (λ y → mapV Times.fwd (mapV (λ x → y , x) p₂)) p₁) !! a) !! b
          ≡⟨ cong (λ x → x !! b) (lookup-map a _ p₁) ⟩
        mapV Times.fwd (mapV (λ x → p₁ !! a , x) p₂) !! b
          ≡⟨ cong (λ x → x !! b) (sym (map-∘ Times.fwd _ p₂)) ⟩
        mapV (Times.fwd ∘ (λ x → p₁ !! a , x)) p₂ !! b
          ≡⟨ lookup-map b _ p₂ ⟩
        Times.fwd (p₁ !! a , p₂ !! b) ∎)
    
  ×c-distrib : ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : FinVec m₁ n₁} → {p₂ : FinVec m₂ n₂}
    → {p₃ : FinVec m₃ m₁} → {p₄ : FinVec m₄ m₂} →
      (p₁ ×c p₂) ∘̂ (p₃ ×c p₄) ≡ (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄)
  ×c-distrib {m₁} {m₂} {m₃} {m₄} {n₁} {n₂} {p₁} {p₂} {p₃} {p₄} =
    let p₃₄ = p₃ ×c p₄ in let p₁₂ = p₁ ×c p₂ in
    let p₂₄ = p₂ ∘̂ p₄ in let p₁₃ = p₁ ∘̂ p₃ in
    let lhs = λ i → p₃₄ !! (p₁₂ !! i) in
    let zss = mapV  (λ b → mapV (λ x → b , x) (p₂ ∘̂ p₄)) (p₁ ∘̂ p₃) in
    begin (
       tabulate {n₁ * n₂} (λ i → p₃₄ !! (p₁₂ !! i))
         ≡⟨ finext (λ j → cong (_!!_ p₃₄) (×c!! p₁ p₂ j)) ⟩
       tabulate {n₁ * n₂}
         (λ i → p₃₄ !! Times.fwd (p₁ !! proj₁ (Times.bwd i) , p₂ !! proj₂ (Times.bwd i)))
         ≡⟨ finext (λ j → ×c!! p₃ p₄ _) ⟩
       tabulate (λ i →
         let k = Times.fwd (p₁ !! proj₁ (Times.bwd i) , p₂ !! proj₂ (Times.bwd i)) in
         Times.fwd (p₃ !! proj₁ (Times.bwd k) , p₄ !! proj₂ (Times.bwd k)))
         ≡⟨ finext (λ i → cong₂ (λ x y → Times.fwd (p₃ !! proj₁ x , p₄ !! proj₂ y))
                   (Times.bwd∘fwd~id {m₁} {m₂} (p₁ !! proj₁ (Times.bwd i) , _))
                   (Times.bwd∘fwd~id (_ , p₂ !! proj₂ (Times.bwd i)))) ⟩
       tabulate (λ i → Times.fwd (p₃ !! (p₁ !! proj₁ (Times.bwd i)) ,
                                  (p₄ !! (p₂ !! proj₂ (Times.bwd i)))))
         ≡⟨ finext (λ k → sym (lookup-2d n₁ n₂ k)) ⟩
       tabulate (λ k →
         concatV (tabulate {n₁} (λ z →
                  tabulate {n₂} (λ w →
                  Times.fwd ((p₃ !! (p₁ !! z)) , (p₄ !! (p₂ !! w))))))
         !! k)
                           
         ≡⟨ tabulate∘lookup _ ⟩
       concatV (tabulate {n₁} (λ z →
                tabulate {n₂} (λ w →
                Times.fwd ((p₃ !! (p₁ !! z)) , (p₄ !! (p₂ !! w))))))
         ≡⟨ cong
             concatV
             (finext (λ i →
               tabulate-∘ Times.fwd (λ w → ((p₃ !! (p₁ !! i)) , (p₄ !! (p₂ !! w)))) )) ⟩
       concatV (tabulate (λ z →
                mapV Times.fwd (tabulate (λ w → (p₃ !! (p₁ !! z)) , (p₄ !! (p₂ !! w))))))
         ≡⟨ cong
             concatV
             (finext (λ i →
               cong
                 (mapV Times.fwd)
                 (tabulate-∘ (λ x → (p₃ !! (p₁ !! i)) , x) (_!!_ p₄ ∘ _!!_ p₂)))) ⟩
       concatV (tabulate (λ z → mapV Times.fwd (mapV (λ x → (p₃ !! (p₁ !! z)) , x) p₂₄)))
         ≡⟨ cong concatV (tabulate-∘ _ (_!!_ p₃ ∘ _!!_ p₁)) ⟩
       concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y , x) p₂₄)) p₁₃)
         ≡⟨ sym (×c-equiv p₁₃ p₂₄) ⟩
       (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄) ∎)

  -- there might be a simpler proofs of this using tablate∘lookup right
  -- at the start.

  1C×1C≡1C : ∀ {m n} → (1C {m} ×c 1C {n}) ≡ 1C {m * n}
  1C×1C≡1C {m} {n} = 
    begin (
      1C {m} ×c 1C
        ≡⟨ ×c-equiv 1C 1C ⟩
      concatV (mapV (λ y → mapV Times.fwd (mapV (_,_ y) (1C {n}))) (1C {m}))
        ≡⟨ cong (concatV {n = m}) (sym (tabulate-∘ _ id)) ⟩
      concatV {n = m} (tabulate (λ y → mapV Times.fwd (mapV (_,_ y) (1C {n}))))
        ≡⟨ cong (concatV {n = m}) (finext (λ y → sym (map-∘ Times.fwd (λ x → y , x) 1C))) ⟩
      concatV (tabulate {n = m} (λ y → mapV (Times.fwd ∘ (_,_ y)) (1C {n})))
        ≡⟨ cong
            (concatV {m = n} {m})
            (finext (λ y → sym (tabulate-∘ (Times.fwd ∘ (_,_ y)) id))) ⟩
      concatV (tabulate {n = m} (λ a → tabulate {n = n} (λ b → Times.fwd (a , b))))
        ≡⟨ sym (tabulate∘lookup _) ⟩
      tabulate (λ k →
      concatV (tabulate {n = m} (λ a → tabulate {n = n} (λ b → Times.fwd (a , b)))) !! k)
        ≡⟨ finext (λ k → lookup-2d m n k) ⟩
      tabulate (λ k → Times.fwd {m} {n} (Times.bwd k))
        ≡⟨ finext (Times.fwd∘bwd~id {m} {n}) ⟩
      1C {m * n} ∎ )

  swap*-inv : ∀ {m n} → swap⋆cauchy m n ∘̂ swap⋆cauchy n m ≡ 1C
  swap*-inv {m} {n} = ~⇒≡ {o = m * n} (Times.swap-inv m n)
  
------------------------------------------------------------------------------
-- Categorical structure

import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)
open import Relation.Binary.PropositionalEquality.Core using (isEquivalence)

open import Categories.Category using (Category; module Category)
open import Categories.Functor using (Functor; module Functor)
open import Categories.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation using () renaming (id to idn)
open import Categories.Monoidal using (Monoidal)
open import Categories.Monoidal.Helpers using (module MonoidalHelperFunctors)
open import Categories.Monoidal.Braided using (Braided; module Braided) 

open import SymmetricMonoidalCategory

open F

-- Objects are natural numbers which are proxies for finite sets of
-- the given size; morphisms between m and n are finite functions, Vec
-- (Fin n) m, mapping each element of Fin m to an element in Fin
-- n. Two morphisms are considered the same if they are ≡ to each other.

finVecC : Category Level.zero Level.zero Level.zero
finVecC = record {
  Obj       = ℕ ;
  _⇒_       = FinVec ;
  _≡_       = _≡_ ;
  id        = 1C ; 
  _∘_       = _∘̂_ ;
  assoc     = λ { {f = f} {g = g} {h = h} → sym (∘̂-assoc h g f) } ;
  identityˡ = λ { {f = f} → ∘̂-lid f } ;
  identityʳ = λ { {f = f} → ∘̂-rid f } ;
  equiv     = isEquivalence ; 
  ∘-resp-≡  = cong₂ _∘̂_ 
  }

⊕-bifunctor : Bifunctor finVecC finVecC finVecC
⊕-bifunctor = record { 
  F₀           = λ { (m , n) → m + n } ;
  F₁           = λ { (f , g) →  f ⊎c g } ; 
  identity     = λ { { (m , n) } → 1C⊎1C≡1C {m} {n} } ;
  homomorphism = λ { {(x₁ , x₂)} {(y₁ , y₂)} {(z₁ , z₂)} {(x₁y₁ , x₂y₂)} {(y₁z₁ , y₂z₂)} →
                   sym (⊎c-distrib {p₁ = y₁z₁} {p₂ = y₂z₂} {p₃ = x₁y₁} {p₄ = x₂y₂}) } ;
  F-resp-≡     = λ { {(x₁ , x₂)} {(y₁ , y₂)} {(p₁ , p₂)} {(p₃ , p₄)} (p₁≡p₃ , p₂≡p₄) →
                   cong₂ _⊎c_ p₁≡p₃ p₂≡p₄ } 
  }

⊗-bifunctor : Bifunctor finVecC finVecC finVecC
⊗-bifunctor = record { 
  F₀           = λ { (m , n) → m * n } ;
  F₁           = λ { (f , g) →  f ×c g } ; 
  identity     = λ { { (m , n) } → 1C×1C≡1C {m} {n} } ;
  homomorphism = λ { {(x₁ , x₂)} {(y₁ , y₂)} {(z₁ , z₂)} {(x₁y₁ , x₂y₂)} {(y₁z₁ , y₂z₂)} →
                   sym (×c-distrib {p₁ = y₁z₁} {p₂ = y₂z₂} {p₃ = x₁y₁} {p₄ = x₂y₂}) } ;
  F-resp-≡     = λ { {(x₁ , x₂)} {(y₁ , y₂)} {(p₁ , p₂)} {(p₃ , p₄)} (p₁≡p₃ , p₂≡p₄) →
                   cong₂ _×c_ p₁≡p₃ p₂≡p₄ } 
  }

{-- 
CommutativeSquare f g h i = h ∘ f ≡ i ∘ g

Functor (C D): 
  F₀           : C.Obj → D.Obj
  F₁           : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]
  identity     : ∀ {A} → D [ F₁ (C.id {A}) ≡ D.id ]
  homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                  → D [ F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ] ]
  F-resp-≡     : ∀ {A B} {F G : C [ A , B ]} → C [ F ≡ G ] → D [ F₁ F ≡ F₁ G ]

NaturalTransformation (F G : Functor C D):
  η       : ∀ X → D [ F₀ X , G₀ X ]
  commute : ∀ {X Y} (f : C [ X , Y ]) → D.CommutativeSquare (F₁ f) (η X) (η Y) (G₁ f)

NaturalIsomorphism (F G : Functor C D):
  F⇒G  : NaturalTransformation F G
  F⇐G  : NaturalTransformation G F
  iso  : ∀ X → Iso (⇒.η X) (⇐.η X)

Monoidal (C : Category):
  identityˡ : NaturalIsomorphism id⊗x x
  identityʳ : NaturalIsomorphism x⊗id x
  assoc     : NaturalIsomorphism [x⊗y]⊗z x⊗[y⊗z]
  triangle  : TriangleLeftSide ≡ⁿ (TriangleRightSide ∘₁ TriangleTopSide)
  pentagon  : (PentagonNESide ∘₁ PentagonNWSide) ≡ⁿ 
              (PentagonSESide ∘₁ (PentagonSSide ∘₁ PentagonSWSide))
--}

finVecAdditiveM : Monoidal finVecC -- power = Fin 1 (so apply everything to zero)
finVecAdditiveM = record {
  ⊗  = ⊕-bifunctor ; 
  id = 0 ;
  identityˡ = record {
    F⇒G = record { 
      η       = λ _ → uniti+ ; 
      commute = λ f → 
                  trans (∘̂-lid (FF.F₁ f)) (trans {!!} (sym (∘̂-rid (GF.F₁ f))))
    } ;
    F⇐G = record { 
      η       = λ _ → unite+ ;
      commute = {!!} 
    } ;
    iso = {!!}
  } ;
  identityʳ = record {
    F⇒G = record { 
      η       = λ X → swap+cauchy 0 (X zero) ; 
      commute = {!!} 
    } ;
    F⇐G = record { 
      η       = λ X → swap+cauchy (X zero) 0 ; 
      commute = {!!} 
    } ;
    iso = {!!}
  } ;
  assoc = {!!} ;
  triangle = {!!} ;
  pentagon = {!!} 
  }
  where
  private module MFunctors = MonoidalHelperFunctors finVecC ⊕-bifunctor 0
  private module FF = Functor MFunctors.id⊗x
  private module GF = Functor MFunctors.x
  
                                           
{--
-- Commutative semiring structure

import Level
open import Algebra
open import Algebra.Structures
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (subst; sym; trans; cong₂)

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
-- Groupoid structure

open import Groupoid

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
