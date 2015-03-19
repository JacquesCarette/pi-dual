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
open import Data.Fin using (Fin; inject+; raise; zero; suc)
open import Function using (_∘_; id)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_;proj₁)

open import Equiv using (p∘!p≡id)
open import TypeEquivalences using (swap₊; swap⋆)
open import VectorLemmas using (_!!_; concat-map; map-map-map)
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
  open import FiniteFunctions
  open import Equiv using (_∼_)
  open import VectorLemmas using (lookupassoc; map-++-commute; 
    tabulate-split; left!!; right!!; lookup-++-raise; unSplit)
  open import Proofs using (congD!)
  open import Data.Vec.Properties using (lookup-allFin; tabulate∘lookup; 
    lookup∘tabulate; tabulate-∘; lookup-++-inject+)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; 
    cong; cong₂; module ≡-Reasoning)
  open ≡-Reasoning

  open V

  -- convenient abbreviations
  Cauchy : ℕ → ℕ → Set
  Cauchy m n = Vec (Fin m) n

  private
    fwd : {m n : ℕ} → (Fin m ⊎ Fin n) → Fin (m + n)
    fwd = proj₁ Plus.fwd-iso

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
  _⊎c'_ α β = mapV fwd (α ⊎v β)
  -- but the above is tedious to work with.  Instead, inline a bit to get
  _⊎c_ : ∀ {m₁ n₁ m₂ n₂} → Cauchy m₁ m₂ → Cauchy n₁ n₂ → Cauchy (m₁ + n₁) (m₂ + n₂)
  _⊎c_ {m₁} α β = tabulate (fwd ∘ inj₁ ∘ _!!_ α) ++V
                                                       tabulate (fwd {m₁} ∘ inj₂ ∘ _!!_ β)
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
  -- Things which are the foundations of other permutations, but coming
  -- from properties, rather than being operators

  assocl+ : {m n o : ℕ} → Cauchy  ((m + n) + o) (m + (n + o))
  assocl+ {m} {n} {o} = tabulate (proj₁ (Plus.assocl+ {m} {n} {o}))

  assocr+ : {m n o : ℕ} → Cauchy  (m + (n + o)) (m + n + o)
  assocr+ {m} {n} {o} = tabulate (proj₁ (Plus.assocr+ {m} {n} {o}))

  unite* : {m : ℕ} → Cauchy m (1 * m)
  unite* {m} = tabulate (proj₁ (Times.unite* {m}))

  uniti* : {m : ℕ} → Cauchy (1 * m) m
  uniti* {m} = tabulate (proj₁ (Times.uniti* {m}))

  assocl* : {m n o : ℕ} → Cauchy  ((m * n) * o) (m * (n * o))
  assocl* {m} {n} {o} = tabulate (proj₁ (Times.assocl* {m} {n} {o}))

  assocr* : {m n o : ℕ} → Cauchy  (m * (n * o)) (m * n * o)
  assocr* {m} {n} {o} = tabulate (proj₁ (Times.assocr* {m} {n} {o}))

  -------------------------------------------------------------------------------------------
  -- Below here, we start with properties


  -- Useful stuff
  infix 4 _∼p_

  _∼p_ : {n m : ℕ} (p₁ p₂ : Vec (Fin m) n) → Set
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
  permext : {m n : ℕ} (π : Cauchy m n) → tabulate (_!!_ π) ≡ π
  permext π = tabulate∘lookup π

  -- we could go through ~p, but this works better in practice
  ~⇒≡ : {m n o : ℕ} {f : Fin m → Fin n} {g : Fin n → Fin m} → 
             (f ∘ g ∼ id) → (tabulate g ∘̂ tabulate f ≡ 1C)
  ~⇒≡ {f = f} {g} β = ∼p⇒≡ (λ i → trans (∘̂⇒∘ g f i) (cong (λ x → x !! i) (finext β)))

  -- properties of sequential composition
  ∘̂-assoc : {m₁ m₂ m₃ m₄ : ℕ} → (a : Vec (Fin m₂) m₁) (b : Vec (Fin m₃) m₂) (c : Vec (Fin m₄) m₃) 
    → a ∘̂ (b ∘̂ c) ≡ (a ∘̂ b) ∘̂ c
  ∘̂-assoc a b c = finext (lookupassoc a b c)

  ∘̂-rid : {m n : ℕ} → (π : Vec (Fin m) n) → π ∘̂ 1C ≡ π
  ∘̂-rid π = trans (finext (λ i → lookup-allFin (π !! i))) (permext π)

  ∘̂-lid : {m n : ℕ} → (π : Vec (Fin m) n) → 1C ∘̂ π ≡ π
  ∘̂-lid π = trans (finext (λ i → cong (_!!_ π) (lookup-allFin i))) (permext π)

  !!⇒∘̂ : {n₁ n₂ n₃ : ℕ} → (π₁ : Vec (Fin n₁) n₂) → (π₂ : Vec (Fin n₂) n₃) → (i : Fin n₃) → π₁ !! (π₂ !! i) ≡ (π₂ ∘̂ π₁) !! i
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

  private
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

    right⊎⊎!! :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → (p₁ : Cauchy m₁ n₁) → (p₂ : Cauchy m₂ n₂)
      → (p₃ : Cauchy m₃ m₁) → (p₄ : Cauchy m₄ m₂) → (i : Fin n₂) → 
      (p₃ ⊎c p₄) !! ( (p₁ ⊎c p₂) !! raise n₁ i ) ≡ raise m₃ ( (p₂ ∘̂ p₄) !! i) 
    right⊎⊎!! {m₁} {m₂} {m₃} {_} {n₁} {_} p₁ p₂ p₃ p₄ i =
      let pp = p₃ ⊎c p₄ in
      let qq = p₁ ⊎c p₂ in
      begin (
        pp !! (qq !! raise n₁ i)
          ≡⟨ cong (_!!_ pp) (lookup-++-raise (tabulate (inject+ m₂ ∘ _!!_ p₁)) 
                                                                  (tabulate (raise m₁ ∘ _!!_ p₂)) i) ⟩
        pp !! (tabulate (raise m₁ ∘ _!!_ p₂) !! i)
          ≡⟨ cong (_!!_ pp) (lookup∘tabulate _ i) ⟩
        pp !! raise m₁ (p₂ !! i)
          ≡⟨ right!! {m₁} (p₂ !! i) (raise m₃ ∘ (_!!_ p₄)) ⟩
        raise m₃ (p₄ !! (p₂ !! i))
          ≡⟨ cong (raise m₃) (sym (lookup∘tabulate _ i)) ⟩
        raise m₃ ((p₂ ∘̂ p₄) !! i) ∎ )

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

{- comment out to check in
    ×c-equiv : {m₁ m₂ n₁ n₂ : ℕ} (p₁ : Cauchy m₁ n₂) (p₂ : Cauchy m₂ n₂) →
      (p₁ ×c p₂) ≡ concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y , x) p₂)) p₁)
    ×c-equiv p₁ p₂ = 
      begin (
        (p₁ ×c p₂)
          ≡⟨ {!!} ⟩
         concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y , x) p₂)) p₁) ∎)
-}
{-  Not the right one?
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

    lookup-2d' : {A : Set} (m n : ℕ) → (k : Fin (m * n)) → {f : Fin (m * n) → A} →
       concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (Times.fwd (i , j))))) !! k ≡ f k
    lookup-2d' m n k {f} = {!!}

    tabulate*-split : ∀ {m n} {A : Set} → {f : Fin (m * n) → A} →
      tabulate {m * n} f ≡ concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (Times.fwd (i , j)))))
    tabulate*-split {m} {n} {f = f} = {!!}
-}

{- comment out to check in
  ×c-distrib : ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : Cauchy m₁ n₁} → {p₂ : Cauchy m₂ n₂}
    → {p₃ : Cauchy m₃ m₁} → {p₄ : Cauchy m₄ m₂} →
      (p₁ ×c p₂) ∘̂ (p₃ ×c p₄) ≡ (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄)
  ×c-distrib {m₁} {m₂} {m₃} {m₄} {n₁} {n₂} {p₁} {p₂} {p₃} {p₄} =
    let p₃₄ = p₃ ×c p₄ in let p₁₂ = p₁ ×c p₂ in
    let p₂₄ = p₂ ∘̂ p₄ in let p₁₃ = p₁ ∘̂ p₃ in
    let lhs = λ i → p₃₄ !! (p₁₂ !! i) in
    let zss = mapV  (λ b → mapV (λ x → b , x) (p₂ ∘̂ p₄)) (p₁ ∘̂ p₃) in
    begin (
       tabulate {n₁ * n₂} (λ i → p₃₄ !! (p₁₂ !! i))
         ≡⟨ {!!} ⟩
       concatV (tabulate {n₁} (λ z → tabulate {n₂} (λ w → Times.fwd ((p₃ !! (p₁ !! z)) , (p₄ !! (p₂ !! w))))))
         ≡⟨ cong concatV (finext (λ i → tabulate-∘ Times.fwd (λ w → ((p₃ !! (p₁ !! i)) , (p₄ !! (p₂ !! w)))) )) ⟩
       concatV (tabulate (λ z → mapV Times.fwd (tabulate (λ w → (p₃ !! (p₁ !! z)) , (p₄ !! (p₂ !! w))))))
         ≡⟨ cong concatV (finext (λ i → cong (mapV Times.fwd) (tabulate-∘ (λ x → (p₃ !! (p₁ !! i)) , x) (_!!_ p₄ ∘ _!!_ p₂)))) ⟩
       concatV (tabulate (λ z → mapV Times.fwd (mapV (λ x → (p₃ !! (p₁ !! z)) , x) p₂₄)))
         ≡⟨ cong concatV (tabulate-∘ _ (_!!_ p₃ ∘ _!!_ p₁)) ⟩
       concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y , x) p₂₄)) p₁₃)
         ≡⟨ refl ⟩
       concatV (mapV (mapV Times.fwd ∘  (λ b → mapV (λ x → b , x) p₂₄)) p₁₃)
         ≡⟨ cong concatV (sym (map-map-map Times.fwd  (λ b → mapV (λ x → b , x) p₂₄) p₁₃)) ⟩
       concatV (mapV (mapV Times.fwd) zss)
          ≡⟨ concat-map  zss Times.fwd ⟩
        mapV Times.fwd (concatV zss )
         ≡⟨ refl ⟩
        mapV Times.fwd ((p₁ ∘̂ p₃) ×v (p₂ ∘̂ p₄))
         ≡⟨ refl ⟩
        (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄) ∎)
-}
  swap*-inv : ∀ {m n} → swap⋆cauchy m n ∘̂ swap⋆cauchy n m ≡ 1C
  swap*-inv {m} {n} = ~⇒≡ {o = m * n} (Times.swap-inv m n)
  
