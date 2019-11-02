{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Comonadic where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _⊔_ to _ℕ⊔_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣; _+_; _⊔_; -_)
open import Data.Rational
  using (ℚ)
  renaming (1/_ to recip)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product -- using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe
open import Function using (id)
open import Relation.Binary.Core using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to R[_])
--  using (_≡_; refl; sym; trans; cong; cong₂; inspect; module ≡-Reasoning)
open import Category.Comonad
open import Pointed
open import PiFrac

------------------------------------------------------------------------------
-- Set up for examples

infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : 𝕌) {t₂ : 𝕌} {t₃ : 𝕌} →
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
_ ⟷⟨ α ⟩ β = α ⊚ β

_□ : (t : 𝕌) → {t : 𝕌} → (t ⟷ t)
_□ t = id⟷

𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

𝔹² : 𝕌
𝔹² = 𝔹 ×ᵤ 𝔹

𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

not : ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧
not (inj₁ tt) = inj₂ tt
not (inj₂ tt) = inj₁ tt

-- this version might look more contrived that the fully expanded
-- one via pattern matching, but it generalizes better.
controlled : ∀ {A} → (⟦ A ⟧ → ⟦ A ⟧) → ⟦ 𝔹 ⟧ × ⟦ A ⟧ → ⟦ 𝔹 ⟧ × ⟦ A ⟧
controlled f (b , a) = (b , [ (λ _ → a) , (λ _ → f a) ]′ b)
-- controlled f (inj₁ tt , a) = (inj₁ tt , a  )
-- controlled f (inj₂ tt , a) = (inj₂ tt , f a)

------------------------------------------------------------------------------
-- Examples

zigzag : ∀ b → ● 𝔹 [ b ] ⟷ ● 𝔹 [ b ]
zigzag b =
  uniti⋆l ⊚                            -- ONE * POINTED TWO
  (η b ⊗ id⟷) ⊚        -- (POINTED TWO * RECIP TWO) * POINTED TWO
  assocr⋆ ⊚                            -- POINTED TWO * (RECIP TWO * POINTED TWO)
  (id⟷ ⊗ swap⋆) ⊚                    -- POINTED TWO * (POINTED TWO * RECIP TWO)
  (id⟷ ⊗ ε b) ⊚                      -- POINTED TWO * ONE
  unite⋆r

test1 = eval (zigzag 𝔽) (⇑ 𝔽 refl)      -- (⇑ #f refl)
-- test2 = eval (zigzag 𝔽) (⇑ 𝕋 refl)   -- typechecks if given proof #f=#t
-- test3 = eval (zigzag 𝕋) (⇑ 𝔽 refl)   -- typechecks if given proof #f=#t
test4 = eval (zigzag 𝕋) (⇑ 𝕋 refl)      -- (⇑ #t refl)

-- Conventional PI examples

NOT : 𝔹 ⟷ 𝔹
NOT = swap₊

NEG1 NEG2 NEG3 NEG4 NEG5 : 𝔹 ⟷ 𝔹
NEG1 = swap₊
NEG2 = id⟷ ⊚ NOT
NEG3 = NOT ⊚ NOT ⊚ NOT
NEG4 = NOT ⊚ id⟷
NEG5 = uniti⋆l ⊚ swap⋆ ⊚ (NOT ⊗ id⟷) ⊚ swap⋆ ⊚ unite⋆l
NEG6 = uniti⋆r ⊚ (NOT ⊗ id⟷) ⊚ unite⋆r -- same as above, but shorter

CNOT : 𝔹² ⟷ 𝔹²
CNOT = 𝔹 ×ᵤ 𝔹
     ⟷⟨ id⟷ ⟩
       (x +ᵤ y) ×ᵤ 𝔹
     ⟷⟨ dist ⟩
       (x ×ᵤ 𝔹) +ᵤ (y ×ᵤ 𝔹)
     ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT) ⟩
       (x ×ᵤ 𝔹) +ᵤ (y ×ᵤ 𝔹)
     ⟷⟨ factor ⟩
       (x +ᵤ y) ×ᵤ 𝔹
     ⟷⟨ id⟷ ⟩
       𝔹 ×ᵤ 𝔹 □
  where x = 𝟙; y = 𝟙

TOFFOLI : 𝔹 ×ᵤ 𝔹² ⟷ 𝔹 ×ᵤ 𝔹²
TOFFOLI = 𝔹 ×ᵤ 𝔹²
        ⟷⟨ id⟷ ⟩
          (x +ᵤ y) ×ᵤ 𝔹²
        ⟷⟨ dist ⟩
          (x ×ᵤ 𝔹²) +ᵤ (y ×ᵤ 𝔹²)
        ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩
          (x ×ᵤ 𝔹²) +ᵤ (y ×ᵤ 𝔹²)
        ⟷⟨ factor ⟩
          (x +ᵤ y) ×ᵤ 𝔹²
        ⟷⟨ id⟷ ⟩
          𝔹 ×ᵤ 𝔹² □
  where x = 𝟙; y = 𝟙

PERES : (𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹 ⟷ (𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹
PERES = (id⟷ ⊗ NOT) ⊚ assocr⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ swap⋆) ⊚ (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚ assocl⋆

SWAP12 SWAP23 SWAP13 ROTL ROTR : 𝟙 +ᵤ 𝟙 +ᵤ 𝟙 ⟷ 𝟙 +ᵤ 𝟙 +ᵤ 𝟙
SWAP12 = assocl₊ ⊚ (swap₊ ⊕ id⟷) ⊚ assocr₊
SWAP23 = id⟷ ⊕ swap₊
SWAP13 = SWAP23 ⊚ SWAP12 ⊚ SWAP23
ROTR   = SWAP12 ⊚ SWAP23
ROTL   = SWAP13 ⊚ SWAP23

t3 : ∀ {b₁ b₂} →
     ● (𝔹 ×ᵤ 𝔹²) [ 𝔽 , (b₁ , b₂) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝔽 , (b₁ , b₂) ]
t3 = lift TOFFOLI

{--
The following do not typecheck. Good

t4 : ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝔽 , 𝔽) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝔽 , 𝕋) ]
t4 = lift TOFFOLI

t5 : ∀ {b₁ b₂} →
     ● (𝔹 ×ᵤ 𝔹²) [ b₁ , (𝔽 , b₂) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ b₁ , (𝔽 , b₂) ]
t5 = lift TOFFOLI
--}

t6 : ∀ {b} →
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝕋 , b) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝕋 , eval NOT b) ]
t6 = lift TOFFOLI

-- Ancilla examples from literature

-- Fig. 2 in Ricercar

CONTROLLED : {A : 𝕌} → (A ⟷ A) → 𝔹 ×ᵤ A ⟷ 𝔹 ×ᵤ A
CONTROLLED c = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ c)) ⊚ factor

fig2a : 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ⟷
        𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹
fig2a = CONTROLLED (CONTROLLED (CONTROLLED NOT))

-- first write the circuit with the additional ancilla

fig2b' : ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) ⟷ ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹)
fig2b' =
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ CONTROLLED (CONTROLLED NOT))  -- first ccnot
  ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷)                        -- move it back
  ⊚
  (assocl⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ swap⋆) ⊚
  (id⟷ ⊗ CONTROLLED (CONTROLLED NOT))  -- second ccnot
  ⊚
  (id⟷ ⊗ swap⋆) ⊚
  assocl⋆ ⊚
  (assocr⋆ ⊗ id⟷)                      -- move it back
  ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ CONTROLLED (CONTROLLED NOT))  -- third ccnot
  ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷)                        -- move it back

-- then prove a theorem that specifies its semantics

fig2b'≡ : (a b c d : ⟦ 𝔹 ⟧) →
          let (_ , e) = eval fig2b' ((a , b , c , d) , 𝔽)
          in e ≡ 𝔽
fig2b'≡ a         (inj₁ tt) c d = refl
fig2b'≡ (inj₁ tt) (inj₂ tt) c d = refl
fig2b'≡ (inj₂ tt) (inj₂ tt) c d = refl

postulate
  -- boring...
  tensor4 : ∀ {a b c d e} →
          (● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ])  ×ᵤ ● 𝔹 [ e ] ⟷
          ● ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (a , b , c , d) , e ]
  itensor4 : ∀ {a b c d e} →
          ● ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (a , b , c , d) , e ] ⟷
          (● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ])  ×ᵤ ● 𝔹 [ e ]

-- now lift it

fig2b : ∀ {a b c d} →
        let ((x , y , z , w) , e) = eval fig2b' ((a , b , c , d) , 𝔽)
        in e ≡ 𝔽 ×
           ● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ] ⟷
           ● 𝔹 [ x ] ×ᵤ ● 𝔹 [ y ] ×ᵤ ● 𝔹 [ z ] ×ᵤ ● 𝔹 [ w ]
fig2b {a} {b} {c} {d} =
  let ((x , y , z , w) , _) = eval fig2b' ((a , b , c , d) , 𝔽)
      e≡𝔽 = fig2b'≡ a b c d
  in e≡𝔽 ,
        uniti⋆r ⊚
        -- (●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × ●𝟙[tt]
        (id⟷ ⊗ η 𝔽) ⊚
        -- (●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × (●𝔹[𝔽] x ●1/𝔹[𝔽])
        assocl⋆ ⊚
        -- ((●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × ●𝔹[𝔽]) x ●1/𝔹[𝔽]
        (tensor4 ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (a,b,c,d),𝔽 ] x ●1/𝔹[𝔽]
        (lift fig2b' ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (x,y,z,w),e ] x ●1/𝔹[𝔽]
        ((== id⟷ (cong (λ H → ((x , y , z , w)) , H) e≡𝔽)) ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (x,y,z,w),𝔽 ] x ●1/𝔹[𝔽]
        (itensor4 ⊗ id⟷) ⊚
         -- ((●𝔹[x] × ●𝔹[y] × ●𝔹[z] × ●𝔹[w]) × ●𝔹[𝔽]) x ●1/𝔹[𝔽]
        assocr⋆ ⊚
        (id⟷ ⊗ ε 𝔽) ⊚
        unite⋆r

------------------------------------------------------------------------------
-- Space denotational semantics

-- for each type, we calculate its memory requirements which are two
-- numbers (m , z). The number m represents the amount of space needed
-- to store values of the type. The number z represents the effect of
-- the value on space when it is interpreted. Ex. a gc process needs m
-- bits to be stored but when run it releases z bits.

-- Number of points in type
card : (t : 𝕌) → ℕ
card 𝟘 = 0
card 𝟙 = 1
card (t₁ +ᵤ t₂) = card t₁ ℕ+ card t₂
card (t₁ ×ᵤ t₂) = card t₁ ℕ* card t₂
card ● t [ v ] = 1
card 𝟙/● t [ v ] = 1

0empty : {t : 𝕌} → card t ≡ 0 → (v : ⟦ t ⟧) → ⊥ 
0empty {𝟘} _ ()
0empty {𝟙} () tt
0empty {t₁ +ᵤ t₂} s (inj₁ v₁)
  with card t₁ | card t₂ | inspect card t₁
0empty {t₁ +ᵤ t₂} refl (inj₁ v₁) | ℕ.zero | ℕ.zero | R[ s₁ ] =
  0empty {t₁} s₁ v₁ 
0empty {t₁ +ᵤ t₂} s (inj₂ v₂)
  with card t₁ | card t₂ | inspect card t₂
0empty {t₁ +ᵤ t₂} refl (inj₂ v₂) | ℕ.zero | ℕ.zero | R[ s₂ ] =
  0empty {t₂} s₂ v₂
0empty {t₁ ×ᵤ t₂} s (v₁ , v₂)
  with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
0empty {t₁ ×ᵤ t₂} refl (v₁ , v₂) | ℕ.zero | _ | R[ s₁ ] | _ =
  0empty {t₁} s₁ v₁
0empty {t₁ ×ᵤ t₂} s (v₁ , v₂) | ℕ.suc n₁ | ℕ.zero | R[ s₁ ] | R[ s₂ ] =
  0empty {t₂} s₂ v₂ 
0empty {● t [ v ]} () (⇑ .v refl)
0empty {𝟙/● t [ v ]} () f 

space : (t : 𝕌) → Maybe (ℕ × ℤ)
space 𝟘 = nothing
space 𝟙 = just (0 , + 0)
space (t₁ +ᵤ t₂) with space t₁ | space t₂
... | just (m , z₁) | just (n , z₂) = just (1 ℕ+ (m ℕ⊔ n) , (+ 1) + (z₁ ⊔ z₂))
... | just (m , z) | nothing = just (m , z)
... | nothing | just (n , z) = just (n , z)
... | nothing | nothing = nothing
space (t₁ ×ᵤ t₂) with space t₁ | space t₂
... | just (m , z₁) | just (n , z₂) = just (m ℕ+ n , z₁ + z₂)
... | just _ | nothing = nothing
... | nothing | just _ = nothing
... | nothing | nothing = nothing
space ● t [ _ ] with space t
... | just (m , z) = just (m , z)
... | nothing = nothing -- impossible
space 𝟙/● t [ _ ] with space t
... | just (m , z) = just (m , - z)
... | nothing = nothing -- impossible

-- The type t has m values
-- we take a value and give it a canonical index
encode : (t : 𝕌) → (v : ⟦ t ⟧) → ℕ
encode 𝟙 tt = 0
encode (t₁ +ᵤ t₂) (inj₁ v₁) = encode t₁ v₁
encode (t₁ +ᵤ t₂) (inj₂ v₂) with space t₁
... | nothing = encode t₂ v₂
... | just (m , z) = m ℕ+ encode t₂ v₂
encode (t₁ ×ᵤ t₂) (v₁ , v₂) with space t₁ | space t₂
... | nothing | _ = {!!}
... | _ | nothing = {!!}
... | just (m₁ , z₁) | just (m₂ , z₂) =
  {!!} -- encode t₁ v₁ ℕ+ encode t₂ v₂
encode (● t [ v ]) w = 1
encode (𝟙/● t [ f ]) g = 1

-- write a version of eval that takes memory of the right size


{--

size : (t : 𝕌) → ℚ
size t = {!!}

-- size (Pointed A v) = size A
-- size (1/A v) = 1/size A or

{--
Actually we need to separate cardinality of the type
and the number of bits needed in memory (log factor)

Write a version of eval that makes it clear that in plain pi every
combinator preserves memory and that fractionals allow intermediate
combinators to allocate memory and gc it. The fractional value's
impact on memory is that it uses negative memory.
--}

𝕊 : (t : 𝕌) → (size t ≡ (+ 0 / 1)) ⊎
              (Σ ℕ (λ m →
              (Σ ℕ (λ n →
              (Vec ⟦ t ⟧ m) ×
              (Vec ⟦ t ⟧ n) ×
              (((+ m / 1) * (recip (+ n / 1))) ≡ (+ 1 / 1))))))
𝕊 = {!!}

-- Groupoids

-- Groupoid for pointed 1/A is point and (size A) loops on point labeled (=
-- a1), (= a2), (= a3), etc.

--}

------------------------------------------------------------------------------
