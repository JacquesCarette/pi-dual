{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Space where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _⊔_ to _ℕ⊔_)
open import Data.Nat.Properties using (*-zeroʳ)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣; _+_; _⊔_; -_)
open import Data.Rational
  using (ℚ)
  renaming (1/_ to recip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to R[_])
  using (_≡_; refl; sym; trans; cong; inspect)

open import Pointed
open import PiFrac

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

-- If number of points is zero then it is impossible to find a value
-- of the type
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

-- Space needed to store a value of the given type

space : (t : 𝕌) → {¬t≡0 : ¬ card t ≡ 0} → ℕ
space 𝟘 {0ne} = ⊥-elim (0ne refl)
space 𝟙 = 0 
space (t₁ +ᵤ t₂) {pne} with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (pne refl) 
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] =
  space t₂ {λ t2≡0 → ⊥-elim (pne (trans (sym s₂) t2≡0))}
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] = {!!}
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] = {!!}
space (t₁ ×ᵤ t₂) {pne} with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (pne refl) 
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] = ⊥-elim (pne refl) 
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (pne (*-zeroʳ (suc m)))
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] = {!!}
space ● t [ v ] = {!!} 
space 𝟙/● t [ v ] = {!!} 

{--
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

--}
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
