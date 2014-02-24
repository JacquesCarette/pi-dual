-- Very simple facts about natural numbers
module NatSimple where

import Data.Fin as F
--
open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Function renaming (_∘_ to _○_) 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import FT
-- open import SimpleHoTT using (_≡_ ; refl ; ! ; _∘_ ; ap ; _≡⟨_⟩_ ; _∎ )

------------------------------------------------------------------------------
-- Equivalences (not used)

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : (A → ⊥) → Dec A
  
sucEq : {n : ℕ} → (i j : F.Fin n) → (F.suc i) ≡ (F.suc j) → i ≡ j
sucEq i .i refl = refl

_=F=_ : {n : ℕ} → (i j : F.Fin n) → Dec (i ≡ j)
F.zero    =F= F.zero                     = yes refl
(F.suc i) =F= F.zero                     = no (λ ())
F.zero    =F= (F.suc j)                  = no (λ ())
(F.suc i) =F= (F.suc j) with i =F= j
(F.suc i) =F= (F.suc .i) | yes refl      = yes refl 
(F.suc i) =F= (F.suc j) | no p           = no (λ q → p (sucEq i j q))

------------------------------------------------------------------
-- Finite Types and the natural numbers are intimately related.

fromℕ : ℕ → FT
fromℕ zero    = ZERO
fromℕ (suc n) = PLUS ONE (fromℕ n)

-- normalize a finite type to (1 + (1 + (1 + ... + (1 + 0) ... )))
-- a bunch of ones ending with zero with left biased + in between

⟦_⟧ℕ : ℕ → Set
⟦ zero ⟧ℕ  = ⊥
⟦ suc n ⟧ℕ = ⊤ ⊎ ⟦ n ⟧ℕ

-- Take a natural number n, and a value of the type represented by that n,
-- and return the canonical finite set of size n.
fromNormalNat : (n : ℕ) → ⟦ n ⟧ℕ → F.Fin n
fromNormalNat zero     ()
fromNormalNat (suc n) (inj₁ tt) = F.zero
fromNormalNat (suc n) (inj₂ x) = F.suc (fromNormalNat n x)

-- Take a natural number n, a finite set of size n, and return a
-- (canonical) value of the type represented by n
toNormalNat : (n : ℕ) → F.Fin n → ⟦ n ⟧ℕ
toNormalNat zero     ()
toNormalNat (suc n) F.zero = inj₁ tt
toNormalNat (suc n) (F.suc f) = inj₂ (toNormalNat n f)

-- BEGIN CODE COPIED (AND SOMEWHAT MODIFIED) FROM Nat.Properties
-- (for some reason +-comm is a private field so I can't get to it without
-- importing superfluous files and going through a bunch of administrative
-- garbage that isn't worth my time)

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

+-identity : {n : ℕ} → n + zero ≡ n
+-identity = n+0≡n _
  where
  n+0≡n : (n : ℕ) → n + zero ≡ n
  n+0≡n zero    = refl
  n+0≡n (suc n) = cong suc (n+0≡n n)

+-comm : (m n : ℕ) → m + n ≡ n + m 
+-comm zero    n = sym +-identity
+-comm (suc m) n = begin
    suc m + n
  ≡⟨ refl ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
    n + suc m
  ∎

-- END CODE COPIED FROM Nat.Properties  

--   
add1modn : ℕ → ℕ → ℕ → ℕ
add1modn zero zero acc = zero
add1modn zero (suc n) acc = (suc n) + acc
add1modn (suc max) zero acc = suc acc
add1modn (suc max) (suc n) acc = add1modn max n (suc acc)

-- Useful for testing
two : ℕ
two = suc (suc zero)

three : ℕ
three = suc two

four : ℕ
four = suc three

five : ℕ
five = suc four
