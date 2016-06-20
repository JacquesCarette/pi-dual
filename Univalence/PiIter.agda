{-# OPTIONS --without-K #-}

module PiIter where

open import Level using (_⊔_) renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Functor using (Functor)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Relation.Binary.PropositionalEquality as P
open import Function using (flip)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Data.Integer using (ℤ;+_;-[1+_]) renaming (suc to ℤsuc; -_ to ℤ-; _+_ to _ℤ+_)

open import PiU using (U; ZERO; ONE; PLUS; TIMES; toℕ)
open import PiLevel0
open import PiLevel1
open import PiEquiv renaming (eval to ap; evalB to apB)
open import Equiv

infix 40 _^_


_^_ : {τ : U} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = id⟷
p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

-- useful properties of ^
-- because ^ is iterated composition of the same thing,
-- then by associativity, we can hive off compositions
-- from left or right

assoc1 : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  (p ◎ (p ^ (+ m))) ⇔ ((p ^ (+ m)) ◎ p)
assoc1 ℕ.zero = trans⇔ idr◎l idl◎r
assoc1 (suc m) = trans⇔ (id⇔ ⊡ assoc1 m) assoc◎l

assoc1- : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  ((! p) ◎ (p ^ -[1+ m ])) ⇔ ((p ^ -[1+ m ]) ◎ (! p))
assoc1- ℕ.zero = id⇔
assoc1- (suc m) = trans⇔ (id⇔ ⊡ assoc1- m) assoc◎l

-- more generally
assoc1g : {τ : U} → {p : τ ⟷ τ} → (i : ℤ) →
  (p ◎ (p ^ i)) ⇔ ((p ^ i) ◎ p)
assoc1g (+_ n) = assoc1 n
assoc1g (-[1+_] zero) = trans⇔ linv◎l rinv◎r
assoc1g (-[1+_] (suc n)) = trans⇔ assoc◎l (trans⇔ (linv◎l ⊡ id⇔) (
  trans⇔ idl◎l (2! (trans⇔ (assoc1- n ⊡ id⇔) (trans⇔ assoc◎r
  (trans⇔ (id⇔ ⊡ rinv◎l) idr◎l))))))

-- Property of ^: negating exponent is same as
-- composing in the other direction, then reversing.
^⇔! : {τ : U} → {p : τ ⟷ τ} → (k : ℤ) →
  (p ^ (ℤ- k)) ⇔ ! (p ^ k)
^⇔! (+_ ℕ.zero) = id⇔
-- need to dig deeper, as we end up negating
^⇔! (+_ (suc ℕ.zero)) = idl◎r
^⇔! (+_ (suc (suc n))) = trans⇔ (assoc1- n) (^⇔! (+ suc n) ⊡ id⇔)
^⇔! {p = p} (-[1+_] ℕ.zero) = trans⇔ idr◎l (2! !!⇔id) -- (!!⇔id {c = p})
^⇔! {p = p} (-[1+_] (suc n)) =
  trans⇔ (assoc1 (suc n)) ((^⇔! -[1+ n ]) ⊡ 2! !!⇔id) -- (!!⇔id p))

-- first match on m, n, then proof is purely PiLevel1
lower : {τ : U} {p : τ ⟷ τ} (m n : ℤ) →
  p ^ (m ℤ+ n) ⇔ ((p ^ m) ◎ (p ^ n))
lower (+_ ℕ.zero) (+_ n) = idl◎r
lower (+_ ℕ.zero) (-[1+_] n) = idl◎r
lower (+_ (suc m)) (+_ n) =
  trans⇔ (id⇔ ⊡ lower (+ m) (+ n)) assoc◎l
lower {p = p} (+_ (suc m)) (-[1+_] ℕ.zero) = 
  trans⇔ idr◎r (trans⇔ (id⇔ ⊡ linv◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔)))  -- p ^ ((m + 1) -1)
lower (+_ (suc m)) (-[1+_] (suc n)) = -- p ^ ((m + 1) -(1+1+n)
  trans⇔ (lower (+ m) (-[1+ n ])) (
  trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ linv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔))))) 
lower (-[1+_] m) (+_ ℕ.zero) = idr◎r
lower (-[1+_] ℕ.zero) (+_ (suc n)) = 2! (trans⇔ assoc◎l (
  trans⇔ (rinv◎l ⊡ id⇔) idl◎l))
lower (-[1+_] (suc m)) (+_ (suc n)) = -- p ^ (-(1+m) + (n+1))
  trans⇔ (lower (-[1+ m ]) (+ n)) (
    trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ rinv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l ((2! (assoc1- m)) ⊡ id⇔)))))
lower (-[1+_] ℕ.zero) (-[1+_] n) = id⇔
lower (-[1+_] (suc m)) (-[1+_] n) = -- p ^ (-(1+1+m) - (1+n))
  trans⇔ (id⇔ ⊡ lower (-[1+ m ]) (-[1+ n ])) assoc◎l

-- i.e. Iter is: for all i, any p' such that
-- p' ⇔ p ^ i

record Iter {τ : U} (p : τ ⟷ τ) : Set where
  constructor iter
  field
    i : ℤ
    p' : τ ⟷ τ
    p'⇔p^i : p' ⇔ (p ^ i)

-- Equality of Iter. 
record _≡c_ {τ : U} {p : τ ⟷ τ} (q r : Iter p) : Set where
  constructor eqc
  field
    iter≡ : Iter.i q ≡ Iter.i r
    p⇔ : Iter.p' q ⇔ Iter.p' r

-- Iterates of id⟷
id^i≡id : {t : U} (i : ℤ) → (id⟷ ^ i) ⇔ (id⟷ {t})
id^i≡id (+_ zero) = id⇔
id^i≡id (+_ (suc n)) = trans⇔ idl◎l (id^i≡id (+ n))
id^i≡id (-[1+_] zero) = id⇔
id^i≡id (-[1+_] (suc n)) = trans⇔ idl◎l (id^i≡id -[1+ n ])

