{-# OPTIONS --universe-polymorphism #-}

{- This module is really a combination of copumpkin's Semigroup and
   CommutativeSemigroup modules, available on github at
   https://github.com/copumpkin/containers.git
-}
module Permutations where

open import Algebra
-- import Algebra.FunctionProperties as FunctionProperties

open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Data.Nat hiding (fold)
open import Data.Nat.Properties using (commutativeSemiring; i+j≡0⇒i≡0)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec

open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming (setoid to ≡-setoid)
import Relation.Binary.EqReasoning as EqReasoning

open CommutativeSemiring commutativeSemiring using (+-identity; +-comm; distrib)
-- open import Containers.Semigroup

-- Full trees, representing associations
data Association : ℕ → Set where
  leaf : Association 1
  node : ∀ {m n} → (l : Association m) → (r : Association n) → Association (m + n)

leftA : ∀ {n} → Association (1 + n)
leftA {zero} = leaf
leftA {suc n} rewrite +-comm 1 n = node (leftA {n}) leaf

rightA : ∀ {n} → Association (1 + n)
rightA {zero} = leaf
rightA {suc n} = node leaf rightA

fold : ∀ {n} {a} {A : Set a} → Association n → (A → A → A) → Vec A n → A
fold leaf _∙_ (x ∷ xs) = x
fold (node {m} l r) _∙_ xs with splitAt m xs
...                        | ls , rs , pf = fold l _∙_ ls ∙ fold r _∙_ rs

foldl₁-fold : ∀ {n} {a} {A : Set a} (f : A → A → A) → (xs : Vec A (1 + n)) → foldl₁ f xs ≡ fold leftA f xs
foldl₁-fold {zero} f (x ∷ []) = refl
foldl₁-fold {suc n} f xs rewrite +-comm 1 n with splitAt (suc n) xs
foldl₁-fold {suc n} f .(ls ++ r ∷ [])           | ls , r ∷ [] , refl rewrite sym (foldl₁-fold f ls) = foldl₁-snoc f r ls
  where
  foldl₁-snoc : ∀ {a} {A : Set a} {n} f x (xs : Vec A (1 + n)) → foldl₁ f (xs ++ x ∷ []) ≡ f (foldl₁ f xs) x
  foldl₁-snoc f x₀ (x₁ ∷ []) = refl
  foldl₁-snoc f x₀ (x₁ ∷ x ∷ xs) = foldl₁-snoc f x₀ (f x₁ x ∷ xs)

foldr-fold : ∀ {n} {a} {A : Set a} (f : A → A → A) z (xs : Vec A n) → foldr _ f z xs ≡ fold rightA f (xs ∷ʳ z)
foldr-fold f z [] = refl
foldr-fold f z (x ∷ xs) = cong (f x) (foldr-fold f z xs)

foldl-fold : ∀ {n} {a} {A : Set a} (f : A → A → A) z (xs : Vec A n) → foldl _ f z xs ≡ fold leftA f (z ∷ xs)
foldl-fold f z xs rewrite sym (foldl₁-fold f (z ∷ xs)) = refl

foldl-elim : ∀ {a b c} {A : Set a} {B : ℕ → Set b} (P : ∀ {n} → Vec A n → B n → Set c) {f : ∀ {n} → B n → A → B (1 + n)} {z : B 0} 
           → P [] z
           → (∀ {n x′ z′} {xs′ : Vec A n} → P xs′ z′ → P (xs′ ∷ʳ x′) (f z′ x′)) 
           → ∀ {n} (xs : Vec A n) → P xs (foldl B f z xs)
foldl-elim P Pz Ps [] = Pz
foldl-elim {A} {B} P {f} {z} Pz Ps (x ∷ xs) = foldl-elim (λ xs′ → P (x ∷ xs′)) (Ps Pz) Ps xs

foldl-lemma : ∀ {a b} {A : Set a} {B : ℕ → Set b} {f : ∀ {n} → B n → A → B (suc n)} {z : B 0} {n} {x} (xs : Vec A n) → f (foldl B f z xs) x ≡ foldl B f z (xs ∷ʳ x)
foldl-lemma [] = refl
foldl-lemma {B = B} (y ∷ ys) = foldl-lemma {B = λ n → B (suc n)} ys

infixr 5 _∷_

data Permutation : ℕ → Set where
  []  : Permutation 0
  _∷_ : {n : ℕ} → (p : Fin (1 + n)) → (ps : Permutation n) → Permutation (1 + n)

max : ∀ {n} → Fin (suc n)
max {zero} = zero
max {suc n} = suc max

idP : ∀ {n} → Permutation n
idP {zero} = []
idP {suc n} = zero ∷ idP

reverseP : ∀ {n} → Permutation n
reverseP {zero} = []
reverseP {suc n} = max ∷ reverseP

insert : ∀ {n} {a} {A : Set a} → Vec A n → Fin (1 + n) → A → Vec A (1 + n)
insert xs zero a = a ∷ xs
insert [] (suc ()) a
insert (x ∷ xs) (suc i) a = x ∷ insert xs i a

permute : ∀ {n} {a} {A : Set a} → Permutation n → Vec A n → Vec A n
permute [] [] = []
permute (p ∷ ps) (x ∷ xs) = insert (permute ps xs) p x

idP-id : ∀ {n} {a} {A : Set a} (xs : Vec A n) → permute idP xs ≡ xs
idP-id [] = refl
idP-id (x ∷ xs) = cong (_∷_ x) (idP-id xs)

insert-max : ∀ {n} {a} {A : Set a} (ys : Vec A n) x → insert ys max x ≡ ys ∷ʳ x
insert-max [] x = refl
insert-max (y ∷ ys) x = cong (_∷_ y) (insert-max ys x)

reverse-∷ʳ : ∀ {n} {a} {A : Set a} (ys : Vec A n) x → reverse ys ∷ʳ x ≡ reverse (x ∷ ys)
reverse-∷ʳ {A = A} xs x = 
  foldl-elim
    (λ xs b → b ∷ʳ x ≡ reverse (x ∷ xs)) 
    refl 
    (λ {_} {_} {_} {xs} eq → trans (cong (_∷_ _) eq) (foldl-lemma {B = λ n -> Vec A (suc n)} xs))
    xs

reverseP-reverse : ∀ {n} {a} {A : Set a} (xs : Vec A n) → permute reverseP xs ≡ reverse xs
reverseP-reverse [] = refl
reverseP-reverse {suc n} {_} {A} (x ∷ xs) = 
    begin
      insert (permute reverseP xs) max x
    ≈⟨ insert-max (permute reverseP xs) x ⟩
      permute reverseP xs ∷ʳ x
    ≈⟨ cong (λ q → q ∷ʳ x) (reverseP-reverse xs) ⟩
      reverse xs ∷ʳ x
    ≈⟨ reverse-∷ʳ xs x ⟩
      reverse (x ∷ xs)
    ∎
  where open EqReasoning (≡-setoid (Vec A (1 + n)))

{-
_◌_ : ∀ {n} → Permutation n → Permutation n → Permutation n
[] ◌ [] = []
(zero ∷ p₁) ◌ (q ∷ q₁) = q ∷ (p₁ ◌ q₁)
(suc p ∷ p₁) ◌ (zero ∷ q₁) = {!!}
(suc p ∷ p₁) ◌ (suc q ∷ q₁) = {!!}

perm◌perm : ∀ {n} {A : Set} → (p q : Permutation n) → (v : Vec A n) → permute q (permute p v) ≡ permute (p ◌ q) v
perm◌perm [] [] [] = refl
perm◌perm (zero ∷ p₁) (q ∷ q₁) (x ∷ v) = cong (λ y → insert y q x) (perm◌perm p₁ q₁ v) 
perm◌perm (suc p ∷ p₁) (q ∷ q₁) (x ∷ v) with permute ((suc p) ∷ p₁) (x ∷ v)
perm◌perm (suc p ∷ p₁) (zero ∷ q₁) (x ∷ v) | y ∷ w = {!!}
perm◌perm (suc p ∷ p₁) (suc q ∷ q₁) (x ∷ v) | y ∷ w = {!!}

p1 : Permutation 5
p1 =  suc (suc zero) ∷ suc (suc zero)  ∷ zero ∷ suc zero ∷ zero ∷ []

p2 : Permutation 5
p2 = suc (suc (suc zero)) ∷ suc (suc (suc zero)) ∷ zero ∷ zero ∷ zero ∷ []

p3 : Permutation 5
p3 = suc (suc (suc (suc zero))) ∷ suc zero ∷ suc zero ∷ suc zero ∷ zero ∷ []

test1 : Vec (Fin 5) 5
test1 = permute p1 (tabulate {5} (λ x → x))

test2 : Vec (Fin 5 ) 5
test2 = permute p2 (tabulate (λ x → x))

test3 : Vec (Fin 5) 5
test3 = permute p1 (test2)

test4 : test3 ≡ permute p3 (tabulate (λ x → x))
test4 = refl
-}
