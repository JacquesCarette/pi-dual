module O where

open import Data.Product
open import Function renaming (_∘_ to _○_)

open import Circle

------------------------------------------------------------------------------
-- Abstract interpretation:
-- natural numbers with paths equating all even numbers in one
-- connected component and all odd numbers in another connected
-- component

-- module with 0,1,2,3,4 ... this is the concrete domain

data N : Set where
  Zero  : N
  One   : N
  Two   : N
  Three : N 
  Four  : N

recN : (C : Set) → C → C → C → C → C → N → C
recN C c0 c1 c2 c3 c4 Zero = c0
recN C c0 c1 c2 c3 c4 One = c1
recN C c0 c1 c2 c3 c4 Two = c2
recN C c0 c1 c2 c3 c4 Three = c3
recN C c0 c1 c2 c3 c4 Four = c4

indN : (C : N → Set) → C Zero → C One → C Two → C Three → C Four → (n : N) → C n
indN C c0 c1 c2 c3 c4 Zero = c0
indN C c0 c1 c2 c3 c4 One = c1
indN C c0 c1 c2 c3 c4 Two = c2
indN C c0 c1 c2 c3 c4 Three = c3
indN C c0 c1 c2 c3 c4 Four = c4

-- module for the abstract domain {even, odd} except that we don't define it
-- this way: we simply add paths between the even elements and paths between
-- the odd elements

module Parity where

  private 
    data N* : Set where
      Zero*  : N*
      One*   : N*
      Two*   : N*
      Three* : N* 
      Four*  : N*

  NA : Set
  NA = N*

  zero : NA
  zero = Zero*   
     
  one : NA
  one = One*

  two : NA
  two = Two*

  three : NA
  three = Three*

  four : NA
  four = Four*

  postulate
    even02 : Zero* ≡ Two*
    even04 : Zero* ≡ Four*
    odd13  : One* ≡ Three*

  recNA : (C : Set) → (c0 c1 c2 c3 c4 : C) → 
    (ceven02 : c0 ≡ c2) → (ceven04 : c0 ≡ c4) → (codd13 : c1 ≡ c3) → 
    NA → C
  recNA C c0 c1 c2 c3 c4 _ _ _ Zero* = c0
  recNA C c0 c1 c2 c3 c4 _ _ _ One* = c1
  recNA C c0 c1 c2 c3 c4 _ _ _ Two* = c2
  recNA C c0 c1 c2 c3 c4 _ _ _ Three* = c3
  recNA C c0 c1 c2 c3 c4 _ _ _ Four* = c4

  postulate
    αrecNA02 : (C : Set) → (c0 c1 c2 c3 c4 : C) → 
      (ceven02 : c0 ≡ c2) → (ceven04 : c0 ≡ c4) → (codd13 : c1 ≡ c3) → 
      ap (recNA C c0 c1 c2 c3 c4 ceven02 ceven04 codd13) even02 ≡ ceven02

    αrecNA04 : (C : Set) → (c0 c1 c2 c3 c4 : C) → 
      (ceven02 : c0 ≡ c2) → (ceven04 : c0 ≡ c4) → (codd13 : c1 ≡ c3) → 
      ap (recNA C c0 c1 c2 c3 c4 ceven02 ceven04 codd13) even04 ≡ ceven04

    αrecNA13 : (C : Set) → (c0 c1 c2 c3 c4 : C) → 
      (ceven02 : c0 ≡ c2) → (ceven04 : c0 ≡ c4) → (codd13 : c1 ≡ c3) → 
      ap (recNA C c0 c1 c2 c3 c4 ceven02 ceven04 codd13) odd13 ≡ codd13

  indNA : (C : NA → Set) → 
    (c0 : C Zero*) → 
    (c1 : C One*) → 
    (c2 : C Two*) → 
    (c3 : C Three*) → 
    (c4 : C Four*) → 
    (ceven02 : transport C even02 c0 ≡ c2) → 
    (ceven04 : transport C even04 c0 ≡ c4) → 
    (codd13 : transport C odd13 c1 ≡ c3) → 
    (n : NA) → C n
  indNA C c0 c1 c2 c3 c4 ceven02 ceven04 codd13 Zero* = c0 
  indNA C c0 c1 c2 c3 c4 ceven02 ceven04 codd13 One* = c1 
  indNA C c0 c1 c2 c3 c4 ceven02 ceven04 codd13 Two* = c2
  indNA C c0 c1 c2 c3 c4 ceven02 ceven04 codd13 Three* = c3
  indNA C c0 c1 c2 c3 c4 ceven02 ceven04 codd13 Four* = c4

open Parity

-- Now we define functions back and forth

abs : N → NA
abs = recN NA zero one two three four

con : NA → N
con = recNA N Zero One Zero One Zero (refl Zero) (refl Zero) (refl One)

conEven02 : ap con even02 ≡ refl Zero
conEven02 = αrecNA02 N Zero One Zero One Zero (refl Zero) (refl Zero) (refl One)

conEven04 : ap con even04 ≡ refl Zero
conEven04 = αrecNA04 N Zero One Zero One Zero (refl Zero) (refl Zero) (refl One)

conOdd13 : ap con odd13 ≡ refl One
conOdd13 = αrecNA13 N Zero One Zero One Zero (refl Zero) (refl Zero) (refl One)

-- Compose both ways

absconeven02 : ap (abs ○ con) even02 ≡ refl zero
absconeven02 = 
  ap (abs ○ con) even02
    ≡⟨ {!!} ⟩
  ap abs (ap con even02)
    ≡⟨ {!!} ⟩
  ap abs (refl Zero)
    ≡⟨ {!!} ⟩
  refl zero ∎

absconeven04 : ap (abs ○ con) even04 ≡ refl zero
absconeven04 = 
  ap (abs ○ con) even04
    ≡⟨ {!!} ⟩
  ap abs (ap con even04)
    ≡⟨ {!!} ⟩
  ap abs (refl Zero)
    ≡⟨ {!!} ⟩
  refl zero ∎

absconodd13 : ap (abs ○ con) odd13 ≡ refl one
absconodd13 = 
  ap (abs ○ con) odd13
    ≡⟨ {!!} ⟩
  ap abs (ap con odd13)
    ≡⟨ {!!} ⟩
  ap abs (refl One)
    ≡⟨ {!!} ⟩
  refl one ∎

αeven02 : transport (λ x → (abs ○ con) x ≡ x) even02 (refl zero) ≡ even02
αeven02 = 
  transport (λ x → (abs ○ con) x ≡ x) even02 (refl zero) 
    ≡⟨ {!!} ⟩
  ! (ap (abs ○ con) even02) ∘ refl zero ∘ ap id even02
    ≡⟨ {!!} ⟩
  ! (ap (abs ○ con) even02) ∘ refl zero ∘ even02
    ≡⟨ {!!} ⟩
  ! (ap (abs ○ con) even02) ∘ even02
    ≡⟨ {!!} ⟩
  refl zero ∘ even02
    ≡⟨ {!!} ⟩
  even02 ∎

αeven04 : transport (λ x → (abs ○ con) x ≡ x) even04 (refl zero) ≡ even04
αeven04 = 
  transport (λ x → (abs ○ con) x ≡ x) even04 (refl zero) 
    ≡⟨ {!!} ⟩ 
  even04 ∎

αodd13 : transport (λ x → (abs ○ con) x ≡ x) odd13 (refl one) ≡ odd13
αodd13 = 
  transport (λ x → (abs ○ con) x ≡ x) odd13 (refl one) 
    ≡⟨ {!!} ⟩ 
  odd13 ∎

-- Galois connections...

αN : con ○ abs ○ con ○ abs ∼ con ○ abs
αN = indN (λ x → (con ○ abs ○ con ○ abs) x ≡ (con ○ abs) x) 
     (refl Zero) (refl One) (refl Zero) (refl One) (refl Zero)

αNA : abs ○ con ∼ id
αNA = indNA (λ x → (abs ○ con) x ≡ x)
        (refl zero) (refl one) even02 odd13 even04
        αeven02 αeven04 αodd13 

-- Computations on N and NA can be related
-- Concrete computation

incN : N → N
incN Zero = One
incN One = Two
incN Two = Three
incN Three = Four
incN Four = Zero

addN : N → N → N
addN Zero b = b
addN a Zero = a
addN One One = Two
addN One Two = Three
addN One Three = Four
addN One Four = Zero
addN Two One = Three
addN Two Two = Four
addN Two Three = Zero
addN Two Four = One
addN Three One = Four
addN Three Two = Zero
addN Three Three = One
addN Three Four = Two
addN Four One = Zero
addN Four Two = One
addN Four Three = Two
addN Four Four = Three

-- we can apply an operation in the abstract domain and report the
-- approximate result

absF : (N → N) → (NA → NA)
absF f = abs ○ f ○ con

approx : (N → N) → (N → N)
approx f n = con ((absF f) (abs n))

test0 : approx incN Zero ≡ One
test0 = refl One

test1 : approx incN One ≡ Zero
test1 = refl Zero

test2 : approx incN Two ≡ One
test2 = refl One

test3 : approx incN Three ≡ Zero
test3 = refl Zero

test4 : approx incN Four ≡ One
test4 = refl One

------------------------------------------------------------------------------

