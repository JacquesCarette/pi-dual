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

open Parity

-- Now we define functions back and forth

abs : N → NA
abs = recN NA zero one two three four

con : NA → N
con = recNA N Zero One Zero One Zero (refl Zero) (refl Zero) (refl One)

-- Computations on N and NA can be related
-- Concrete computation

incN : N → N

incN Zero = One
incN One = Two
incN Two = Three
incN Three = Four
incN Four = Zero

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

