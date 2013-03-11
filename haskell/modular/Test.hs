{-# LANGUAGE ScopedTypeVariables #-}

-- Based on code
-- Copyright (c) 2011, William J. Bowman, Roshan P. James, and Amr
-- Sabry. The code is released under the MIT license.
--
-- Original code used GADTs.  Now do 'tagless final' using classes.
--   (Jacques Carette)
-- This code tested with GHC version 7.0.3

module Test where

import Lang
import Prelude hiding (id)

------------------------------------------------------------------------
-- Combinational circuits 

-- Not works by first converting the Haskell boolean via a Unfold to
-- either Left () or Right (), where True is Left (), False is Right ().
-- not can simply use CommutePlus to perform a not, then Fold up the
-- bool.
-- REPL Session:
-- *Pi> inot @@ True
-- False
-- *Pi> inot @@ False
inot :: PiBool eq => eq Bool Bool
inot = unfoldB %. commutePlus %. foldB

-- Cond takes two isomorphisms from some type a to some type b, and 
-- creates an isomorphism between a pair of (Bool, a) which will apply
-- the first isomorphism if the Bool is True, and the second if the Bool
-- is False.
cond :: PiBool eq => eq a b -> eq a b -> eq (Bool, a) (Bool, b)
cond f g = (unfoldB %* id) 
           %. distribute 
           %. ((id %* f) %+ (id %* g))
           %. factor 
           %. (foldB %* id) 

-- controlled takes an isomorphism between a type a to type a, and 
-- creates an isomorphism (using cond) that will apply the isomorphism to
-- the second value of the pair, if the first value if True, and apply
-- Id otherwise.
controlled :: PiBool eq => eq a a -> eq (Bool, a) (Bool, a)
controlled f = cond f id

-- cnot is Controlled Not, as found in reversible computing papers such
-- as Reversible Computing by Toffoli. It takes a pair of bools, and
-- applies not to the second Bool if the first is True, and otherwise
-- leaves the value unchanged.
-- REPL Session:
-- *Pi> cnot @@ (True, True)
-- (True, False)
-- *Pi> cnot @@ (False, True)
-- (False, True)
-- *Pi> cnot @@ (True, False)
-- (True, False)
cnot :: PiBool eq => eq (Bool, Bool) (Bool, Bool)
cnot = controlled inot

-- Toffoli is the universal nand/and gate presented in Reversible
-- Computing by Toffoli.  It is equivalent to controlled controlled
-- not. It takes 3 bools, if the first is True, if applies controlled not
-- to the second 2 bools.
-- REPL Session:
-- *Pi> toffoli @@ ((True, True), False)
-- ((True, True), True)
-- *Pi> toffoli @@ ((True, False), False)
-- ((True, False), False)
-- *Pi> toffoli @@ ((True, True), True)
-- ((True, True), False)
-- *Pi> toffoli @@ ((False, True), False)
-- ((False, True), False)
toffoli :: PiBool eq => eq ((Bool,Bool),Bool) ((Bool,Bool),Bool)
toffoli = assocTimesR %. controlled cnot %. assocTimesL

-- The Fredkin gate is a well known universal gate.
-- If the first bool is true, it swaps the second two, otherwise it
-- leaves the values unchanged.
fredkin :: PiBool eq => eq (Bool,(Bool,Bool)) (Bool,(Bool,Bool))
fredkin = controlled commuteTimes

-- The Peres gate is a universal gate: it takes three inputs a, b, and c, 
-- and produces a, a xor b, (a and b) xor c
peres :: PiBool eq => eq ((Bool,Bool),Bool) ((Bool,Bool),Bool)
peres = toffoli %. (cnot %* id) 

-- fullAdder can be interpreted as an irreversible 2 bit adder with
-- carry, by fixing the first input to be False and interpreting the
-- inputs and outputs as follows:
--
-- Input: (Constant, ((Number1, Number2), CarryIn)))
-- Output (Garbage1, (Garbage2, (Sum, Carry_Out)))
--
-- All values should be booleans, where False is 0 and True is 1.
-- Constant must be initialized to 0.
fullAdder :: PiBool eq => eq (Bool, ((Bool, Bool), Bool)) (Bool,(Bool,(Bool,Bool)))
fullAdder = commuteTimes %. (commuteTimes %* id) %. 
            assocTimesR %. commuteTimes %. (peres %* id) %.
            assocTimesR %. (id %* commuteTimes) %. 
            assocTimesR %. (id %* assocTimesL) %.
            (id %* peres) %. (id %* assocTimesR)

--------------------------------------------------------------
-- Some handy swaps etc.

sw :: Pi eq => eq (a, (b, c)) (b, (a, c))
sw = assocTimesL %. (commuteTimes %* id) %. assocTimesR

sw2 :: Pi eq => eq ((a, b), (c, d)) ((a, c), (b, d))
sw2 = assocTimesR %. (id %* sw) %. assocTimesL

-- We can introduce unit freely. hide_unit makes something 
-- that needs a unit temporary value, and creates a new isomorphism that 
-- performs the same function, but automatically introduces and removes
-- a unit temp value.
hide_unit :: Pi eq => eq (c, ()) (c, ()) -> eq c c
hide_unit c = timesOneR %. commuteTimes %. c %. commuteTimes %. timesOneL

------------------------------------------------------------------------
-- Simple primitives on inductive types

-- addSub1 can be thought of as the function add1 mod (the sum of both
-- inputs), by ignoring the second input and output. 
-- 
-- By ignoring the first input and first output, the function can be
-- thought of as sub1 (mod the sum of both inputs)
-- 
-- REPL Session:
-- *Pi> addSub1 @@ (10, 1)
-- (11, 0)
-- *Pi> addSub1 @@ (1, 10)
-- (2, 9)
-- *Pi> addSub1 @@ (10, 0)
-- (0, 10)
addSub1 :: PiNat eq => eq (Int, Int) (Int, Int)
addSub1 = commuteTimes 
            %. (unfoldN %* id) 
            %. distribute 
            %. (id %+ commuteTimes)
            %. factor 
            %. (foldN %* id) 

--------------------------------------------------------------------------
-- Iterating a list of nats.

-- iter_ls_nat takes an isomorphism which represents a single step of a
-- loop over a list, and creates an isomorphism which loops over a list,
-- threading through any other arbitrary values.
--
-- To do this, we introduce a unit, which is used to build up a new
-- list, as we traverse the input list.  This is necessary, as information
-- preservation is needed to maintain reversibility.
-- After introducing the unit, we trace a body that does some
-- rearranging and deconstruction of the list.
-- 
-- Step should be an isomorphism that takes a pair, whose first element
-- is a pair of the head and tail of the list at a given step, and whose
-- second element is a pair of the list that is being built to preserve
-- information, and the threaded values of its choosing.
--
-- The resulting isomorphism will take a list and some threaded values,
-- and iterate over the list, performing step each time a tail operation
-- is performed (i.e. the list is 'decremented')
iter_ls_nat :: (PiLNat eq, PiTracePlus eq) => 
               eq ((Int, [Int]), ([Int], a)) ((Int, [Int]), ([Int], a)) -> 
               eq ([Int], a) ([Int], a)
iter_ls_nat step = timesOneR 
                   %. (tracePlus body)
                   %. timesOneL
    where
      -- body :: eq (Either ((Int, [Int]), ([Int], a)) ((), ([Int], a)))
      --            (Either ((Int, [Int]), ([Int], a)) ((), ([Int], a)))
      body = factor 
             %. ((commutePlus %. foldLN) %* id)
             %. sw
             %. ((unfoldLN %. commutePlus) %* id)
             %. distribute
             %. ((step %. sw2) %+ id)

-- Isomorphisms over lists

-- To reverse a list, we introduce a unit value, as iterating requires
-- (or allows, depending on perspective) that we give some values to
-- thread through the loop, and performs Id at each step.  The resulting
-- list is inherently reversed, due to how the list has to be built up
-- as we iterate it.
--
-- REPL Session:
-- *Pi> ireverse @@ [1..5]
-- [5,4,3,2,1]
-- *Pi> ireverse @@ [5,4..1]
-- [1,2,3,4,5]
ireverse :: (PiLNat eq, PiTracePlus eq) => eq [Int] [Int]
ireverse = hide_unit (iter_ls_nat id)

-- shuffle performs a shuffle on the list; it reverses the tail of the
-- list at each step of iteration, before recurring on it.
-- *Pi> shuffle @@ [1..5]
-- [1,5,2,4,3]
shuffle :: (PiTracePlus eq, PiLNat eq) => eq [Int] [Int]
shuffle = hide_unit (iter_ls_nat rev') %. ireverse
    where rev' = (id %* ireverse) %* id
    
------------------------------------------------------------------------
-- Iterating on a nat.
-- 
-- Given an isomorphism between a type a, generates a isomorphism 
-- between a pair of an Int and type a, which will apply the given
-- isomorphism at each step, as it iterates over the int.  At each step,
-- the given isomorphism has access to only the values of a, which are
-- threaded through the loop.
iter_nat ::  (PiTracePlus eq, PiNat eq) => eq a a -> eq (Int, a) (Int, a)
iter_nat step = timesOneR 
                %. (tracePlus body)
                %. timesOneL
    where
      -- body :: eq (Either (Int, (Int, a)) ((), (Int, a)))
      --            (Either (Int, (Int, a)) ((), (Int, a)))
      body = factor 
             %. ((commutePlus %. foldN) %* id)
             %. sw
             %. ((unfoldN %. commutePlus) %* id)
             %. distribute
             %. (((id %* (id %* step)) %. sw) %+ id)

iter_nat_i ::  (PiNat eq, PiTracePlus eq) => eq (Int, a) (Int, a) -> eq (Int, a) (Int, a)
iter_nat_i step = timesOneR 
                %. (tracePlus body)
                %. timesOneL
    where
      -- body :: eq (Either (Int, (Int, a)) ((), (Int, a)))
      --            (Either (Int, (Int, a)) ((), (Int, a)))
      body = factor 
             %. ((commutePlus %. foldN) %* id)
             %. sw
             %. ((unfoldN %. commutePlus) %* id)
             %. distribute
             %. (((id %* (step)) %. sw) %+ id)
-- evenOdd can be thought of as the irreversible function even, by
-- fixing the second input to True, and ignoring the first output. It
-- can also represent the irreversible function odd by fixing the second
-- output to False, and again ignoring the first output.
--
-- REPL Session:
-- *Pi> evenOdd @@ (0, True)
-- (0, True)
-- *Pi> evenOdd @@ (1, True)
-- (1, False)
-- *Pi> evenOdd @@ (0, False)
-- (0, False)
-- *Pi> evenOdd @@ (1, False)
-- (1, True)
-- *Pi> evenOdd @@ (4, False)
-- (4, False)
-- *Pi> evenOdd @@ (5, False)
-- (5, True)
-- *Pi> evenOdd @@ (4, True)
-- (4, True)
evenOdd :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq (Int, Bool) (Int, Bool)
evenOdd = iter_nat inot

-- addSubN can be thought of the irreversible function add by providing
-- h_large for the second input, a first number as the first input, and
-- the second number in the third input, and ignoring the last 2 outputs
--
-- addSubN can be thought of as the irreversible function subtract by
-- providing h_large in the first input, and treating the last two
-- inputs as the inputs to subtract.  By ignoring the first and third
-- outputs, you have the result.
--
-- Note that both addition and subtraction is performed mod the sum of
-- both the first 2 inputs plus 1.  So, if you try to perform 
-- subtraction with h_large = 10, and arguments 0 and 1, the result 
-- will wrap around to 10.
--
-- Sample REPL session:
-- *P> addSubN @@ ((10, 10), 7)
-- ((17,3),7)
-- *P> addSubN @@ ((10, 1000000), 7)
-- ((17,999993),7)
-- *P> addSubN @@ ((10, 1000000), 200)
-- ((210,999800),200)
-- *P> addSubN @@ ((10, 0), 0)
-- ((10,0),0)
-- *P> addSubN @@ ((10, 0), 1)
-- ((0,10),1)
-- *P> addSubN @@ ((10, 0), 2)
-- ((1,9),2)
addSubN :: (PiNat eq, PiTracePlus eq) => eq ((Int, Int), Int) ((Int, Int), Int)
addSubN = commuteTimes %. (iter_nat addSub1) %. commuteTimes

-- Mult can be thought of as the irreversible function multiply by
-- fixing the first two arguments to 0 and h_large, respectively, and
-- using the last two inputs as the arguments to multiply.
-- (again, mod the sum of the first two arguments + 1)
--
-- The result is obtained by ignoring the last 3 inputs:
-- 
--
-- mult(((accumulator, heap), n1), n2)
-- Sample REPL Session:
--
-- *P> mult @@ (((0,10000), 2), 3)
-- (((6,9994),2),3)
-- *P> mult @@ (((0,10000), 7), 11)
-- (((77,9923),7),11)
-- *P> mult @@ (((0,10000), 7), 0)
-- (((0,10000),7),0)
-- *P> mult @@ (((0,10000), 0), 11)
-- (((0,10000),0),11)
mult :: (PiNat eq, PiTracePlus eq) => eq (((Int, Int), Int), Int) (((Int, Int), Int), Int)
mult = commuteTimes %. (iter_nat addSubN) %. commuteTimes

-- Factorial. Shuffle the accumulator and the 2nd input around.  Assumes the same
-- input as mult.  Used for fact.
fshuf :: PiNat eq => eq (((Int, Int), Int), Int) (((Int, Int), Int), Int)
fshuf = assocTimesR 
        %. assocTimesR 
        %. (id %* (assocTimesL %. commuteTimes)) 
        %. assocTimesL 
        %. commuteTimes 
        %. (commuteTimes %* id) 
        %. assocTimesL

-- (((((Acc, Heap), ?), Input), []), [0, 0..]) ->
-- (((((0, Heap), Acc), Input), [?]), [0..])
-- Collect garbage does a massive amount of shuffling, and pushes some
-- garbage onto a garbage list, and pulls a fresh 0 off the 0 list for
-- the new accumulator.
-- It was written in a very systematic way, and as a result is much more
-- verbose than necessary, and rather inefficient.
collect_garbage :: PiLNat eq => eq
                       (((((Int, Int), Int), Int), [Int]), [Int])
                       (((((Int, Int), Int), Int), [Int]), [Int])
collect_garbage = (assocTimesR %* id)
                  %. ((id %* commuteTimes) %* id)
                  %. (assocTimesR %* id)
                  %. ((id %* assocTimesL) %* id)
                  %. (id %* unfoldLN)
                  %. commuteTimes %. distribute
                  %. (commuteTimes %+ commuteTimes)
                  %. (assocTimesR %+ id)
                  %. ((id %* (assocTimesR %* id)) %+ (assocTimesR))
                  %. ((id %* ((id %* commuteTimes) %* id)) %+
                          (id %* assocTimesL))
                  %. ((id %* (assocTimesL %* id)) %+ 
                          (id %* ((commuteTimes %* id) %* id)))
                  %. (id %+ (id %* (commuteTimes %* id)))
                  %. (id %+ (id %* (assocTimesL %* id)))
                  %. (id %+ (id %* assocTimesR))
                  %. (id %+ (id %* (id %* commuteTimes)))
                  %. (id %+ (id %* assocTimesL))
                  %. (assocTimesL %+ assocTimesL)
                  %. (commuteTimes %+ commuteTimes)
                  %. factor
                  %. commuteTimes
                  %. (assocTimesR)
                  %. (id %* (id %* foldLN))
                  %. assocTimesL
                  %. (assocTimesL %* id)
                  %. ((assocTimesL %* id) %* id)
                  %. (assocTimesR)
                  %. (id %* commuteTimes)
                  %. assocTimesL
                  %. ((fshuf %* id) %* id)
-- Reversible fact!
-- Sample Input: ((([], [0,0,0,0,0,0,0]), (((0, 10000), 1), 5)), 5)
-- Sample Output: ((([120,60,20,5,1],[0,0,0,0,0,0]),(((0,9680),120),0)),5)
--
-- Requires a garbage list to store junk in, a (sufficiently large) list
-- of zeros, a (sufficiently large) heap number, and 1.  Requires the
-- input twice.  This restriction could be lifted by initializing one of
-- them to 0 and counting up during the recursion instead of down, but
-- this way it much easier.
--
-- It should also be possible to eliminate one input by using a
-- different sort of iteration over nats, that gives us access to
-- intermediate values.
-- There are many optimizations possible in this code.
fact :: (PiLNat eq, PiTracePlus eq)
              => eq ((([Int], [Int]), (((Int, Int), Int), Int)), Int)
                    ((([Int], [Int]), (((Int, Int), Int), Int)), Int)
fact =  commuteTimes %. iter_nat ((id %* mult)
                %. (commuteTimes %. assocTimesL %. collect_garbage)
                %. assocTimesR
                %. commuteTimes -- Garbage collected, and accumulator 
                                 -- reinitialized
                %. (id %* (assocTimesR -- Sub1 from the recursive step
                %. (id %* addSub1)
                %. assocTimesL 
                %. (assocTimesR %* id)
                %. ((id %* addSub1) %* id)
                %. (assocTimesL %* id)
                ))) %. commuteTimes

------------------------------------------------------------------------
-- Infinite loops

-- Isomorphic inc function
-- (n, True) --> (n+1, True)
-- (n, False) --> (n-1, False)
-- (0, False) --> (0, True)
-- 
-- the adjoint of this function is also an isomorphism. 
iso_inc :: (PiBool eq, PiNat eq) => eq (Int, Bool) (Int, Bool)
iso_inc = commuteTimes 
          %. (unfoldB %* id)
          %. distribute
          %. (timesOneL %+ timesOneL)
          %. (id %+ unfoldN)
          %. assocPlusL
          %. ((commutePlus %. foldN) %+ id)
          %. (timesOneR %+ timesOneR)
          %. factor
          %. (foldB %* id)
          %. commuteTimes

-- inc function
-- n --> n+1
-- 
-- the adjoint of this function is undefined for 0. 
inc :: (PiTracePlus eq, PiNat eq) => eq Int Int
inc = tracePlus body
  where 
    body = ((unfoldN %. commutePlus) %+ id) %. assocPlusR %. (id %+ foldN)

dec :: (PiNat eq, PiTracePlus eq) => eq Int Int
dec = adj inc

-- A total function that will turn a () into False
introFalse :: (PiTracePlus eq, PiBool eq, PiNat eq) => eq () Bool
introFalse = tracePlus body
           where 
             body = assocPlusR
                    %. (unfoldN %. commutePlus %+ foldB)

introTrue :: (PiBool eq, PiTracePlus eq, PiNat eq) => eq () Bool
introTrue = introFalse %. inot

-- A partial function that will delete a False.  Only defined on input
-- False
deleteFalse :: (PiBool eq, PiTracePlus eq, PiNat eq) => eq Bool ()
deleteFalse = adj introFalse

-- A partial function that will delete True.
deleteTrue :: (PiBool eq, PiTracePlus eq, PiNat eq) => eq Bool ()
deleteTrue = adj introTrue

-- A total function which will introduce a 0
introZero :: (PiNat eq, PiTracePlus eq, PiBool eq) => eq () Int
introZero = tracePlus body
     where 
       body = commutePlus -- () + Int
              %. foldN -- Int
              %. timesOneR -- ((), Int)
              %. (introFalse %* id) -- (Bool, Int)
              %. (unfoldB %* id) -- (() + (), Int)
              %. distribute -- ((), Int + (), Int)
              %. (timesOneL %+ timesOneL)

-- A partial function which will delete a zero
deleteZero :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq Int ()
deleteZero = adj introZero

-- Convenient ways to introduce zeros.
introZeroL :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq a (Int, a)
introZeroL = timesOneR %. (introZero %* id)

deleteZeroL :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq (Int, a) a
deleteZeroL = adj introZeroL

-- Some more interesting functions that do unexpected things
--
-- intToBool is a partial function, undefined for all n > 1.
-- It transforms 1 to False and 0 to True
intToBool :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq Int Bool
intToBool = unfoldN %. (id %+ deleteZero) %. foldB

-- A total function which converts True to 0 and False to 1
boolToInt :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq Bool Int
boolToInt = adj intToBool

-- A partial function defined only on zero.  It's inverse is also
-- defined only on zero.
zero :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq Int Int
zero = timesOneR 
       %. commuteTimes 
       %. iter_nat_i body 
       %. commuteTimes
       %. timesOneL
     where
       body = (id %* introFalse)
              %. iso_inc
              %. (id %* unfoldB)
              %. (id %* (introZero %+ id)) 
              %. (id %* commutePlus)
              %. (id %* (foldN %. deleteZero))

add :: (PiNat eq, PiTracePlus eq) => eq (Int, Int) (Int, Int)
add = iter_nat inc

mult' :: (PiNat eq, PiTracePlus eq) => eq (Int, (Int,Int)) (Int, (Int, Int))
mult' = iter_nat add

-- Some list operations
cons :: (PiLNat eq, PiTracePlus eq) => eq (Int, [Int]) [Int]
cons = tracePlus body
     where
       body = assocPlusR 
              %. ((unfoldN %. commutePlus) %+ foldLN)

car :: (PiLNat eq, PiTracePlus eq) => eq [Int] (Int, [Int])
car = adj cons

nil :: (PiLNat eq, PiTracePlus eq, PiBool eq) => eq () [Int]
nil = tracePlus body
    where
       body = commutePlus -- () + (Int, [Int])
              %. foldLN -- [Int]
              %. timesOneR -- ((), [Int])
              %. (introFalse %* id) -- (Bool, [Int])
              %. (unfoldB %* id) -- (() + (), [Int])
              %. distribute -- ((), [Int] + (), [Int])
              %. ((introZero %* id) %+ timesOneL)

-- Convenient way to introduce nil
introNilR :: (PiLNat eq, PiTracePlus eq, PiBool eq) => eq a (a, [Int])
introNilR = timesOneR %. (nil %* id) %. commuteTimes

deleteNilR :: (PiLNat eq, PiTracePlus eq, PiBool eq) => eq (a, [Int]) a
deleteNilR = adj introNilR

-- Duplicate an integer
duplicate :: (PiNat eq, PiTracePlus eq, PiBool eq) => eq Int (Int, Int)
duplicate = introZeroL %. commuteTimes %. add

-- A much better implementation of fact' !
fact' :: (PiLNat eq, PiTracePlus eq, PiBool eq) => eq Int (Int, [Int])
fact' = heap
        %. arrangeIn
        %. (iter_nat_i (arrangeOut %. body %. arrangeIn)) 
        %. arrangeOut
        %. garbage
      where
        -- Introduces some extra terms to work with.
        heap :: (PiLNat eq, PiBool eq, PiTracePlus eq) => eq Int ((Int, (Int, Int)), [Int])
        heap = introNilR 
             %. ((duplicate 
                 %. introZeroL
                 %. commuteTimes 
                 %. assocTimesR) %* id) 
        -- ((Int, (Int, 0)), [Int]) :<=> (Int, (Int, (0, [Int])))
        -- Arranges the terms in the way iter_nat_i expects
        arrangeIn :: Pi eq => eq ((Int, (Int, Int)), [Int]) (Int, (Int, (Int, [Int])))
        arrangeIn = (assocTimesL %* id) %. assocTimesR %. assocTimesR

        -- Arranges the terms in a more friendly way to work with
        arrangeOut :: Pi eq => eq (Int, (Int, (Int, [Int]))) ((Int, (Int, Int)), [Int])
        arrangeOut = adj arrangeIn
        -- ((int, (Int, Int)), [Int]) :<=> ((Int, (Int, Int)), [Int])
        -- The main loop, which performs incremental multiplication,
        -- and cons intermediate values onto the garbage list
        body = ((inc %* id) %* id) 
               %. (mult' %* id)
               %. ((id %* commuteTimes) %* id)
               %. (assocTimesL %* id)
               %. assocTimesR
               %. (id %* (cons %. introZeroL)) 
               %. assocTimesL
               %. (assocTimesR %* id)
               %. ((dec %* id) %* id)
        -- ((Int, (Int, 0)), [Int]) :<=> (Int, (Int, [Int]))
        -- Delete the leftover zero.
        deleteZero :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq ((Int, (Int, Int)), [Int]) (Int, (Int, [Int]))
        deleteZero = ((id %* (commuteTimes %. deleteZeroL)) %* id)
                     %. assocTimesR
        -- After deleting the zero, our answer isn't in the nicest
        -- place, and we still have 1 intermediate value left, and the
        -- original input. Let's put the answer in a nicer place, and
        -- put those unneeded values in the garbage list.
        garbage :: (PiLNat eq, PiBool eq, PiTracePlus eq) => eq ((Int, (Int, Int)),[Int]) (Int, [Int])
        garbage = deleteZero
                  %. (id %* (id %* car)) -- (Int, (Int, (Int, [Int])))
                  %. (id %* (id %* commuteTimes))
                  %. assocTimesL
                  %. sw2 -- ((Int, [Int]), (Int, Int))
                  %. (cons %* id) -- ([Int], (Int, Int))
                        %. assocTimesL -- (([Int], Int), Int)
                        %. ((commuteTimes %. cons) %* id)
                        %. commuteTimes

-- Some interesting divergent functions (partial bijections)
--
omega0 :: (PiBool eq, PiNat eq, PiTracePlus eq) => eq (Int, Bool) (Int, Bool)
omega0 = timesOneR
         %. (tracePlus body)
         %. timesOneL
    where
      -- body :: eq (Either (Int, (Int, a)) ((), (Int, a)))
      --            (Either (Int, (Int, a)) ((), (Int, a)))
      body = factor -- (Int + (), (Int, a)) 
             %. ((commutePlus %. foldN) %* id) -- (Int (0 or i+1), (Int, a))
             %. sw -- (Int, (Int (0 or i+1), a))
             %. ((unfoldN %. commutePlus) %* id) -- (Int + (), (Int, a))
             %. distribute  -- (Int, (Int, a)) + ((), (Int, a))
             %. ((sw %. (id %* iso_inc)) %+ id) 

-- A couple of functions based on how we compose the above. 
--
-- This is a partial function. It is the identity on the defined
-- inputs.  i.e. (c v) |-->* v if it terminates.
omega0_partial_id :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq (Int, Bool) (Int, Bool)
omega0_partial_id = omega0 %. (adj omega0)

-- This is just the identity. 
omega0_id :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq (Int,Bool) (Int, Bool)
omega0_id = (adj omega0) %. omega0

-- Another infinite loop, but this time on a finite type.  This is
-- defined only on input False. Input True causes it to diverge. Since
-- this is on a finite type, we can ask our usual information
-- theoretic questions about this: Does this function preserve
-- information?
omega1 :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq Bool Bool
omega1 = timesOneR 
         %. (tracePlus body)
         %. timesOneL
    where
      -- body :: eq (Either (Int, a) ((), a))
      --            (Either (Int, a) ((), a))
      body = factor 
             %. ((commutePlus %. foldN) %* id)
             %. iso_inc
             %. ((unfoldN %. commutePlus) %* id)
             %. distribute


-- Undefined on all inputs. Does this constitute some form of
-- "deleting a bit"? Entropy of bool is 1. 
omega1_bool :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq Bool Bool
omega1_bool = omega1 %. omega1

-- Another infinite loop.  Unit however is supposed to have no
-- information, so what does non-termination mean in this case?
-- Entropy of unit is 0.
omega1_unit :: (PiNat eq, PiBool eq, PiTracePlus eq) => eq () ()
omega1_unit = tracePlus (foldB %. omega1 %. unfoldB)

------------------------------------------------------------------------

class CreateConst a where 
    createConst :: (PiBool eq, PiLNat eq, PiTracePlus eq) => eq () a

instance CreateConst () where 
    createConst = id 

instance (CreateConst a, CreateConst b) => CreateConst (a, b) where 
    createConst =  timesOneR %.  (createConst %* createConst)

instance (CreateConst a, CreateConst b) => CreateConst (Either a b) where 
    createConst =  introTrue %. unfoldB %.  (createConst %+ createConst)

instance CreateConst Int where 
    createConst =  introZero

instance CreateConst a => CreateConst [a] where 
    createConst = tracePlus body 
        where 
          body :: (PiBool eq, PiLNat eq, PiTracePlus eq) => eq (Either (a, [a]) ()) (Either (a, [a]) [a])
          body = commutePlus
                 %. foldL 
                 %. withUnit (introFalse %. unfoldB)
                 %. distribute 
                 %. ((createConst %* id) %+ timesOneL)

withUnit :: Pi eq => eq () b -> eq a (b, a)
withUnit c = timesOneR %. (c %* id)
