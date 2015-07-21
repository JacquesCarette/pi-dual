module Univalence where

------------------------------------------------------------------------------
-- Basic utilities

open import LeqLemmas
open import FinNatLemmas
open import SubstLemmas
open import FiniteFunctions
open import PathLemmas
open import VectorLemmas
open import Proofs

-- Proofs is a wrapper over all the basic utilities
-- The only thing imported from now on is Proofs

------------------------------------------------------------------------------
-- Structures (Definitions)

-- We use (and extend) the package Categories.
-- 
-- Everything we need works but some of the other parts do not work with
-- current version of Agda
-- 
{--
open import Everything
--}

------------------------------------------------------------------------------
-- Equivalences

open import Equiv
-- Defines extensional equality of functions ∼; quasi-inverses; and
-- then equivalences ≃

------------------------------------------------------------------------------
-- Equivalences between types (type isomorphisms)

open import TypeEquiv
-- Proves that types and type equivalences form a commutative semiring

open import Data.Sum.Properties
open import Data.SumProd.Properties
open import TypeEquivCat                  -- TODO

------------------------------------------------------------------------------
-- Equivalences between finite sets (enumerations and permutations)

open import FinVec                        -- TODO
open import ConcretePermutation           -- TODO

open import EnumEquiv
-- An enumeration of a set A is an equivalence between A and Fin m
open import FinEquiv
-- Proves that that finite sets and equivalences form a commutative
-- semiring

------------------------------------------------------------------------------
-- Equivalences between Pi-types

open import PiU
open import PiLevel0                      -- TODO
open import PiLevel1                      -- TODO

open import Pim2Cat                       -- TODO
open import Pim1Cat                       -- TODO
open import Pi0Cat                        -- TODO
open import Pi1Cat                        -- TODO

------------------------------------------------------------------------------
-- Equivalences between setoids

open import SetoidEquiv                   -- HERE
-- do a version of EquivSetoid specialized for finite sets that
-- include an enumeration just like quasi-inverses include one
-- particular function to specify the equivalence; must really be done
-- in conjection with SEquivSCPermEquiv so let's wait until
-- dependencies satisfied...

------------------------------------------------------------------------------
-- Equivalences between equivalences

open import SEquivSCPermEquiv             -- TODO
open import PiPerm                        -- TODO
open import PiEquiv                       -- TODO

------------------------------------------------------------------------------
-- Unfinished files

{--
open import SkFinSetCategory  
open import CPermCat 
open import Pim1Cat
--}

------------------------------------------------------------------------------
-- Not used 

{--
open import LeftCancellation              
-- Proves that ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A ≃ B
open import RepresPerm
open import Groupoid
-- should be subsumed by Categories.Groupoid
--}

------------------------------------------------------------------------------
