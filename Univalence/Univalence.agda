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
-- then equivalences ≃ between spaces

------------------------------------------------------------------------------
-- Equivalences between types (type isomorphisms)

open import TypeEquiv
-- Proves that types and type equivalences form a commutative semiring
-- in the Algebra sense
open import Data.Sum.Properties
-- Proves simple properties about type equivalences such as:
-- inj₂ (unite₊ x) ≡ x
open import Data.SumProd.Properties
-- Proves simple properties about type equivalences such as:
-- distzr x ≡ distz (swap⋆ x)
open import TypeEquivCat
-- Proves that types and type equivalences form a commutative rig
-- groupoid. The equality between morphisms is extensional.

------------------------------------------------------------------------------
-- Equivalences between Pi-types

-- First we introduce a univere U of finite types

-- A trivial relation on finite types is to identify all the types;
-- this makes U a contractible (-2)-type, i.e., a singleton

-- The same relation makes U a non-empty (-1)-type.

-- If the relation on finite types is modeled after type isomorphisms
-- and all isomorphisms of the same type are equated, we collapse U to
-- the set of natural numbers which makes it a 0-type. (We do not
-- distinguish 'id' and 'not'.)

-- If the relation on finite types is modeled after type isomorphisms
-- and only the isomorphisms corresponding to the coherence conditions
-- of rig categories are equated, we make U a 1-type. (We do
-- distinguish 'id' and 'not'.) The higher-level equality on the
-- 2-morphisms is extensional. 

-- How to make U a 2-type, 3-type, etc. ???

open import PiU
open import PiLevelm2
open import PiLevelm1
open import PiLevel0
open import PiLevel1

open import Pim2Cat
open import Pim1Cat
open import Pi0Cat
open import Pi1Cat

------------------------------------------------------------------------------
-- Now we want to relate Pi-types and type equivalences; we will use
-- permutations as an intermediary


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
