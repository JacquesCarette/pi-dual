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

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Functor
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric
open import Categories.RigCategory
open import Categories.2-Category

------------------------------------------------------------------------------
-- Equivalences

open import Equiv
-- Defines extensional equality of functions ∼; quasi-inverses; and
-- then equivalences ≃ between spaces
open import EquivEquiv
-- Defines an extensional equivalence relation to be used to equate
-- equivalences so we can talk about equivalences up to equivalence

------------------------------------------------------------------------------
-- Equivalences between Agda types (type isomorphisms)

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
-- Proves that types and type equivalences form a symmetric rig
-- groupoid up to extensional equality of equivalences

------------------------------------------------------------------------------
-- Equivalences between Pi types (combinators)

open import PiU
-- First we introduce a univere U of finite types

open import PiLevelm2
open import Pim2Cat
-- A trivial relation on finite types is to identify all the types;
-- this makes U a contractible (-2)-type, i.e., a singleton.
--
-- The Pi types with the trivial relation that identifies all the
-- types form a trivial symmetric rig groupoid up to propositional
-- equality.
--
-- A (-1)-type is either empty or a singleton. The previous setup at
-- level -2 collapsed U to a singleton and hence also makes U a
-- (-1)-type

open import PiLevel0
open import Pi0Cat
-- If the relation on finite types is modeled after type isomorphisms
-- and all isomorphisms of the same type are equated, we collapse U to
-- the set of natural numbers which makes it a 0-type. (We do not
-- distinguish 'id' and 'not'.)

open import Pi0Examples
-- Pi0 is interesting as a programming language for reversible
-- circuits. This module has a few examples.

open import PiLevel1
-- open import Pi1Cat -- UNDER DEVELOPMENT
-- If the relation on finite types is modeled after type isomorphisms
-- and only the isomorphisms corresponding to the coherence conditions
-- of rig categories are equated, we make U a 1-type. (We do
-- distinguish 'id' and 'not'.) The higher-level equality on the
-- 2-morphisms is trivial, i.e., all two level morphisms are equated.

open import Pi1Examples
-- Pi1 is interesting as a programming language for reversible
-- circuits that has its own optimizer. This module has a few
-- examples.

-- How to make U a 2-type, 3-type, etc. ???

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
