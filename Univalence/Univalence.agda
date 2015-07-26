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
open import Categories.Bicategory

------------------------------------------------------------------------------
-- Equivalences

open import Equiv
-- Defines extensional equality of functions ∼; quasi-inverses; and
-- then equivalences ≃ between spaces
open import EquivEquiv
-- Defines an extensional equivalence relation to be used to equate
-- equivalences so we can talk about equivalences up to equivalence

------------------------------------------------------------------------------
-- Equivalences between Agda types (extensional type isomorphisms)

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
open import Pi1Cat
-- If the relation on finite types is modeled after type isomorphisms
-- and only the isomorphisms corresponding to the coherence conditions
-- of rig categories are equated, we make U a 1-type. (We do
-- distinguish 'id' and 'not'.) The higher-level equality on the
-- 2-morphisms is trivial, i.e., all two level morphisms are
-- equated. This should yield a weak 2-category (i.e., a bicategory).

open import Pi1Examples
-- Pi1 is interesting as a programming language for reversible
-- circuits that has its own optimizer. This module has a few
-- examples.

-- How to make U a 2-type, 3-type, etc. ???

------------------------------------------------------------------------------
-- Equivalences between enumerated types (permutations) 

-- Finding a good representation of permutations is tricky.

-- We begin (in FinEquiv) by proving various equivalences between
-- finite sets like:
--   Fin (m + n) ≃ Fin m ⊎ Fin n
-- and
--   Fin (m * n) ≃ Fin m × Fin n
-- We make sure we have enough equivalences to model a commutative
-- semiring.

-- We can compose equivalences from FinEquiv and TypeEquiv to get
-- equivalences that correspond to permutations on finite sets, e.g.,
--   Fin (m + n) ≃ Fin m ⊎ Fin n ≃ Fin n ⊎ Fin m ≃ Fin (n + m)
-- At this point these permutations are represented as extensional
-- functions. In FinVec, we represent these extensional functions
-- using the one-line notation of permutations represented in Agda as
-- the type 'Vec (Fin m) n' (which we abbreviate as 'FinVec m n').
-- The setup allows us to directly extract one-line permutations from
-- the equivalences. For example, the one-line notation for:
--   FinVec ((m + n) + o) (m + (n + o))
-- is extracted using 'tabulate' of the equivalence between:
--   Fin ((m + n) + o) and Fin (m + (n + o))
-- The fact that we have equivalences for the entire commutative
-- semiring axioms means that we also easily define the one-line
-- notation for composing permutations:
--   FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ + n₁) (m₂ + n₂)
--   FinVec m₁ m₂ → FinVec n₁ n₂ → FinVec (m₁ * n₁) (m₂ * n₂)

-- What remains now is to explicitly include proofs that the one-line
-- notation has an inverse and that the two compositions yield the
-- identity permutation. This is one in ConcretePermutation and
-- consists mostly of making explicit the proofs that are implicit in
-- FinEquiv and FinVec.

-- The punchline is that finite sets and permutations form a symmetric
-- rig category.

open import FinEquiv
-- Establishes that Fin m ≃ Fin n is a commutative semiring

open import FinVec
-- Establishes that Vec (Fin m) n is a commutative semiring
-- (modulo symmetry)

open import FinVecProperties
-- Establishes properties of permutations represented in the one-line
-- notation by either exploiting their connections to type
-- equivalences or their representations as vectors. The most involved
-- property is probably:
-- (p₁ ×c p₂) ∘̂ (p₃ ×c p₄) ≡ (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄)

open import ConcretePermutation
-- Establishes that CPerm m n is a commutative semiring (including
-- symmetry now)

open import ConcretePermutationProperties
-- Establishes properties of concrete permutations that are necessary
-- to show that it is symmetric rig category

-- open import CPermCat -- IN PROGRESS
-- Establishes that CPerm m n is a symmetric rig category

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Wavefront ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~











-- Now we want to relate Pi-types and type equivalences. The punchline
-- would be that TypeEquivCat is isomorphic to Pi1Cat. But the setup
-- for Pi1Cat allows us to keep going up and down the levels unlike
-- the setup for TypeEquivCat which has extensional equivalence
-- hardwired and can't be generalized to level 2.

-- Are they really really necessary as a stepping stone to prove the
-- correspondence between TypeEquivCat and Pi1Cat ???

-- Equivalences between finite sets (enumerations and permutations);
-- Equivalences between setoids; Equivalences between equivalences;
-- Unfinished files; Unused files

open import EnumEquiv
-- equivalence between A and Fin m is an enumeration of A

open import SetoidEquiv
-- do a version of EquivSetoid specialized for finite sets that
-- include an enumeration just like quasi-inverses include one
-- particular function to specify the equivalence; must really be done
-- in conjection with SEquivSCPermEquiv so let's wait until
-- dependencies satisfied...

open import SEquivSCPermEquiv
-- open import PiPerm -- IN PROGRESS
open import PiEquiv

-- open import SkFinSetCategory
-- open import Pim1Cat

-- open import LeftCancellation
-- Proves that ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A ≃ B
-- open import RepresPerm
-- open import Groupoid
-- should be subsumed by Categories.Groupoid

------------------------------------------------------------------------------
