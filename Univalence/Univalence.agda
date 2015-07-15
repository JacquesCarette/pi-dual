module Univalence where

-- Basic utilities                        -- clean up 14 July

open import LeqLemmas                     -- clean up 13 July
open import FinNatLemmas                  -- clean up 13 July
open import SubstLemmas                   -- clean up 13 July
open import FiniteFunctions               -- clean up 13 July
open import PathLemmas                    -- clean up 14 July
open import VectorLemmas                  -- clean up 13 July
open import Proofs                        -- clean up 14 July

-- Proofs is a wrapper over all the basic utilities
-- The only thing imported from now on is Proofs

-- Structures (Definitions)               -- clean up 14 July

open import Groupoid                      -- clean up 14 July

{--
We use (and extend) the package Categories.

Everything we need works but some of the other parts do not work with
current version of Agda

open import Everything
--}

-- Equivalences and their properties      -- 

open import Equiv                         -- clean up 14 July
-- Defines extensional equality of functions ∼; quasi-inverses; and
-- then equivalences ≃
open import TypeEquiv                     -- clean up 14 July
-- Proves that types and type equivalences form a commutative semiring
open import FinEquiv                      -- clean up 14 July
-- Proves that that finite sets and equivalences form a commutative
-- semiring
open import LeftCancellation              -- clean up 14 July
-- Proves that ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A ≃ B
open import Enumeration                   -- 
open import EquivSetoid                   -- 

-- Permutations                           -- 

open import FinVec                        -- 
open import ConcretePermutation           --
open import RepresPerm                    --

-- Relating Equivalences and Permutations -- 

open import SEquivSCPermEquiv             -- 

-- Pi                                     --

open import PiLevel0                      -- 
open import PiLevel1                      -- 

-- Relating Pi and Permutations           -- 

open import PiPerm                        -- 

-- Relating Pi and Equivalences           -- 

open import PiEquiv                       --

-- Structures (Instances)                 -- 

open import TypeEquivCat                  -- 
open import Pim2Cat                       -- 
open import Pi0Cat                        -- 
open import Pi1Cat                        -- 

{-- 

Unfinished files

open import SkFinSetCategory  
open import CPermCat 
open import Pim1Cat
--}
