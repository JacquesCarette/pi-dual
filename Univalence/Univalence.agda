module Univalence where

-- Basic utilities                      -- clean up 14 July

open import LeqLemmas                   -- clean up 13 July
open import FinNatLemmas                -- clean up 13 July
open import SubstLemmas                 -- clean up 13 July
open import FiniteFunctions             -- clean up 13 July
open import PathLemmas                  -- clean up 14 July
open import VectorLemmas                -- clean up 13 July
open import Proofs                      -- clean up 14 July
-- open import DivModUtils              -- no longer  

-- Proofs is a wrapper over all the basic utilities
-- The only thing imported from now on is Proofs

-- Structures (Definitions)

open import SetoidUtils                 -- 
open import Groupoid                    -- 

{--
from Categories but does not all work with new Agda version yet
open import Everything
--}

-- Equivalences and their properties

open import Equiv                       -- 
open import TypeEquiv                   -- 
open import FinEquiv                    -- 
open import LeftCancellation            -- 
open import Enumeration                 -- 
open import EquivSetoid                 -- 

-- Permutations

open import FinVec                      -- 
open import ConcretePermutation         --
open import RepresPerm                  --

-- Relating Equivalences and Permutations

open import SEquivSCPermEquiv           -- 

-- Pi

open import PiLevel0                    -- 
open import PiLevel1                    -- 

-- Relating Pi and Permutations
open import PiPerm                      -- 

-- Relating Pi and Equivalences
open import PiEquiv                     --

-- Structures (Instances)

open import TypeEquivCat                -- 
open import Pim2Cat                     -- 
open import Pi0Cat                      -- 
open import Pi1Cat                      -- 

{-- 
Unfinished
open import SkFinSetCategory  
open import CPermCat 
open import Pim1Cat
--}
