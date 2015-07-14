module Univalence where

-- Basic utilities

open import LeqLemmas                   -- clean up 13 July
open import FinNatLemmas                -- clean up 13 July
open import SubstLemmas                 -- 
open import VectorLemmas                -- 
open import FiniteFunctions             -- 
open import Proofs                      -- 
open import PathLemmas                  -- 
open import DivModUtils                 -- 
open import LeftCancellation            -- 
open import Enumeration                 -- 
open import EquivSetoid                 -- 

-- Structures (Definitions)

open import SetoidUtils                 -- 
open import Groupoid                    -- 

{--
from Categories but does not all work with new Agda version yet
open import Everything
--}

-- Equivalences

open import Equiv                       -- 
open import TypeEquiv                   -- 
open import FinEquiv                    -- 
open import SEquivSCPermEquiv           -- 

-- Permutations

open import ConcretePermutation         -- 
open import PiPerm                      -- 

-- Structures (Instances)

open import FinVec                      -- 
open import TypeEquivCat                -- 
open import PiLevel0                    -- 
open import PiLevel1                    -- 
open import Pim2Cat                     -- 
open import Pi0Cat                      -- 
open import Pi1Cat                      -- 

{-- 
Unfinished
open import SkFinSetCategory  
open import CPermCat 
open import Pim1Cat
--}
