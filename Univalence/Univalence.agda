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

open import Groupoid                      

{--
We use (and extend) the package Categories.

Everything we need works but some of the other parts do not work with
current version of Agda

open import Everything
--}

------------------------------------------------------------------------------
-- Equivalences and their properties      

open import Equiv                         
-- Defines extensional equality of functions ∼; quasi-inverses; and
-- then equivalences ≃
open import TypeEquiv                     
-- Proves that types and type equivalences form a commutative semiring
open import FinEquiv                      
-- Proves that that finite sets and equivalences form a commutative
-- semiring
open import SetoidEquiv                   -- HERE
open import EnumEquiv                     -- TODO
-- do a version of EquivSetoid specialized for finite sets that
-- include an enumeration just like quasi-inverses include one
-- particular function to specify the equivalence

------------------------------------------------------------------------------
-- Permutations                           -- TODO

open import FinVec                        -- TODO
open import ConcretePermutation           -- TODO

------------------------------------------------------------------------------
-- Relating Equivalences and Permutations -- TODO

open import SEquivSCPermEquiv             -- TODO

------------------------------------------------------------------------------
-- Pi                                     -- TODO

open import PiLevel0                      -- TODO
open import PiLevel1                      -- TODO

------------------------------------------------------------------------------
-- Relating Pi and Permutations           -- TODO

open import PiPerm                        -- TODO

------------------------------------------------------------------------------
-- Relating Pi and Equivalences           -- TODO

open import PiEquiv                       -- TODO

------------------------------------------------------------------------------
-- Structures (Instances)                 -- TODO

open import TypeEquivCat                  -- TODO
open import Pim2Cat                       -- TODO
open import Pi0Cat                        -- TODO
open import Pi1Cat                        -- TODO

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
--}

------------------------------------------------------------------------------
