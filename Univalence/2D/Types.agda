{-# OPTIONS --without-K #-}

module Types where

import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary

--

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

⟦_⟧ : U → Set 
⟦ ZERO ⟧        = ⊥ 
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

U∼ : U → Set₁
U∼ u = Rel ⟦ u ⟧ (Level.zero)

record Typ : Set₁ where
  field 
    carr : U
    auto : U∼ carr

BOOL : U
BOOL = PLUS ONE ONE

FALSE TRUE : ⟦ BOOL ⟧
FALSE = inj₁ tt
TRUE  = inj₂ tt

data ONE∼ : U∼ ONE where
  id : ONE∼ tt tt

data BOOL∼ : U∼ BOOL where
  idff : BOOL∼ FALSE FALSE
  idft : BOOL∼ FALSE TRUE
  idtf : BOOL∼ TRUE  FALSE
  idtt : BOOL∼ TRUE  TRUE

--


{--
Then < Bool , ~* > is essentially < Unit , ~= >

Now we need to define what it means to say < U1, ~1> + < U2, ~2 > etc.
and then what it means for two types to be equivalent etc. etc. etc.
--}
