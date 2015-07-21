{-# OPTIONS --without-K #-}

module PiLevelm2 where

open import PiU using (U)

------------------------------------------------------------------------------
-- We define a trivial relation on finite types that identifies all
-- types; this effectively makes U a contractible (-2)-type, i.e., a
-- singleton

data _⟷_ : U → U → Set where
  collapse : {t₁ t₂ : U} → t₁ ⟷ t₂

------------------------------------------------------------------------------
