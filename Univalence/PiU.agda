{-# OPTIONS --without-K #-}

module PiU where

open import Data.Nat using (ℕ; _+_; _*_)

------------------------------------------------------------------------------
-- Define the ``universe'' for Pi.  All versions of Pi share the same
-- universe.  Where they differ is in what combinators exist between
-- members of the universe.
-- 
-- ZERO is a type with no elements
-- ONE is a type with one element 'tt'
-- PLUS ONE ONE is a type with elements 'false' and 'true'
-- and so on for all finite types built from ZERO, ONE, PLUS, and TIMES
-- 
-- We also have that U is a type with elements ZERO, ONE, PLUS ONE ONE, 
--   TIMES BOOL BOOL, etc.

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

-- defines the size of a finite type

toℕ : U → ℕ
toℕ ZERO = 0
toℕ ONE = 1
toℕ (PLUS t₁ t₂) = toℕ t₁ + toℕ t₂
toℕ (TIMES t₁ t₂) = toℕ t₁ * toℕ t₂ 

------------------------------------------------------------------------------
