{-# OPTIONS --without-K #-}

{- Define the ``universe'' for Pi.  All versions of Pi
  share the same universe.  Where they differ is in what
  combinators exist between members of the universe. -}

module PiU where

open import Data.Nat using (ℕ; _+_; _*_)

data U : Set where
  ZERO  : U
  ONE   : U
  PLUS  : U → U → U
  TIMES : U → U → U

toℕ : U → ℕ
toℕ ZERO = 0
toℕ ONE = 1
toℕ (PLUS t₁ t₂) = toℕ t₁ + toℕ t₂
toℕ (TIMES t₁ t₂) = toℕ t₁ * toℕ t₂ 
