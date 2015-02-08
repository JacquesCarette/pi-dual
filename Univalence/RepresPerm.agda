{-# OPTIONS --without-K #-}

module RepresPerm where

open import Enumeration
open import Equiv
open import TypeEquivalences using (idequiv; path⊎)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero)
open import Data.Product using (_,_)
open import FinEquiv
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import LeftCancellation

-- A Representable Permutation consists of
-- 1. an Enumeration of A
-- 2. an Enumeration of B
-- 3. an isomorphism between A and B

record RPerm (A : Set) (B : Set) : Set where
  constructor rp
  field
    #A : Enum A
    #B : Enum B
    iso : A ≃ B

open RPerm
open Enum

-- first theorem about these: same size!
{-# TERMINATING #-}
thm1 : ∀ {A B} → (X : RPerm A B) → (n (#A X) ≡ n (#B X))
thm1 (rp (enum 0 _) (enum 0 _) _) = refl
thm1 (rp (enum Data.Nat.zero (fA , isoA)) (enum (suc m) (fB , mkqinv g α β)) (f , iso)) with fA (I.g (g zero))
  where module I = qinv iso
... | ()
thm1 (rp (enum (suc n) (fA , isoA)) (enum Data.Nat.zero B≃Fm) (f , iso)) with B≃Fm ⋆ f (IA.g zero)
  where module IA = qinv isoA
... | ()
thm1 {A} {B} (rp (enum (suc n) A≃Fsn) (enum (suc m) B≃Fsm) A≃B) = 
  cong suc (thm1 {Fin n} {Fin m} (rp (enum n idequiv) (enum m idequiv) Fn≃Fm))
  where
    Fsn≃Fsm : Fin (suc n) ≃ Fin (suc m)
    Fsn≃Fsm = trans≃ (trans≃ (sym≃ A≃Fsn) A≃B) B≃Fsm
    1+n≃1+m : (Fin 1 ⊎ Fin n) ≃ (Fin 1 ⊎ Fin m)
    1+n≃1+m = trans≃ (trans≃ (Plus.fwd-iso {suc 0} {n}) Fsn≃Fsm)
                                                    (sym≃ (Plus.fwd-iso {suc 0} {m}))
    ⊤⊎n≃⊤⊎m : (⊤ ⊎ Fin n) ≃ (⊤ ⊎ Fin m)
    ⊤⊎n≃⊤⊎m = trans≃ (trans≃ (path⊎ (sym≃ Plus.Fin1≃⊤)  idequiv) 1+n≃1+m) 
                                                    (path⊎ Plus.Fin1≃⊤ idequiv)
    Fn≃Fm = left-cancel-⊤ ⊤⊎n≃⊤⊎m
