{-# OPTIONS --without-K #-}

module RepresPerm where

open import Enumeration
open import Equiv
open import TypeEquivalences using (idequiv)
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

record RPerm (A : Set) (n : ℕ) (B : Set) (m : ℕ) : Set where
  constructor rp
  field
    #A : Enum A n
    #B : Enum B m
    iso : A ≃ B

open RPerm

-- first theorem about these: same size!
thm1 : ∀ {n m} {A B} → (X : RPerm A n B m) → n ≡ m
thm1 {0} {0 } (rp _ _ _ ) = refl
thm1 {0} {suc m} (rp (fA , isoA) (fB , mkqinv g α β) (f , iso)) with fA (I.g (g zero))
  where module I = qinv iso
... | ()
thm1 {suc n} {0} (rp (fA , isoA) B≃Fm (f , iso)) with B≃Fm ⋆ f (IA.g zero)
  where module IA = qinv isoA
... | ()
thm1 {suc n} {suc m} {A} {B} (rp A≃Fsn B≃Fsm A≃B) = 
  cong suc (thm1 {n} {m} {Fin n} {Fin m} (rp idequiv idequiv Fn≃Fm))
  where
    Fsn≃Fsm : Fin (suc n) ≃ Fin (suc m)
    Fsn≃Fsm = trans≃ (trans≃ (sym≃ A≃Fsn) A≃B) B≃Fsm
    1+n≃1+m : (Fin 1 ⊎ Fin n) ≃ (Fin 1 ⊎ Fin m)
    1+n≃1+m = trans≃ (trans≃ (Plus.fwd-iso {suc 0} {n}) Fsn≃Fsm)
                                                    (sym≃ (Plus.fwd-iso {suc 0} {m}))
    ⊤⊎n≃⊤⊎m : (⊤ ⊎ Fin n) ≃ (⊤ ⊎ Fin m)
    ⊤⊎n≃⊤⊎m = trans≃ (trans≃ (path⊎ (sym≃ Fin1≃⊤)  idequiv) 1+n≃1+m) 
                                                    (path⊎ Fin1≃⊤ idequiv)
    Fn≃Fm = left-cancel-⊤ ⊤⊎n≃⊤⊎m
