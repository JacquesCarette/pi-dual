{-# OPTIONS --without-K #-}

module FinEquivEquivPlusTimes where

open import Data.Product using (_×_; proj₁; proj₂)

open import Equiv using (refl∼; sym∼; sym≃; _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv)

open import FinEquivPlusTimes using (F0≃⊥; module Plus; module Times)
open Plus using (⊎≃+; +≃⊎)
open Times using (×≃*; *≃×)

open import FinEquivTypeEquiv
  using (_fin≃_; module PlusE; module TimesE; module PlusTimesE)
open PlusE using (_+F_; unite+; uniti+; unite+r; uniti+r; assocr+; assocl+;
                 swap+; sswap+)
open TimesE using (_*F_; unite*; uniti*; unite*r; uniti*r; assocr*; assocl*;
                  swap*; sswap*)
open PlusTimesE using (distz; factorz; distzr; factorzr;
                       dist; factor; distl; factorl)
open import EquivEquiv
open import TypeEquiv
  using (unite₊equiv; unite₊′equiv; assocl₊equiv)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as P using (refl)

import TypeEquivEquiv as T
  using ([id,id]≋id; ⊎●≋●⊎; _⊎≋_; sym≃-distrib⊎;
    unite₊-nat; assocl₊-nat;
    [g+1]●[1+f]≋[1+f]●[g+1]; unite₊′-nat;
    id×id≋id; ×●≋●×;
    -- much lower down
    0×0≃0)

------------------------------------------------------------------------------
-- Equivalences for distributivity

distl-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} →
    distl {m'} {n'} {o'} ● (f *F (g +F h)) ≋
      ((f *F g) +F (f *F h)) ● distl {m} {n} {o}
distl-nat = {!!} 

factorl-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} →
    factorl {m'} {n'} {o'} ● ((f *F g) +F (f *F h)) ≋
      (f *F (g +F h)) ● factorl {m} {n} {o}
factorl-nat = {!!} 

dist-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} →
    dist {m'} {n'} {o'} ● ((f +F g) *F h) ≋
      ((f *F h) +F (g *F h)) ● dist {m} {n} {o}
dist-nat = {!!} 

factor-nat : {m n o m' n' o' : ℕ}
    {f : m fin≃ m'} {g : n fin≃ n'} {h : o fin≃ o'} →
    factor {m'} {n'} {o'} ● ((f *F h) +F (g *F h)) ≋
      ((f +F g) *F h) ● factor {m} {n} {o}
factor-nat = {!!} 

distzr-nat : {m n : ℕ} {f : m fin≃ n} {g : 0 fin≃ 0} →
    distzr {n} ● (f *F g) ≋ g ● distzr {m}
distzr-nat = {!!} 

factorzr-nat : {m n : ℕ} {f : m fin≃ n} {g : 0 fin≃ 0} →
    factorzr {n} ● g ≋ (f *F g) ● factorzr {m}
factorzr-nat = {!!} 

distz-nat : {m n : ℕ} → {f : m fin≃ n} → {g : 0 fin≃ 0} →
    distz {n} ● (g *F f) ≋ g ● distz {m}
distz-nat = {!!} 

factorz-nat : {m n : ℕ} → {f : m fin≃ n} → {g : 0 fin≃ 0} →
    factorz {n} ● g ≋ (g *F f) ● factorz {m}
factorz-nat = {!!} 

A×[B⊎C]≃[A×C]⊎[A×B] : {m n o : ℕ} → 
    distl {m} {o} {n} ● (id≃ {A = Fin m} *F swap+ {n} {o}) ≋
    swap+ {m * n} {m * o} ● distl {m} {n} {o}
A×[B⊎C]≃[A×C]⊎[A×B] = {!!} 

[A⊎B]×C≃[C×A]⊎[C×B] : {m n o : ℕ} → 
    (swap* {m} {o} +F swap* {n} {o}) ● dist {m} {n} {o} ≋
    distl {o} {m} {n} ● swap* {m + n} {o}
[A⊎B]×C≃[C×A]⊎[C×B] = {!!} 

[A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D : {m n o p : ℕ} →
    (dist {m} {n} {p} +F id≃ {A = Fin (o * p)}) ●
      dist {m + n} {o} {p} ● (assocl+ {m} {n} {o} *F id≃ {A = Fin p}) ≋
    assocl+ {m * p} {n * p} {o * p} ●
      (id≃ {A = Fin (m * p)} +F dist {n} {o} {p}) ● dist {m} {n + o} {p}
[A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D = {!!} 

A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D : {m n o p : ℕ} →
    distl {m * n} {o} {p} ● assocl* {m} {n} {o + p} ≋
    (assocl* {m} {n} {o} +F assocl* {m} {n} {p}) ●
      distl {m} {n * o} {n * p} ● (id≃ {A = Fin m} *F distl {n} {o} {p})
A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D = {!!} 

[A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D : {m n o p : ℕ} →
    assocl+ {(m * o) + (n * o)} {m * p} {n * p} ●
      (dist {m} {n} {o} +F dist {m} {n} {p}) ●
      distl {m + n} {o} {p} ≋
    (assocl+ {m * o} {n * o} {m * p} +F id≃ {A = Fin (n * p)}) ●
      ((id≃ {A = Fin (m * o)} +F swap+ {m * p} {n * o}) +F id≃ {A = Fin (n * p)}) ●
      (assocr+ {m * o} {m * p} {n * o} +F id≃ {A = Fin (n * p)}) ●
      assocl+ {(m * o) + (m * p)} {n * o} {n * p} ● 
      (distl {m} {o} {p} +F distl {n} {o} {p}) ● dist {m} {n} {o + p}
[A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D = {!!} 

-- can't be done via equational reasoning!?!?
-- cannot even dig into T.0×0≃0 as f≋ is abstract
0×0≃0 : distz {0} ≋ distzr {0}
0×0≃0 = eq (λ {()}) (λ {()}) -- wow, talk about low-level reasoning!
  
0×[A⊎B]≃0 : {m n : ℕ} →
    distz {m + n} ≋ unite+ ● (distz {m} +F distz {n}) ● distl {0} {m} {n}
0×[A⊎B]≃0 = {!!} 

0×1≃0 : unite*r ≋ distz {1}
0×1≃0 = {!!} 

A×0≃0 : {m : ℕ} → distzr {m} ≋ distz {m} ● swap* {m} {0}
A×0≃0 = {!!} 

0×A×B≃0 : {m n : ℕ} →
    distz {m * n} ≋
    distz {n} ● (distz {m} *F id≃ {A = Fin n}) ● assocl* {0} {m} {n}
0×A×B≃0 = {!!} 

A×0×B≃0 : {m n : ℕ} →
    distzr {m} ● (id≃ {A = Fin m} *F distz {n})  ≋ 
    distz {n} ● (distzr {m} *F id≃ {A = Fin n}) ● assocl* {m} {0} {n}
A×0×B≃0 = {!!} 

A×[0+B]≃A×B : {m n : ℕ} →
    (id≃ {A = Fin m} *F unite+ {n}) ≋
    unite+ ● (distzr {m} +F id≃) ● distl {m} {0} {n}
A×[0+B]≃A×B = {!!} 

1×[A⊎B]≃A⊎B : {m n : ℕ} →
    unite* ≋ (unite* {m} +F unite* {n}) ● distl {1} {m} {n}
1×[A⊎B]≃A⊎B = {!!} 

------------------------------------------------------------------------------
