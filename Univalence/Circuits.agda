{-# OPTIONS --without-K #-}

module Circuits where

open import PiLevel0
  using (U; ZERO; ONE; PLUS; TIMES; BOOL; BOOL²;
         _⟷_;
        unite₊; uniti₊; swap₊; assocl₊; assocr₊;
        unite⋆; uniti⋆; swap⋆; assocl⋆; assocr⋆;
        absorbr; absorbl; factorzr; factorzl; dist; factor;
        id⟷; _◎_; _⊕_; _⊗_;
        _⟷⟨_⟩_; _□;
        NOT; CNOT; TOFFOLI)

------------------------------------------------------------------------------

SWAP : BOOL² ⟷ BOOL²
SWAP = swap⋆

CONTROL : {t : U} → (t ⟷ t) → (TIMES BOOL t ⟷ TIMES BOOL t)
CONTROL {t} f = TIMES BOOL t
                  ⟷⟨ id⟷ ⟩ 
                TIMES (PLUS x y) t
                  ⟷⟨ dist ⟩
                PLUS (TIMES x t) (TIMES y t)
                  ⟷⟨ id⟷ ⊕ (id⟷ ⊗ f) ⟩ 
                PLUS (TIMES x t) (TIMES y t)
                  ⟷⟨ factor ⟩
                TIMES (PLUS x y) t
                  ⟷⟨ id⟷ ⟩
                TIMES BOOL t □
  where x = ONE; y = ONE

FREDKIN : TIMES BOOL BOOL² ⟷ TIMES BOOL BOOL²
FREDKIN = CONTROL SWAP

------------------------------------------------------------------------------
-- Fig. 4 in http://arxiv.org/pdf/1110.2574v2.pdf

-- (e) cycles

-- (c) reversible truth table

------------------------------------------------------------------------------

