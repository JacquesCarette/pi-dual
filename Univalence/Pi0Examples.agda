{-# OPTIONS --without-K #-}

module Pi0Examples where

open import PiU using (U; ZERO; ONE; PLUS; TIMES) 
open import PiLevel0
  using (_⟷_; 
         unite₊l; uniti₊l; unite₊r; uniti₊r; swap₊; assocl₊; assocr₊;
         unite⋆l; uniti⋆l; unite⋆r; uniti⋆r; swap⋆; assocl⋆; assocr⋆;
         absorbr; absorbl; factorzr; factorzl;
         dist; factor; distl; factorl;
         id⟷; _◎_; _⊕_; _⊗_)

------------------------------------------------------------------------------
-- Example circuits on booleans

BOOL : U
BOOL  = PLUS ONE ONE 

BOOL² : U
BOOL² = TIMES BOOL BOOL

-- Nicer syntax that shows intermediate values instead of the above
-- point-free notation of permutations

infixr 2  _⟷⟨_⟩_   
infix  2  _□       

_⟷⟨_⟩_ : (t₁ : U) {t₂ : U} {t₃ : U} → 
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃) 
_ ⟷⟨ α ⟩ β = α ◎ β

_□ : (t : U) → {t : U} → (t ⟷ t)
_□ t = id⟷

foldBool unfoldBool : BOOL ⟷ BOOL
foldBool = id⟷
unfoldBool = id⟷

------------------------------------------------------------------------------
-- Many ways of negating a BOOL. 

NOT : BOOL ⟷ BOOL
NOT = unfoldBool ◎ swap₊ ◎ foldBool
-- spec: (false , true) ∷ (true , false) ∷ []

NEG1 NEG2 NEG3 NEG4 NEG5 : BOOL ⟷ BOOL
NEG1 = unfoldBool ◎ swap₊ ◎ foldBool
-- spec: (false , true) ∷ (true , false) ∷ []
NEG2 = id⟷ ◎ NOT 
-- spec: (false , true) ∷ (true , false) ∷ []
NEG3 = NOT ◎ NOT ◎ NOT 
-- spec: (false , true) ∷ (true , false) ∷ []
NEG4 = NOT ◎ id⟷
-- spec: (false , true) ∷ (true , false) ∷ []
NEG5 = uniti⋆l ◎ swap⋆ ◎ (NOT ⊗ id⟷) ◎ swap⋆ ◎ unite⋆l
-- spec: (false , true) ∷ (true , false) ∷ []
NEG6 = uniti⋆r ◎ (NOT ⊗ id⟷) ◎ unite⋆r -- same as above, but shorter

-- CNOT

CNOT : BOOL² ⟷ BOOL²
CNOT = TIMES BOOL BOOL
         ⟷⟨ unfoldBool ⊗ id⟷ ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ dist ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT) ⟩
       PLUS (TIMES x BOOL) (TIMES y BOOL)
         ⟷⟨ factor ⟩
       TIMES (PLUS x y) BOOL
         ⟷⟨ foldBool ⊗ id⟷ ⟩
       TIMES BOOL BOOL □
  where x = ONE; y = ONE

-- spec: 
-- ((false , false) , false , false) ∷
-- ((false , true)  , false , true)  ∷
-- ((true  , false) , true  , true)  ∷
-- ((true  , true)  , true  , false) ∷ []

-- TOFFOLI

TOFFOLI : TIMES BOOL BOOL² ⟷ TIMES BOOL BOOL²
TOFFOLI = TIMES BOOL BOOL² 
            ⟷⟨ unfoldBool ⊗ id⟷ ⟩
          TIMES (PLUS x y) BOOL² 
            ⟷⟨ dist ⟩
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩ 
          PLUS (TIMES x BOOL²) (TIMES y BOOL²)
            ⟷⟨ factor ⟩
          TIMES (PLUS x y) BOOL²
            ⟷⟨ foldBool ⊗ id⟷ ⟩
         TIMES BOOL BOOL² □
  where x = ONE; y = ONE

-- spec:
-- ((false , false , false) , false , false , false) ∷
-- ((false , false , true)  , false , false , true)  ∷
-- ((false , true  , false) , false , true  , false) ∷
-- ((false , true  , true)  , false , true  , true)  ∷
-- ((true  , false , false) , true  , false , false) ∷
-- ((true  , false , true)  , true  , false , true)  ∷
-- ((true  , true  , false) , true  , true  , true)  ∷
-- ((true  , true  , true)  , true  , true  , false) ∷ []

-- Swaps for the type 1+(1+1)
-- We have three values in the type 1+(1+1) 
-- Let's call them a, b, and c
-- There 6 permutations. Using the swaps below we can express every permutation:
-- a b c id⟷
-- a c b SWAP23
-- b a c SWAP12
-- b c a ROTL
-- c a b ROTR
-- c b a SWAP13

SWAP12 SWAP23 SWAP13 ROTL ROTR : 
  PLUS ONE (PLUS ONE ONE) ⟷ PLUS ONE (PLUS ONE ONE)
SWAP12 = assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊
-- spec: 
-- (inj₁ tt        , inj₂ (inj₁ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₁ tt)        ∷ 
-- (inj₂ (inj₂ tt) , inj₂ (inj₂ tt)) ∷ []
SWAP23 = id⟷ ⊕ swap₊
-- spec: 
-- (inj₁ tt        , inj₁ tt)        ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₂ tt)) ∷
-- (inj₂ (inj₂ tt) , inj₂ (inj₁ tt)) ∷ []
SWAP13 = SWAP23 ◎ SWAP12 ◎ SWAP23 
-- spec: 
-- (inj₁ tt        , inj₂ (inj₂ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₁ tt)) ∷ 
-- (inj₂ (inj₂ tt) , inj₁ tt)        ∷ []
ROTR   = SWAP12 ◎ SWAP23
-- spec: 
-- (inj₁ tt        , inj₂ (inj₂ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₁ tt)        ∷ 
-- (inj₂ (inj₂ tt) , inj₂ (inj₁ tt)) ∷ []
ROTL   = SWAP13 ◎ SWAP23
-- spec: 
-- (inj₁ tt        , inj₂ (inj₁ tt)) ∷
-- (inj₂ (inj₁ tt) , inj₂ (inj₂ tt)) ∷ 
-- (inj₂ (inj₂ tt) , inj₁ tt)        ∷ []

-- The Peres gate is a universal gate: it takes three inputs a, b, and c, and
-- produces a, a xor b, (a and b) xor c

PERES : TIMES (TIMES BOOL BOOL) BOOL ⟷ TIMES (TIMES BOOL BOOL) BOOL
PERES = (id⟷ ⊗ NOT) ◎ assocr⋆ ◎ (id⟷ ⊗ swap⋆) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ (NOT ⊗ id⟷)) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ swap⋆) ◎ (id⟷ ⊗ (NOT ⊗ id⟷)) ◎ 
        TOFFOLI ◎ 
        (id⟷ ⊗ (NOT ⊗ id⟷)) ◎ assocl⋆
-- spec:
-- (((false , false) , false) , (false , false) , false) ∷
-- (((false , false) , true)  , (false , false) , true)  ∷
-- (((false , true)  , false) , (false , true)  , false) ∷
-- (((false , true)  , true)  , (false , true)  , true)  ∷
-- (((true  , false) , false) , (true  , true)  , false) ∷
-- (((true  , false) , true)  , (true  , true)  , true)  ∷
-- (((true  , true)  , false) , (true  , false) , true)  ∷
-- (((true  , true)  , true)  , (true  , false) , false) ∷ []

-- A reversible full adder: See http://arxiv.org/pdf/1008.3533.pdf
-- Input: (z, ((n1, n2), cin)))
-- Output (g1, (g2, (sum, cout)))
-- where sum = n1 xor n2 xor cin
-- and cout = ((n1 xor n2) and cin) xor (n1 and n2) xor z
FULLADDER : TIMES BOOL (TIMES (TIMES BOOL BOOL) BOOL) ⟷
            TIMES BOOL (TIMES BOOL (TIMES BOOL BOOL))
FULLADDER = 
  -- (z,((n1,n2),cin))
  swap⋆ ◎ 
  -- (((n1,n2),cin),z)
  (swap⋆ ⊗ id⟷) ◎ 
  -- ((cin,(n1,n2)),z)
  assocr⋆ ◎ 
  -- (cin,((n1,n2),z))
  swap⋆ ◎ 
  -- (((n1,n2),z),cin)
  (PERES ⊗ id⟷) ◎     
  -- (((n1,n1 xor n2),(n1 and n2) xor z),cin) 
  assocr⋆ ◎ 
  -- ((n1,n1 xor n2),((n1 and n2) xor z,cin))
  (id⟷ ⊗ swap⋆) ◎ 
  -- ((n1,n1 xor n2),(cin,(n1 and n2) xor z))
  assocr⋆ ◎ 
  -- (n1,(n1 xor n2,(cin,(n1 and n2) xor z)))
  (id⟷ ⊗ assocl⋆) ◎ 
  -- (n1,((n1 xor n2,cin),(n1 and n2) xor z))
  (id⟷ ⊗ PERES) ◎ 
  -- (n1,((n1 xor n2,n1 xor n2 xor cin),
  --      ((n1 xor n2) and cin) xor (n1 and n2) xor z))
  (id⟷ ⊗ assocr⋆)
  -- (n1,(n1 xor n2,
  --      (n1 xor n2 xor cin,((n1 xor n2) and cin) xor (n1 and n2) xor z)))
-- spec: 
-- ((false , (false , false) , false) , false , false , false , false) ∷
-- ((false , (false , false) , true)  , false , false , true  , false) ∷
-- ((false , (false , true)  , false) , false , true  , true  , false) ∷
-- ((false , (false , true)  , true)  , false , true  , false , true)  ∷
-- ((false , (true  , false) , false) , true  , true  , true  , false) ∷
-- ((false , (true  , false) , true)  , true  , true  , false , true)  ∷
-- ((false , (true  , true)  , false) , true  , false , false , true)  ∷
-- ((false , (true  , true)  , true)  , true  , false , true  , true)  ∷
-- ((true  , (false , false) , false) , false , false , false , true)  ∷
-- ((true  , (false , false) , true)  , false , false , true  , true)  ∷
-- ((true  , (false , true)  , false) , false , true  , true  , true)  ∷
-- ((true  , (false , true)  , true)  , false , true  , false , false) ∷
-- ((true  , (true  , false) , false) , true  , true  , true  , true)  ∷
-- ((true  , (true  , false) , true)  , true  , true  , false , false) ∷
-- ((true  , (true  , true)  , false) , true  , false , false , false) ∷
-- ((true  , (true  , true)  , true)  , true  , false , true  , false) ∷ []

------------------------------------------------------------------------------
-- Generalized CNOT and TOFFOLI

ttt : {t₁ t₂ t₃ t₄ : U} → 
  (TIMES (PLUS t₁ t₂) (PLUS t₃ t₄)) ⟷
  (PLUS (PLUS (PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)) (TIMES t₁ t₄))) (TIMES t₂ t₄)
ttt {t₁} {t₂} {t₃} {t₄} =
  (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊

-- generalized CNOT

gcnot : {A B C : U} →
        (TIMES (PLUS A B) (PLUS C C)) ⟷ (TIMES (PLUS A B) (PLUS C C))
gcnot = dist ◎ (id⟷ ⊕ (id⟷ ⊗ swap₊)) ◎ factor

-- Generalized Toffolli gate.  See what 'arithmetic' it performs.

GToffoli : {A B C D E : U} →
           TIMES (PLUS A B) (TIMES (PLUS C D) (PLUS E E)) ⟷
           TIMES (PLUS A B) (TIMES (PLUS C D) (PLUS E E))
GToffoli = dist ◎ (id⟷ ⊕ (id⟷ ⊗ gcnot)) ◎ factor

------------------------------------------------------------------------------

