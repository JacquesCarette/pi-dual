module NCCorrectness where

open import NC

-- Correctness proofs for normal combinators, to be used in a univalence proof

-- TODO: define the "meaning" of a combinator (ideally somewhere else)
-- There seem to be a few functions that evaluate a combinator; we should probably just
-- choose one and call it "evalComb" or something so we have something to work with here.

-- To show: equivToVec and vecToEquiv preserve meaning
-- To show: equivToVec ∘ vecToEquiv is the identity, on the nose
-- To show: a similar property for the composition in the other direction?

-- To show: vecToComb and combToVec preserve meaning (so normalizing like this is safe)

