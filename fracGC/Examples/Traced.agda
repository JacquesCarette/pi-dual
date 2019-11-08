{-# OPTIONS --without-K #-}

module Examples.Traced where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Singleton
open import PiFrac
open import Trace
open import Reasoning

open import Examples.BooleanCircuits

------------------------------------------------------------------

-- Example in Sec. 4.3 from Abramsky's paper
-- http://www.cs.ox.ac.uk/files/341/calco05.pdf

q : {A1 A2 A3 A4 B1 B2 B3 B4 : 𝕌} →
  (f1 : A1 ⟷ B2) →
  (f2 : A2 ⟷ B4) →
  (f3 : A3 ⟷ B3) →
  (f4 : A4 ⟷ B1) →
  A1 ×ᵤ (A2 ×ᵤ (A3 ×ᵤ A4)) ⟷ B1 ×ᵤ (B2 ×ᵤ (B3 ×ᵤ B4))
q {A1} {A2} {A3} {A4} {B1} {B2} {B3} {B4} f1 f2 f3 f4 =
  (A1 ×ᵤ A2 ×ᵤ A3 ×ᵤ A4)     ⟷⟨ f1 ⊗ (f2 ⊗ (f3 ⊗ f4)) ⟩
  (B2 ×ᵤ B4 ×ᵤ B3 ×ᵤ B1)     ⟷⟨ assocl⋆ ⟩
  (B2 ×ᵤ B4) ×ᵤ (B3 ×ᵤ B1)   ⟷⟨ swap⋆ ⟩
  (B3 ×ᵤ B1) ×ᵤ (B2 ×ᵤ B4)   ⟷⟨ swap⋆ ⊗ id⟷ ⟩
  (B1 ×ᵤ B3) ×ᵤ (B2 ×ᵤ B4)   ⟷⟨ assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⟩
  B1 ×ᵤ ((B3 ×ᵤ B2) ×ᵤ B4)   ⟷⟨ id⟷ ⊗ ((swap⋆ ⊗ id⟷) ⊚ assocr⋆) ⟩
  B1 ×ᵤ (B2 ×ᵤ (B3 ×ᵤ B4)) □

q' : {A1 U2 U3 U4 B1 : 𝕌} →
  (f1 : A1 ⟷ U2) →
  (f2 : U2 ⟷ U4) →
  (f3 : U3 ⟷ U3) →
  (f4 : U4 ⟷ B1) → (v : ⟦ A1 ⟧) (u3 : ⟦ U3 ⟧)  → (u3-fix : eval f3 u3 ≡ u3) →
  let u2 = eval f1 v in
  let u4 = eval f2 u2 in
  ● A1 [ v ] ⟷ ● B1 [ proj₁ (eval (q f1 f2 f3 f4) (v , u2 , u3 , u4)) ]
q' f1 f2 f3 f4 v u3 u3fix =
  trace v (q f1 f2 f3 f4) (( u2 , ( u3 , u4 ) ), cong₂ _,_ refl (cong₂ _,_ u3fix refl))
  where
    u2 = eval f1 v
    u3′ = eval f3 u3
    u4 = eval f2 u2

-- The point is that q' acts in a very particular way:
q'-closed-form : {A1 U2 U3 U4 B1 : 𝕌} →
  (f1 : A1 ⟷ U2) →
  (f2 : U2 ⟷ U4) →
  (f3 : U3 ⟷ U3) →
  (f4 : U4 ⟷ B1) → (u3 : ⟦ U3 ⟧) (u3-fix : eval f3 u3 ≡ u3) → (v : ⟦ A1 ⟧) →
  proj₁ (eval (q' f1 f2 f3 f4 v u3 u3-fix) (v , refl)) ≡ eval (f1 ⊚ f2 ⊚ f4) v
q'-closed-form f1 f2 f3 f4 u3 u3fix v = refl

---------------------------------------------------------------------------------
-- I think the examples below are 'obsolete', in the sense that the one above
-- is more faithful to the original, and more general too.  Delete?
p : {A1 A2 A3 A4 : 𝕌} →
    (A1 ×ᵤ A2) ×ᵤ (A3 ×ᵤ A4) ⟷ (A2 ×ᵤ A4) ×ᵤ (A3 ×ᵤ A1)
p = (swap⋆ ⊗ swap⋆) ⊚
       assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⊚ (id⟷ ⊗ (swap⋆ ⊗ id⟷)) ⊚
       (id⟷ ⊗ assocr⋆) ⊚ assocl⋆ ⊚ (id⟷ ⊗ swap⋆)

p' : {A1 A2 A3 A4 : 𝕌} →
    ((A1 ×ᵤ A2) ×ᵤ A4) ×ᵤ A3 ⟷ ((A2 ×ᵤ A4) ×ᵤ A1) ×ᵤ A3
p' = assocr⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚ p ⊚ (id⟷ ⊗ swap⋆) ⊚ assocl⋆

p2 : 𝔹 ×ᵤ (𝔹 ×ᵤ (𝔹 ×ᵤ 𝔹)) ⟷ 𝔹 ×ᵤ (𝔹 ×ᵤ (𝔹 ×ᵤ 𝔹))
p2 = assocl⋆ ⊚ (swap⋆ ⊗ swap⋆) ⊚
       assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⊚ (id⟷ ⊗ (swap⋆ ⊗ id⟷)) ⊚
       (id⟷ ⊗ assocr⋆) ⊚ assocl⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚ assocr⋆

p2' : (v : ⟦ 𝔹 ⟧) →
      ● 𝔹 [ v ] ⟷ ● 𝔹 [ proj₁ (proj₁ (eval p ((v , v) , (v , v)))) ]
p2' v = trace v p2 ((v , (v , v)) , refl)

---------------------------------------------------------------------------------
-- Examples to build

-- A <-> 1 / (1/A)
-- 1 / (A x B) <-> 1/A x 1/B
-- (A <-> B) -> (1/A <-> 1/B)

-- Intuition:
-- 1/A x B is a space transformer; takes A space and returns B space
-- denote space transformers as A ⊸ B
--
-- Best we can do:
-- we need Singletons, so |a ⊸ b| is 1 component of a function.
_⊸_ : {A : 𝕌} → (a : ⟦ A ⟧) → {B : 𝕌} → (b : ⟦ B ⟧) → 𝕌
_⊸_ {A} a {B} b = 𝟙/● A [ a ] ×ᵤ ● B [ b ]

-- revrev : {A : 𝕌} {a : ⟦ A ⟧} {a⋆ : ⟦ 𝟙/● A [ a ] ⟧} →
--          ● A [ a ] ⟷ 𝟙/● A [ {!!} ]
-- revrev = {!!}

-- It can be applied in a very special case:  (a ⊸ b) x ● A [ a ] <-> ● B [ b ]
app : {A B : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} → (a ⊸ b) ×ᵤ ● A [ a ] ⟷ ● B [ b ]
app {A} {B} {a} {b} =
  (𝟙/● A [ a ] ×ᵤ ● B [ b ]) ×ᵤ ● A [ a ] ⟷⟨ swap⋆ ⊗ id⟷ ⟩
  (● B [ b ] ×ᵤ 𝟙/● A [ a ]) ×ᵤ ● A [ a ] ⟷⟨ assocr⋆ ⊚ (id⟷ ⊗ (swap⋆ ⊚ ε a)) ⟩
  ● B [ b ] ×ᵤ 𝟙                          ⟷⟨ unite⋆r ⟩
  ● B [ b ] □

id⊸ : {A : 𝕌} {a : ⟦ A ⟧} → (a ⊸ a) ⟷ 𝟙
id⊸ {A} {a} =
  (𝟙/● A [ a ] ×ᵤ ● A [ a ]) ⟷⟨ swap⋆ ⟩
  (● A [ a ] ×ᵤ 𝟙/● A [ a ]) ⟷⟨ ε a ⟩
  𝟙 □

comp⊸ : {A B C : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {c : ⟦ C ⟧} → (a ⊸ b) ×ᵤ (b ⊸ c) ⟷ (a ⊸ c)
comp⊸ {A} {B} {C} {a} {b} {c} =
  (𝟙/● A [ a ] ×ᵤ ● B [ b ]) ×ᵤ (𝟙/● B [ b ] ×ᵤ ● C [ c ]) ⟷⟨ assocr⋆ ⟩
  𝟙/● A [ a ] ×ᵤ (● B [ b ] ×ᵤ (𝟙/● B [ b ] ×ᵤ ● C [ c ])) ⟷⟨ id⟷ ⊗ assocl⋆ ⟩
  𝟙/● A [ a ] ×ᵤ (● B [ b ] ×ᵤ 𝟙/● B [ b ]) ×ᵤ ● C [ c ]   ⟷⟨ id⟷ ⊗ (ε b ⊗ id⟷) ⟩
  𝟙/● A [ a ] ×ᵤ (𝟙 ×ᵤ ● C [ c ])                          ⟷⟨ id⟷ ⊗ unite⋆l ⟩
  𝟙/● A [ a ] ×ᵤ ● C [ c ] □

-- can we do this?
-- curry⊸ : {A B C : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {c : ⟦ C ⟧}
--        → (● A [ a ] ×ᵤ (b ⊸ c)) ⟷ (a ⊸ {!!}) -- what do we put here?
-- curry⊸ {A} {B} {C} {a} {b} {c} = {!!}

-- B/A × D/C ⟷ B × D / A × C
dist×/ : {A B C D : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {c : ⟦ C ⟧} {d : ⟦ D ⟧}
       → (a ⊸ b) ×ᵤ (c ⊸ d) ⟷ ((a , c) ⊸ (b , d))
dist×/ {A} {B} {C} {D} {a} {b} {c} {d} =
  (𝟙/● A [ a ] ×ᵤ ● B [ b ]) ×ᵤ (𝟙/● C [ c ] ×ᵤ ● D [ d ]) ⟷⟨ assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⟩
  (𝟙/● A [ a ] ×ᵤ (● B [ b ] ×ᵤ 𝟙/● C [ c ]) ×ᵤ ● D [ d ]) ⟷⟨ id⟷ ⊗ (swap⋆ ⊗ id⟷) ⟩
  (𝟙/● A [ a ] ×ᵤ (𝟙/● C [ c ] ×ᵤ ● B [ b ]) ×ᵤ ● D [ d ]) ⟷⟨ (id⟷ ⊗ assocr⋆) ⊚ assocl⋆ ⟩
  (𝟙/● A [ a ] ×ᵤ 𝟙/● C [ c ]) ×ᵤ (● B [ b ] ×ᵤ ● D [ d ]) ⟷⟨ fracr ⊗ tensorr ⟩
  (𝟙/● A ×ᵤ C [ a , c ]) ×ᵤ (● B ×ᵤ D [ b , d ]) □

-- 1/A x 1/B <-> 1 / (A x B)
rev× : {A B : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
     → (a ⊸ tt) ×ᵤ (b ⊸ tt) ⟷ ((a , b) ⊸ tt)
rev× {A} {B} {a} {b} =
  (𝟙/● A [ a ] ×ᵤ ● 𝟙 [ tt ]) ×ᵤ (𝟙/● B [ b ] ×ᵤ ● 𝟙 [ tt ]) ⟷⟨ dist×/ ⟩
  (𝟙/● A ×ᵤ B [ a , b ] ×ᵤ ● 𝟙 ×ᵤ 𝟙 [ tt , tt ]) ⟷⟨ id⟷ ⊗ lift unite⋆l ⟩
  (𝟙/● A ×ᵤ B [ a , b ] ×ᵤ ● 𝟙 [ tt ]) □

-- trivial : ● 𝟙 [ tt ] ⟷ 𝟙
-- trivial = {!!}

-- (A <-> B) -> (1/A <-> 1/B)
-- rev : {A B : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
--     → ● A [ a ] ⟷ ● B [ b ] → (a ⊸ tt) ⟷ (b ⊸ tt)
-- rev {A} {B} {a} {b} p =
--   (𝟙/● A [ a ] ×ᵤ ● 𝟙 [ tt ]) ⟷⟨ {!!} ⟩
--   (𝟙/● B [ b ] ×ᵤ ● 𝟙 [ tt ]) □

-- this is strange
-- A/C + B/C <-> (A + B) / C
-- factor+/l : {A B C : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {c : ⟦ C ⟧}
--           → (c ⊸ a) +ᵤ (c ⊸ b) ⟷ (_⊸_ {C} c {A +ᵤ B} (inj₁ a))
-- factor+/l {A} {B} {C} {a} {b} {c} =
--   (𝟙/● C [ c ] ×ᵤ ● A [ a ] +ᵤ 𝟙/● C [ c ] ×ᵤ ● B [ b ]) ⟷⟨ factorl ⟩
--   (𝟙/● C [ c ] ×ᵤ (● A [ a ] +ᵤ ● B [ b ])) ⟷⟨ id⟷ ⊗ {!!} ⟩
--   (𝟙/● C [ c ] ×ᵤ ● A +ᵤ B [ inj₁ a ]) □

-- same issue here with the +
-- A/B + C/D <-> (A x D + B x C) / (B x D)

-- SAT solver Sec. 5 from https://www.cs.indiana.edu/~sabry/papers/rational.pdf
