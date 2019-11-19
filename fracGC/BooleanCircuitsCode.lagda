\newcommand{\BCCONE}{%
\begin{code}
{-# OPTIONS --without-K #-}

module BooleanCircuitsCode where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Singleton
open import PiFrac
open import Reasoning

------------------------------------------------------------------------------
\end{code}}
\newcommand{\Bexamples}{%
\begin{code}
𝔹 𝔹² 𝔹³ 𝔹⁴ : 𝕌
𝔹   = 𝟙 +ᵤ 𝟙
𝔹²  = 𝔹 ×ᵤ 𝔹
𝔹³  = 𝔹 ×ᵤ 𝔹²
𝔹⁴  = 𝔹 ×ᵤ 𝔹³

ctrl : {A : 𝕌} → (A ⟷ A) → 𝔹 ×ᵤ A ⟷ 𝔹 ×ᵤ A
ctrl c = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ c)) ⊚ factor

NOT : 𝔹 ⟷ 𝔹
NOT = swap₊

CNOT : 𝔹² ⟷ 𝔹²
CNOT = ctrl NOT

TOFFOLI : 𝔹³ ⟷ 𝔹³
TOFFOLI = ctrl (ctrl NOT)

CTOFFOLI : 𝔹⁴ ⟷ 𝔹⁴
CTOFFOLI = ctrl (ctrl (ctrl NOT))
\end{code}}  
\newcommand{\BCCTWO}{%
\begin{code}
-- Ancilla examples from literature

-- Fig. 2 in Ricercar

fig2a : 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ⟷
        𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹
fig2a = ctrl (ctrl (ctrl NOT))

-- first write the circuit with the additional ancilla

fig2b' : ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) ⟷ ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹)
fig2b' =
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ ctrl (ctrl NOT))  -- first ccnot
  ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷)                        -- move it back
  ⊚
  (assocl⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ swap⋆) ⊚
  (id⟷ ⊗ ctrl (ctrl NOT))  -- second ccnot
  ⊚
  (id⟷ ⊗ swap⋆) ⊚
  assocl⋆ ⊚
  (assocr⋆ ⊗ id⟷)                      -- move it back
  ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ ctrl (ctrl NOT))  -- third ccnot
  ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷)                        -- move it back

------------------------------------------------------------------------------
-- Examples


PERES : (𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹 ⟷ (𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹
PERES = (id⟷ ⊗ NOT) ⊚ assocr⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ swap⋆) ⊚ (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚
        TOFFOLI ⊚
        (id⟷ ⊗ (NOT ⊗ id⟷)) ⊚ assocl⋆

SWAP12 SWAP23 SWAP13 ROTL ROTR : 𝟙 +ᵤ 𝟙 +ᵤ 𝟙 ⟷ 𝟙 +ᵤ 𝟙 +ᵤ 𝟙
SWAP12 = assocl₊ ⊚ (swap₊ ⊕ id⟷) ⊚ assocr₊
SWAP23 = id⟷ ⊕ swap₊
SWAP13 = SWAP23 ⊚ SWAP12 ⊚ SWAP23
ROTR   = SWAP12 ⊚ SWAP23
ROTL   = SWAP13 ⊚ SWAP23

pattern ?𝔽 = inj₁ tt
pattern ?𝕋 = inj₂ tt

-- this version might look more contrived that the fully expanded
-- one via pattern matching, but it generalizes better.
-- controlled f (b , a) = (b , [ (λ _ → a) , (λ _ → f a) ]′ b)


𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

not : ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧
not ?𝔽 = 𝕋
not ?𝕋 = 𝔽

controlled : ∀ {A} → (⟦ A ⟧ → ⟦ A ⟧) → ⟦ 𝔹 ⟧ × ⟦ A ⟧ → ⟦ 𝔹 ⟧ × ⟦ A ⟧
controlled f (?𝔽 , a) = (𝔽 , a  )
controlled f (?𝕋 , a) = (𝕋 , f a)

t3 : ∀ {b₁ b₂} →
     ● (𝔹 ×ᵤ 𝔹²) [ 𝔽 , (b₁ , b₂) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝔽 , (b₁ , b₂) ]
t3 = lift TOFFOLI

t6 : ∀ {b} →
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝕋 , b) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝕋 , eval NOT b) ]
t6 = lift TOFFOLI

NEG1 NEG2 NEG3 NEG4 NEG5 : 𝔹 ⟷ 𝔹
NEG1 = swap₊
NEG2 = id⟷ ⊚ NOT
NEG3 = NOT ⊚ NOT ⊚ NOT
NEG4 = NOT ⊚ id⟷
NEG5 = uniti⋆l ⊚ swap⋆ ⊚ (NOT ⊗ id⟷) ⊚ swap⋆ ⊚ unite⋆l
NEG6 = uniti⋆r ⊚ (NOT ⊗ id⟷) ⊚ unite⋆r -- same as above, but shorter

zigzag : ∀ b → ● 𝔹 [ b ] ⟷ ● 𝔹 [ b ]
zigzag b =
  uniti⋆l ⊚                -- ONE * POINTED TWO
  (η b ⊗ id⟷) ⊚          -- (POINTED TWO * RECIP TWO) * POINTED TWO
  assocr⋆ ⊚                -- POINTED TWO * (RECIP TWO * POINTED TWO)
  (id⟷ ⊗ swap⋆) ⊚         -- POINTED TWO * (POINTED TWO * RECIP TWO)
  (id⟷ ⊗ ε b) ⊚           -- POINTED TWO * ONE
  unite⋆r

test1 = eval (zigzag 𝔽) (𝔽 , refl)      -- (⇑ #f refl)
-- test2 = eval (zigzag 𝔽) (𝕋 , refl)   -- typechecks if given proof #f=#t
-- test3 = eval (zigzag 𝕋) (𝔽 , refl)   -- typechecks if given proof #f=#t
test4 = eval (zigzag 𝕋) (𝕋 , refl)      -- (⇑ #t refl)

zigzagU : ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧ 
zigzagU b = unfocus (eval (zigzag b) (focus b))

-- then prove a theorem that specifies its semantics

fig2b'≡ : (a b c d : ⟦ 𝔹 ⟧) →
          proj₂ (eval fig2b' ((a , b , c , d) , 𝔽)) ≡ 𝔽
fig2b'≡ a         (inj₁ tt) c d = refl
fig2b'≡ (inj₁ tt) (inj₂ tt) c d = refl
fig2b'≡ (inj₂ tt) (inj₂ tt) c d = refl

-- generalize above?  Method:
-- for 'dist' to evaluate, need to split on b first
--   in first case, split on e (same reason)
--   in second case, split on a (same reason)
--     split on e
--     split on e
foo : (a b c d e : ⟦ 𝔹 ⟧) →
          proj₂ (eval fig2b' ((a , b , c , d) , e)) ≡ e
foo a         (inj₁ x) c d (inj₁ x₁) = refl
foo a         (inj₁ x) c d (inj₂ y)  = refl
foo (inj₁ x)  (inj₂ y) c d (inj₁ x₁) = refl
foo (inj₁ x)  (inj₂ y) c d (inj₂ y₁) = refl
foo (inj₂ y₁) (inj₂ y) c d (inj₁ x)  = refl
foo (inj₂ y₁) (inj₂ y) c d (inj₂ y₂) = refl

postulate
  -- boring...
  tensor4 : ∀ {a b c d e} →
          (● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ])  ×ᵤ ● 𝔹 [ e ] ⟷
          ● ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (a , b , c , d) , e ]
  itensor4 : ∀ {a b c d e} →
          ● ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (a , b , c , d) , e ] ⟷
          (● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ])  ×ᵤ ● 𝔹 [ e ]

-- now lift it

fig2b : ∀ {a b c d e} →
        let ((x , y , z , w) , u) = eval fig2b' ((a , b , c , d) , e)
        in
           ● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ] ⟷
           ● 𝔹 [ x ] ×ᵤ ● 𝔹 [ y ] ×ᵤ ● 𝔹 [ z ] ×ᵤ ● 𝔹 [ w ]
fig2b {a} {b} {c} {d} {e} =
  let ((x , y , z , w) , u) = eval fig2b' ((a , b , c , d) , e)
  in    uniti⋆r ⊚
        -- (●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × ●𝟙[e]
        (id⟷ ⊗ η e) ⊚
        -- (●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × (●𝔹[e] x ●1/𝔹[e])
        assocl⋆ ⊚
        -- ((●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × ●𝔹[e) x ●1/𝔹[e]
        (tensor4 ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (a,b,c,d),e ] x ●1/𝔹[e]
        (lift fig2b' ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (x,y,z,w),e ] x ●1/𝔹[e]
        (((== id⟷ (cong (λ H → ((x , y , z , w)) , H) (foo a b c d e))) ⊗ id⟷)) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (x,y,z,w),e ] x ●1/𝔹[e]
        (itensor4 ⊗ id⟷) ⊚
         -- ((●𝔹[x] × ●𝔹[y] × ●𝔹[z] × ●𝔹[w]) × ●𝔹[e]) x ●1/𝔹[e]
        assocr⋆ ⊚
        (id⟷ ⊗ ε e) ⊚
        unite⋆r

-- This is mostly to show that == is really 'subst' in hiding.
fig2b₂ : ∀ {a b c d e} →
        let ((x , y , z , w) , u) = eval fig2b' ((a , b , c , d) , e)
        in
           ● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ] ⟷
           ● 𝔹 [ x ] ×ᵤ ● 𝔹 [ y ] ×ᵤ ● 𝔹 [ z ] ×ᵤ ● 𝔹 [ w ]
fig2b₂ {a} {b} {c} {d} {e} =
  let ((x , y , z , w) , u) = eval fig2b' ((a , b , c , d) , e)
  in    uniti⋆r ⊚
        -- (●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × ●𝟙[e]
        (id⟷ ⊗ η e) ⊚
        -- (●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × (●𝔹[e] x ●1/𝔹[e])
        assocl⋆ ⊚
        -- ((●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × ●𝔹[e) x ●1/𝔹[e]
        (tensor4 ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (a,b,c,d),e ] x ●1/𝔹[e]
        (lift fig2b' ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (x,y,z,w),e ] x ●1/𝔹[e]
        (itensor4 ⊗ id⟷) ⊚
         -- ((●𝔹[x] × ●𝔹[y] × ●𝔹[z] × ●𝔹[w]) × ●𝔹[e]) x ●1/𝔹[e]
        assocr⋆ ⊚
        (id⟷ ⊗ (subst (λ ee → ● 𝔹 [ ee ] ×ᵤ 𝟙/● 𝔹 [ e ] ⟷ 𝟙) (sym (foo a b c d e)) (ε e))) ⊚
        unite⋆r

------------------------------------------------------------------------------
\end{code}}
