{-# OPTIONS --without-K #-}

module Examples.New where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Singleton
open import PiPointedFrac

------------------------------------------------------------------------------
-- Conventional PI examples

𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

𝔹² : 𝕌
𝔹² = 𝔹 ×ᵤ 𝔹

𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

NOT : 𝔹 ⟷ 𝔹
NOT = swap₊

NEG1 NEG2 NEG3 NEG4 NEG5 : 𝔹 ⟷ 𝔹
NEG1 = swap₊
NEG2 = id⟷ ⊚ NOT
NEG3 = NOT ⊚ NOT ⊚ NOT
NEG4 = NOT ⊚ id⟷
NEG5 = uniti⋆l ⊚ swap⋆ ⊚ (NOT ⊗ id⟷) ⊚ swap⋆ ⊚ unite⋆l
NEG6 = uniti⋆r ⊚ (NOT ⊗ id⟷) ⊚ unite⋆r

CONTROL : {A : 𝕌} → (A ⟷ A) → (𝔹 ×ᵤ A ⟷ 𝔹 ×ᵤ A)
CONTROL f = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ f)) ⊚ factor

CNOT : 𝔹² ⟷ 𝔹²
CNOT = CONTROL NOT

TOFFOLI : 𝔹 ×ᵤ 𝔹² ⟷ 𝔹 ×ᵤ 𝔹²
TOFFOLI = CONTROL (CONTROL NOT)

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

------------------------------------------------------------------------------
-- Pointed versions

∙TOFFOLI-1 : ∀ {b₁ b₂} →
           (𝔹 ×ᵤ 𝔹²) # (𝔽 , (b₁ , b₂)) ∙⟶ (𝔹 ×ᵤ 𝔹²) # (𝔽 , (b₁ , b₂))
∙TOFFOLI-1 = ∙c TOFFOLI

∙TOFFOLI-2 : ∀ {b} →
           (𝔹 ×ᵤ 𝔹²) # (𝕋 , (𝔽 , b)) ∙⟶ (𝔹 ×ᵤ 𝔹²) # (𝕋 , (𝔽 , b))
∙TOFFOLI-2 = ∙c TOFFOLI

∙TOFFOLI-3 : ∀ {b} →
           (𝔹 ×ᵤ 𝔹²) # (𝕋 , (𝕋 , b)) ∙⟶ (𝔹 ×ᵤ 𝔹²) # (𝕋 , (𝕋 , eval swap₊ b))
∙TOFFOLI-3 = ∙c TOFFOLI

-- Ancilla examples from literature

-- Fig. 2 in Ricercar

fig2a : 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ⟷
        𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹
fig2a = CONTROL (CONTROL (CONTROL NOT))

-- first write the circuit with the additional ancilla

fig2b' : ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) ⟷ ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹)
fig2b' =
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ CONTROL (CONTROL NOT))  -- first ccnot
  ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷)                        -- move it back
  ⊚
  (assocl⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ swap⋆) ⊚
  (id⟷ ⊗ CONTROL (CONTROL NOT))  -- second ccnot
  ⊚
  (id⟷ ⊗ swap⋆) ⊚
  assocl⋆ ⊚
  (assocr⋆ ⊗ id⟷)                      -- move it back
  ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ CONTROL (CONTROL NOT))  -- third ccnot
  ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷)                        -- move it back

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

{--
postulate
  -- boring...
  tensor4 : ∀ {a b c d e} →
          (● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ])  ×ᵤ ● 𝔹 [ e ] ⟷
          ● ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (a , b , c , d) , e ]
  itensor4 : ∀ {a b c d e} →
          ● ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (a , b , c , d) , e ] ⟷
          (● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ])  ×ᵤ ● 𝔹 [ e ]
--}
-- now lift it
{--
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
--}
{--
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
--}
-- Examples

infixr 2  _→⟨_⟩_
infix  3  _□

_→⟨_⟩_ : (T₁ : ∙𝕌) → {T₂ T₃ : ∙𝕌} →
          (T₁ ∙⟶ T₂) → (T₂ ∙⟶ T₃) → (T₁ ∙⟶ T₃)
_ →⟨ α ⟩ β = α ∙⊚ β

_□ : (T : ∙𝕌) → {T : ∙𝕌} → (T ∙⟶ T)
_□ T = ∙id⟷

zigzag : ∀ b → 𝔹 # b ∙⟶ 𝔹 # b
zigzag b =
  (𝔹 # b)
        →⟨ (∙c uniti⋆l) ⟩
  (𝟙 ×ᵤ 𝔹) # (tt , b)
        →⟨ ∙times# ⟩
  (𝟙 # tt) ∙×ᵤ (𝔹 # b)
        →⟨ ∙id⟷ ∙⊗ return (𝔹 # b) ⟩
  (𝟙 # tt) ∙×ᵤ (Singᵤ (𝔹 # b))
        →⟨ η (𝔹 # b) ∙⊗ ∙id⟷ ⟩
  ((Singᵤ (𝔹 # b)) ∙×ᵤ (Recipᵤ (𝔹 # b))) ∙×ᵤ (Singᵤ (𝔹 # b))
        →⟨ ∙assocr⋆ ⟩ 
  Singᵤ (𝔹 # b) ∙×ᵤ (Recipᵤ (𝔹 # b) ∙×ᵤ (Singᵤ (𝔹 # b)))
        →⟨ ∙id⟷ ∙⊗ ∙swap⋆ ⟩
  Singᵤ (𝔹 # b) ∙×ᵤ ((Singᵤ (𝔹 # b)) ∙×ᵤ (Recipᵤ (𝔹 # b)))
        →⟨ ∙id⟷ ∙⊗ ε (𝔹 # b) ⟩
  Singᵤ (𝔹 # b) ∙×ᵤ (𝟙 # tt)
        →⟨ extract (𝔹 # b) ∙⊗ ∙id⟷ ⟩
  (𝔹 # b) ∙×ᵤ (𝟙 # tt)
        →⟨ ∙#times  ⟩
  (𝔹 ×ᵤ 𝟙) # (b , tt)
        →⟨ ∙c unite⋆r  ⟩
  (𝔹 # b) □

test1 : proj₁ (∙eval (zigzag 𝔽)) 𝔽 ≡ 𝔽
test1 = proj₂ (∙eval (zigzag 𝔽))

test2 : proj₁ (∙eval (zigzag 𝕋)) 𝕋 ≡ 𝕋
test2 = proj₂ (∙eval (zigzag 𝕋))


------------------------------------------------------------------------------
