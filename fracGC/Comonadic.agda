{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Comonadic where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
  renaming (_+_ to _ℕ+_; _⊔_ to _ℕ⊔_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; ∣_∣; _+_; _⊔_; -_)
open import Data.Rational
  using (ℚ)
  renaming (1/_ to recip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product -- using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.Core using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Category.Comonad

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_

------------------------------------------------------------------------------
-- Pi with fractionals comonad

record Pointed (A : Set) (v : A) : Set where
  constructor ⇑
  field
    ● : A
    v≡● : v ≡ ●

open Pointed public

pointed-contr : {A : Set} {v : A} {p : Pointed A v} → ⇑ v refl ≡ p
pointed-contr {p = ⇑ v refl} = refl

pointed-all-paths : {A : Set} {v : A} {p q : Pointed A v} → p ≡ q
pointed-all-paths {p = p} {q} = trans (sym pointed-contr) pointed-contr

Recip : (A : Set) → (v : A) → Set
Recip A v = (w : A) → (v ≡ w) → ⊤
-- Recip A v = Pointed A v → ⊤

--

data 𝕌 : Set
⟦_⟧ : (A : 𝕌) → Set
data _⟷_ : 𝕌 → 𝕌 → Set
eval : {A B : 𝕌} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧

data 𝕌 where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌
  ●_[_]   : (A : 𝕌) → ⟦ A ⟧ → 𝕌
  𝟙/●_[_] : (A : 𝕌) → ⟦ A ⟧ → 𝕌

⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ ● A [ v ] ⟧ = Pointed ⟦ A ⟧ v -- type has a parameter v and a point ● such that v ≡ ●
⟦ 𝟙/● A [ v ] ⟧ = Recip ⟦ A ⟧ v -- type inhabited by just one function from Pointed A v to ⊤


data _⟷_ where
  unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ⟷ t
  uniti₊l : {t : 𝕌} → t ⟷ 𝟘 +ᵤ t
  unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ⟷ t
  uniti₊r : {t : 𝕌} → t ⟷ t +ᵤ 𝟘
  swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ⟷ t₂ +ᵤ t₁
  assocl₊ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ +ᵤ t₂) +ᵤ t₃
  assocr₊ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ⟷ t₁ +ᵤ (t₂ +ᵤ t₃)
  unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ⟷ t
  uniti⋆l : {t : 𝕌} → t ⟷ 𝟙 ×ᵤ t
  unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ⟷ t
  uniti⋆r : {t : 𝕌} → t ⟷ t ×ᵤ 𝟙
  swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ⟷ t₂ ×ᵤ t₁
  assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ⟷ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  absorbr : {t : 𝕌} → 𝟘 ×ᵤ t ⟷ 𝟘
  absorbl : {t : 𝕌} → t ×ᵤ 𝟘 ⟷ 𝟘
  factorzr : {t : 𝕌} → 𝟘 ⟷ t ×ᵤ 𝟘
  factorzl : {t : 𝕌} → 𝟘 ⟷ 𝟘 ×ᵤ t
  dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
  factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤ t₃)
  id⟷     : {t : 𝕌} → t ⟷ t
  _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)
  -- comonad
  -- extract not information preserving; not reversible
  extract : {t : 𝕌} → {v : ⟦ t ⟧} → ● t [ v ] ⟷ t
  extend : {t₁ t₂ : 𝕌} → {v₁ : ⟦ t₁ ⟧} →
           (c : ● t₁ [ v₁ ] ⟷ t₂) →
           (● t₁ [ v₁ ] ⟷ ● t₂ [ eval c (⇑ v₁ refl) ])
  tensorl : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            ● t₁ ×ᵤ t₂ [ v₁ , v₂ ] ⟷ ● t₁ [ v₁ ] ×ᵤ ● t₂ [ v₂ ]
  tensorr : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            ● t₁ [ v₁ ] ×ᵤ ● t₂ [ v₂ ] ⟷ ● t₁ ×ᵤ t₂ [ v₁ , v₂ ]
  plusl : {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} →
            ● (t₁ +ᵤ t₂) [ inj₁ v ] ⟷ ● t₁ [ v ]
  plusr : {t₁ t₂ : 𝕌} {v : ⟦ t₂ ⟧} →
            ● (t₁ +ᵤ t₂) [ inj₂ v ] ⟷ ● t₂ [ v ]
  -- fractionals
  η : {t : 𝕌} → (v : ⟦ t ⟧) → 𝟙 ⟷ ● t [ v ] ×ᵤ 𝟙/● t [ v ]
  ε : {t : 𝕌} → (v : ⟦ t ⟧) → ● t [ v ] ×ᵤ 𝟙/● t [ v ] ⟷ 𝟙
  -- prop eq
  == : ∀ {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} {w w' : ⟦ t₂ ⟧} →
       (● t₁ [ v ] ⟷ ● t₂ [ w ]) → (w ≡ w') → (● t₁ [ v ] ⟷ ● t₂ [ w' ])

eval unite₊l (inj₂ v) = v
eval uniti₊l v  = inj₂ v
eval unite₊r (inj₁ v) = v
eval uniti₊r v  = inj₁ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆l (tt , v) = v
eval uniti⋆l v = (tt , v)
eval unite⋆r (v , tt) = v
eval uniti⋆r v = (v , tt)
eval swap⋆ (v₁ , v₂)          = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbl ()
eval absorbr ()
eval factorzl ()
eval factorzr ()
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval distl (v , inj₁ v₁) = inj₁ (v , v₁)
eval distl (v , inj₂ v₂) = inj₂ (v , v₂)
eval factorl (inj₁ (v , v₁)) = (v , inj₁ v₁)
eval factorl (inj₂ (v , v₂)) = (v , inj₂ v₂)
eval id⟷ v = v
eval (c₁ ⊚ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)
eval extract p = ● p
eval (extend {v₁ = v₁} c) p = ⇑ (eval c (⇑ (● p) (v≡● p))) (cong (eval c) pointed-all-paths)
eval tensorl p = ⇑ (proj₁ (● p)) (cong proj₁ (v≡● p)) , ⇑ (proj₂ (● p)) (cong proj₂ (v≡● p))
eval tensorr (p₁ , p₂) = ⇑ ((● p₁) , (● p₂)) (cong₂ _,_ (v≡● p₁) (v≡● p₂))
eval (η v) tt = ⇑ v refl , λ w v≡w → tt
eval (ε v) (p , f) = f (● p) (v≡● p)
eval (plusl {v = v₁}) (⇑ ● refl) = ⇑ v₁ refl
eval (plusr {v = v₂}) (⇑ ● refl) = ⇑ v₂ refl
eval (== c eq) v = let r = eval c v in ⇑ (● r) (trans (sym eq) (v≡● r))

------------------------------------------------------------------------------
-- Set up for examples

infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : 𝕌) {t₂ : 𝕌} {t₃ : 𝕌} →
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
_ ⟷⟨ α ⟩ β = α ⊚ β

_□ : (t : 𝕌) → {t : 𝕌} → (t ⟷ t)
_□ t = id⟷

𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

𝔹² : 𝕌
𝔹² = 𝔹 ×ᵤ 𝔹

𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

lift : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} →
       (c : t₁ ⟷ t₂) → (● t₁ [ v₁ ] ⟷ ● t₂ [ eval c v₁ ])
lift c = extend (extract ⊚ c)

{--
-- Is it possible to unlift ?

unlift : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} →
         (● t₁ [ v₁ ] ⟷ t₂) → (t₁ ⟷ t₂)
unlift uniti₊l = {!!}
unlift uniti₊r = {!!}
unlift uniti⋆l = {!!}
unlift uniti⋆r = {!!}
unlift id⟷ = {!!}
unlift (c₁ ⊚ c₂) = {!!}
unlift extract = {!!}
unlift (extend c) = {!!}
unlift tensorl = {!!}
unlift plusl = {!!}
unlift plusr = {!!}
unlift (== c q) = {!!}
--}

not : ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧
not (inj₁ tt) = inj₂ tt
not (inj₂ tt) = inj₁ tt

controlled : ∀ {A} → (⟦ A ⟧ → ⟦ A ⟧) → ⟦ 𝔹 ⟧ × ⟦ A ⟧ → ⟦ 𝔹 ⟧ × ⟦ A ⟧
controlled f (inj₁ tt , a) = (inj₁ tt , a)
controlled f (inj₂ tt , a) = (inj₂  tt , f a)

------------------------------------------------------------------------------
-- Examples

zigzag : ∀ b → ● 𝔹 [ b ] ⟷ ● 𝔹 [ b ]
zigzag b =
  lift uniti⋆l ⊚                       -- POINTED (ONE * TWO)
  tensorl ⊚                            -- POINTED ONE * POINTED TWO
  ((extract ⊚ η b) ⊗ id⟷) ⊚          -- (POINTED TWO * RECIP TWO) * POINTED TWO
  assocr⋆ ⊚                            -- POINTED TWO * (RECIP TWO * POINTED TWO)
  (id⟷ ⊗ swap⋆) ⊚                    -- POINTED TWO * (POINTED TWO * RECIP TWO)
  (id⟷ ⊗ ε b) ⊚                      -- POINTED TWO * ONE
  unite⋆r

test1 = eval (zigzag 𝔽) (⇑ 𝔽 refl)      -- (⇑ #f refl)
-- test2 = eval (zigzag 𝔽) (⇑ 𝕋 refl)   -- typechecks if given proof #f=#t
-- test3 = eval (zigzag 𝕋) (⇑ 𝔽 refl)   -- typechecks if given proof #f=#t
test4 = eval (zigzag 𝕋) (⇑ 𝕋 refl)      -- (⇑ #t refl)

-- Conventional PI examples

NOT : 𝔹 ⟷ 𝔹
NOT = swap₊

NEG1 NEG2 NEG3 NEG4 NEG5 : 𝔹 ⟷ 𝔹
NEG1 = swap₊
NEG2 = id⟷ ⊚ NOT
NEG3 = NOT ⊚ NOT ⊚ NOT
NEG4 = NOT ⊚ id⟷
NEG5 = uniti⋆l ⊚ swap⋆ ⊚ (NOT ⊗ id⟷) ⊚ swap⋆ ⊚ unite⋆l
NEG6 = uniti⋆r ⊚ (NOT ⊗ id⟷) ⊚ unite⋆r -- same as above, but shorter

CNOT : 𝔹² ⟷ 𝔹²
CNOT = 𝔹 ×ᵤ 𝔹
     ⟷⟨ id⟷ ⟩
       (x +ᵤ y) ×ᵤ 𝔹
     ⟷⟨ dist ⟩
       (x ×ᵤ 𝔹) +ᵤ (y ×ᵤ 𝔹)
     ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT) ⟩
       (x ×ᵤ 𝔹) +ᵤ (y ×ᵤ 𝔹)
     ⟷⟨ factor ⟩
       (x +ᵤ y) ×ᵤ 𝔹
     ⟷⟨ id⟷ ⟩
       𝔹 ×ᵤ 𝔹 □
  where x = 𝟙; y = 𝟙

TOFFOLI : 𝔹 ×ᵤ 𝔹² ⟷ 𝔹 ×ᵤ 𝔹²
TOFFOLI = 𝔹 ×ᵤ 𝔹²
        ⟷⟨ id⟷ ⟩
          (x +ᵤ y) ×ᵤ 𝔹²
        ⟷⟨ dist ⟩
          (x ×ᵤ 𝔹²) +ᵤ (y ×ᵤ 𝔹²)
        ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩
          (x ×ᵤ 𝔹²) +ᵤ (y ×ᵤ 𝔹²)
        ⟷⟨ factor ⟩
          (x +ᵤ y) ×ᵤ 𝔹²
        ⟷⟨ id⟷ ⟩
          𝔹 ×ᵤ 𝔹² □
  where x = 𝟙; y = 𝟙

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

t3 : ∀ {b₁ b₂} →
     ● (𝔹 ×ᵤ 𝔹²) [ 𝔽 , (b₁ , b₂) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝔽 , (b₁ , b₂) ]
t3 = lift TOFFOLI

{--
The following do not typecheck. Good

t4 : ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝔽 , 𝔽) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝔽 , 𝕋) ]
t4 = lift TOFFOLI

t5 : ∀ {b₁ b₂} →
     ● (𝔹 ×ᵤ 𝔹²) [ b₁ , (𝔽 , b₂) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ b₁ , (𝔽 , b₂) ]
t5 = lift TOFFOLI
--}

t6 : ∀ {b} →
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝕋 , b) ] ⟷
     ● (𝔹 ×ᵤ 𝔹²) [ 𝕋 , (𝕋 , eval NOT b) ]
t6 = lift TOFFOLI

-- Ancilla examples from literature

-- Fig. 2 in Ricercar

CONTROLLED : {A : 𝕌} → (A ⟷ A) → 𝔹 ×ᵤ A ⟷ 𝔹 ×ᵤ A
CONTROLLED c = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ c)) ⊚ factor

fig2a : 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ⟷
        𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹
fig2a = CONTROLLED (CONTROLLED (CONTROLLED NOT))

-- first write the circuit with the additional ancilla

fig2b' : ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) ⟷ ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹)
fig2b' =
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ CONTROLLED (CONTROLLED NOT))  -- first ccnot
  ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷)                        -- move it back
  ⊚
  (assocl⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ swap⋆) ⊚
  (id⟷ ⊗ CONTROLLED (CONTROLLED NOT))  -- second ccnot
  ⊚
  (id⟷ ⊗ swap⋆) ⊚
  assocl⋆ ⊚
  (assocr⋆ ⊗ id⟷)                      -- move it back
  ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocr⋆ ⊚
  (id⟷ ⊗ CONTROLLED (CONTROLLED NOT))  -- third ccnot
  ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷) ⊚
  assocl⋆ ⊚
  (swap⋆ ⊗ id⟷)                        -- move it back

-- then prove a theorem that specifies its semantics

fig2b'≡ : (a b c d : ⟦ 𝔹 ⟧) →
          let (_ , e) = eval fig2b' ((a , b , c , d) , 𝔽)
          in e ≡ 𝔽
fig2b'≡ a (inj₁ tt) c d = refl
fig2b'≡ (inj₁ tt) (inj₂ tt) c d = refl
fig2b'≡ (inj₂ tt) (inj₂ tt) c d = refl

postulate
  -- boring...
  tensor4 : ∀ {a b c d e} →
          (● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ])  ×ᵤ ● 𝔹 [ e ] ⟷
          ● ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (a , b , c , d) , e ]
  itensor4 : ∀ {a b c d e} →
          ● ((𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹) [ (a , b , c , d) , e ] ⟷
          (● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ])  ×ᵤ ● 𝔹 [ e ]

-- now lift it

fig2b : ∀ {a b c d} →
        let ((x , y , z , w) , e) = eval fig2b' ((a , b , c , d) , 𝔽)
        in e ≡ 𝔽 ×
           ● 𝔹 [ a ] ×ᵤ ● 𝔹 [ b ] ×ᵤ ● 𝔹 [ c ] ×ᵤ ● 𝔹 [ d ] ⟷
           ● 𝔹 [ x ] ×ᵤ ● 𝔹 [ y ] ×ᵤ ● 𝔹 [ z ] ×ᵤ ● 𝔹 [ w ]
fig2b {a} {b} {c} {d} =
  let ((x , y , z , w) , _) = eval fig2b' ((a , b , c , d) , 𝔽)
      e≡𝔽 = fig2b'≡ a b c d
  in e≡𝔽 ,
        uniti⋆r ⊚
        -- (●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × ●𝟙[tt]
        (id⟷ ⊗ η 𝔽) ⊚
        -- (●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × (●𝔹[𝔽] x ●1/𝔹[𝔽])
        assocl⋆ ⊚
        -- ((●𝔹[a] × ●𝔹[b] × ●𝔹[c] × ●𝔹[d]) × ●𝔹[𝔽]) x ●1/𝔹[𝔽]
        (tensor4 ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (a,b,c,d),𝔽 ] x ●1/𝔹[𝔽]
        (lift fig2b' ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (x,y,z,w),e ] x ●1/𝔹[𝔽]
        ((== id⟷ (cong (λ H → ((x , y , z , w)) , H) e≡𝔽)) ⊗ id⟷) ⊚
         -- ● ((𝔹 × 𝔹 × 𝔹 × 𝔹) × 𝔹) [ (x,y,z,w),𝔽 ] x ●1/𝔹[𝔽]
        (itensor4 ⊗ id⟷) ⊚
         -- ((●𝔹[x] × ●𝔹[y] × ●𝔹[z] × ●𝔹[w]) × ●𝔹[𝔽]) x ●1/𝔹[𝔽]
        assocr⋆ ⊚
        (id⟷ ⊗ ε 𝔽) ⊚
        unite⋆r

------------------------------------------------------------------------------
-- Space denotational semantics

-- for each type, we calculate its memory requirements which are two
-- numbers (m , z). The number m represents the amount of space need
-- to store values of the type. The number z represents the effect of
-- the value on space when it is executed. Ex. a gc process needs m
-- bits to be stored but when run it releases z bits.

-- For plain types, the number z is the log of the number of values
-- (rounded up). For pointed types, the number m is 1 but z is the
-- amount of space for the values of the underlying type. For
-- fractional types, the number m is also 1 but z is negative, i.e.,
-- we release memory. Note that log(1/X) is -log(X)

space : (t : 𝕌) → Maybe (ℕ × ℤ)
space 𝟘 = nothing
space 𝟙 = just (0 , + 0)
space (t₁ +ᵤ t₂) with space t₁ | space t₂
... | just (m , z₁) | just (n , z₂) = just (1 ℕ+ (m ℕ⊔ n) , (+ 1) + (z₁ ⊔ z₂))
... | just (m , z) | nothing = just (m , z)
... | nothing | just (n , z) = just (n , z)
... | nothing | nothing = nothing
space (t₁ ×ᵤ t₂) with space t₁ | space t₂
... | just (m , z₁) | just (n , z₂) = just (m ℕ+ n , z₁ + z₂)
... | just _ | nothing = nothing
... | nothing | just _ = nothing
... | nothing | nothing = nothing
space ● t [ _ ] with space t
... | just (m , z) = just (1 , + m)  --- ???
... | nothing = nothing -- impossible
space 𝟙/● t [ _ ] with space t
... | just (m , z) = just (m , - z)
... | nothing = nothing -- impossible

encode : (t : 𝕌) → (v : ⟦ t ⟧) → ℕ
encode 𝟙 tt = 0
encode (t₁ +ᵤ t₂) (inj₁ v₁) = encode t₁ v₁
encode (t₁ +ᵤ t₂) (inj₂ v₂) = {!encode t₂ v₂!}
encode (t₁ ×ᵤ t₂) (v₁ , v₂) = {!!}
encode ● t [ v ] w = {!!}
encode 𝟙/● t [ f ] g = {!!}

-- write a version of eval that takes memory of the right size


{--

size : (t : 𝕌) → ℚ
size t = {!!}

-- size (Pointed A v) = size A
-- size (1/A v) = 1/size A or

{--
Actually we need to separate cardinality of the type
and the number of bits needed in memory (log factor)

Write a version of eval that makes it clear that in plain pi every
combinator preserves memory and that fractionals allow intermediate
combinators to allocate memory and gc it. The fractional value's
impact on memory is that it uses negative memory.
--}

𝕊 : (t : 𝕌) → (size t ≡ (+ 0 / 1)) ⊎
              (Σ ℕ (λ m →
              (Σ ℕ (λ n →
              (Vec ⟦ t ⟧ m) ×
              (Vec ⟦ t ⟧ n) ×
              (((+ m / 1) * (recip (+ n / 1))) ≡ (+ 1 / 1))))))
𝕊 = {!!}

-- Groupoids

-- Groupoid for pointed 1/A is point and (size A) loops on point labeled (=
-- a1), (= a2), (= a3), etc.

--}

------------------------------------------------------------------------------
