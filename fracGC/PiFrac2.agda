{-# OPTIONS --without-K #-}

-- Definition of Pi with fractionals

module PiFrac2 where

-- From the standard library:
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

-- The basic types we add:
open import Singleton

infix  80 ●_ 𝟙/●_
infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_

------------------------------------------------------------------------------
-- Pi with fractionals

-- The following are all mutually dependent:

data 𝕌 : Set                               -- 𝕌niverse of types
⟦_⟧ : (A : 𝕌) → Set                        -- denotation of types
data _⟷_ : 𝕌 → 𝕌 → Set                     -- type equivalences
eval : {A B : 𝕌} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧ -- evaluating an equivalence

data 𝕌 where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌
  ●_   : {A : 𝕌} → ⟦ A ⟧ → 𝕌
  𝟙/●_ : {A : 𝕌} → ⟦ A ⟧ → 𝕌

⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ ● v ⟧ = Singleton _ v
⟦ 𝟙/● v ⟧ = Recip _ v

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
  -- new operations on Singleton
{--
  lift : {t₁ t₂ : 𝕌} → {v₁ : ⟦ t₁ ⟧} →
           (c : t₁ ⟷ t₂) →
           ((● v₁) ⟷ (● (eval c v₁)))
  tensorl : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            ●_ {A = t₁ ×ᵤ t₂} (v₁ , v₂) ⟷ ● v₁ ×ᵤ ● v₂
  tensorr : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            ● v₁ ×ᵤ ● v₂ ⟷ ●_ {A = t₁ ×ᵤ t₂} (v₁ , v₂)
  plusll : {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} →
            ●_ {A = t₁ +ᵤ t₂} (inj₁ v) ⟷ ● v
  pluslr : {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} →
             ● v ⟷ ●_ {A = t₁ +ᵤ t₂} (inj₁ v)
  plusrl : {t₁ t₂ : 𝕌} {v : ⟦ t₂ ⟧} →
            ●_ {A = t₁ +ᵤ t₂} (inj₂ v) ⟷ ● v
  plusrr : {t₁ t₂ : 𝕌} {v : ⟦ t₂ ⟧} →
             ● v ⟷ ●_ {A = t₁ +ᵤ t₂} (inj₂ v)
  fracl : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            𝟙/●_ {A = t₁ ×ᵤ t₂} (v₁ , v₂) ⟷ 𝟙/● v₁ ×ᵤ 𝟙/● v₂
  fracr : {t₁ t₂ : 𝕌} {v₁ : ⟦ t₁ ⟧} {v₂ : ⟦ t₂ ⟧} →
            𝟙/● v₁ ×ᵤ 𝟙/● v₂ ⟷ 𝟙/●_ {A = t₁ ×ᵤ t₂} (v₁ , v₂)
--}
  -- fractionals
  η : {t : 𝕌} → (v : ⟦ t ⟧) → 𝟙 ⟷ ● v ×ᵤ 𝟙/● v
  ε : {t : 𝕌} → (v : ⟦ t ⟧) → ● v ×ᵤ 𝟙/● v ⟷ 𝟙
  -- double lift prop eq
{--
  ll : ∀ {t : 𝕌} {v : ⟦ t ⟧} {w : ⟦ ● v ⟧} → 
        ●_ {A = ● v} w  ⟷ ● v
  == : ∀ {t₁ t₂ : 𝕌} {v : ⟦ t₁ ⟧} {w w' : ⟦ t₂ ⟧} →
       (● v ⟷ ● w) → (w ≡ w') → (● v ⟷ ● w')
--}

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
{--
eval (lift c) (w , v≡w) = eval c w , cong (eval c) v≡w 
eval tensorl ((w₁ , w₂) , vp≡wp) =
  (w₁ , cong proj₁ vp≡wp) , (w₂ , cong proj₂ vp≡wp)
eval tensorr ((w₁ , p₁) , (w₂ , p₂)) =
  (w₁ , w₂) , cong₂ _,_ p₁ p₂ 
--}
eval (η v) tt = (v , refl) , λ _ → tt 
eval (ε v) (p , f) = f p
{--
eval (plusll {v = .w₁}) (inj₁ w₁ , refl) = w₁ , refl 
eval pluslr (v₁ , refl) = inj₁ v₁ , refl
eval (plusrl {v = .w₂}) (inj₂ w₂ , refl) = w₂ , refl
eval plusrr (v₂ , refl) = inj₂ v₂ , refl
eval (fracl {v₁ = v₁} {v₂ = v₂}) f = (λ _ → f ((v₁ , v₂) , refl)) , (λ _ → f ((v₁ , v₂) , refl))
eval fracr (f₁ , f₂) ((w₁ , w₂) , refl) = let _ = f₁ (w₁ , refl) ; _ = f₂ (w₂ , refl) in tt
eval (ll {t} {v} {.w}) (w , refl) = v , refl 
eval (== c eq) s₁ = let (w₂ , p) = eval c s₁ in w₂ , trans (sym eq) p 
--}

-- monad/comonad pair




{--

focus : {t : 𝕌} → (v : ⟦ t ⟧) → Singleton ⟦ t ⟧ v
focus v = (v , refl)

unfocus : {t : 𝕌} {v : ⟦ t ⟧} → Singleton ⟦ t ⟧ v → ⟦ t ⟧
unfocus (v , refl) = v

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------------
-- Useful for examples

infixr 2  _⟷⟨_⟩_
infix  3  _□

_⟷⟨_⟩_ : (t₁ : 𝕌) {t₂ : 𝕌} {t₃ : 𝕌} →
          (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
_ ⟷⟨ α ⟩ β = α ⊚ β

_□ : (t : 𝕌) → {t : 𝕌} → (t ⟷ t)
_□ t = id⟷

------------------------------------------------------------------------------

𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

𝔹² : 𝕌
𝔹² = 𝔹 ×ᵤ 𝔹

𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

not : ⟦ 𝔹 ⟧ → ⟦ 𝔹 ⟧
not (inj₁ tt) = inj₂ tt
not (inj₂ tt) = inj₁ tt

-- this version might look more contrived that the fully expanded
-- one via pattern matching, but it generalizes better.
controlled : ∀ {A} → (⟦ A ⟧ → ⟦ A ⟧) → ⟦ 𝔹 ⟧ × ⟦ A ⟧ → ⟦ 𝔹 ⟧ × ⟦ A ⟧
controlled f (b , a) = (b , [ (λ _ → a) , (λ _ → f a) ]′ b)
-- controlled f (inj₁ tt , a) = (inj₁ tt , a  )
-- controlled f (inj₂ tt , a) = (inj₂ tt , f a)

------------------------------------------------------------------------------
-- Examples

zigzag : ∀ b → ●_ {𝔹} b ⟷ ● b
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
CNOT =
  𝔹 ×ᵤ 𝔹                ⟷⟨ id⟷ ⟩
  (x +ᵤ y) ×ᵤ 𝔹         ⟷⟨ dist ⟩
  (x ×ᵤ 𝔹) +ᵤ (y ×ᵤ 𝔹)  ⟷⟨ id⟷ ⊕ (id⟷ ⊗ NOT) ⟩
  (x ×ᵤ 𝔹) +ᵤ (y ×ᵤ 𝔹)  ⟷⟨ factor ⟩
  (x +ᵤ y) ×ᵤ 𝔹         ⟷⟨ id⟷ ⟩
  𝔹 ×ᵤ 𝔹 □
  where x = 𝟙; y = 𝟙

TOFFOLI : 𝔹 ×ᵤ 𝔹² ⟷ 𝔹 ×ᵤ 𝔹²
TOFFOLI =
  𝔹 ×ᵤ 𝔹²                 ⟷⟨ id⟷ ⟩
  (x +ᵤ y) ×ᵤ 𝔹²          ⟷⟨ dist ⟩
  (x ×ᵤ 𝔹²) +ᵤ (y ×ᵤ 𝔹²)  ⟷⟨ id⟷ ⊕ (id⟷ ⊗ CNOT) ⟩
  (x ×ᵤ 𝔹²) +ᵤ (y ×ᵤ 𝔹²)  ⟷⟨ factor ⟩
  (x +ᵤ y) ×ᵤ 𝔹²          ⟷⟨ id⟷ ⟩
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
     ● (𝔽 , (b₁ , b₂)) ⟷
     ● (𝔽 , (b₁ , b₂))
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
     ● (𝕋 , (𝕋 , b)) ⟷
     ● (𝕋 , (𝕋 , eval NOT b))
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
          (●_ {𝔹} a ×ᵤ ●_ {𝔹} b ×ᵤ ●_ {𝔹} c ×ᵤ ●_ {𝔹} d) ×ᵤ ●_ {𝔹} e ⟷
          ●_ {(𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹} ((a , b , c , d) , e)
  itensor4 : ∀ {a b c d e} →
          ●_ {(𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹 ×ᵤ 𝔹) ×ᵤ 𝔹} ((a , b , c , d) , e) ⟷
          (● a ×ᵤ ● b ×ᵤ ● c ×ᵤ ● d)  ×ᵤ ● e

-- now lift it

fig2b : ∀ {a b c d e} →
        let ((x , y , z , w) , u) = eval fig2b' ((a , b , c , d) , e)
        in
           ● a ×ᵤ ● b ×ᵤ ● c ×ᵤ ● d ⟷
           ● x ×ᵤ ● y ×ᵤ ● z ×ᵤ ● w 
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
           ● a ×ᵤ ● b ×ᵤ ● c ×ᵤ ● d ⟷
           ● x ×ᵤ ● y ×ᵤ ● z ×ᵤ ● w 
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
        (id⟷ ⊗ (subst (λ ee → ● ee ×ᵤ 𝟙/● e ⟷ 𝟙) (sym (foo a b c d e)) (ε e))) ⊚
        unite⋆r

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst)

------------------------------------------------------------------

dual : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) →
                   (𝟙/● (eval f v) ⟷ 𝟙/● v)
dual f v = uniti⋆l ⊚ (η v ⊗ id⟷) ⊚ ((lift f ⊗ id⟷) ⊗ id⟷) ⊚
  assocr⋆ ⊚ (id⟷ ⊗ swap⋆) ⊚ assocl⋆ ⊚ (ε (eval f v) ⊗ id⟷) ⊚ unite⋆l

-- name, coname
name : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) → 𝟙 ⟷ ● (eval f v) ×ᵤ 𝟙/● v
name f v = η v ⊚ (lift f ⊗ id⟷)

coname : {A B : 𝕌} → (f : A ⟷ B) → (v : ⟦ A ⟧ ) → ● v ×ᵤ 𝟙/● (eval f v) ⟷ 𝟙
coname f v = (lift f ⊗ id⟷) ⊚ ε (eval f v)

-- and 'trace' reveals something neat: we can't choose just any random 'a' and 'c'
-- to start with, but we need that make a coherence choice of a and c !!
trace : {A B C : 𝕌} (a : ⟦ A ⟧ ) → (f : A ×ᵤ C ⟷ B ×ᵤ C) →
  (coh : Σ ⟦ C ⟧ (λ c → proj₂ (eval f (a , c)) ≡ c)) →
  ● a ⟷ ● (proj₁ (eval f (a , proj₁ coh)))
trace {A} {B} {C} a f (c , choice) =
  uniti⋆r ⊚        -- A ×ᵤ 1
  (id⟷ ⊗ η c) ⊚   -- A ×ᵤ (C ×ᵤ 1/C)
  assocl⋆ ⊚       -- (A ×ᵤ C) ×ᵤ 1/C
  (tensorr ⊗ id⟷) ⊚ -- bring in the ●
  (lift f ⊗ id⟷) ⊚ -- (B ×ᵤ C) ×ᵤ 1/C
  (tensorl ⊗ id⟷) ⊚ -- bring out the ●
  assocr⋆ ⊚          -- B ×ᵤ (C ×ᵤ 1/C)
  (id⟷ ⊗ (subst fixer choice id⟷ ⊚ ε c)) ⊚ -- B ×ᵤ 1
  unite⋆r
  where
    fixer : ⟦ C ⟧ → Set
    fixer d = (● (proj₂ (eval f (a , c))) ×ᵤ 𝟙/● d) ⟷ (● d ×ᵤ 𝟙/● d)


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
  ● v ⟷ ● (proj₁ (eval (q f1 f2 f3 f4) (v , u2 , u3 , u4)))
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
      ● v ⟷ ● (proj₁ (proj₁ (eval p ((v , v) , (v , v)))))
p2' v = trace v p2 ((v , (v , v)) , refl)

---------------------------------------------------------------------------------
-- Examples inspired by compact closed categories and fractional numbers.

-- Intuition:
-- 1/A x B is a space transformer; takes A space and returns B space
-- denote space transformers as A ⊸ B

-- Best we can do:
-- we need Singletons, so |a ⊸ b| is 1 component of a function.

_⊸_ : {A : 𝕌} → (a : ⟦ A ⟧) → {B : 𝕌} → (b : ⟦ B ⟧) → 𝕌
_⊸_ {A} a {B} b = 𝟙/● a ×ᵤ ● b

id⊸ : {A : 𝕌} {a : ⟦ A ⟧} → (a ⊸ a) ⟷ 𝟙
id⊸ {A} {a} =
  (𝟙/● a ×ᵤ ● a) ⟷⟨ swap⋆ ⟩
  (● a ×ᵤ 𝟙/● a) ⟷⟨ ε a ⟩
  𝟙 □

comp⊸ : {A B C : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {c : ⟦ C ⟧} →
        (a ⊸ b) ×ᵤ (b ⊸ c) ⟷ (a ⊸ c)
comp⊸ {A} {B} {C} {a} {b} {c} =
  (𝟙/● a ×ᵤ ● b) ×ᵤ (𝟙/● b ×ᵤ ● c) ⟷⟨ assocr⋆ ⟩
  𝟙/● a ×ᵤ (● b ×ᵤ (𝟙/● b ×ᵤ ● c)) ⟷⟨ id⟷ ⊗ assocl⋆ ⟩
  𝟙/● a ×ᵤ (● b ×ᵤ 𝟙/● b) ×ᵤ ● c   ⟷⟨ id⟷ ⊗ (ε b ⊗ id⟷) ⟩
  𝟙/● a ×ᵤ (𝟙 ×ᵤ ● c)                          ⟷⟨ id⟷ ⊗ unite⋆l ⟩
  𝟙/● a ×ᵤ ● c □

app : {A B : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} → (a ⊸ b) ×ᵤ ● a ⟷ ● b 
app {A} {B} {a} {b} =
  (𝟙/● a ×ᵤ ● b) ×ᵤ ● a ⟷⟨ swap⋆ ⊗ id⟷ ⟩
  (● b ×ᵤ 𝟙/● a) ×ᵤ ● a ⟷⟨ assocr⋆ ⊚ (id⟷ ⊗ (swap⋆ ⊚ ε a)) ⟩
  ● b ×ᵤ 𝟙                          ⟷⟨ unite⋆r ⟩
  ● b □

-- B/A × D/C ⟷ B × D / A × C
dist×/ : {A B C D : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {c : ⟦ C ⟧} {d : ⟦ D ⟧}
       → (a ⊸ b) ×ᵤ (c ⊸ d) ⟷ ((a , c) ⊸ (b , d))
dist×/ {A} {B} {C} {D} {a} {b} {c} {d} =
  (𝟙/● a ×ᵤ ● b) ×ᵤ (𝟙/● c ×ᵤ ● d) ⟷⟨ assocr⋆ ⊚ (id⟷ ⊗ assocl⋆) ⟩
  (𝟙/● a ×ᵤ (● b ×ᵤ 𝟙/● c) ×ᵤ ● d) ⟷⟨ id⟷ ⊗ (swap⋆ ⊗ id⟷) ⟩
  (𝟙/● a ×ᵤ (𝟙/● c ×ᵤ ● b) ×ᵤ ● d) ⟷⟨ (id⟷ ⊗ assocr⋆) ⊚ assocl⋆ ⟩
  (𝟙/● a ×ᵤ 𝟙/● c) ×ᵤ (● b ×ᵤ ● d) ⟷⟨ fracr ⊗ tensorr ⟩
  (𝟙/●_ {A ×ᵤ C} (a , c)) ×ᵤ (●_ {B ×ᵤ D} (b , d)) □

-- 1/A x 1/B <-> 1 / (A x B)
rev× : {A B : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
     → (a ⊸ tt) ×ᵤ (b ⊸ tt) ⟷ ((a , b) ⊸ tt)
rev× {A} {B} {a} {b} =
  (𝟙/● a ×ᵤ ● tt) ×ᵤ (𝟙/● b ×ᵤ ● tt) ⟷⟨ dist×/ ⟩
  (𝟙/● (a , b) ×ᵤ ● (tt , tt)) ⟷⟨ id⟷ ⊗ lift unite⋆l ⟩
  (𝟙/●_ {A ×ᵤ B} (a , b) ×ᵤ ● tt) □

{--
trivial : ● 𝟙 [ tt ] ⟷ 𝟙
trivial = {!!}
--}

-- (A <-> B) -> (1/A <-> 1/B)
--rev : {A B : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
--     → ● A [ a ] ⟷ ● B [ b ] → (b ⊸ tt) ⟷ (a ⊸ tt)
--  (𝟙/● A [ a ] ×ᵤ ● 𝟙 [ tt ]) ⟷⟨ {!!} ⟩
--  (𝟙/● B [ b ] ×ᵤ ● 𝟙 [ tt ]) □

rev : {A B : 𝕌} {a : ⟦ A ⟧} 
     → (f : A ⟷ B) → (𝟙/● (eval f a) ⟷ 𝟙/● a)
rev {A} {B} {a} f = dual f a

-- A <-> 1 / (1/A)
revrev : {A : 𝕌} {a : ⟦ A ⟧} {a⋆ : ⟦ 𝟙/● a ⟧} →
         ● a ⟷ 𝟙/● a⋆
revrev {A} {a} {a⋆} =
  ● a ⟷⟨ uniti⋆r ⟩
  ● a ×ᵤ 𝟙 ⟷⟨ {!id⟷ ⊗ η a⋆!} ⟩
  ● a ×ᵤ (𝟙/● a ×ᵤ 𝟙/● a⋆) ⟷⟨ {!!} ⟩ 
  𝟙/● a⋆ □

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

-- can we do this?
-- curry⊸ : {A B C : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {c : ⟦ C ⟧}
--        → (● A [ a ] ×ᵤ (b ⊸ c)) ⟷ (a ⊸ {!!}) -- what do we put here?
-- curry⊸ {A} {B} {C} {a} {b} {c} = {!!}


------------------------------------------------------------------------------

--}
