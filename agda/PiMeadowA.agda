{-# OPTIONS --no-termination-check #-}

module PiMeadowA where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Universe of types

-- The type < v > is the singleton type containing the one value v. We can
-- construct values of this type using (singleton v' proof) where the proof
-- asserts that v is propositionally equal to v.

data <_> {a : Level} {A : Set a} (x : A) : Set a where
  singleton : (y : A) → y ≡ x → < x > 

-- The types of Pi include 0, 1, +, * as usual but they also include three
-- new type expressions:
-- * SING v whose denotation is the singleton type < v > 
-- * RECIP v whose denotation is a pattern expressed in Agda as 
--   < v > -> Unit that matches v and nothing but v
-- * DTIMES b c which is a dependent version of TIMES: the first component is
--   a value v of type b and the second component is a value of type (c v)
--   that depends on the value in the first component. This dependent pair
--   will be used in the types of eta and epsilon.

mutual

  data B : Set₁ where
    ZERO   : B 
    ONE    : B
    PLUS   : B → B → B
    TIMES  : B → B → B
    SING   : {b : B} → ⟦ b ⟧ → B
    RECIP  : {b : B} → ⟦ b ⟧ → B
    DTIMES : (b : B) → (⟦ b ⟧ → B) → B

  ⟦_⟧ : B → Set
  ⟦ ZERO ⟧        = ⊥
  ⟦ ONE ⟧         = ⊤
  ⟦ PLUS b₁ b₂ ⟧  = ⟦ b₁ ⟧ ⊎ ⟦ b₂ ⟧
  ⟦ TIMES b₁ b₂ ⟧ = ⟦ b₁ ⟧ × ⟦ b₂ ⟧
  ⟦ SING v ⟧      = < v > 
  ⟦ RECIP v ⟧     = < v > → ⊤
  ⟦ DTIMES b c ⟧  = Σ ⟦ b ⟧ (λ v → ⟦ c v ⟧)

------------------------------------------------------------------------------
-- Abbreviations and general definitions

-- Useful abbrev: call this 'match' or 'inner product' ???
--   I would lead towards 'inner product'
leftIdemp : {b : B} → ⟦ b ⟧ → B
leftIdemp {b} v = TIMES (SING {b} v) (RECIP {b} v)

-- Courtesy of Wolfram Kahl, a dependent cong₂
cong₂D  :  {a b c : Level} {A : Set a} {B : A → Set b} {C : Set c} 
             (f : (x : A) → B x → C)
          →  {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
          →  (x₁≡x₂ : x₁ ≡ x₂) → y₁ ≡ subst B (sym x₁≡x₂) y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂D f refl refl = refl

------------------------------------------------------------------------------
-- Giant mutually recursive definition: 
-- syntax and types of combinators ⟷ refers to eval
-- eval refers to evalB
-- evalB refers to eval and reverse
-- reverse refers to reverse'
-- reverse' refers to reverse

mutual 

  -- syntax and types of combinators

  data _⟷_ : B → B → Set₁ where
    unite₊ : {b : B} → PLUS ZERO b ⟷ b
    uniti₊ : {b : B} → b ⟷ PLUS ZERO b
    swap₊ : {b₁ b₂ : B} → PLUS b₁ b₂ ⟷ PLUS b₂ b₁
    assocl₊ : { b₁ b₂ b₃ : B } → PLUS b₁ (PLUS b₂ b₃) ⟷ PLUS (PLUS b₁ b₂) b₃
    assocr₊ : { b₁ b₂ b₃ : B } → PLUS (PLUS b₁ b₂) b₃ ⟷ PLUS b₁ (PLUS b₂ b₃)
    unite⋆  : { b : B } → TIMES ONE b ⟷ b
    uniti⋆  : { b : B } → b ⟷ TIMES ONE b
    swap⋆ : {b₁ b₂ : B} → TIMES b₁ b₂ ⟷ TIMES b₂ b₁
    assocl⋆ : { b₁ b₂ b₃ : B } → TIMES b₁ (TIMES b₂ b₃) ⟷ TIMES (TIMES b₁ b₂) b₃
    assocr⋆ : { b₁ b₂ b₃ : B } → TIMES (TIMES b₁ b₂) b₃ ⟷ TIMES b₁ (TIMES b₂ b₃)
    id⟷ : {b : B } → b ⟷ b
    op    : { b₁ b₂ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₁)
    _◎_    : { b₁ b₂ b₃ : B } → (b₁ ⟷ b₂) → (b₂ ⟷ b₃) → (b₁ ⟷ b₃)
    _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
             (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
    _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
             (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)
    η : {b : B} → b ⟷ DTIMES b (λ v → leftIdemp {b} v)
    ε : {b : B} → (DTIMES b (λ v → leftIdemp {b} v)) ⟷ b 
    slide : { b₁ : B } {c d : ⟦ b₁ ⟧ → B} → 
            (∀ {v} → c v ⟷ d v) → DTIMES b₁ c ⟷ DTIMES b₁ d
    lift    : { b₁ b₂ : B } {v : ⟦ b₁ ⟧ } {w : ⟦ b₂ ⟧ } 
                (c : b₁ ⟷ b₂) → (w ≡ eval c v) → 
                (SING {b₁} v ⟷ SING {b₂} w) 

  -- Semantics

  eval : {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → ⟦ b₁ ⟧ → ⟦ b₂ ⟧
  eval unite₊ (inj₁ ())
  eval unite₊ (inj₂ v) = v
  eval uniti₊ v = inj₂ v
  eval swap₊ (inj₁ x) = inj₂ x
  eval swap₊ (inj₂ y) = inj₁ y
  eval assocl₊ (inj₁ x) = inj₁ (inj₁ x)
  eval assocl₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  eval assocl₊ (inj₂ (inj₂ x)) = inj₂ x
  eval assocr₊ (inj₁ (inj₁ x)) = inj₁ x
  eval assocr₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  eval assocr₊ (inj₂ y) = inj₂ (inj₂ y)
  eval unite⋆ (tt , x) = x
  eval uniti⋆ v = ( tt , v)
  eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
  eval assocl⋆ (x , (y , z)) = ((x , y), z)
  eval assocr⋆ ((x , y), z) = (x , (y , z))
  eval id⟷ v = v
  eval (op c) v = evalB c v
  eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
  eval (c₁ ⊕ c₂) (inj₁ x) = inj₁ (eval c₁ x)
  eval (c₁ ⊕ c₂) (inj₂ y) = inj₂ (eval c₂ y)
  eval (c₁ ⊗ c₂) (x , y) = (eval c₁ x , eval c₂ y)
  eval η v = v , ((singleton v refl) , (λ x → tt))
  eval ε (w , _) = w  -- the types insure the rhs is unique
  eval (lift c z) (singleton v prf) = 
    singleton (eval c v) (trans (cong (eval c) prf) (sym z))
  eval (slide t) (v , w) = v , eval t w 

  evalB :  {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → ⟦ b₂ ⟧ → ⟦ b₁ ⟧
  evalB uniti₊ (inj₁ ())
  evalB uniti₊ (inj₂ v) = v
  evalB unite₊ v = inj₂ v
  evalB swap₊ (inj₁ x) = inj₂ x
  evalB swap₊ (inj₂ y) = inj₁ y
  evalB assocr₊ (inj₁ x) = inj₁ (inj₁ x)
  evalB assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalB assocr₊ (inj₂ (inj₂ x)) = inj₂ x
  evalB assocl₊ (inj₁ (inj₁ x)) = inj₁ x
  evalB assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalB assocl₊ (inj₂ y) = inj₂ (inj₂ y)
  evalB uniti⋆ (tt , x) = x
  evalB unite⋆ v = ( tt , v)
  evalB swap⋆ (v₁ , v₂) = (v₂ , v₁)
  evalB assocr⋆ (x , (y , z)) = ((x , y), z)
  evalB assocl⋆ ((x , y), z) = (x , (y , z))
  evalB id⟷ v = v
  evalB (op c) v = eval c v
  evalB (c₁ ◎ c₂) v = evalB c₁ (evalB c₂ v)
  evalB (c₁ ⊕ c₂) (inj₁ x) = inj₁ (evalB c₁ x)
  evalB (c₁ ⊕ c₂) (inj₂ y) = inj₂ (evalB c₂ y)
  evalB (c₁ ⊗ c₂) (x , y) = (evalB c₁ x , evalB c₂ y)
  evalB η (w , _) = w
  evalB ε v = v , ((singleton v refl) , (λ x → tt))
  evalB (lift {v = v} c _) _ = 
    eval (lift (op c) (reverse c v)) (singleton (eval c v) refl)
  evalB (slide c₁) (v , w) = v , evalB c₁ w

  -- reversibility

  reverse : {b₁ b₂ : B} (c : b₁ ⟷ b₂) → (v : ⟦ b₁ ⟧) → v ≡ evalB c (eval c v)
  reverse unite₊ (inj₁ ())
  reverse unite₊ (inj₂ y) = refl
  reverse uniti₊ v = refl
  reverse swap₊ (inj₁ x) = refl
  reverse swap₊ (inj₂ y) = refl
  reverse assocl₊ (inj₁ x) = refl
  reverse assocl₊ (inj₂ (inj₁ x)) = refl
  reverse assocl₊ (inj₂ (inj₂ y)) = refl
  reverse assocr₊ (inj₁ (inj₁ x)) = refl
  reverse assocr₊ (inj₁ (inj₂ y)) = refl
  reverse assocr₊ (inj₂ y) = refl
  reverse unite⋆ v = refl
  reverse uniti⋆ v = refl
  reverse swap⋆ v = refl
  reverse assocl⋆ v = refl
  reverse assocr⋆ v = refl
  reverse id⟷ v = refl
  reverse (op c) v = reverse' c v
  reverse (c ◎ c₁) v = trans (reverse c v) 
                             (cong (evalB c) (reverse c₁ (eval c v)))
  reverse (lift {v = v₂} c prf₂) (singleton _ prf₁) =
      cong₂D singleton 
             (trans prf₁ (reverse c v₂)) (proof-irrelevance prf₁ _) 
  reverse (c ⊕ _) (inj₁ x) = cong inj₁ (reverse c x)
  reverse (_ ⊕ c) (inj₂ y) = cong inj₂ (reverse c y)
  reverse (c₁ ⊗ c₂) (x , y) = cong₂ _,_ (reverse c₁ x) (reverse c₂ y)
  reverse η v = refl
  reverse ε (v , (singleton .v refl , _)) = refl
  reverse (slide c) (_ , w) rewrite (sym (reverse c w)) = refl

  reverse' : {b₁ b₂ : B} (c : b₁ ⟷ b₂) → (w : ⟦ b₂ ⟧) → w ≡ eval c (evalB c w)
  reverse' unite₊ w = refl
  reverse' uniti₊ (inj₁ ())
  reverse' uniti₊ (inj₂ y) = refl
  reverse' swap₊ (inj₁ x) = refl
  reverse' swap₊ (inj₂ y) = refl
  reverse' assocl₊ (inj₁ (inj₁ x)) = refl
  reverse' assocl₊ (inj₁ (inj₂ y)) = refl
  reverse' assocl₊ (inj₂ y) = refl
  reverse' assocr₊ (inj₁ x) = refl
  reverse' assocr₊ (inj₂ (inj₁ x)) = refl
  reverse' assocr₊ (inj₂ (inj₂ y)) = refl
  reverse' unite⋆ w = refl
  reverse' uniti⋆ w = refl
  reverse' swap⋆ w = refl
  reverse' assocl⋆ w = refl
  reverse' assocr⋆ w = refl
  reverse' id⟷ w = refl
  reverse' (op c) w = reverse c w
  reverse' (c ◎ c₁) w = trans (reverse' c₁ w) 
                              (cong (eval c₁) (reverse' c (evalB c₁ w)))
  reverse' (lift {v = v} {w = .(eval c v)} c refl) (singleton ._ refl) = 
    cong₂D singleton (reverse' c (eval c v)) (proof-irrelevance refl _)
  reverse' (c ⊕ _) (inj₁ x) = cong inj₁ (reverse' c x)
  reverse' (_ ⊕ c) (inj₂ y) = cong inj₂ (reverse' c y)
  reverse' (c₁ ⊗ c₂) (x , y) = cong₂ _,_ (reverse' c₁ x) (reverse' c₂ y)
  reverse' η (v , singleton .v refl , _ ) = refl
  reverse' ε _ = refl
  reverse' (slide c) (v , w) rewrite (sym (reverse' c w)) = refl

------------------------------------------------------------------------------
-- Proofs of reversibility

-- they are properly inverse of each other
-- easy direction
η∘ε : {b : B} (v : ⟦ b ⟧) → eval {b} (η ◎ ε) v ≡ v
η∘ε _ = refl

-- hard direction.
ε∘η : {b : B} (v : ⟦ b ⟧) → { w : Σ < v > (λ _ → < v > → ⊤) } 
      → (eval {DTIMES b (leftIdemp {b}) } {_} (ε ◎ η) (v , w)) ≡ (v , w)
ε∘η {b} v {(singleton .v refl , r )} = cong f {v , v , (singleton v refl)} refl
    where f : Σ ⟦ b ⟧ (λ x → Σ ⟦ b ⟧ (λ y → < v >)) → 
                Σ ⟦ b ⟧ (λ z → Σ < z > (λ x → < z > → ⊤ ))
          f (_ , (_ , j)) = (v , j , r)

------------------------------------------------------------------------------
-- Examples
-- Now need to write some actual programs...

makeFunc : {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → 
            b₁ ⟷ DTIMES b₁ (λ x → TIMES (SING (eval c x)) (RECIP x))
makeFunc c = η ◎ slide (λ {_} →  (lift c refl) ⊗ id⟷)


------------------------------------------------------------------------------
------------------------------------------------------------------------------


