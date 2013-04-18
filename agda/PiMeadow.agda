
{-# OPTIONS --no-termination-check #-}
module PiMeadow where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- infixr 20 _◎_

{-
postulate
  A : Set
  a b c : A
  p : a ≡ b
  q : b ≡ c

data <_> {a : Level} {A : Set a} (x : A) : Set a where
         singleton : {y : A} → y ≡ x -> < x > 

irr : singleton {_} {A} {b} p ≡ singleton {_} {A} {b} (sym q)
irr = {!!}

-}
data <_> {a : Level} {A : Set a} (x : A) : Set a where
         singleton : {y : A} → y ≡ x -> < x > 

-- Courtesy of Wolfram Kahl, a dependent cong₂
cong₂D  :  {a b c : Level} {A : Set a} {B : A → Set b} {C : Set c} (f : (x : A) → B x → C)
          →  {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
          →  (x₁≡x₂ : x₁ ≡ x₂) → y₁ ≡ subst B (sym x₁≡x₂) y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂D f refl refl = refl

mutual
  data B : Set₁ where
    ZERO  : B 
    ONE   : B
    PLUS  : B → B → B
    TIMES : B → B → B
    SING  : (b : B) → ⟦ b ⟧ → B
    RECIP : (b : B) → ⟦ b ⟧ → B
    DPAIR : (b : B) → (⟦ b ⟧ → B) → B

  ⟦_⟧ : B → Set
  ⟦ ZERO ⟧         = ⊥
  ⟦ ONE ⟧          = ⊤
  ⟦ PLUS b₁ b₂ ⟧   = ⟦ b₁ ⟧ ⊎ ⟦ b₂ ⟧
  ⟦ TIMES b₁ b₂ ⟧  = ⟦ b₁ ⟧ × ⟦ b₂ ⟧
  ⟦ SING b v ⟧  = <_> {A = ⟦ b ⟧} v
  ⟦ RECIP b v ⟧      = <_> {A = ⟦ b ⟧} v → ⊤
  ⟦ DPAIR b c ⟧ = Σ ⟦ b ⟧ (λ v → ⟦ c v ⟧)

-- Useful abbrev
leftIdemp : (b : B) → ⟦ b ⟧ → B
leftIdemp b v = TIMES (SING b v) (RECIP b v)

mutual 
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
    _◑_    : { b₁ b₂ : B } {c d : ⟦ b₂ ⟧ → B} → 
               (b₁ ⟷ DPAIR b₂ c) →
               (∀ {v} → c v ⟷ d v ) → (b₁ ⟷ DPAIR b₂ d )
 {-   _◐_    : { b₁ b₂ : B } {c d : ⟦ b₂ ⟧ → B} → 
               (∀ {v} → c v ⟷ d v ) → (b₁ ⟷ DPAIR b₂ c) →
                (b₁ ⟷ DPAIR b₂ d ) -}
    lift    : { b₁ b₂ : B } {v : ⟦ b₁ ⟧ } {w : ⟦ b₂ ⟧ } 
                (c : b₁ ⟷ b₂) → (w ≡ eval c v) → 
                (SING b₁ v ⟷ SING b₂ w) 
    _⊕_    : { b₁ b₂ b₃ b₄ : B } → 
             (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (PLUS b₁ b₂ ⟷ PLUS b₃ b₄)
    _⊗_    : { b₁ b₂ b₃ b₄ : B } → 
             (b₁ ⟷ b₃) → (b₂ ⟷ b₄) → (TIMES b₁ b₂ ⟷ TIMES b₃ b₄)
    η : {b : B} → b ⟷ DPAIR b (λ v → leftIdemp b v)
    ε : {b : B} → (DPAIR b (λ v → leftIdemp b v)) ⟷ b 

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
  eval (η {b}) v = v , ((singleton refl) , (λ x → tt))
  eval (ε {b}) (w , c) = w
  eval (c₁ ◑ c₂) v = proj₁ v₂ , eval (c₂ {proj₁ v₂}) (proj₂ v₂)  
    where v₂ = eval c₁ v
{-  eval (c₁ ◐ c₂) v = proj₁ v₂ , eval (c₁ {proj₁ v₂}) (proj₂ v₂)
    where v₂ = eval c₂ v -}
  eval (lift c z) (singleton {y = v} prf) = singleton {y = eval c v} (trans (cong (eval c) prf) (sym z))
  -- eval (lift c z) (singleton {y = v} refl) = singleton {y = eval c v} (sym z)
  -- eval (lift {- w = .(eval c v) -} c refl) (singleton {y = v} refl) = singleton {y = eval c v} refl
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
  evalB (η {b}) (w , c) = w
  evalB (ε {b}) v = v , ((singleton refl) , (λ x → tt))
  evalB (c₁ ◑ c₂) (v , x) = evalB c₁ (v , evalB c₂ x)
{-  evalB (c₁ ◐ c₂) (v , x) = evalB c₂ (v , evalB c₁ x) -}
  evalB (lift {v = v} c z) _ = eval (lift (op c) (reverse v c)) (singleton {y = eval c v} refl)

  reverse : {b₁ b₂ : B} (v : ⟦ b₁ ⟧) → (c : b₁ ⟷ b₂) → v ≡ evalB c (eval c v)
  reverse (inj₁ ()) unite₊
  reverse (inj₂ y) unite₊ = refl
  reverse v uniti₊ = refl
  reverse (inj₁ x) swap₊ = refl
  reverse (inj₂ y) swap₊ = refl
  reverse (inj₁ x) assocl₊ = refl
  reverse (inj₂ (inj₁ x)) assocl₊ = refl
  reverse (inj₂ (inj₂ y)) assocl₊ = refl
  reverse (inj₁ (inj₁ x)) assocr₊ = refl
  reverse (inj₁ (inj₂ y)) assocr₊ = refl
  reverse (inj₂ y) assocr₊ = refl
  reverse v unite⋆ = refl
  reverse v uniti⋆ = refl
  reverse v swap⋆ = refl
  reverse v assocl⋆ = refl
  reverse v assocr⋆ = refl
  reverse v id⟷ = refl
  reverse v (op c) = reverse' c v
  reverse v (c ◎ c₁) = trans (reverse v c) (cong (evalB c) eq)
     where eq : eval c v ≡ evalB c₁ (eval c₁ (eval c v))
           eq = reverse (eval c v) c₁
  reverse v (_◑_ {_} {b₂} {c} c₁ u) = trans eq₁ (cong (evalB c₁) eq₃)
    where y : Σ ⟦ b₂ ⟧ (λ ww → ⟦ c ww ⟧)
          y = eval c₁ v
          eq₁ : v ≡ evalB c₁ y
          eq₁ = reverse v c₁
          eq₂ : proj₂ y ≡ evalB u (eval u (proj₂ y))
          eq₂ = reverse (proj₂ y) u
          eq₃ : y ≡ (proj₁ y , evalB u (eval u (proj₂ y)))
          eq₃ = cong (λ z → (proj₁ y , z)) eq₂
{-  reverse v (_◐_ {_} {b₂} {c} c₁ c₂) = {!!} -}
--  reverse (singleton {.v₂} refl) (lift {v = v₂} {.(eval c v₂)} c refl) =  {!cong singleton {! proof-irrelevance  {! (reverse v₂ c)  !} ?!} !}
  reverse (singleton prf₁) (lift {v = v₂} c prf₂) =
      cong₂D (λ x e → singleton {y = x} e) 
            (trans prf₁ (reverse v₂ c)) (proof-irrelevance prf₁ _) 
  reverse (inj₁ x) (c ⊕ _) = cong inj₁ (reverse x c)
  reverse (inj₂ y) (_ ⊕ c) = cong inj₂ (reverse y c)
  reverse (x , y) (c₁ ⊗ c₂) = cong₂ _,_ (reverse x c₁) (reverse y c₂)
  reverse v η = refl
  reverse (_ , (singleton refl , _)) ε = refl

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
  reverse' (op c) w = reverse w c
  reverse' (c ◎ c₁) w = trans (reverse' c₁ w) (cong (eval c₁) (reverse' c (evalB c₁ w)))
  reverse' {b₁} {DPAIR b₂ d} (_◑_ {c = c} c₁ c₂) (w₁ , w₂) 
    rewrite (sym (reverse' c₁ (w₁ , evalB c₂ w₂))) | (sym (reverse' c₂ w₂)) =  refl
{-  reverse' (c₁ ◐ c₂) w = {!!} -}
  reverse' (lift {v = v} {w = .(eval c v)} c refl) (singleton refl) = cong₂D (λ x e → singleton {y = x} e) (reverse' c (eval c v)) (proof-irrelevance refl _)
  reverse' (c ⊕ _) (inj₁ x) = cong inj₁ (reverse' c x)
  reverse' (_ ⊕ c) (inj₂ y) = cong inj₂ (reverse' c y)
  reverse' (c₁ ⊗ c₂) (x , y) = cong₂ _,_ (reverse' c₁ x) (reverse' c₂ y)
  reverse' η (_ , singleton refl , _ ) = refl
  reverse' ε w = refl

-- they are properly inverse of each other
-- easy direction
η∘ε : {b : B} (v : ⟦ b ⟧) → eval {b} (η ◎ ε) v ≡ v
η∘ε _ = refl

-- hard direction.
ε∘η : {b : B} (v : ⟦ b ⟧) → { w : Σ < v > (λ _ → < v > → ⊤) } 
      → (eval {DPAIR b (leftIdemp b) } {_} (ε ◎ η) (v , w)) ≡ (v , w)
ε∘η {b} v {(singleton refl , r )} = cong f {v , v , (singleton refl)} refl
    where f : Σ ⟦ b ⟧ (λ x → Σ ⟦ b ⟧ (λ y → < v >)) → 
                Σ ⟦ b ⟧ (λ z → Σ < z > (λ x → < z > → ⊤ ))
          f (_ , (_ , j)) = (v , j , r)

-- Now need to write some actual programs...
makeFunc : {b₁ b₂ : B} → (c : b₁ ⟷ b₂) → b₁ ⟷ DPAIR b₁ (λ x → TIMES (SING b₂ (eval c x)) (RECIP b₁ x))
makeFunc {b₁} {b₂} c = η {b₁} ◑ (λ {v₁} →  (lift c refl) ⊗ id⟷)
