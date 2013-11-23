-- {-# OPTIONS --without-K #-}

module F2a where

open import Agda.Prim
open import Data.Unit
open import Data.Sum 
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Paths

---------------------------------------------------------------------------

-- functions between pointed types

record _→•_ {ℓ ℓ' : Level} (A• : Set• {ℓ}) (B• : Set• {ℓ'}) : Set (ℓ ⊔ ℓ') where
  field 
    f : ∣ A• ∣ → ∣ B• ∣
    resp• : f (• A•) ≡ • B•

open _→•_ public

-- composition of functions between pointed types
_⊚_ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A• : Set• {ℓ₁}} {B• : Set• {ℓ₂}} {C• : Set• {ℓ₃}} 
    → (A• →• B•) → (B• →• C•) → (A• →• C•)
g ⊚ h = record { f = f h ∘ f g ; resp• = trans (cong (f h) (resp• g)) (resp• h) }

-- See:
-- http://homotopytypetheory.org/2012/11/21/on-heterogeneous-equality/

beta : {ℓ : Level} {A : Set ℓ} {a : A} → • •[ A , a ] ≡ a
beta {ℓ} {A} {a} = refl

eta : {ℓ : Level} → (A• : Set• {ℓ}) → •[ ∣ A• ∣ , • A• ] ≡ A•
eta {ℓ} A• = refl

---------------------------------------------------------------------------
-- Isomorphisms (or more accurately equivalences) between pointed types

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (lsuc (lsuc ℓ') ⊔ ℓ)
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → Path (f x) (g x)

_∼•_ : ∀ {ℓ ℓ'} → {A• : Set• {ℓ}} → {B• : Set• {ℓ'}} →
      (A• →• B•) → (A• →• B•) → Set (lsuc (lsuc ℓ'))
_∼•_ {ℓ} {ℓ'} {A•} {B•} f• g• = Path (f f• (• A•)) (f g• (• A•)) 

-- ∼ is an equivalence relation

refl∼ : {A B : Set} {f : A → B} → (f ∼ f)
refl∼ {A} {B} {f} x = id⇛ (f x)

sym∼ : {A B : Set} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = sym⇛ (H x) 

trans∼ : {A B : Set} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = trans⇛ (H x) (G x)

-- quasi-inverses

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (lsuc (lsuc ℓ) ⊔ lsuc (lsuc ℓ')) where
  constructor mkqinv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id

idqinv : ∀ {ℓ} → {A : Set ℓ} → qinv {ℓ} {ℓ} {A} {A} id
idqinv = record {
           g = id ;
           α = λ b → id⇛ b ; 
           β = λ a → id⇛ a
         } 

-- equivalences

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (lsuc (lsuc ℓ) ⊔ lsuc (lsuc ℓ')) where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ∘ g) ∼ id
    h : B → A
    β : (h ∘ f) ∼ id

equiv₁ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {f : A → B} → qinv f → isequiv f
equiv₁ (mkqinv qg qα qβ) = mkisequiv qg qα qg qβ

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (lsuc (lsuc ℓ) ⊔ lsuc (lsuc ℓ'))
A ≃ B = Σ (A → B) isequiv

idequiv : ∀ {ℓ} {A : Set ℓ} → A ≃ A
idequiv = (id , equiv₁ idqinv)

------------------------------------------------------------------------------
-- We can extract a forward evaluator (i.e. paths really are functions)

eval :  {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
    •[ A , a ] ⇛ •[ B , b ] → A → B
eval (swap₁₊⇛ a) (inj₁ x) = inj₂ x
eval (swap₁₊⇛ a) (inj₂ y) = inj₁ y
eval (swap₂₊⇛ b) (inj₁ x) = inj₂ x
eval (swap₂₊⇛ b) (inj₂ y) = inj₁ y
eval (assocl₁₊⇛ a) (inj₁ x) = inj₁ (inj₁ x)
eval (assocl₁₊⇛ a) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
eval (assocl₁₊⇛ a) (inj₂ (inj₂ y)) = inj₂ y
eval (assocl₂₁₊⇛ b) (inj₁ x) = inj₁ (inj₁ x)
eval (assocl₂₁₊⇛ b) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
eval (assocl₂₁₊⇛ b) (inj₂ (inj₂ y)) = inj₂ y
eval (assocl₂₂₊⇛ c) (inj₁ x) = inj₁ (inj₁ x)
eval (assocl₂₂₊⇛ c) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
eval (assocl₂₂₊⇛ c) (inj₂ (inj₂ y)) = inj₂ y
eval (assocr₁₁₊⇛ a) (inj₁ (inj₁ x)) = inj₁ x
eval (assocr₁₁₊⇛ a) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
eval (assocr₁₁₊⇛ a) (inj₂ y) = inj₂ (inj₂ y)
eval (assocr₁₂₊⇛ b) (inj₁ (inj₁ x)) = inj₁ x
eval (assocr₁₂₊⇛ b) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
eval (assocr₁₂₊⇛ b) (inj₂ y) = inj₂ (inj₂ y)
eval (assocr₂₊⇛ c) (inj₁ (inj₁ x)) = inj₁ x
eval (assocr₂₊⇛ c) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
eval (assocr₂₊⇛ c) (inj₂ y) = inj₂ (inj₂ y)
eval {b = b} (unite⋆⇛ .b) (tt , x) = x
eval {a = a} (uniti⋆⇛ .a) x = tt , x
eval (swap⋆⇛ a b) (x , y) = y , x
eval (assocl⋆⇛ a b c) (x , y , z) = (x , y) , z
eval (assocr⋆⇛ a b c) ((x , y) , z) = x , y , z
eval (dist₁⇛ a c) (inj₁ x , y) = inj₁ (x , y)
eval (dist₁⇛ a c) (inj₂ x , y) = inj₂ (x , y)
eval (dist₂⇛ b c) (inj₁ x , z) = inj₁ (x , z)
eval (dist₂⇛ b c) (inj₂ y , z) = inj₂ (y , z)
eval (factor₁⇛ a c) (inj₁ (x , y)) = inj₁ x , y
eval (factor₁⇛ a c) (inj₂ (x , y)) = inj₂ x , y
eval (factor₂⇛ b c) (inj₁ (x , y)) = inj₁ x , y
eval (factor₂⇛ b c) (inj₂ (x , y)) = inj₂ x , y
eval {a = a} (id⇛ .a) x = x
eval (trans⇛ c d) x = eval d (eval c x)
eval (plus₁⇛ c d) (inj₁ x) = inj₁ (eval c x)
eval (plus₁⇛ c d) (inj₂ x) = inj₂ (eval d x)
eval (plus₂⇛ c d) (inj₁ x) = inj₁ (eval c x)
eval (plus₂⇛ c d) (inj₂ x) = inj₂ (eval d x)
eval (times⇛ c d) (x , y) = (eval c x , eval d y)

-- and a backwards one too

evalB : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
        •[ A , a ] ⇛ •[ B , b ] → B → A
evalB (swap₂₊⇛ a) (inj₁ x) = inj₂ x
evalB (swap₂₊⇛ a) (inj₂ y) = inj₁ y
evalB (swap₁₊⇛ b) (inj₁ x) = inj₂ x
evalB (swap₁₊⇛ b) (inj₂ y) = inj₁ y
evalB (assocr₂₊⇛ a) (inj₁ x) = inj₁ (inj₁ x)
evalB (assocr₂₊⇛ a) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB (assocr₂₊⇛ a) (inj₂ (inj₂ y)) = inj₂ y
evalB (assocr₁₂₊⇛ b) (inj₁ x) = inj₁ (inj₁ x)
evalB (assocr₁₂₊⇛ b) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB (assocr₁₂₊⇛ b) (inj₂ (inj₂ y)) = inj₂ y
evalB (assocr₁₁₊⇛ c) (inj₁ x) = inj₁ (inj₁ x)
evalB (assocr₁₁₊⇛ c) (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB (assocr₁₁₊⇛ c) (inj₂ (inj₂ y)) = inj₂ y
evalB (assocl₂₂₊⇛ a) (inj₁ (inj₁ x)) = inj₁ x
evalB (assocl₂₂₊⇛ a) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB (assocl₂₂₊⇛ a) (inj₂ y) = inj₂ (inj₂ y)
evalB (assocl₂₁₊⇛ b) (inj₁ (inj₁ x)) = inj₁ x
evalB (assocl₂₁₊⇛ b) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB (assocl₂₁₊⇛ b) (inj₂ y) = inj₂ (inj₂ y)
evalB (assocl₁₊⇛ c) (inj₁ (inj₁ x)) = inj₁ x
evalB (assocl₁₊⇛ c) (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB (assocl₁₊⇛ c) (inj₂ y) = inj₂ (inj₂ y)
evalB {a = a} (uniti⋆⇛ .a) (tt , x) = x
evalB {b = b} (unite⋆⇛ .b) x = tt , x
evalB (swap⋆⇛ a b) (x , y) = y , x
evalB (assocr⋆⇛ a b c) (x , y , z) = (x , y) , z
evalB (assocl⋆⇛ a b c) ((x , y) , z) = x , y , z
evalB (dist₁⇛ a c) (inj₁ (x , y)) = inj₁ x , y
evalB (dist₁⇛ a c) (inj₂ (x , y)) = inj₂ x , y
evalB (dist₂⇛ b c) (inj₁ (x , z)) = inj₁ x , z
evalB (dist₂⇛ b c) (inj₂ (y , z)) = inj₂ y , z
evalB (factor₁⇛ a c) (inj₁ x , y) = inj₁ (x , y)
evalB (factor₁⇛ a c) (inj₂ x , y) = inj₂ (x , y)
evalB (factor₂⇛ b c) (inj₁ x , y) = inj₁ (x , y)
evalB (factor₂⇛ b c) (inj₂ x , y) = inj₂ (x , y)
evalB {a = a} (id⇛ .a) x = x
evalB (trans⇛ c d) x = evalB c (evalB d x)
evalB (plus₁⇛ c d) (inj₁ x) = inj₁ (evalB c x)
evalB (plus₁⇛ c d) (inj₂ x) = inj₂ (evalB d x)
evalB (plus₂⇛ c d) (inj₁ x) = inj₁ (evalB c x)
evalB (plus₂⇛ c d) (inj₂ x) = inj₂ (evalB d x)
evalB (times⇛ c d) (x , y) = (evalB c x , evalB d y)

eval-resp-• : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
              (c : •[ A , a ] ⇛ •[ B , b ]) → eval c a ≡ b
eval-resp-• (swap₁₊⇛ a) = refl
eval-resp-• (swap₂₊⇛ b) = refl
eval-resp-• (assocl₁₊⇛ a) = refl
eval-resp-• (assocl₂₁₊⇛ b) = refl
eval-resp-• (assocl₂₂₊⇛ c) = refl
eval-resp-• (assocr₁₁₊⇛ a) = refl
eval-resp-• (assocr₁₂₊⇛ b) = refl
eval-resp-• (assocr₂₊⇛ c) = refl
eval-resp-• {b = b} (unite⋆⇛ .b) = refl
eval-resp-• {a = a} (uniti⋆⇛ .a) = refl
eval-resp-• (swap⋆⇛ a b) = refl
eval-resp-• (assocl⋆⇛ a b c) = refl
eval-resp-• (assocr⋆⇛ a b c) = refl
eval-resp-• (dist₁⇛ a c) = refl
eval-resp-• (dist₂⇛ b c) = refl
eval-resp-• (factor₁⇛ a c) = refl
eval-resp-• (factor₂⇛ b c) = refl
eval-resp-• {a = a} (id⇛ .a) = refl
eval-resp-• {a = a} (trans⇛ c d) rewrite eval-resp-• c | eval-resp-• d = refl
eval-resp-• (plus₁⇛ c d) rewrite eval-resp-• c = refl 
eval-resp-• (plus₂⇛ c d) rewrite eval-resp-• d = refl 
eval-resp-• (times⇛ c d) rewrite eval-resp-• c | eval-resp-• d = refl 

evalB-resp-• : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
              (c : •[ A , a ] ⇛ •[ B , b ]) → evalB c b ≡ a
evalB-resp-• (swap₁₊⇛ a) = refl
evalB-resp-• (swap₂₊⇛ b) = refl
evalB-resp-• (assocl₁₊⇛ a) = refl
evalB-resp-• (assocl₂₁₊⇛ b) = refl
evalB-resp-• (assocl₂₂₊⇛ c) = refl
evalB-resp-• (assocr₁₁₊⇛ a) = refl
evalB-resp-• (assocr₁₂₊⇛ b) = refl
evalB-resp-• (assocr₂₊⇛ c) = refl
evalB-resp-• {b = b} (unite⋆⇛ .b) = refl
evalB-resp-• {a = a} (uniti⋆⇛ .a) = refl
evalB-resp-• (swap⋆⇛ a b) = refl
evalB-resp-• (assocl⋆⇛ a b c) = refl
evalB-resp-• (assocr⋆⇛ a b c) = refl
evalB-resp-• (dist₁⇛ a c) = refl
evalB-resp-• (dist₂⇛ b c) = refl
evalB-resp-• (factor₁⇛ a c) = refl
evalB-resp-• (factor₂⇛ b c) = refl
evalB-resp-• {a = a} (id⇛ .a) = refl
evalB-resp-• {a = a} (trans⇛ c d) rewrite evalB-resp-• d | evalB-resp-• c = refl
evalB-resp-• (plus₁⇛ c d) rewrite evalB-resp-• c = refl 
evalB-resp-• (plus₂⇛ c d) rewrite evalB-resp-• d = refl 
evalB-resp-• (times⇛ c d) rewrite evalB-resp-• c | evalB-resp-• d = refl 

-- the proof that eval ∙ evalB x ≡ x will be useful below
eval∘evalB≡id :  {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → 
  (c : •[ A , a ] ⇛ •[ B , b ]) → evalB c (eval c a) ≡ a
eval∘evalB≡id c rewrite eval-resp-• c | evalB-resp-• c = refl

eval-gives-id⇛ : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → 
  (c : •[ A , a ] ⇛ •[ B , b ]) → •[ B , eval c a ] ⇛ •[ B , b ]
eval-gives-id⇛ {b = b} c rewrite eval-resp-• c = id⇛ b

eval• :  {ℓ : Level} {A• B• : Set• {ℓ}} → A• ⇛ B• → (A• →• B•)
eval• c = record { f = eval c ; resp• = eval-resp-• c } 

evalB• :  {ℓ : Level} {A• B• : Set• {ℓ}} → A• ⇛ B• → (B• →• A•)
evalB• c = record { f = evalB c ; resp• = evalB-resp-• c } 

------------------------------------------------------------------------------
-- Univalence
-- 
-- as a postulate for now but hopefully we can actually prove it since
-- the pi-combinators are sound and complete for isomorphisms between
-- finite types

postulate 
  univalence : {ℓ : Level} {A B : Set ℓ} → (Path A B) ≃ (A ≃ B)

-- This is at the wrong level... We need to define equivalences ≃ between
-- pointed sets too...

-- path2iso : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → Path a b → A ≃ B
-- path2iso {ℓ} {A} {B} {a} {b} p = (eval p , {!!})
