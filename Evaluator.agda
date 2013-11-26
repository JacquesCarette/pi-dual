-- {-# OPTIONS --without-K #-}

module Evaluator where

open import Agda.Prim
open import Data.Unit
open import Data.Nat hiding (_⊔_)
open import Data.Sum 
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Paths

------------------------------------------------------------------------------
-- For the usual situation, we can only establish one direction of univalence

swap₊ : {ℓ : Level} {A B : Set ℓ} → A ⊎ B → B ⊎ A
swap₊ (inj₁ a) = inj₂ a
swap₊ (inj₂ b) = inj₁ b

assocl₊ : {ℓ : Level} {A B C : Set ℓ} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
assocl₊ (inj₁ a) = inj₁ (inj₁ a)
assocl₊ (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
assocl₊ (inj₂ (inj₂ c)) = inj₂ c

assocr₊ : {ℓ : Level} {A B C : Set ℓ} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
assocr₊ (inj₁ (inj₁ a)) = inj₁ a
assocr₊ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
assocr₊ (inj₂ c) = inj₂ (inj₂ c)

unite⋆ : {ℓ : Level} {A : Set ℓ} → ⊤ × A → A
unite⋆ (tt , a) = a

uniti⋆ : {ℓ : Level} {A : Set ℓ} → A → ⊤ × A 
uniti⋆ a = (tt , a)

swap⋆ : {ℓ : Level} {A B : Set ℓ} → A × B → B × A
swap⋆ (a , b) = (b , a) 

assocl⋆ : {ℓ : Level} {A B C : Set ℓ} → A × (B × C) → (A × B) × C
assocl⋆ (a , (b , c)) = ((a , b) , c) 

assocr⋆ : {ℓ : Level} {A B C : Set ℓ} → (A × B) × C → A × (B × C)
assocr⋆ ((a , b) , c) = (a , (b , c))

dist : {ℓ : Level} {A B C : Set ℓ} → (A ⊎ B) × C → (A × C ⊎ B × C)
dist (inj₁ a , c) = inj₁ (a , c)
dist (inj₂ b , c) = inj₂ (b , c)

fact : {ℓ : Level} {A B C : Set ℓ} → (A × C ⊎ B × C) → (A ⊎ B) × C
fact (inj₁ (a , c)) = (inj₁ a , c) 
fact (inj₂ (b , c)) = (inj₂ b , c) 

eval : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → Path a b → (A → B)
eval (swap₁₊⇛ _)           = swap₊ 
eval (swap₂₊⇛ _)           = swap₊ 
eval (assocl₁₊⇛ _)         = assocl₊ 
eval (assocl₂₁₊⇛ _)        = assocl₊ 
eval (assocl₂₂₊⇛ _)        = assocl₊ 
eval (assocr₁₁₊⇛ _)        = assocr₊
eval (assocr₁₂₊⇛ _)        = assocr₊
eval (assocr₂₊⇛ _)         = assocr₊
eval (unite⋆⇛ _)           = unite⋆
eval (uniti⋆⇛ _)           = uniti⋆
eval (swap⋆⇛ _ _)          = swap⋆ 
eval (assocl⋆⇛ _ _ _)      = assocl⋆
eval (assocr⋆⇛ _ _ _)      = assocr⋆
eval (dist₁⇛ _ _)          = dist
eval (dist₂⇛ _ _)          = dist
eval (factor₁⇛ _ _)        = fact
eval (factor₂⇛ _ _)        = fact
eval (id⇛ _)               = id
eval (trans⇛ c d)          = eval d ∘ eval c
eval (plus₁⇛ c d)          = Data.Sum.map (eval c) (eval d) 
eval (plus₂⇛ c d)          = Data.Sum.map (eval c) (eval d) 
eval (times⇛ c d)          = Data.Product.map (eval c) (eval d)

-- Inverses

evalB : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → Path a b → (B → A) 
evalB (swap₂₊⇛ _)          = swap₊
evalB (swap₁₊⇛ _)          = swap₊
evalB (assocr₂₊⇛ _)        = assocl₊
evalB (assocr₁₂₊⇛ _)       = assocl₊
evalB (assocr₁₁₊⇛ _)       = assocl₊
evalB (assocl₂₂₊⇛ _)       = assocr₊
evalB (assocl₂₁₊⇛ _)       = assocr₊
evalB (assocl₁₊⇛ _)        = assocr₊
evalB (uniti⋆⇛ _)          = unite⋆
evalB (unite⋆⇛ _)          = uniti⋆
evalB (swap⋆⇛ _ _)         = swap⋆
evalB (assocr⋆⇛ _ _ _)     = assocl⋆
evalB (assocl⋆⇛ _ _ _)     = assocr⋆
evalB (dist₁⇛ _ _)         = fact
evalB (dist₂⇛ _ _)         = fact
evalB (factor₁⇛ _ _)       = dist
evalB (factor₂⇛ _ _)       = dist
evalB (id⇛ _)              = id
evalB (trans⇛ c d)         = evalB c ∘ evalB d
evalB (plus₁⇛ c d)         = Data.Sum.map (evalB c) (evalB d) 
evalB (plus₂⇛ c d)         = Data.Sum.map (evalB c) (evalB d) 
evalB (times⇛ c d)         = Data.Product.map (evalB c) (evalB d) 

------------------------------------------------------------------------------
-- Proving univalence•

eval-resp-• : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} →
              (c : Path a b) → eval c a ≡ b
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
              (c : Path a b) → evalB c b ≡ a
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
  (c : Path a b) → evalB c (eval c a) ≡ a
eval∘evalB≡id c rewrite eval-resp-• c | evalB-resp-• c = refl

-- if this is useful, move it elsewhere
-- but it might not be, as it appears to be 'level raising'
cong⇚ : {ℓ : Level} {A B : Set ℓ} {a₁ a₂ : A}
       (f : Path a₁ a₂ ) → (x : A) → Path (evalB f x) (evalB f x)
cong⇚ f x = id⇛ (evalB f x)

{--
eval∘evalB :  {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → 
  (c : Path a b) → (x : A) → Path (evalB c (eval c x)) x
eval∘evalB (swap₁₊⇛ a) (inj₁ x) = id⇛ (inj₁ x)
eval∘evalB (swap₁₊⇛ a) (inj₂ y) = id⇛ (inj₂ y)
eval∘evalB (swap₂₊⇛ b) (inj₁ x) = id⇛ (inj₁ x)
eval∘evalB (swap₂₊⇛ b) (inj₂ y) = id⇛ (inj₂ y)
eval∘evalB (assocl₁₊⇛ a) (inj₁ x) = id⇛ (inj₁ x)
eval∘evalB (assocl₁₊⇛ a) (inj₂ (inj₁ x)) = id⇛ (inj₂ (inj₁ x))
eval∘evalB (assocl₁₊⇛ a) (inj₂ (inj₂ y)) = id⇛ (inj₂ (inj₂ y))
eval∘evalB (assocl₂₁₊⇛ b) (inj₁ x) = id⇛ (inj₁ x)
eval∘evalB (assocl₂₁₊⇛ b) (inj₂ (inj₁ x)) = id⇛ (inj₂ (inj₁ x))
eval∘evalB (assocl₂₁₊⇛ b) (inj₂ (inj₂ y)) = id⇛ (inj₂ (inj₂ y))
eval∘evalB (assocl₂₂₊⇛ c) (inj₁ x) = id⇛ (inj₁ x)
eval∘evalB (assocl₂₂₊⇛ c) (inj₂ (inj₁ x)) = id⇛ (inj₂ (inj₁ x))
eval∘evalB (assocl₂₂₊⇛ c) (inj₂ (inj₂ y)) = id⇛ (inj₂ (inj₂ y))
eval∘evalB (assocr₁₁₊⇛ a) (inj₁ (inj₁ x)) = id⇛ (inj₁ (inj₁ x))
eval∘evalB (assocr₁₁₊⇛ a) (inj₁ (inj₂ y)) = id⇛ (inj₁ (inj₂ y))
eval∘evalB (assocr₁₁₊⇛ a) (inj₂ y) = id⇛ (inj₂ y)
eval∘evalB (assocr₁₂₊⇛ b) (inj₁ (inj₁ x)) = id⇛ (inj₁ (inj₁ x))
eval∘evalB (assocr₁₂₊⇛ b) (inj₁ (inj₂ y)) = id⇛ (inj₁ (inj₂ y))
eval∘evalB (assocr₁₂₊⇛ b) (inj₂ y) = id⇛ (inj₂ y)
eval∘evalB (assocr₂₊⇛ c) (inj₁ (inj₁ x)) = id⇛ (inj₁ (inj₁ x))
eval∘evalB (assocr₂₊⇛ c) (inj₁ (inj₂ y)) = id⇛ (inj₁ (inj₂ y))
eval∘evalB (assocr₂₊⇛ c) (inj₂ y) = id⇛ (inj₂ y)
eval∘evalB {b = b} (unite⋆⇛ .b) (tt , x) = id⇛ (tt , x)
eval∘evalB {a = a} (uniti⋆⇛ .a) x = id⇛ x
eval∘evalB (swap⋆⇛ a b) (x , y) = id⇛ (x , y)
eval∘evalB (assocl⋆⇛ a b c) (x , y , z) = id⇛ (x , y , z)
eval∘evalB (assocr⋆⇛ a b c) ((x , y) , z) = id⇛ ((x , y) , z)
eval∘evalB (dist₁⇛ a c) (inj₁ x , y) = id⇛ (inj₁ x , y)
eval∘evalB (dist₁⇛ a c) (inj₂ y , z) = id⇛ (inj₂ y , z)
eval∘evalB (dist₂⇛ b c) (inj₁ x , z) = id⇛ (inj₁ x , z)
eval∘evalB (dist₂⇛ b c) (inj₂ y , z) = id⇛ (inj₂ y , z)
eval∘evalB (factor₁⇛ a c) (inj₁ (x , y)) = id⇛ (inj₁ (x , y))
eval∘evalB (factor₁⇛ a c) (inj₂ (x , y)) = id⇛ (inj₂ (x , y))
eval∘evalB (factor₂⇛ b c) (inj₁ (x , y)) = id⇛ (inj₁ (x , y))
eval∘evalB (factor₂⇛ b c) (inj₂ (x , y)) = id⇛ (inj₂ (x , y))
eval∘evalB {a = a} (id⇛ .a) x = id⇛ x
eval∘evalB (trans⇛ {A = A} {B} {C} {a} {b} {c} c₁ c₂) x = trans⇛ {!cong⇚ ? (id⇛ (eval c₁ x))!} (eval∘evalB c₁ x) 
eval∘evalB (plus₁⇛ {b = b} c₁ c₂) (inj₁ x) = plus₁⇛ (eval∘evalB c₁ x) (id⇛ b)
eval∘evalB (plus₁⇛ {a = a} c₁ c₂) (inj₂ y) = plus₂⇛ (id⇛ a) (eval∘evalB c₂ y)
eval∘evalB (plus₂⇛ {b = b} c₁ c₂) (inj₁ x) = plus₁⇛ (eval∘evalB c₁ x) (id⇛ b)
eval∘evalB (plus₂⇛ {a = a} c₁ c₂) (inj₂ y) = plus₂⇛ (id⇛ a) (eval∘evalB c₂ y)
eval∘evalB (times⇛ c₁ c₂) (x , y) = times⇛ (eval∘evalB c₁ x) (eval∘evalB c₂ y) 
--}

eval-gives-id⇛ : {ℓ : Level} {A B : Set ℓ} {a : A} {b : B} → 
  (c : Path a b) → Path (eval c a) b 
eval-gives-id⇛ {b = b} c rewrite eval-resp-• c = id⇛ b
