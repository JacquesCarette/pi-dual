{-# OPTIONS --without-K #-}
module UnivalenceFiniteTypes where

open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Function renaming (_∘_ to _○_)

open import FT
open import HoTT
open import Equivalences
open import TypeEquivalences
open import Path2Equiv

-- Reverse direction

toℕ : FT → ℕ
toℕ ZERO = zero
toℕ ONE = suc zero
toℕ (PLUS b₀ b₁) = (toℕ b₀) + (toℕ b₁) 
toℕ (TIMES b₀ b₁) = (toℕ b₀) * (toℕ b₁)

fromℕ : ℕ → FT
fromℕ zero = ZERO
fromℕ (suc n) = PLUS ONE (fromℕ n)

toℕ∘fromℕ : toℕ ○ fromℕ ∼ id
toℕ∘fromℕ zero = refl zero
toℕ∘fromℕ (suc n) =
  pathInd
    (λ {x} {y} p → suc x ≡ suc y)
    (λ n → refl (suc n))
    (toℕ∘fromℕ n)

assocr : {m : ℕ} (n : ℕ) → (PLUS (fromℕ n) (fromℕ m)) ⇛ fromℕ (n + m)
assocr zero = unite₊⇛
assocr (suc n) = assocr₊⇛ ◎ (id⇛ ⊕ (assocr n))

distr : (n₀ : ℕ) {n₁ : ℕ} → TIMES (fromℕ n₀) (fromℕ n₁) ⇛ fromℕ (n₀ * n₁)
distr zero = distz⇛
distr (suc n) {m} = dist⇛ ◎ ((unite⋆⇛ ⊕ id⇛) ◎ ((id⇛ ⊕ distr n) ◎ assocr m))

-- normalize a finite type to (1 + (1 + (1 + ... + (1 + 0) ... )))
-- a bunch of ones ending with zero with left biased + in between

normalize : FT → FT
normalize = fromℕ ○ toℕ

normal : (b : FT) → b ⇛ normalize b
normal ZERO = id⇛
normal ONE = uniti₊⇛ ◎ swap₊⇛
normal (PLUS b₀ b₁) = (normal b₀ ⊕ normal b₁) ◎ assocr (toℕ b₀)
normal (TIMES b₀ b₁) = (normal b₀ ⊗ normal b₁) ◎ distr (toℕ b₀)

normalizeC : {B : FT} → ⟦ normalize B ⟧ ≃ ⟦ B ⟧
normalizeC {B} = path2equiv (sym⇛ (normal B))

mapNorm :  {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → ⟦ normalize B₁ ⟧ ≃ ⟦ normalize B₂ ⟧
mapNorm {B₁} {B₂} eq = trans≃ (trans≃ (normalizeC {B₁}) eq) (sym≃ (normalizeC {B₂}))

------------------------------------------------------------------------
-- Inspect on steroids (borrowed from standard library)

-- Inspect on steroids can be used when you want to pattern match on
-- the result r of some expression e, and you also need to "remember"
-- that r ≡ e.

data Reveal_is_ {a} {A : Set a} (x : Hidden A) (y : A) : Set a where
  ⟪_⟫ : (eq : reveal x ≡ y) → Reveal x is y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal (hide f x) is (f x)
inspect f x = ⟪ refl (f x) ⟫

{-
sub1 : {A B : Set} → ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A → B
sub1 {A} {B} (f , mkisequiv g α h β) with f (inj₁ tt) | inspect f (inj₁ tt)
... | inj₂ b  | _      = 
       λ a → case f (inj₂ a) of λ
              { (inj₁ tt) -> b
              ; (inj₂ b') -> b' }
... | inj₁ tt | ⟪ eq₁ ⟫ = k eq₁
  where  k : f (inj₁ tt) ≡ inj₁ tt → A → B 
         k eq a with f (inj₂ a) | inspect f (inj₂ a)
         k eq a | inj₂ b  | _      = b
         k eq a | inj₁ tt | ⟪ eq₂ ⟫ with (proj₁ (inj₁₂path tt a)) (! inject)
            where inject = inj≃ (f , mkisequiv g α h β) (inj₂ a) (inj₁ tt) (eq₂ ∘ ! eq)
         k eq a | inj₁ tt | ⟪ eq₂ ⟫ | ()
-}
sub2 : {A B : Set} →  ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A ≃ B
sub2 {A} {B}  (f₁ , mkisequiv g₁ α₁ h₁ β₁) with f₁ (inj₁ tt) | inspect f₁ (inj₁ tt) | g₁ (inj₁ tt) | inspect g₁ (inj₁ tt)
sub2 {A} {B} (f₁ , mkisequiv g₁ α₁ h₁ β₁) | inj₁ tt | ⟪ eq₁ ⟫ | inj₁ tt | ⟪ eq₂ ⟫ = f , equiv₁ (mkqinv g α β)
  where 
        f : A → B
        f a with f₁ (inj₂ a) | inspect f₁ (inj₂ a)
        f a | inj₂ b  | _ = b
        f a | inj₁ tt | ⟪ eq ⟫ with (proj₁ (thm2-12-5 tt (inj₂ a)) inject)
          where inject = inj≃ (f₁ , mkisequiv g₁ α₁ h₁ β₁) (inj₁ tt) (inj₂ a) (eq₁ ∘ ! eq)
        f a | inj₁ tt | ⟪ eq ⟫ | ()
        g : B → A
        g b with g₁ (inj₂ b) | inspect g₁ (inj₂ b)
        g b | inj₂ a  | _ = a
        g b | inj₁ tt | ⟪ eq ⟫ with (proj₁ (thm2-12-5 tt (inj₂ b)) inject)
          where equiv = (f₁ , mkisequiv g₁ α₁ h₁ β₁)
                inject = inj≃ (sym≃ equiv) (inj₁ tt) (inj₂ b) (eq₂ ∘ ! eq) 
        g b | inj₁ tt | ⟪ eq ⟫ | () 
        α : f ○ g ∼ id
        α b with g₁ (inj₂ b) | inspect g₁ (inj₂ b)
        α b | inj₁ tt | ⟪ eq ⟫ with (proj₁ (thm2-12-5 tt (inj₂ b)) inject) 
          where equiv = (f₁ , mkisequiv g₁ α₁ h₁ β₁)
                inject = inj≃ (sym≃ equiv) (inj₁ tt) (inj₂ b) (eq₂ ∘ ! eq) 
        α b | inj₁ tt | ⟪ eq ⟫ | ()
        α b | inj₂ a  | ⟪ eq ⟫ with f₁ (inj₂ a) | inspect f₁ (inj₂ a) 
        α b | inj₂ a | ⟪ eq ⟫ | inj₁ tt | ⟪ eq₃ ⟫ with (proj₁ (thm2-12-5 tt (inj₂ a)) inject)
          where inject = inj≃ (f₁ , mkisequiv g₁ α₁ h₁ β₁) (inj₁ tt) (inj₂ a) (eq₁ ∘ ! eq₃)
        α b | inj₂ a | ⟪ eq ⟫ | inj₁ tt | ⟪ eq₃ ⟫ | ()
        α b | inj₂ a | ⟪ eq ⟫ | inj₂ b′ | ⟪ eq₃ ⟫ = proj₁ (inj₁₁path b′ b) (ap swap₊ (! (ap f₁ eq ∘ eq₃) ∘ α₁ (inj₂ b)))
        β : g ○ f ∼ id
        β = {!!}

sub2 (f₁ , mkisequiv g α h β) | inj₁ tt | ⟪ eq₁ ⟫ | inj₂ a | ⟪ eq₂ ⟫ with (proj₁ (thm2-12-5 tt (inj₂ a)) inject)
  where inject = inj≃ (f₁ , mkisequiv g α h β) (inj₁ tt) (inj₂ a) (eq₁ ∘ ! (α (inj₁ tt)) ∘ (ap f₁ eq₂))
sub2 (f₁ , mkisequiv g α h β) | inj₁ tt | ⟪ eq₁ ⟫ | inj₂ a | ⟪ eq₂ ⟫ | ()

sub2 (f₁ , mkisequiv g α h β) | inj₂ b | ⟪ eq₁ ⟫ | inj₁ tt | ⟪ eq₂ ⟫ with proj₁ (thm2-12-5 tt (inj₂ b)) (! (α (inj₁ tt)) ∘ (ap f₁ eq₂) ∘ eq₁ )
... | ()
sub2 (f , mkisequiv g α h β) | inj₂ b | ⟪ eq₁ ⟫ | inj₂ a | ⟪ eq₂ ⟫ = {!!}

lemma⊤⊎ : {B₁ B₂ : FT} → ⟦ PLUS ONE B₁ ⟧ ≃ ⟦ PLUS ONE B₂ ⟧ → ⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧
lemma⊤⊎ eq = sub2 eq

⟦_⟧ℕ : ℕ → Set
⟦ zero ⟧ℕ = ⊥
⟦ suc n ⟧ℕ = ⊤ ⊎ ⟦ n ⟧ℕ

ℕrespects⟦⟧ : {n : ℕ} → ⟦ fromℕ n ⟧ ≃ ⟦ n ⟧ℕ
ℕrespects⟦⟧ {zero} = id≃
ℕrespects⟦⟧ {suc n} = path⊎ id≃ (ℕrespects⟦⟧ {n})

lemmaℕ⊤⊎ : {n₁ n₂ : ℕ} → ⟦ suc n₁ ⟧ℕ ≃ ⟦ suc n₂ ⟧ℕ → ⟦ n₁ ⟧ℕ ≃ ⟦ n₂ ⟧ℕ
lemmaℕ⊤⊎ eq = sub2 eq

liftℕ : (n₁ n₂ : ℕ) → ⟦ n₁ ⟧ℕ ≃ ⟦ n₂ ⟧ℕ → (fromℕ n₁) ≡ (fromℕ n₂)
liftℕ zero zero eq = refl ZERO
liftℕ zero (suc n₂) (_ , mkisequiv g α h β) with h (inj₁ tt)
liftℕ zero (suc n₂) (_ , mkisequiv g α h β) | ()
liftℕ (suc n₁) zero (f , _) with f (inj₁ tt)
liftℕ (suc n₁) zero (f , _) | ()
liftℕ (suc n₁) (suc n₂) eq = ap (λ x → PLUS ONE x) (liftℕ n₁ n₂ (lemmaℕ⊤⊎ eq))

liftNormal : {B₁ B₂ : FT} →  ⟦ normalize B₁ ⟧ ≃ ⟦ normalize B₂ ⟧ → (normalize B₁) ≡ (normalize B₂)
liftNormal {B₁} {B₂} eq =
  liftℕ (toℕ B₁) (toℕ B₂)
    (⟦ toℕ B₁ ⟧ℕ ≃⟨ sym≃ (ℕrespects⟦⟧ {toℕ B₁}) ⟩ ⟦ normalize B₁ ⟧ ≃⟨ eq ⟩ ⟦ normalize B₂ ⟧ ≃⟨ ℕrespects⟦⟧ {toℕ B₂} ⟩ id≃)

sameNorm : {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → (normalize B₁) ≡ (normalize B₂)
sameNorm {B₁} {B₂} eq = liftNormal {B₁} {B₂} (mapNorm eq)

bridge : {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → (normalize B₁) ⇛ (normalize B₂)
bridge eq =
  pathInd
    (λ {B₁} {B₂} p → B₁ ⇛ B₂)
    (λ B → id⇛)
    (sameNorm eq)

equiv2path : {B₁ B₂ : FT} → (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → (B₁ ⇛ B₂)
-- not sure why typechecking this fails to terminate for me
-- equiv2path {B₁} {B₂} eq = ((normal B₁) ◎ bridge eq) ◎ (sym⇛ (normal B₂))
equiv2path {B₁} {B₂} eq = {!!}

-- univalence

univalence₁ : {B₁ B₂ : FT} → 
  (e : ⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) → path2equiv (equiv2path e) ≡ e
univalence₁ {B₁} {B₂} (f , feq) with equiv₂ feq
... | mkqinv g  α  β = {!!} 

univalence₂ : {B₁ B₂ : FT} → (p : B₁ ⇛ B₂) → equiv2path (path2equiv p) ≡ p
univalence₂ unite₊⇛ = {!!}
univalence₂ uniti₊⇛ = {!!}
univalence₂ swap₊⇛ = {!!}
univalence₂ assocl₊⇛ = {!!}
univalence₂ assocr₊⇛ = {!!}
univalence₂ unite⋆⇛ = {!!}
univalence₂ uniti⋆⇛ = {!!}
univalence₂ swap⋆⇛ = {!!}
univalence₂ assocl⋆⇛ = {!!}
univalence₂ assocr⋆⇛ = {!!}
univalence₂ distz⇛ = {!!}
univalence₂ factorz⇛ = {!!}
univalence₂ dist⇛ = {!!}
univalence₂ factor⇛ = {!!}
univalence₂ id⇛ = {!!}
univalence₂ (sym⇛ p) = {!!}
univalence₂ (p ◎ q) = {!!} 
univalence₂ (p ⊕ q) = {!!}
univalence₂ (p ⊗ q) = {!!} 

univalence : {B₁ B₂ : FT} → (B₁ ⇛ B₂) ≃ (⟦ B₁ ⟧ ≃ ⟦ B₂ ⟧) 
univalence = 
  (path2equiv , equiv₁ (mkqinv equiv2path univalence₁ univalence₂))

------------------------------------------------------------------------------

{--

Not used

exf : ⊤ ⊎ ℕ → ℕ
exf (inj₁ tt) = 0 
exf (inj₂ n) = suc n

exg : ℕ → ⊤ ⊎ ℕ
exg 0 = inj₁ tt
exg (suc n) = inj₂ n

exα : exf ○ exg ∼ id
exα 0 = refl 0
exα (suc n) = refl (suc n)

exβ : exg ○ exf ∼ id
exβ (inj₁ tt) = refl (inj₁ tt)
exβ (inj₂ n) = refl (inj₂ n) 

ex : (⊤ ⊎ ℕ) ≃ ℕ
ex = (exf , equiv₁ (mkqinv exg exα exβ))

exf2 : (⊤ ⊎ (⊤ ⊎ ℕ)) → (⊤ ⊎ ℕ)
exf2 (inj₁ tt) = inj₂ 0
exf2 (inj₂ (inj₁ tt)) = inj₂ 1
exf2 (inj₂ (inj₂ 0)) = inj₁ tt
exf2 (inj₂ (inj₂ (suc n))) = inj₂ (suc (suc n))

exg2 : (⊤ ⊎ ℕ) → (⊤ ⊎ (⊤ ⊎ ℕ))
exg2 (inj₁ tt) = inj₂ (inj₂ 0)
exg2 (inj₂ 0) = inj₁ tt
exg2 (inj₂ 1) = inj₂ (inj₁ tt)
exg2 (inj₂ (suc (suc n))) = inj₂ (inj₂ (suc n))

exα2 : exf2 ○ exg2 ∼ id
exα2 (inj₁ tt) = refl (inj₁ tt)
exα2 (inj₂ 0) = refl (inj₂ 0) 
exα2 (inj₂ 1) = refl (inj₂ 1) 
exα2 (inj₂ (suc (suc n))) = refl (inj₂ (suc (suc n))) 

exβ2 : exg2 ○ exf2 ∼ id
exβ2 (inj₁ tt) = refl (inj₁ tt) 
exβ2 (inj₂ (inj₁ tt)) = refl (inj₂ (inj₁ tt)) 
exβ2 (inj₂ (inj₂ 0)) = refl (inj₂ (inj₂ 0)) 
exβ2 (inj₂ (inj₂ (suc n))) = refl (inj₂ (inj₂ (suc n))) 

ex2 : (⊤ ⊎ (⊤ ⊎ ℕ)) ≃ (⊤ ⊎ ℕ)
ex2 = (exf2 , equiv₁ (mkqinv exg2 exα2 exβ2)) 

s1 : {A B : Set} → ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → A ≃ B
s1 (f , mkisequiv g α h β) with f (inj₁ tt) | g (inj₁ tt) 
... | inj₁ tt | inj₁ tt = {!!} 
... | inj₁ tt | inj₂ x = {!!} 
... | inj₂ x | inj₁ tt = {!!} 
... | inj₂ x | inj₂ y = {!!} 

--}
