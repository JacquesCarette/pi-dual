module MemSem where

open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec
open import Data.Vec.Relation.Unary.Any.Properties
open import Data.Vec.Any hiding (map)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_
infix  80 ∣_∣

data 𝕌 : Set where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌

⟦_⟧ : (A : 𝕌) → Set
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

data _⟷_ : 𝕌 → 𝕌 → Set where
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

∣_∣ : (A : 𝕌) → ℕ
∣ 𝟘 ∣ = 0
∣ 𝟙 ∣ = 1
∣ A₁ +ᵤ A₂ ∣ = ∣ A₁ ∣ + ∣ A₂ ∣
∣ A₁ ×ᵤ A₂ ∣ = ∣ A₁ ∣ * ∣ A₂ ∣

Vec× : ∀ {n m} {A B : Set} → Vec A n → Vec B m → Vec (A × B) (n * m)
Vec× va vb = concat (map (λ a₁ → map (a₁ ,_) vb) va)

∈map : ∀ {ℓ₁ ℓ₂} {n} {A : Set ℓ₁} {B : Set ℓ₂} {v : Vec A n} → (f : A → B) → (a : A)
     → Any (a ≡_) v → Any (f a ≡_) (map f v)
∈map f a (here refl) = here refl
∈map f a (there a∈v) = there (∈map f a a∈v)

inVec× : ∀ {n m} {A B : Set} → (va : Vec A n) → (vb : Vec B m)
       → (a : A) (b : B)
       → Any (a ≡_) va → Any (b ≡_) vb
       → Any ((a , b) ≡_) (Vec× va vb)
inVec× (a ∷ va) vb .a b (here refl) b∈vb = ++⁺ˡ {xs = map (a ,_) vb} (∈map _ _ b∈vb)
inVec× (x ∷ va) vb a b (there a∈va) b∈vb = ++⁺ʳ (map (x ,_) vb) (inVec× va vb a b a∈va b∈vb)

any≡← : ∀ {ℓ} {A : Set ℓ} {n} {a} → (v : Vec A n) → (i : Fin n) → a ≡ lookup v i → Any (a ≡_) v
any≡← (_ ∷ _)  Fin.0F refl = here refl
any≡← (_ ∷ v) (suc i) refl = there (any≡← v i refl)

Enum : (A : 𝕌) → Vec ⟦ A ⟧ ∣ A ∣
Enum 𝟘         = []
Enum 𝟙          = tt ∷ []
Enum (A₁ +ᵤ A₂) = map inj₁ (Enum A₁) ++ map inj₂ (Enum A₂)
Enum (A₁ ×ᵤ A₂) = Vec× (Enum A₁) (Enum A₂)

Find : {A : 𝕌} (x : ⟦ A ⟧) → Σ[ i ∈ Fin ∣ A ∣ ] (x ≡ lookup (Enum A) i)
Find {𝟘} ()
Find {𝟙} tt = index tt∈𝟙 , lookup-index tt∈𝟙
  where
    tt∈𝟙 : Any (tt ≡_) (Enum 𝟙)
    tt∈𝟙 = here refl
Find {A₁ +ᵤ A₂} (inj₁ x) =
  let i , p₁ = Find x in
  let x∈A₁ : Any ((inj₁ x) ≡_) (Enum (A₁ +ᵤ A₂))
      x∈A₁ = ++⁺ˡ {xs = map inj₁ (Enum A₁)} (∈map inj₁ x (any≡← _ i p₁)) in
  index x∈A₁ , lookup-index x∈A₁
Find {A₁ +ᵤ A₂} (inj₂ y) =
  let j , p₂ = Find y in
  let y∈A₂ : Any ((inj₂ y) ≡_) (Enum (A₁ +ᵤ A₂))
      y∈A₂ = ++⁺ʳ (map inj₁ (Enum A₁)) (∈map inj₂ y (any≡← _ j p₂)) in
  index y∈A₂ , lookup-index y∈A₂
Find {A₁ ×ᵤ A₂} (x , y) =
  let i , p₁ = Find x
      j , p₂ = Find y in
  let xy∈A₁×A₂ : Any ((x , y) ≡_) (Enum (A₁ ×ᵤ A₂))
      xy∈A₁×A₂ = inVec× (Enum A₁) (Enum A₂) x y (any≡← (Enum A₁) i p₁) (any≡← (Enum A₂) j p₂) in
  index xy∈A₁×A₂ , lookup-index xy∈A₁×A₂

Find' : {A : 𝕌} (x : ⟦ A ⟧) → Fin ∣ A ∣
Find' = proj₁ ∘ Find

card= : {t₁ t₂ : 𝕌} (C : t₁ ⟷ t₂) → (∣ t₁ ∣ ≡ ∣ t₂ ∣)
card= unite₊l = refl
card= uniti₊l = refl
card= {_} {t₂} unite₊r rewrite +-identityʳ ∣ t₂ ∣ = refl
card= {t₁} {_} uniti₊r rewrite +-identityʳ ∣ t₁ ∣ = refl
card= {t₁ +ᵤ t₂} {_} swap₊ rewrite +-comm ∣ t₁ ∣ ∣ t₂ ∣ = refl
card= {t₁ +ᵤ t₂ +ᵤ t₃} {_} assocl₊ rewrite +-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= {(t₁ +ᵤ t₂) +ᵤ t₃} {_} assocr₊  rewrite +-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= {_} {t₂} unite⋆l  rewrite +-identityʳ ∣ t₂ ∣ = refl
card= {t₁} {_} uniti⋆l  rewrite +-identityʳ ∣ t₁ ∣ = refl
card= {_} {t₂} unite⋆r  rewrite *-identityʳ ∣ t₂ ∣ = refl
card= {t₁} {_} uniti⋆r  rewrite *-identityʳ ∣ t₁ ∣ = refl
card= {t₁ ×ᵤ t₂} {_} swap⋆  rewrite *-comm ∣ t₁ ∣ ∣ t₂ ∣ = refl
card= {t₁ ×ᵤ t₂ ×ᵤ t₃} {_} assocl⋆  rewrite *-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= {(t₁ ×ᵤ t₂) ×ᵤ t₃} {_} assocr⋆  rewrite *-assoc ∣ t₁ ∣ ∣ t₂ ∣ (∣ t₃ ∣) = refl
card= absorbr  = refl
card= {t ×ᵤ 𝟘} {_} absorbl  rewrite *-zeroʳ ∣ t ∣ = refl
card= {_} {t ×ᵤ 𝟘} factorzr  rewrite *-zeroʳ ∣ t ∣ = refl
card= factorzl  = refl
card= {(t₁ +ᵤ t₂) ×ᵤ t₃} {_} dist  rewrite *-distribʳ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= {_} {(t₁ +ᵤ t₂) ×ᵤ t₃} factor  rewrite *-distribʳ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= {t₃ ×ᵤ (t₁ +ᵤ t₂)} {_} distl  rewrite *-distribˡ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= {_} {t₃ ×ᵤ (t₁ +ᵤ t₂)} factorl  rewrite *-distribˡ-+ ∣ t₃ ∣ ∣ t₁ ∣ (∣ t₂ ∣) = refl
card= id⟷  = refl
card= {t₁} {t₂} (c₁ ⊚ c₂)  rewrite card= c₁ | card= c₂ = refl
card= {t₁ +ᵤ t₂} {t₃ +ᵤ t₄} (c₁ ⊕ c₂) rewrite card= c₁ | card= c₂ = refl
card= {t₁ ×ᵤ t₂} {t₃ ×ᵤ t₄} (c₁ ⊗ c₂) rewrite card= c₁ | card= c₂ = refl

data State (A : 𝕌) : ℕ → Set where
  ⟪_[_]⟫ : Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State A ∣ A ∣

step : {A B : 𝕌} (c : A ⟷ B) → State A ∣ A ∣ → Σ[ C ∈ 𝕌 ] (C ⟷ B × State C ∣ A ∣)
step (unite₊l {t}) ⟪ v [ i ]⟫ with lookup v i
... | inj₂ x = _ , id⟷ , ⟪ Enum t [ Find' x ]⟫
step (uniti₊l {t}) ⟪ v [ i ]⟫ with lookup v i
... | x = _ , id⟷ , ⟪ (Enum (𝟘 +ᵤ t)) [ Find' x ]⟫
step (unite₊r {t}) ⟪ v [ i ]⟫ with lookup v i
... | inj₁ x rewrite card= (unite₊r {t}) = _ , id⟷ , ⟪ Enum t [ Find' x ]⟫
step (uniti₊r {t}) ⟪ v [ i ]⟫ with lookup v i
... | x rewrite card= (uniti₊r {t}) = _ , id⟷ , ⟪ (Enum (t +ᵤ 𝟘)) [ Find' {t +ᵤ 𝟘} (inj₁ x) ]⟫
step (swap₊ {t₁} {t₂}) ⟪ v [ i ]⟫ rewrite card= (swap₊ {t₁} {t₂}) with lookup v i
... | inj₁ x = _ , id⟷ , ⟪ Enum (t₂ +ᵤ t₁) [ Find' {t₂ +ᵤ t₁} (inj₂ x) ]⟫
... | inj₂ y = _ , id⟷ , ⟪ Enum (t₂ +ᵤ t₁) [ Find' {t₂ +ᵤ t₁} (inj₁ y) ]⟫
step (assocl₊ {t₁} {t₂} {t₃}) ⟪ v [ i ]⟫ rewrite card= (assocl₊ {t₁} {t₂} {t₃}) with lookup v i
... | inj₁ x = _ , id⟷ , ⟪ Enum ((t₁ +ᵤ t₂) +ᵤ t₃) [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₁ (inj₁ x)) ]⟫
... | inj₂ (inj₁ y) = _ , id⟷ , ⟪ Enum ((t₁ +ᵤ t₂) +ᵤ t₃) [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₁ (inj₂ y)) ]⟫
... | inj₂ (inj₂ z) = _ , id⟷ , ⟪ Enum ((t₁ +ᵤ t₂) +ᵤ t₃) [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₂ z) ]⟫
step (assocr₊ {t₁} {t₂} {t₃}) ⟪ v [ i ]⟫ rewrite card= (assocr₊ {t₁} {t₂} {t₃}) with lookup v i
... | inj₁ (inj₁ x) = _ , id⟷ , ⟪ Enum (t₁ +ᵤ t₂ +ᵤ t₃) [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₁ x) ]⟫
... | inj₁ (inj₂ y) = _ , id⟷ , ⟪ Enum (t₁ +ᵤ t₂ +ᵤ t₃) [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₂ (inj₁ y)) ]⟫
... | inj₂ z = _ , id⟷ , ⟪ Enum (t₁ +ᵤ t₂ +ᵤ t₃) [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₂ (inj₂ z)) ]⟫
step (unite⋆l {t}) ⟪ v [ i ]⟫ rewrite card= (unite⋆l {t}) with lookup v i
... | (tt , x) = _ , id⟷ , ⟪ Enum t [ Find' x ]⟫
step (uniti⋆l {t}) ⟪ v [ i ]⟫ rewrite card= (uniti⋆l {t}) with lookup v i
... | x = _ , id⟷ , ⟪ Enum (𝟙 ×ᵤ t) [ Find' (tt , x) ]⟫
step (unite⋆r {t}) ⟪ v [ i ]⟫ rewrite card= (unite⋆r {t}) with lookup v i
... | (x , tt) = _ , id⟷ , ⟪ Enum t [ Find' x ]⟫
step (uniti⋆r {t}) ⟪ v [ i ]⟫ rewrite card= (uniti⋆r {t}) with lookup v i
... | x = _ , id⟷ , ⟪ Enum (t ×ᵤ 𝟙) [ Find' (x , tt) ]⟫
step (swap⋆ {t₁} {t₂}) ⟪ v [ i ]⟫ rewrite card= (swap⋆ {t₁} {t₂}) with lookup v i
... | (x , y) = _ , id⟷ , ⟪ Enum (t₂ ×ᵤ t₁) [ Find' (y , x) ]⟫
step (assocl⋆ {t₁} {t₂} {t₃}) ⟪ v [ i ]⟫ rewrite card= (assocl⋆ {t₁} {t₂} {t₃}) with lookup v i
... | x , y , z = _ , id⟷ , ⟪ Enum ((t₁ ×ᵤ t₂) ×ᵤ t₃) [ Find' ((x , y) , z) ]⟫
step (assocr⋆ {t₁} {t₂} {t₃}) ⟪ v [ i ]⟫ rewrite card= (assocr⋆ {t₁} {t₂} {t₃}) with lookup v i
... | (x , y) , z = _ , id⟷ , ⟪ Enum (t₁ ×ᵤ t₂ ×ᵤ t₃) [ Find' (x , y , z) ]⟫
step absorbr ⟪ v [ i ]⟫ with lookup v i
... | ()
step absorbl ⟪ v [ i ]⟫ with lookup v i
... | ()
step factorzr ⟪ v [ i ]⟫ with lookup v i
... | ()
step factorzl ⟪ v [ i ]⟫ with lookup v i
... | ()
step (dist {t₁} {t₂} {t₃}) ⟪ v [ i ]⟫ rewrite card= (dist {t₁} {t₂} {t₃}) with lookup v i
... | (inj₁ x , z) = _ , id⟷ , ⟪ Enum ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)) [ Find' {(t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)} (inj₁ (x , z)) ]⟫
... | (inj₂ y , z) = _ , id⟷ , ⟪ Enum ((t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)) [ Find' {(t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)} (inj₂ (y , z)) ]⟫
step (factor {t₁} {t₂} {t₃}) ⟪ v [ i ]⟫ rewrite card= (factor {t₁} {t₂} {t₃}) with lookup v i
... | (inj₁ (x , z)) = _ , id⟷ , ⟪ Enum ((t₁ +ᵤ t₂) ×ᵤ t₃) [ Find' {(t₁ +ᵤ t₂) ×ᵤ t₃} (inj₁ x , z) ]⟫
... | (inj₂ (y , z)) = _ , id⟷ , ⟪ Enum ((t₁ +ᵤ t₂) ×ᵤ t₃) [ Find' {(t₁ +ᵤ t₂) ×ᵤ t₃} (inj₂ y , z) ]⟫
step (distl {t₁} {t₂} {t₃}) ⟪ v [ i ]⟫ rewrite card= (distl {t₁} {t₂} {t₃}) with lookup v i
... | (x , inj₁ y) = _ , id⟷ , ⟪ (Enum ((t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃))) [ Find' {(t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)} (inj₁ (x , y)) ]⟫
... | (x , inj₂ z) = _ , id⟷ , ⟪ (Enum ((t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃))) [ Find' {(t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)} (inj₂ (x , z)) ]⟫
step (factorl {t₁} {t₂} {t₃}) ⟪ v [ i ]⟫ rewrite card= (factorl {t₁} {t₂} {t₃}) with lookup v i
... | inj₁ (x , y) = _ , id⟷ , ⟪ (Enum (t₁ ×ᵤ (t₂ +ᵤ t₃))) [ Find' {t₁ ×ᵤ (t₂ +ᵤ t₃)} (x , inj₁ y) ]⟫
... | inj₂ (x , z) = _ , id⟷ , ⟪ (Enum (t₁ ×ᵤ (t₂ +ᵤ t₃))) [ Find' {t₁ ×ᵤ (t₂ +ᵤ t₃)} (x , inj₂ z) ]⟫
step id⟷ st = _ , id⟷ , st
step (id⟷ ⊚ c₂) st = _ , c₂ , st
step (c₁ ⊚ c₂) st with step c₁ st
... | _ , c₁' , st' = _ , c₁' ⊚ c₂ , st'
step (_⊕_ {t₁} {t₂} {t₃} {t₄} c₁ c₂) ⟪ v [ i ]⟫ with lookup v i
step (_⊕_ {t₁} {t₂} {t₃} {t₄} c₁ c₂) ⟪ v [ i ]⟫ | inj₁ x with c₁
... | id⟷ rewrite card= c₂ = _ , id⟷ , ⟪ Enum (t₃ +ᵤ t₄) [ Find' {t₃ +ᵤ t₄} (inj₁ x) ]⟫
... | _   with step c₁ ⟪ Enum t₁ [ Find' x ]⟫
... | t₁' , c₁' , st' rewrite trans (card= c₁) (sym (card= c₁')) with st'
... | ⟪ v' [ i' ]⟫ = _ , (c₁' ⊕ c₂) , ⟪ Enum (t₁' +ᵤ t₂) [ Find' {t₁' +ᵤ t₂} (inj₁ (lookup v' i')) ]⟫
step (_⊕_ {t₁} {t₂} {t₃} {t₄} c₁ c₂) ⟪ v [ i ]⟫ | inj₂ y with c₂
... | id⟷ rewrite card= c₁ = _ , id⟷ , ⟪ Enum (t₃ +ᵤ t₄) [ Find' {t₃ +ᵤ t₄} (inj₂ y) ]⟫
... | _   with step c₂ ⟪ Enum t₂ [ Find' y ]⟫
... | t₂' , c₂' , st' rewrite trans (card= c₂) (sym (card= c₂')) with st'
... | ⟪ v' [ i' ]⟫ = _ , (c₁ ⊕ c₂') , ⟪ Enum (t₁ +ᵤ t₂') [ Find' {t₁ +ᵤ t₂'} (inj₂ (lookup v' i')) ]⟫
step (id⟷ ⊗ id⟷) st = _ , id⟷ , st
step (_⊗_ {t₁} {t₂} {t₃} {t₄} id⟷ c₂) ⟪ v [ i ]⟫ with lookup v i
... | (x , y) with step c₂ ⟪ Enum t₂ [ Find' y ]⟫
... | t₂' , c₂' , st' rewrite trans (card= c₂) (sym (card= c₂')) with st'
... | ⟪ v' [ i' ]⟫ = _ , (id⟷ ⊗ c₂') , ⟪ Enum (t₁ ×ᵤ t₂') [ Find' (x , (lookup v' i')) ]⟫
step (_⊗_ {t₁} {t₂} {t₃} {t₄} c₁ c₂) ⟪ v [ i ]⟫ with lookup v i
... | (x , y) with step c₁ ⟪ Enum t₁ [ Find' x ]⟫
... | t₁' , c₁' , st' rewrite trans (card= c₁) (sym (card= c₁')) with st'
... | ⟪ v' [ i' ]⟫ = _ , (c₁' ⊗ c₂) , ⟪ Enum (t₁' ×ᵤ t₂) [ Find' ((lookup v' i') , y) ]⟫

data State' (n : ℕ) : Set where
  ⟪_∥_,_[_]⟫ : {A B : 𝕌} → A ⟷ B → (∣ A ∣ ≡ n) → Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State' n

step' : {A : 𝕌} → State' ∣ A ∣ → State' ∣ A ∣
step' {A} ⟪ c ∥ p , v [ i ]⟫ with step c ⟪ v [ i ]⟫
... | A' , c' , st rewrite trans (card= c) (sym (card= c')) with st
... | ⟪ v' [ i' ]⟫ = ⟪ c' ∥ p , v' [ i' ]⟫

𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

𝔽 𝕋 : ⟦ 𝔹 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

run : (sz n : ℕ) → State' sz → Vec (State' sz) (suc n)
run sz 0 st = [ st ]
run sz (suc n) st with run sz n st
... | sts with last sts
... | ⟪_∥_,_[_]⟫ {A} {B} cx refl vx ix rewrite +-comm 1 (suc n) = sts ++ [ step' {A} ⟪ cx ∥ refl , vx [ ix ]⟫ ]

CNOT : 𝔹 ×ᵤ 𝔹 ⟷ 𝔹 ×ᵤ 𝔹
CNOT = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ swap₊)) ⊚ factor

ex₁ : Vec (State' ∣ 𝔹 ×ᵤ 𝔹 ∣) 8
ex₁ = run ∣ 𝔹 ×ᵤ 𝔹 ∣ 7 ⟪ CNOT ∥ refl , Enum (𝔹 ×ᵤ 𝔹) [ Fin.fromℕ 3 ]⟫
