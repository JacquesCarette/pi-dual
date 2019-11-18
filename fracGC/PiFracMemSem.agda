{-# OPTIONS --without-K --safe #-}
module PiFracMemSem where

open import Relation.Binary.Core
open import Data.Empty
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
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  renaming ([_] to R[_])

infixr 70 _×ᵤ_
infixr 60 _+ᵤ_
infixr 50 _⊚_
infix  80 ∣_∣

data 𝕌 : Set where
  𝟘       : 𝕌
  𝟙       : 𝕌
  _+ᵤ_    : 𝕌 → 𝕌 → 𝕌
  _×ᵤ_    : 𝕌 → 𝕌 → 𝕌
  𝟙/_ : 𝕌 → 𝕌

data ◯ : Set where
  ○ : ◯

⟦_⟧ : (A : 𝕌) → Set
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ 𝟙/ t ⟧ = ◯

mutual
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
    η : {t : 𝕌} {t≠0 : ¬ ∣ t ∣ ≡ 0} → 𝟙 ⟷ t ×ᵤ (𝟙/ t)
    ε : {t : 𝕌} {t≠0 : ¬ ∣ t ∣ ≡ 0} → t ×ᵤ (𝟙/ t) ⟷ 𝟙

  ∣_∣ : (A : 𝕌) → ℕ
  ∣ 𝟘 ∣ = 0
  ∣ 𝟙 ∣ = 1
  ∣ A₁ +ᵤ A₂ ∣ = ∣ A₁ ∣ + ∣ A₂ ∣
  ∣ A₁ ×ᵤ A₂ ∣ = ∣ A₁ ∣ * ∣ A₂ ∣
  ∣ 𝟙/ A ∣ = 1

default : (t : 𝕌) → {t≠0 : ¬ ∣ t ∣ ≡ 0} → ⟦ t ⟧
default 𝟘 {t≠0} = ⊥-elim (t≠0 refl) 
default 𝟙 = tt
default (t₁ +ᵤ t₂) {p≠0} with ∣ t₁ ∣ | ∣ t₂ ∣ | inspect ∣_∣ t₁ | inspect ∣_∣ t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 refl)
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] =
  inj₂ (default t₂ {λ t2≡0 → ⊥-elim (p≠0 (trans (sym s₂) t2≡0))})
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] =
  inj₁ (default t₁ {λ t1≡0 →
    ⊥-elim (p≠0 ((trans (sym (trans s₁ (sym (+-identityʳ (suc m))))) t1≡0)))})
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] =
  inj₁ (default t₁ {λ t1≡0 → ⊥-elim (1+n≢0 (trans (sym s₁) t1≡0))})
default (t₁ ×ᵤ t₂) {p≠0} with ∣ t₁ ∣ | ∣ t₂ ∣ | inspect ∣_∣ t₁ | inspect ∣_∣ t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 refl)
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 refl)
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 (*-zeroʳ (suc m)))
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] =
  default t₁ {λ t1≡0 → ⊥-elim (1+n≢0 (trans (sym s₁) t1≡0))},
  default t₂ {λ t2≡0 → ⊥-elim (1+n≢0 (trans (sym s₂) t2≡0))}
default (𝟙/ t) = ○ 

𝕌dec : (t : 𝕌) → Decidable (_≡_ {A = ⟦ t ⟧})
𝕌dec 𝟘 ()
𝕌dec 𝟙 tt tt = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ y) with 𝕌dec t₁ x y
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ .x) | yes refl = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₁ y)  | no ¬p = no (λ {refl → ¬p refl})
𝕌dec (t₁ +ᵤ t₂) (inj₁ x) (inj₂ y) = no (λ ())
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₁ y) = no (λ ())
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ y) with 𝕌dec t₂ x y
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ .x) | yes refl = yes refl
𝕌dec (t₁ +ᵤ t₂) (inj₂ x) (inj₂ y) | no ¬p = no (λ {refl → ¬p refl})
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , y₂) with 𝕌dec t₁ x₁ x₂ | 𝕌dec t₂ y₁ y₂
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (.x₁ , .y₁) | yes refl | yes refl = yes refl
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (.x₁ , y₂) | yes refl | no ¬p = no (λ p → ¬p (cong proj₂ p))
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , .y₁) | no ¬p | yes refl = no (λ p → ¬p (cong proj₁ p))
𝕌dec (t₁ ×ᵤ t₂) (x₁ , y₁) (x₂ , y₂) | no ¬p | no ¬p₁ = no (λ p → ¬p (cong proj₁ p))
𝕌dec (𝟙/ t) ○ ○ = yes refl

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
Enum (𝟙/ A) = ○ ∷ []

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
Find {𝟙/ A} ○ = index ○∈𝟙/A , lookup-index ○∈𝟙/A
  where
    ○∈𝟙/A : Any (○ ≡_) (Enum (𝟙/ A))
    ○∈𝟙/A = here refl

Find' : {A : 𝕌} (x : ⟦ A ⟧) → Fin ∣ A ∣
Find' = proj₁ ∘ Find

data State (A : 𝕌) : Set where
  ⟪_[_]⟫ : Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State A

resolve : {A : 𝕌} → State A → ⟦ A ⟧
resolve ⟪ v [ i ]⟫ = lookup v i

st : {A B : 𝕌} → ⟦ A ⟧ → (c : A ⟷ B) → Σ[ C ∈ 𝕌 ] (C ⟷ B × State C)
st (inj₂ y) (unite₊l {t})                   = _ , id⟷ , ⟪ Enum t [ Find' y ]⟫
st a (uniti₊l {t})                          = _ , id⟷ , ⟪ (Enum (𝟘 +ᵤ t)) [ Find' a ]⟫
st (inj₁ x) (unite₊r {t})                   = _ , id⟷ , ⟪ Enum t [ Find' x ]⟫
st a (uniti₊r {t})                          = _ , id⟷ , ⟪ (Enum (t +ᵤ 𝟘)) [ Find' {t +ᵤ 𝟘} (inj₁ a) ]⟫
st (inj₁ x) (swap₊ {t₁} {t₂})               = _ , id⟷ , ⟪ Enum _ [ Find' {t₂ +ᵤ t₁} (inj₂ x) ]⟫
st (inj₂ y) (swap₊ {t₁} {t₂})               = _ , id⟷ , ⟪ Enum _ [ Find' {t₂ +ᵤ t₁} (inj₁ y) ]⟫
st (inj₁ x) (assocl₊ {t₁} {t₂} {t₃})        = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₁ (inj₁ x)) ]⟫
st (inj₂ (inj₁ x)) (assocl₊ {t₁} {t₂} {t₃}) = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₁ (inj₂ x)) ]⟫
st (inj₂ (inj₂ y)) (assocl₊ {t₁} {t₂} {t₃}) = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) +ᵤ t₃} (inj₂ y) ]⟫
st (inj₁ (inj₁ x)) (assocr₊ {t₁} {t₂} {t₃}) = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₁ x) ]⟫
st (inj₁ (inj₂ y)) (assocr₊ {t₁} {t₂} {t₃}) = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₂ (inj₁ y)) ]⟫
st (inj₂ y) (assocr₊ {t₁} {t₂} {t₃})        = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ +ᵤ t₂ +ᵤ t₃} (inj₂ (inj₂ y)) ]⟫
st (tt , y) unite⋆l                         = _ , id⟷ , ⟪ Enum _ [ Find' y ]⟫
st a uniti⋆l                                = _ , id⟷ , ⟪ Enum _ [ Find' (tt , a) ]⟫
st (x , tt) unite⋆r                         = _ , id⟷ , ⟪ Enum _ [ Find' x ]⟫
st a uniti⋆r                                = _ , id⟷ , ⟪ Enum _ [ Find' (a , tt) ]⟫
st (x , y) swap⋆                            = _ , id⟷ , ⟪ Enum _ [ Find' (y , x) ]⟫
st (x , y , z) assocl⋆                      = _ , id⟷ , ⟪ Enum _ [ Find' ((x , y) , z) ]⟫
st ((x , y) , z) assocr⋆                    = _ , id⟷ , ⟪ Enum _ [ Find' (x , y , z) ]⟫
st (inj₁ x , y) (dist {t₁} {t₂} {t₃})       = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ ×ᵤ t₃ +ᵤ t₂ ×ᵤ t₃} (inj₁ (x , y)) ]⟫
st (inj₂ x , y) (dist {t₁} {t₂} {t₃})       = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ ×ᵤ t₃ +ᵤ t₂ ×ᵤ t₃} (inj₂ (x , y)) ]⟫
st (inj₁ (x , y)) (factor {t₁} {t₂} {t₃})   = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) ×ᵤ t₃} (inj₁ x , y) ]⟫
st (inj₂ (y , z)) (factor {t₁} {t₂} {t₃})   = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ +ᵤ t₂) ×ᵤ t₃} (inj₂ y , z) ]⟫
st (x , inj₁ y) (distl {t₁} {t₂} {t₃})      = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)} (inj₁ (x , y)) ]⟫
st (x , inj₂ y) (distl {t₁} {t₂} {t₃})      = _ , id⟷ , ⟪ Enum _ [ Find' {(t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)} (inj₂ (x , y)) ]⟫
st (inj₁ (x , y)) (factorl {t₁} {t₂} {t₃})  = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ ×ᵤ (t₂ +ᵤ t₃)} (x , inj₁ y) ]⟫
st (inj₂ (x , z)) (factorl {t₁} {t₂} {t₃})  = _ , id⟷ , ⟪ Enum _ [ Find' {t₁ ×ᵤ (t₂ +ᵤ t₃)} (x , inj₂ z) ]⟫
st tt (η {t} {nz})                          = _ , id⟷ , ⟪ Enum (t ×ᵤ (𝟙/ t)) [ Find' {t ×ᵤ (𝟙/ t)} (default t {nz} , ○) ]⟫
st (x , ○) (ε {t} {nz}) with 𝕌dec t (default t {nz}) x
st (x , ○) (ε {t} {nz}) | yes _ = _ , id⟷ , ⟪ Enum _ [ Find' tt ]⟫
st (x , ○) (ε {t} {nz}) | no  _ = _ , (ε {t} {nz}) , ⟪ Enum (t ×ᵤ (𝟙/ t)) [ Find' {t ×ᵤ (𝟙/ t)} (x , ○) ]⟫
st a id⟷                                    = _ , id⟷ , ⟪ Enum _ [ Find' a ]⟫
st a (id⟷ ⊚ c)                              = _ , c , ⟪ Enum _ [ Find' a ]⟫
st a (c₁ ⊚ c₂)                              = let _ , c , st' = st a c₁ in
                                              _ , c ⊚ c₂ , st'
st (inj₁ x) (_⊕_ {t₁} {t₂} {_} {t₄} id⟷ c₂) = _ , id⟷ , ⟪ Enum _ [ Find' {_ +ᵤ t₄} (inj₁ x) ]⟫
st (inj₁ x) (_⊕_ {t₁} {t₂} c₁ c₂)           = let _ , c , st' = st x c₁ in
                                              _ , c ⊕ c₂ , ⟪ Enum _ [ Find' {_ +ᵤ t₂} (inj₁ $ resolve st') ]⟫
st (inj₂ y) (_⊕_ {t₁} {t₂} {t₃} {_} c₁ id⟷) = _ , id⟷ , ⟪ Enum _ [ Find' {t₃ +ᵤ _} (inj₂ y) ]⟫
st (inj₂ y) (_⊕_ {t₁} c₁ c₂)                = let _ , c , st' = st y c₂ in
                                              _ , c₁ ⊕ c , ⟪ Enum _ [ Find' {t₁ +ᵤ _} (inj₂ $ resolve st') ]⟫
st (x , y) (id⟷ ⊗ id⟷)                      = _ , id⟷ , ⟪ Enum _ [ Find' (x , y) ]⟫
st (x , y) (id⟷ ⊗ c₂)                       = let _ , c , st' = st y c₂ in
                                               _ , id⟷ ⊗ c , ⟪ Enum _ [ Find' (x , resolve st') ]⟫
st (x , y) (c₁ ⊗ c₂)                        = let _ , c , st' = st x c₁ in
                                              _ , c ⊗ c₂ , ⟪ Enum _ [ Find' (resolve st' , y) ]⟫

step : {A B : 𝕌} (c : A ⟷ B) → State A → Σ[ C ∈ 𝕌 ] (C ⟷ B × State C)
step c ⟪ v [ i ]⟫ = st (lookup v i) c

data State' : Set where
  ⟪_∥_[_]⟫ : {A B : 𝕌} → A ⟷ B → Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State'

step' : State' → State'
step' ⟪ c ∥ v [ i ]⟫ with step c ⟪ v [ i ]⟫
step' ⟪ c ∥ v [ i ]⟫ | _ , c' , ⟪ v' [ i' ]⟫ = ⟪ c' ∥ v' [ i' ]⟫

run : (n : ℕ) → State' → Vec State' (suc n)
run 0 st = [ st ]
run (suc n) st with run n st
... | sts with last sts
... | ⟪ cx ∥ vx [ ix ]⟫ rewrite +-comm 1 (suc n) = sts ++ [ step' ⟪ cx ∥ vx [ ix ]⟫ ]

𝟚 : 𝕌
𝟚 = 𝟙 +ᵤ 𝟙

𝔽 𝕋 : ⟦ 𝟚 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

xorr xorl : 𝟚 ×ᵤ 𝟚 ⟷ 𝟚 ×ᵤ 𝟚
xorr = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ swap₊)) ⊚ factor
xorl = distl ⊚ (id⟷ ⊕ (swap₊ ⊗ id⟷)) ⊚ factorl


𝟚≠0 : ¬ (∣ 𝟚 ∣ ≡ 0)
𝟚≠0 ()

η𝟚 : 𝟙 ⟷ 𝟚 ×ᵤ (𝟙/ 𝟚)
η𝟚 = η {t≠0 = 𝟚≠0}

ε𝟚 : 𝟚 ×ᵤ (𝟙/ 𝟚) ⟷ 𝟙
ε𝟚 = ε {t≠0 = 𝟚≠0}

--   ─────┬────⊕───  ───────
--        |    |   ⨉
--     ┌──⊕────┴───  ───┐
--     └────────────────┘
id' : 𝟚 ⟷ 𝟚
id' = uniti⋆r ⊚ (id⟷ ⊗ η𝟚) ⊚ assocl⋆ ⊚
      ((xorr ⊚ xorl ⊚ swap⋆) ⊗ id⟷) ⊚
      assocr⋆ ⊚ (id⟷ ⊗ ε𝟚) ⊚ unite⋆r

ex₁ : Vec State' 33
ex₁ = run 32 ⟪ id' ∥ Enum 𝟚 [ Fin.fromℕ 1 ]⟫

