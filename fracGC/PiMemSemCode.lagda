\newcommand{\PIMEM}{% Not used
\begin{code}
{-# OPTIONS --without-K --safe #-}
module _ where

open import Function using (_∘_; _$_)
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
infix 100 !_
\end{code}}
\newcommand{\PI}{
\begin{code}
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
  swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ⟷ t₂ +ᵤ t₁
  dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ⟷ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ⟷ (t₁ +ᵤ t₂) ×ᵤ t₃
  _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ +ᵤ t₂ ⟷ t₃ +ᵤ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ×ᵤ t₂ ⟷ t₃ ×ᵤ t₄)
  -- (elided)
\end{code}
\begin{code}[hide]
  unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ⟷ t
  uniti₊l : {t : 𝕌} → t ⟷ 𝟘 +ᵤ t
  unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ⟷ t
  uniti₊r : {t : 𝕌} → t ⟷ t +ᵤ 𝟘
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
  distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ⟷ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
  factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ⟷ t₁ ×ᵤ (t₂ +ᵤ t₃)
  id⟷     : {t : 𝕌} → t ⟷ t
\end{code}}
\newcommand{\PIrev}{% Not used
\begin{code}
!_ : {A B : 𝕌} → A ⟷ B → B ⟷ A
! (c₁ ⊚ c₂) = (! c₂) ⊚ (! c₁)
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)
! swap⋆ = swap⋆
-- (elided)
\end{code}
\begin{code}[hide]
! unite₊l = uniti₊l
! uniti₊l = unite₊l
! unite₊r = uniti₊r
! uniti₊r = unite₊r
! swap₊ = swap₊
! assocl₊ = assocr₊
! assocr₊ = assocl₊
! unite⋆l = uniti⋆l
! uniti⋆l = unite⋆l
! unite⋆r = uniti⋆r
! uniti⋆r = unite⋆r
! assocl⋆ = assocr⋆
! assocr⋆ = assocl⋆
! absorbr = factorzl
! absorbl = factorzr
! factorzr = absorbl
! factorzl = absorbr
! dist = factor
! factor = dist
! distl = factorl
! factorl = distl
! id⟷ = id⟷
\end{code}}
\newcommand{\PIMEMcard}{% Not used
\begin{code}
∣_∣ : (A : 𝕌) → ℕ
∣ 𝟘 ∣ = 0
∣ 𝟙 ∣ = 1
∣ A₁ +ᵤ A₂ ∣ = ∣ A₁ ∣ + ∣ A₂ ∣
∣ A₁ ×ᵤ A₂ ∣ = ∣ A₁ ∣ * ∣ A₂ ∣
\end{code}}
\newcommand{\PIMEMvec}{% Not used
\begin{code}
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
\end{code}}
\newcommand{\PIMEMenum}{% Not used
\begin{code}
Enum : (A : 𝕌) → Vec ⟦ A ⟧ ∣ A ∣
Enum 𝟘         = []
Enum 𝟙          = tt ∷ []
Enum (A₁ +ᵤ A₂) = map inj₁ (Enum A₁) ++ map inj₂ (Enum A₂)
Enum (A₁ ×ᵤ A₂) = Vec× (Enum A₁) (Enum A₂)

Find : {A : 𝕌} (x : ⟦ A ⟧) → Σ[ i ∈ Fin ∣ A ∣ ] (x ≡ lookup (Enum A) i)
\end{code}
\begin{code}
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
\end{code}
\begin{code}
Find' : {A : 𝕌} (x : ⟦ A ⟧) → Fin ∣ A ∣
Find' = proj₁ ∘ Find
\end{code}}
\newcommand{\PIMEMcardeq}{%
\begin{code}
card= : {t₁ t₂ : 𝕌} (C : t₁ ⟷ t₂) → (∣ t₁ ∣ ≡ ∣ t₂ ∣)
\end{code}}
\newcommand{\PIMEMcardeqrest}{% Not used
\begin{code}
card=                   unite₊l   = refl
card=                   uniti₊l   = refl
card=                   unite₊r   = +-identityʳ _
card=                   uniti₊r   = sym $ +-identityʳ _
card= {t₁ +ᵤ t₂}        swap₊     = +-comm ∣ t₁ ∣ ∣ t₂ ∣
card= {t₁ +ᵤ t₂ +ᵤ t₃}  assocl₊   = sym $ +-assoc ∣ t₁ ∣ _ _
card= {(t₁ +ᵤ t₂) +ᵤ t₃} assocr₊  = +-assoc ∣ t₁ ∣ ∣ t₂ ∣ _
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
card=              id⟷       = refl
card=              (c₁ ⊚ c₂) = trans (card= c₁) (card= c₂)
card=              (c₁ ⊕ c₂) = cong₂ _+_ (card= c₁) (card= c₂)
card=              (c₁ ⊗ c₂) = cong₂ _*_ (card= c₁) (card= c₂)
\end{code}}
\newcommand{\PIMEMstate}{% Not used
\begin{code}
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
\end{code}}
\newcommand{\PIMEMstep}{%
\begin{code}
data State' : ℕ → Set where
  ⟪_∥_[_]⟫ : {A B : 𝕌} →
    A ⟷ B → Vec ⟦ A ⟧ ∣ A ∣ → Fin ∣ A ∣ → State' ∣ A ∣

step' : ∀ {n} → State' n → State' n
\end{code}
\begin{code}[hide]
step' (⟪_∥_[_]⟫ {A} {B} c v i) with step c ⟪ v [ i ]⟫
... | _ , c' , ⟪ v' [ i' ]⟫ rewrite card= (c ⊚ ! c') = ⟪ c' ∥ v' [ i' ]⟫
\end{code}}
\newcommand{\PIMEMrun}{% Not used
\begin{code}
run : (sz n : ℕ) → (st : State' sz) → Vec (State' sz) (suc n)
run sz 0 st = [ st ]
run sz (suc n) st with run sz n st
... | sts with last sts
... | ⟪_∥_[_]⟫ {A} {B} cx vx ix rewrite +-comm 1 (suc n) = sts ++ [ step' ⟪ cx ∥ vx [ ix ]⟫ ]
\end{code}}
\newcommand{\PIMEMex}{% Not used
\begin{code}[hide]
𝔹 : 𝕌
𝔹 = 𝟙 +ᵤ 𝟙

pattern 𝔽 = inj₁ tt
pattern 𝕋 = inj₂ tt
\end{code}
\begin{code}
CNOT : 𝔹 ×ᵤ 𝔹 ⟷ 𝔹 ×ᵤ 𝔹
CNOT = dist ⊚ (id⟷ ⊕ (id⟷ ⊗ swap₊)) ⊚ factor

ex₁ : Vec (State' ∣ 𝔹 ×ᵤ 𝔹 ∣) 8
ex₁ = run ∣ 𝔹 ×ᵤ 𝔹 ∣ 7 ⟪ CNOT ∥ Enum (𝔹 ×ᵤ 𝔹) [ Fin.fromℕ 3 ]⟫
\end{code}}
