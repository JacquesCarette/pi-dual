
\newcommand{\Preamble}{%
\begin{code}
{-# OPTIONS --without-K #-}
module _ where
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Function
open import Relation.Binary.PropositionalEquality
  renaming ([_] to R[_])
open import Relation.Binary.Core
open import Relation.Nullary

infix  70 _×ᵤ_
infix  60 _+ᵤ_
infix  40 _↔_
infixr 50 _⊚_

data ◯ : Set where
  ○ : ◯

-- Pi

mutual
\end{code}}
\newcommand{\Udef}{%
\begin{code}
  data 𝕌 : Set where
    𝟘     : 𝕌
    𝟙     : 𝕌
    _+ᵤ_  : 𝕌 → 𝕌 → 𝕌
    _×ᵤ_  : 𝕌 → 𝕌 → 𝕌
    𝟙/_   : 𝕌 → 𝕌
\end{code}}
\newcommand{\CodeA}{%
\begin{code}
  ⟦_⟧ : 𝕌 → Set
  ⟦ 𝟘 ⟧ = ⊥
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ 𝟙/ t ⟧ = ◯

  data _↔_ : 𝕌 → 𝕌 → Set where
    unite₊l : {t : 𝕌} → 𝟘 +ᵤ t ↔ t
    uniti₊l : {t : 𝕌} → t ↔ 𝟘 +ᵤ t
    unite₊r : {t : 𝕌} → t +ᵤ 𝟘 ↔ t
    uniti₊r : {t : 𝕌} → t ↔ t +ᵤ 𝟘
    swap₊   : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ↔ t₂ +ᵤ t₁
    assocl₊ : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ↔ (t₁ +ᵤ t₂) +ᵤ t₃
    assocr₊ : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ↔ t₁ +ᵤ (t₂ +ᵤ t₃)
    unite⋆l : {t : 𝕌} → 𝟙 ×ᵤ t ↔ t
    uniti⋆l : {t : 𝕌} → t ↔ 𝟙 ×ᵤ t
    unite⋆r : {t : 𝕌} → t ×ᵤ 𝟙 ↔ t
    uniti⋆r : {t : 𝕌} → t ↔ t ×ᵤ 𝟙
    swap⋆   : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ↔ t₂ ×ᵤ t₁
    assocl⋆ : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ ×ᵤ t₂) ×ᵤ t₃
    assocr⋆ : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ↔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
    absorbr : {t : 𝕌} → 𝟘 ×ᵤ t ↔ 𝟘
    absorbl : {t : 𝕌} → t ×ᵤ 𝟘 ↔ 𝟘
    factorzr : {t : 𝕌} → 𝟘 ↔ t ×ᵤ 𝟘
    factorzl : {t : 𝕌} → 𝟘 ↔ 𝟘 ×ᵤ t
    dist    : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ↔ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
    factor  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ +ᵤ t₂) ×ᵤ t₃
    distl   : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ↔ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
    factorl : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ↔ t₁ ×ᵤ (t₂ +ᵤ t₃)
    id↔     : {t : 𝕌} → t ↔ t
    _⊚_     : {t₁ t₂ t₃ : 𝕌} → (t₁ ↔ t₂) → (t₂ ↔ t₃) → (t₁ ↔ t₃)
    _⊕_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ +ᵤ t₂ ↔ t₃ +ᵤ t₄)
    _⊗_     : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ ×ᵤ t₂ ↔ t₃ ×ᵤ t₄)
\end{code}}
\newcommand{\EtaEpsilon}{%
\begin{code}
    η : {t : 𝕌} {t≠0 : ¬ card t ≡ 0} → 𝟙 ↔ t ×ᵤ (𝟙/ t)
    ε : {t : 𝕌} {t≠0 : ¬ card t ≡ 0} → t ×ᵤ (𝟙/ t) ↔ 𝟙
\end{code}}
\newcommand{\CodeB}{%
\begin{code}
-- Number of points in type
  card : (t : 𝕌) → ℕ
  card 𝟘 = 0
  card 𝟙 = 1
  card (t₁ +ᵤ t₂) = card t₁ + card t₂
  card (t₁ ×ᵤ t₂) = card t₁ * card t₂
  card 𝟙/● = 1

-- If number of points is zero then it is impossible to find a value
-- of the type
0empty : {t : 𝕌} → card t ≡ 0 → (v : ⟦ t ⟧) → ⊥
0empty {𝟘} _ ()
0empty {𝟙} () tt
0empty {t₁ +ᵤ t₂} s (inj₁ v₁)
  with card t₁ | card t₂ | inspect card t₁
0empty {t₁ +ᵤ t₂} refl (inj₁ v₁) | 0 | 0 | R[ s₁ ] =
  0empty {t₁} s₁ v₁
0empty {t₁ +ᵤ t₂} s (inj₂ v₂)
  with card t₁ | card t₂ | inspect card t₂
0empty {t₁ +ᵤ t₂} refl (inj₂ v₂) | ℕ.zero | ℕ.zero | R[ s₂ ] =
  0empty {t₂} s₂ v₂
0empty {t₁ ×ᵤ t₂} s (v₁ , v₂)
  with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
0empty {t₁ ×ᵤ t₂} refl (v₁ , v₂) | ℕ.zero | _ | R[ s₁ ] | _ =
  0empty {t₁} s₁ v₁
0empty {t₁ ×ᵤ t₂} s (v₁ , v₂) | ℕ.suc n₁ | ℕ.zero | R[ s₁ ] | R[ s₂ ] =
  0empty {t₂} s₂ v₂
0empty {𝟙/ t} () f

default : (t : 𝕌) → {t≠0 : ¬ card t ≡ 0} → ⟦ t ⟧
default 𝟘 {t≠0} = ⊥-elim (t≠0 refl) 
default 𝟙 = tt
default (t₁ +ᵤ t₂) {p≠0} with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
... | 0 | 0 | R[ s₁ ] | R[ s₂ ] = ⊥-elim (p≠0 refl)
... | 0 | suc n | R[ s₁ ] | R[ s₂ ] =
  inj₂ (default t₂ {λ t2≡0 → ⊥-elim (p≠0 (trans (sym s₂) t2≡0))})
... | suc m | 0 | R[ s₁ ] | R[ s₂ ] =
  inj₁ (default t₁ {λ t1≡0 →
    ⊥-elim (p≠0 ((trans (sym (trans s₁ (sym (+-identityʳ (suc m))))) t1≡0)))})
... | suc m | suc n | R[ s₁ ] | R[ s₂ ] =
  inj₁ (default t₁ {λ t1≡0 → ⊥-elim (1+n≢0 (trans (sym s₁) t1≡0))})
default (t₁ ×ᵤ t₂) {p≠0} with card t₁ | card t₂ | inspect card t₁ | inspect card t₂
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
\end{code}}
\newcommand{\dyninterp}{%
\begin{code}
interp : {t₁ t₂ : 𝕌} → (t₁ ↔ t₂) → ⟦ t₁ ⟧ → Maybe ⟦ t₂ ⟧
\end{code}}
\newcommand{\PFDCONE}{%
\begin{code}
interp unite₊l (inj₁ ())
interp unite₊l (inj₂ v) = just v
interp uniti₊l v = just (inj₂ v)
interp unite₊r (inj₁ v) = just v
interp unite₊r (inj₂ ())
interp uniti₊r v = just (inj₁ v)
interp swap₊ (inj₁ v) = just (inj₂ v)
interp swap₊ (inj₂ v) = just (inj₁ v)
interp assocl₊ (inj₁ v) = just (inj₁ (inj₁ v))
interp assocl₊ (inj₂ (inj₁ v)) = just (inj₁ (inj₂ v))
interp assocl₊ (inj₂ (inj₂ v)) = just (inj₂ v)
interp assocr₊ (inj₁ (inj₁ v)) = just (inj₁ v)
interp assocr₊ (inj₁ (inj₂ v)) = just (inj₂ (inj₁ v))
interp assocr₊ (inj₂ v) = just (inj₂ (inj₂ v))
interp unite⋆l v = just (proj₂ v)
interp uniti⋆l v = just (tt , v)
interp unite⋆r v = just (proj₁ v)
interp uniti⋆r v = just (v , tt)
interp swap⋆ (v₁ , v₂) = just (v₂ , v₁)
interp assocl⋆ (v₁ , v₂ , v₃) = just ((v₁ , v₂) , v₃)
interp assocr⋆ ((v₁ , v₂) , v₃) = just (v₁ , v₂ , v₃)
interp absorbr (() , v)
interp absorbl (v , ())
interp factorzr ()
interp factorzl ()
interp dist (inj₁ v₁ , v₃) = just (inj₁ (v₁ , v₃))
interp dist (inj₂ v₂ , v₃) = just (inj₂ (v₂ , v₃))
interp factor (inj₁ (v₁ , v₃)) = just (inj₁ v₁ , v₃)
interp factor (inj₂ (v₂ , v₃)) = just (inj₂ v₂ , v₃)
interp distl (v₁ , inj₁ v₂) = just (inj₁ (v₁ , v₂))
interp distl (v₁ , inj₂ v₃) = just (inj₂ (v₁ , v₃))
interp factorl (inj₁ (v₁ , v₂)) = just (v₁ , inj₁ v₂)
interp factorl (inj₂ (v₁ , v₃)) = just (v₁ , inj₂ v₃)
interp id↔ v = just v
interp (c₁ ⊚ c₂) v = interp c₁ v >>= interp c₂
interp (c₁ ⊕ c₂) (inj₁ v) = interp c₁ v >>= just ∘ inj₁
interp (c₁ ⊕ c₂) (inj₂ v) = interp c₂ v >>= just ∘ inj₂
interp (c₁ ⊗ c₂) (v₁ , v₂) = interp c₁ v₁ >>= (λ v₁' → interp c₂ v₂ >>= λ v₂' → just (v₁' , v₂'))
\end{code}}
\newcommand{\EtaEpsilonEval}{%
\begin{code}
interp (η {t} {t≠0}) tt = just (default t {t≠0} , ○)
interp (ε {t} {t≠0}) (v' , ○) with 𝕌dec t (default t {t≠0}) v'
... | yes _ = just tt
... | no _ = nothing
\end{code}}  
\newcommand{\CodeC}{%
\begin{code}
--- Examples

𝟚 : 𝕌
𝟚 = 𝟙 +ᵤ 𝟙

𝔽 𝕋 : ⟦ 𝟚 ⟧
𝔽 = inj₁ tt
𝕋 = inj₂ tt

xorr xorl : 𝟚 ×ᵤ 𝟚 ↔ 𝟚 ×ᵤ 𝟚
xorr = dist ⊚ (id↔ ⊕ (id↔ ⊗ swap₊)) ⊚ factor
xorl = distl ⊚ (id↔ ⊕ (swap₊ ⊗ id↔)) ⊚ factorl


𝟚≠0 : ¬ (card 𝟚 ≡ 0)
𝟚≠0 ()

η𝟚 : 𝟙 ↔ 𝟚 ×ᵤ (𝟙/ 𝟚)
η𝟚 = η {t≠0 = 𝟚≠0}

ε𝟚 : 𝟚 ×ᵤ (𝟙/ 𝟚) ↔ 𝟙
ε𝟚 = ε {t≠0 = 𝟚≠0}
\end{code}}
\newcommand{\EtaEpsilonExamples}{%

\tikzset{every picture/.style={line width=0.75pt}} %set default line width to 0.75pt        

\begin{tikzpicture}[x=0.75pt,y=0.75pt,scale=0.8, yscale=-1]
%uncomment if require: \path (0,300); %set diagram left start at 0, and has height of 300

%Straight Lines [id:da05403550183378514] 
\draw    (10,20) -- (190,20) ;


%Shape: Circle [id:dp8701819096818126] 
\draw   (138.75,21.25) .. controls (138.75,15.04) and (143.79,10) .. (150,10) .. controls (156.21,10) and (161.25,15.04) .. (161.25,21.25) .. controls (161.25,27.46) and (156.21,32.5) .. (150,32.5) .. controls (143.79,32.5) and (138.75,27.46) .. (138.75,21.25) -- cycle ;
%Straight Lines [id:da3470499764023487] 
\draw    (150,80) -- (150,10) ;


%Straight Lines [id:da9303973632982276] 
\draw    (40,80) -- (190,80) ;


%Shape: Circle [id:dp03942567054970991] 
\draw   (48.75,81.33) .. controls (48.75,75.12) and (53.79,70.08) .. (60,70.08) .. controls (66.21,70.08) and (71.25,75.12) .. (71.25,81.33) .. controls (71.25,87.55) and (66.21,92.58) .. (60,92.58) .. controls (53.79,92.58) and (48.75,87.55) .. (48.75,81.33) -- cycle ;
%Straight Lines [id:da08295302434157614] 
\draw    (60,92.58) -- (60,20) ;


%Shape: Arc [id:dp2904677718814479] 
\draw  [draw opacity=0] (38.49,110.13) .. controls (28.3,109.22) and (20.27,102.7) .. (20.15,94.89) .. controls (20.02,86.57) and (28.89,79.93) .. (40,80) -- (40.38,95.12) -- cycle ; \draw   (38.49,110.13) .. controls (28.3,109.22) and (20.27,102.7) .. (20.15,94.89) .. controls (20.02,86.57) and (28.89,79.93) .. (40,80) ;
%Straight Lines [id:da32172184710713914] 
\draw    (38.49,110.13) -- (250,110) ;


%Shape: Arc [id:dp8398868072937593] 
\draw  [draw opacity=0] (248.77,109.75) .. controls (262.77,109.82) and (274.32,103.33) .. (274.64,95.17) .. controls (274.95,87.02) and (263.95,80.28) .. (250,80) -- (249.05,94.87) -- cycle ; \draw   (248.77,109.75) .. controls (262.77,109.82) and (274.32,103.33) .. (274.64,95.17) .. controls (274.95,87.02) and (263.95,80.28) .. (250,80) ;
%Straight Lines [id:da5220296307776525] 
\draw    (190,20) -- (250,80) ;


%Straight Lines [id:da320377013704656] 
\draw    (190,80) -- (250,20) ;


%Straight Lines [id:da8933694171914682] 
\draw    (250,20) -- (308,20) ;

\end{tikzpicture}

\begin{code}
id' : 𝟚 ↔ 𝟚
id' = uniti⋆r ⊚ (id↔ ⊗ η𝟚) ⊚ assocl⋆ ⊚
      ((xorr ⊚ xorl ⊚ swap⋆) ⊗ id↔) ⊚
      assocr⋆ ⊚ (id↔ ⊗ ε𝟚) ⊚ unite⋆r
\end{code}
\begin{tikzpicture}[x=0.75pt,y=0.75pt,scale=0.8, yscale=-1]
%uncomment if require: \path (0,300); %set diagram left start at 0, and has height of 300

%Straight Lines [id:da9303973632982276] 
\draw    (40,80) -- (190,80) ;


%Shape: Arc [id:dp2904677718814479] 
\draw  [draw opacity=0] (38.49,110.13) .. controls (28.3,109.22) and (20.27,102.7) .. (20.15,94.89) .. controls (20.02,86.57) and (28.89,79.93) .. (40,80) -- (40.38,95.12) -- cycle ; \draw   (38.49,110.13) .. controls (28.3,109.22) and (20.27,102.7) .. (20.15,94.89) .. controls (20.02,86.57) and (28.89,79.93) .. (40,80) ;
%Straight Lines [id:da32172184710713914] 
\draw    (38.49,110.13) -- (250,110) ;


%Shape: Arc [id:dp8398868072937593] 
\draw  [draw opacity=0] (248.77,109.75) .. controls (262.77,109.82) and (274.32,103.33) .. (274.64,95.17) .. controls (274.95,87.02) and (263.95,80.28) .. (250,80) -- (249.05,94.87) -- cycle ; \draw   (248.77,109.75) .. controls (262.77,109.82) and (274.32,103.33) .. (274.64,95.17) .. controls (274.95,87.02) and (263.95,80.28) .. (250,80) ;
%Straight Lines [id:da7474565765110813] 
\draw    (40.09,30.3) -- (190.09,30.3) ;


%Shape: Arc [id:dp593084478238281] 
\draw  [draw opacity=0] (38.58,60.43) .. controls (28.39,59.52) and (20.36,53) .. (20.23,45.19) .. controls (20.11,36.87) and (28.98,30.23) .. (40.09,30.3) -- (40.47,45.42) -- cycle ; \draw   (38.58,60.43) .. controls (28.39,59.52) and (20.36,53) .. (20.23,45.19) .. controls (20.11,36.87) and (28.98,30.23) .. (40.09,30.3) ;
%Straight Lines [id:da5682447818267274] 
\draw    (38.58,60.43) -- (250.09,60.3) ;


%Shape: Arc [id:dp8936250935910023] 
\draw  [draw opacity=0] (248.86,60.05) .. controls (262.86,60.12) and (274.41,53.63) .. (274.72,45.47) .. controls (275.03,37.32) and (264.04,30.58) .. (250.09,30.3) -- (249.13,45.17) -- cycle ; \draw   (248.86,60.05) .. controls (262.86,60.12) and (274.41,53.63) .. (274.72,45.47) .. controls (275.03,37.32) and (264.04,30.58) .. (250.09,30.3) ;
%Straight Lines [id:da9423433355546923] 
\draw    (190,30) -- (250,80) ;


%Straight Lines [id:da8064437888434692] 
\draw    (190,80) -- (250.09,30.3) ;

\end{tikzpicture}
\begin{code}
switch : 𝟙 ↔ 𝟙
switch = uniti⋆r ⊚ (η𝟚 ⊗ η𝟚) ⊚ assocl⋆ ⊚
         (((swap⋆ ⊗ id↔) ⊚ assocr⋆ ⊚
         (id↔ ⊗ swap⋆) ⊚ assocl⋆ ⊚ (swap⋆ ⊗ id↔)) ⊗ id↔) ⊚ 
         assocr⋆ ⊚ (ε𝟚 ⊗ ε𝟚) ⊚ unite⋆r
\end{code}}
\newcommand{\CodeD}{%
\begin{code}

ex1 : interp id' 𝕋 ≡ just 𝕋
ex1 = refl

ex2 : interp id' 𝔽 ≡ just 𝔽
ex2 = refl

bad : 𝟚 ↔ 𝟚
bad = uniti⋆r ⊚ (id↔ ⊗ η𝟚) ⊚ assocl⋆ ⊚
      ((xorr ⊚ swap⋆) ⊗ id↔) ⊚
      assocr⋆ ⊚ (id↔ ⊗ ε𝟚) ⊚ unite⋆r

ex3 : interp bad 𝔽 ≡ just 𝔽
ex3 = refl

ex4 : interp bad 𝕋 ≡ nothing
ex4 = refl

{--
shouldn't_type_check : 𝟙 ↔ 𝟙
shouldn't_type_check = η {v = 𝔽} ⊚ ε {v = 𝕋}

ex5 : interp shouldn't_type_check tt ≡ nothing
ex5 = refl

more : 𝟙 ↔ 𝟙
more = η {v = 𝔽} ⊚ (swap₊ ⊗ id↔) ⊚ ε {v = 𝕋}

ex6 : interp more tt ≡ just tt
ex6 = refl
--}
\end{code}}
