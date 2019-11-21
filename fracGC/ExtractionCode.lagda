\newcommand{\EXTRACT}{%
\begin{code}
{-# OPTIONS --safe #-}
module _ where
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
open import Relation.Nullary
open import PiPointedFrac as Pi/ hiding (𝕌; ⟦_⟧; eval)
open import PiFracDyn
\end{code}}
\newcommand{\INJU}{%
\begin{code}
Inj𝕌 : Pi/.𝕌 → 𝕌
Inj𝕌 𝟘 = 𝟘
Inj𝕌 𝟙 = 𝟙
Inj𝕌 (t₁ +ᵤ t₂) = Inj𝕌 t₁ +ᵤ Inj𝕌 t₂
Inj𝕌 (t₁ ×ᵤ t₂) = Inj𝕌 t₁ ×ᵤ Inj𝕌 t₂

Inj⟦𝕌⟧ : {t : Pi/.𝕌} → Pi/.⟦ t ⟧ → ⟦ Inj𝕌 t ⟧
Inj⟦𝕌⟧ {𝟙} tt = tt
Inj⟦𝕌⟧ {t₁ +ᵤ t₂} (inj₁ x) = inj₁ (Inj⟦𝕌⟧ x)
Inj⟦𝕌⟧ {t₁ +ᵤ t₂} (inj₂ y) = inj₂ (Inj⟦𝕌⟧ y)
Inj⟦𝕌⟧ {t₁ ×ᵤ t₂} (x , y) = Inj⟦𝕌⟧ x , Inj⟦𝕌⟧ y
\end{code}}
\newcommand{\INJcomb}{%
\begin{code}
Inj⟷ : ∀ {t₁ t₂} → t₁ ⟷ t₂ → Inj𝕌 t₁ ↔ Inj𝕌 t₂
\end{code}
\begin{code}[hide]
Inj⟷ unite₊l = unite₊l
Inj⟷ uniti₊l = uniti₊l
Inj⟷ unite₊r = unite₊r
Inj⟷ uniti₊r = uniti₊r
Inj⟷ swap₊ = swap₊
Inj⟷ assocl₊ = assocl₊
Inj⟷ assocr₊ = assocr₊
Inj⟷ unite⋆l = unite⋆l
Inj⟷ uniti⋆l = uniti⋆l
Inj⟷ unite⋆r = unite⋆r
Inj⟷ uniti⋆r = uniti⋆r
Inj⟷ swap⋆ = swap⋆
Inj⟷ assocl⋆ = assocl⋆
Inj⟷ assocr⋆ = assocr⋆
Inj⟷ absorbr = absorbr
Inj⟷ absorbl = absorbl
Inj⟷ factorzr = factorzr
Inj⟷ factorzl = factorzl
Inj⟷ dist = dist
Inj⟷ factor = factor
Inj⟷ distl = distl
Inj⟷ factorl = factorl
Inj⟷ id⟷ = id↔
Inj⟷ (c₁ ⊚ c₂) = Inj⟷ c₁ ⊚ Inj⟷ c₂
Inj⟷ (c₁ ⊕ c₂) = Inj⟷ c₁ ⊕ Inj⟷ c₂
Inj⟷ (c₁ ⊗ c₂) = Inj⟷ c₁ ⊗ Inj⟷ c₂
\end{code}}
\newcommand{\INJUeq}{%
\begin{code}
Inj𝕌≡ : (t : Pi/.𝕌) → Pi/.⟦ t ⟧ ≡ ⟦ Inj𝕌 t ⟧
\end{code}
\begin{code}[hide]
Inj𝕌≡ 𝟘 = refl
Inj𝕌≡ 𝟙 = refl
Inj𝕌≡ (t₁ +ᵤ t₂) rewrite (Inj𝕌≡ t₁) | (Inj𝕌≡ t₂) = refl
Inj𝕌≡ (t₁ ×ᵤ t₂) rewrite (Inj𝕌≡ t₁) | (Inj𝕌≡ t₂) = refl
\end{code}}
\newcommand{\INJVeq}{%
\begin{code}
Inj⟦𝕌⟧≅ : {t : Pi/.𝕌} (x : Pi/.⟦ t ⟧) → x ≅ Inj⟦𝕌⟧ x
\end{code}
\begin{code}[hide]
Inj⟦𝕌⟧≅ {𝟙} tt = refl
Inj⟦𝕌⟧≅ {t₁ +ᵤ t₂} (inj₁ x) = inj1 (Inj𝕌≡ t₂) (Inj⟦𝕌⟧≅ x)
  where
    inj1 : {A B A' B' : Set} {x : A} {x' : A'}
         → B ≡ B' → x ≅ x'
         → inj₁ {B = B} x ≅ inj₁ {B = B'} x'
    inj1 refl refl = refl
Inj⟦𝕌⟧≅ {t₁ +ᵤ t₂} (inj₂ y) = inj2 (Inj𝕌≡ t₁) (Inj⟦𝕌⟧≅ y)
  where
    inj2 : {A B A' B' : Set} {y : B} {y' : B'}
         → A ≡ A' → y ≅ y'
         → inj₂ {A = A} y ≅ inj₂ {A = A'} y'
    inj2 refl refl = refl
Inj⟦𝕌⟧≅ {t₁ ×ᵤ t₂} (x , y) = ⦅ Inj⟦𝕌⟧≅ x , Inj⟦𝕌⟧≅ y ⦆
  where
    ⦅_,_⦆ : {A B A' B' : Set} {x : A} {y : B} {x' : A'} {y' : B'}
         → x ≅ x' → y ≅ y'
         → (x , y) ≅ (x' , y')
    ⦅ refl , refl ⦆ = refl
\end{code}}
\newcommand{\INJEvaleq}{%
\begin{code}
Eval≡ : ∀ {t₁ t₂} {v} (c : t₁ ⟷ t₂)
      → interp (Inj⟷ c) (Inj⟦𝕌⟧ v) ≡ just (Inj⟦𝕌⟧ (Pi/.eval c v))
\end{code}
\begin{code}[hide]
Eval≡ {_} {_} {inj₂ y} unite₊l = refl
Eval≡ {_} {_} {x} uniti₊l = refl
Eval≡ {_} {_} {inj₁ x} unite₊r = refl
Eval≡ {_} {_} {x} uniti₊r = refl
Eval≡ {_} {_} {inj₁ x} swap₊ = refl
Eval≡ {_} {_} {inj₂ y} swap₊ = refl
Eval≡ {_} {_} {inj₁ x} assocl₊ = refl
Eval≡ {_} {_} {inj₂ (inj₁ y)} assocl₊ = refl
Eval≡ {_} {_} {inj₂ (inj₂ z)} assocl₊ = refl
Eval≡ {_} {_} {inj₁ (inj₁ x)} assocr₊ = refl
Eval≡ {_} {_} {inj₁ (inj₂ y)} assocr₊ = refl
Eval≡ {_} {_} {inj₂ z} assocr₊ = refl
Eval≡ {_} {_} {x} unite⋆l = refl
Eval≡ {_} {_} {x} uniti⋆l = refl
Eval≡ {_} {_} {x} unite⋆r = refl
Eval≡ {_} {_} {x} uniti⋆r = refl
Eval≡ {_} {_} {x , y} swap⋆ = refl
Eval≡ {_} {_} {x , y , z} assocl⋆ = refl
Eval≡ {_} {_} {(x , y) , z} assocr⋆ = refl
Eval≡ {_} {_} {inj₁ x , z} dist = refl
Eval≡ {_} {_} {inj₂ y , z} dist = refl
Eval≡ {_} {_} {inj₁ (x , z)} factor = refl
Eval≡ {_} {_} {inj₂ (y , z)} factor = refl
Eval≡ {_} {_} {x , inj₁ y} distl = refl
Eval≡ {_} {_} {x , inj₂ z} distl = refl
Eval≡ {_} {_} {inj₁ (x , y)} factorl = refl
Eval≡ {_} {_} {inj₂ (x , z)} factorl = refl
Eval≡ {_} {_} {x} id⟷ = refl
Eval≡ {_} {_} {x} (c₁ ⊚ c₂) rewrite Eval≡ {v = x} c₁ = Eval≡ c₂
Eval≡ {_} {_} {inj₁ x} (c₁ ⊕ c₂) rewrite Eval≡ {v = x} c₁ = refl
Eval≡ {_} {_} {inj₂ y} (c₁ ⊕ c₂) rewrite Eval≡ {v = y} c₂ = refl
Eval≡ {_} {_} {x , y} (c₁ ⊗ c₂) rewrite Eval≡ {v = x} c₁ | Eval≡ {v = y} c₂ = refl
\end{code}}
\newcommand{\EXTU}{%
\begin{code}
Ext𝕌 : ∙𝕌 → Σ[ t ∈ 𝕌 ] ⟦ t ⟧
Ext𝕌 (t # v) = (Inj𝕌 t , Inj⟦𝕌⟧ v)
Ext𝕌 (t₁ ∙×ᵤ t₂) with Ext𝕌 t₁ | Ext𝕌 t₂
... | (t₁' , v₁') | (t₂' , v₂') = t₁' ×ᵤ t₂' , v₁' , v₂'
Ext𝕌 (t₁ ∙+ᵤl t₂) with Ext𝕌 t₁ | Ext𝕌 t₂
... | (t₁' , v₁') | (t₂' , v₂') = t₁' +ᵤ t₂' , inj₁ v₁'
Ext𝕌 (t₁ ∙+ᵤr t₂) with Ext𝕌 t₁ | Ext𝕌 t₂
... | (t₁' , v₁') | (t₂' , v₂') = t₁' +ᵤ t₂' , inj₂ v₂'
Ext𝕌 (Singᵤ T) with Ext𝕌 T
... | (t , v) = t , v
Ext𝕌 (Recipᵤ T) with Ext𝕌 T
... | (t , v) = 𝟙/ v , ○
\end{code}}
\newcommand{\EXTUComb}{%
\begin{code}
Ext∙⟶ : ∀ {t₁ t₂} → t₁ ∙⟶ t₂ → proj₁ (Ext𝕌 t₁) ↔ proj₁ (Ext𝕌 t₂)
Ext∙⟶ (∙c c) = Inj⟷ c
Ext∙⟶ ∙times# = id↔
Ext∙⟶ ∙#times = id↔
Ext∙⟶ ∙id⟷ = id↔
Ext∙⟶ (c₁ ∙⊚ c₂) = Ext∙⟶ c₁ ⊚ Ext∙⟶ c₂
Ext∙⟶ ∙unite⋆l = unite⋆l
Ext∙⟶ ∙uniti⋆l = uniti⋆l
Ext∙⟶ ∙unite⋆r = unite⋆r
Ext∙⟶ ∙uniti⋆r = uniti⋆r
Ext∙⟶ ∙swap⋆ = swap⋆
Ext∙⟶ ∙assocl⋆ = assocl⋆
Ext∙⟶ ∙assocr⋆ = assocr⋆
Ext∙⟶ (c₁ ∙⊗ c₂) = Ext∙⟶ c₁ ⊗ Ext∙⟶ c₂
Ext∙⟶ (return T) = id↔
\end{code}
\begin{code}[hide]
Ext∙⟶ (plusl T₁ T₂) = id↔
Ext∙⟶ (plusr T₁ T₂) = id↔
Ext∙⟶ (extract T) = id↔
Ext∙⟶ (coplusl T₁ T₂) = id↔
Ext∙⟶ (coplusr T₁ T₂) = id↔
\end{code}
$\;\;\;\;\vdots$
\begin{code}
Ext∙⟶ (∙Singᵤ T₁ T₂ c) = Ext∙⟶ c
Ext∙⟶ (η T) = η (proj₂ (Ext𝕌 T))
Ext∙⟶ (ε T) = ε (proj₂ (Ext𝕌 T))
\end{code}}
\newcommand{\EXTeq}{%
\begin{code}
Ext≡ : ∀ {t₁ t₂} → (c : t₁ ∙⟶ t₂)
     → let (t₁' , v₁') = Ext𝕌 t₁
           (t₂' , v₂') = Ext𝕌 t₂
       in  interp (Ext∙⟶ c) v₁' ≡ just v₂'
Ext≡ (∙c c) = Eval≡ c
Ext≡ ∙times# = refl
Ext≡ ∙#times = refl
Ext≡ ∙id⟷ = refl
Ext≡ (c₁ ∙⊚ c₂) rewrite Ext≡ c₁ | Ext≡ c₂ = refl
Ext≡ ∙unite⋆l = refl
Ext≡ ∙uniti⋆l = refl
Ext≡ ∙unite⋆r = refl
Ext≡ ∙uniti⋆r = refl
Ext≡ ∙swap⋆ = refl
Ext≡ ∙assocl⋆ = refl
Ext≡ ∙assocr⋆ = refl
Ext≡ (c₁ ∙⊗ c₂) rewrite Ext≡ c₁ | Ext≡ c₂ = refl
\end{code}
\begin{code}[hide]
Ext≡ (return T) = refl
Ext≡ (plusl T₁ T₂) = refl
Ext≡ (plusr T₁ T₂) = refl
Ext≡ (extract T) = refl
Ext≡ (coplusl T₁ T₂) = refl
Ext≡ (coplusr T₁ T₂) = refl
\end{code}
$\;\;\;\;\vdots$
\begin{code}
Ext≡ (∙Singᵤ T₁ T₂ c) rewrite Ext≡ c = refl
Ext≡ (η T) = refl
Ext≡ (ε T) with (proj₂ (Ext𝕌 T)) ≟ᵤ (proj₂ (Ext𝕌 T))
Ext≡ (ε T) | yes p = refl
Ext≡ (ε T) | no ¬p = ⊥-elim (¬p refl)
\end{code}}

