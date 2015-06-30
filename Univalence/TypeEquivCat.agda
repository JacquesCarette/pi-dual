{-# OPTIONS --without-K #-}

module TypeEquivCat where

open import Level using (zero; suc)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using (Rel)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product using (_,_; proj₁; proj₂;_×_; Σ) renaming (map to map×)
open import Data.Unit
open import Data.Empty
import Function as F

open import Categories.Category
open import Categories.Groupoid
open import Categories.Monoidal
open import Categories.Monoidal.Helpers
open import Categories.Bifunctor
open import Categories.NaturalIsomorphism
open import Categories.Monoidal.Braided
open import Categories.Monoidal.Symmetric
open import Categories.RigCategory

open import Equiv
open import TypeEquiv
open import Data.Sum.Properties
open import Data.SumProd.Properties

-- see EquivSetoid for some additional justification
-- basically we need g to "pin down" the inverse, else we
-- get lots of unsolved metas.
record _≋_ {A B : Set} (eq₁ eq₂ : A ≃ B) : Set where
  constructor eq
  field
    f≡ : ∀ x → eq₁ ⋆ x P.≡ eq₂ ⋆ x
    g≡ : ∀ x → (sym≃ eq₁) ⋆ x P.≡ (sym≃ eq₂) ⋆ x
 
id≋ : ∀ {A B : Set} {x : A ≃ B} → x ≋ x
id≋ = record { f≡ = λ x → P.refl ; g≡ = λ x → P.refl }

sym≋ : ∀ {A B : Set} {x y : A ≃ B} → x ≋ y → y ≋ x
sym≋ (eq f≡ g≡) = eq (λ a → P.sym (f≡ a)) (λ b → P.sym (g≡ b))

flip≋ : {A B : Set} {x y : A ≃ B} → x ≋ y → (sym≃ x) ≋ (sym≃ y)
flip≋ (eq f≡ g≡) = eq g≡ f≡

trans≋ : ∀ {A B : Set} {x y z : A ≃ B} → x ≋ y → y ≋ z → x ≋ z
trans≋ (eq f≡ g≡) (eq h≡ i≡) =
   eq (λ a → P.trans (f≡ a) (h≡ a)) (λ b → P.trans (g≡ b) (i≡ b))

●-resp-≋ : {A B C : Set} {f h : B ≃ C} {g i : A ≃ B} → f ≋ h → g ≋ i →
  (f ● g) ≋ (h ● i)
●-resp-≋ {f = f , _} {_ , mkqinv h⁻¹ _ _} {_ , mkqinv g⁻¹ _ _} {i , _}
  (eq f≡ g≡) (eq h≡ i≡) =
  eq (λ x → P.trans (P.cong f (h≡ x)) (f≡ (i x)))
     (λ x → P.trans (P.cong g⁻¹ (g≡ x)) (i≡ (h⁻¹ x)))

-- underlying it all, it uses ∘ and ≡ 
●-assoc : {A B C D : Set} {f : A ≃ B} {g : B ≃ C} {h : C ≃ D} →
      ((h ● g) ● f) ≋ (h ● (g ● f))
●-assoc = eq (λ x → P.refl) (λ x → P.refl)

TypeEquivCat : Category (suc zero) zero zero
TypeEquivCat = record
  { Obj = Set
  ; _⇒_ = _≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = _●_
  ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → ●-assoc {A} {B} {C} {D} {f} {g} {h}
  ; identityˡ = eq (λ _ → P.refl) (λ _ → P.refl)
  ; identityʳ = eq (λ _ → P.refl) (λ _ → P.refl)
  ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ }
  ; ∘-resp-≡ = ●-resp-≋
  }

TypeEquivGroupoid : Groupoid TypeEquivCat
TypeEquivGroupoid = record 
  { _⁻¹ = sym≃ 
  ; iso = λ { {_} {_} {f , mkqinv g α β} → record
    { isoˡ = eq β β
    ; isoʳ = eq α α
    } }
  }


⊎-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
⊎-bifunctor = record
  { F₀ = λ {( x , y) → x ⊎ y}
  ; F₁ = λ {(x , y) → path⊎ x y}
  ; identity = eq map⊎idid≡id map⊎idid≡id
  ; homomorphism = eq map⊎-∘ map⊎-∘
  ; F-resp-≡ = λ { (e₁ , e₂) → eq (map⊎-resp-≡ {e₁ = f≡ e₁} {f≡ e₂}) (map⊎-resp-≡ {e₁ =  g≡ e₁} {g≡ e₂}) }
  }
  where open _≋_
  
module ⊎h = MonoidalHelperFunctors TypeEquivCat ⊎-bifunctor ⊥

0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊎x≡x = record 
  { F⇒G = record
    { η = λ X → unite₊equiv
    ; commute = λ f → eq unite₊∘[id,f]≡f∘unite₊ (λ x → P.refl) } 
  ; F⇐G = record
    { η = λ X → uniti₊equiv
    ; commute = λ f → eq (λ x → P.refl) (sym∼ unite₊∘[id,f]≡f∘unite₊) } 
  ; iso = λ X → record
    { isoˡ = eq inj₂∘unite₊~id inj₂∘unite₊~id
    ; isoʳ = eq (λ _ → P.refl) (λ _ → P.refl)
    }
  }

x⊎0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊎0≡x = record
  { F⇒G = record
    { η = λ X → unite₊′equiv
    ; commute = λ f → eq unite₊′∘[id,f]≡f∘unite₊′ (λ x → P.refl)
    }
  ; F⇐G = record
    { η = λ X → uniti₊′equiv
    ; commute = λ f → eq (λ x → P.refl) f∘unite₊′≡unite₊′∘[f,id]
    }
  ; iso = λ X → record
    { isoˡ = eq inj₁∘unite₊′~id inj₁∘unite₊′~id
    ; isoʳ = eq (λ x → P.refl) (λ x → P.refl)
    }
  }

[x⊎y]⊎z≡x⊎[y⊎z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
[x⊎y]⊎z≡x⊎[y⊎z] = record
  { F⇒G = record
    { η = λ X → assocr₊equiv
    ; commute = λ f → eq assocr₊∘[[,],] [[,],]∘assocl₊
    }
  ; F⇐G = record
    { η = λ X → assocl₊equiv
    ; commute = λ f → eq (sym∼ [[,],]∘assocl₊) (sym∼ assocr₊∘[[,],])
    }
  ; iso = λ X → record
    { isoˡ = eq (p∘!p≡id {p = assocr₊equiv}) (p∘!p≡id {p = assocr₊equiv})
    ; isoʳ = eq ((p∘!p≡id {p = assocl₊equiv})) ((p∘!p≡id {p = assocl₊equiv}))
    }
  }

CPM⊎ : Monoidal TypeEquivCat
CPM⊎ = record
  { ⊗ = ⊎-bifunctor
   ; id = ⊥
   ; identityˡ = 0⊎x≡x
   ; identityʳ = x⊎0≡x
   ; assoc = [x⊎y]⊎z≡x⊎[y⊎z]
   ; triangle = eq triangle⊎-right triangle⊎-left
   ; pentagon = eq pentagon⊎-right pentagon⊎-left
   }

-------
-- and below, we will have a lot of things which belong in
-- Data.Product.Properties.  In fact, some of them are ``free'',
-- in that β-reduction is enough.  However, it might be a good
-- idea to fully mirror all the ones needed for ⊎.


path×-resp-≡ : {A B C D : Set} → {f₀ g₀ : A → B} {f₁ g₁ : C → D} →
  {e₁ : f₀ ∼ g₀} → {e₂ : f₁ ∼ g₁} →  
  (x : A × C) → (f₀ (proj₁ x) , f₁ (proj₂ x)) P.≡
                (g₀ (proj₁ x) , g₁ (proj₂ x))
path×-resp-≡ {e₁ = f≡} {h≡} (a , c) = P.cong₂ _,_ (f≡ a) (h≡ c)

×-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
×-bifunctor = record
  { F₀ = λ {( x , y) → x × y}
  ; F₁ = λ {(x , y) → path× x y }
  ; identity = eq (λ x → P.refl) (λ x → P.refl) -- η for products gives this
  ; homomorphism = eq (λ x → P.refl) (λ x → P.refl) -- again η for products!
  ; F-resp-≡ = λ { (e₁ , e₂) → eq (path×-resp-≡ {e₁ = f≡ e₁} {f≡ e₂}) ((path×-resp-≡ {e₁ = g≡ e₁} {g≡ e₂}))}
  }
  where open _≋_

module ×h = MonoidalHelperFunctors TypeEquivCat ×-bifunctor ⊤

-- again because of η for products, lots of the following have trivial proofs
1×y≡y : NaturalIsomorphism ×h.id⊗x ×h.x
1×y≡y = record
  { F⇒G = record
    { η = λ X → unite⋆equiv
    ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl)
    }
  ; F⇐G = record
    { η = λ X → uniti⋆equiv
    ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl)
    }
  ; iso = λ X → record
    { isoˡ = eq (λ x → P.refl) (λ x → P.refl)
    ; isoʳ = eq (λ x → P.refl) (λ x → P.refl)
    }
  }

y×1≡y : NaturalIsomorphism ×h.x⊗id ×h.x
y×1≡y = record
  { F⇒G = record 
    { η = λ X → unite⋆′equiv 
    ;  commute = λ f → eq (λ x → P.refl) (λ x → P.refl) 
    }
  ; F⇐G = record 
    { η = λ X → uniti⋆′equiv 
    ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl) 
    }
  ; iso = λ X → record 
    { isoˡ = eq (λ x → P.refl) (λ x → P.refl) 
    ; isoʳ = eq (λ x → P.refl) (λ x → P.refl) 
    }
  }

[x×y]×z≡x×[y×z] : NaturalIsomorphism ×h.[x⊗y]⊗z ×h.x⊗[y⊗z]
[x×y]×z≡x×[y×z] = record
  { F⇒G = record
    { η = λ X → assocr⋆equiv
    ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl) }
  ; F⇐G = record
    { η = λ X → assocl⋆equiv
    ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl) }
  ; iso = λ X → record
    { isoˡ = eq (λ x → P.refl) (λ x → P.refl)
    ; isoʳ = eq (λ x → P.refl) (λ x → P.refl) }
  }

CPM× : Monoidal TypeEquivCat
CPM× = record
  { ⊗ = ×-bifunctor
  ; id = ⊤
  ; identityˡ = 1×y≡y
  ; identityʳ = y×1≡y
  ; assoc = [x×y]×z≡x×[y×z]
  ; triangle = eq (λ x → P.refl) (λ x → P.refl)
  ; pentagon = eq (λ x → P.refl) (λ x → P.refl)
  }

x⊎y≈y⊎x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
x⊎y≈y⊎x = record 
  { F⇒G = record 
    { η = λ X → swap₊equiv 
    ; commute = λ f → eq swap₊∘[f,g]≡[g,f]∘swap₊ (sym∼ swap₊∘[f,g]≡[g,f]∘swap₊) 
    } 
  ; F⇐G = record 
    { η = λ X → swap₊equiv 
    ; commute = λ f → eq swap₊∘[f,g]≡[g,f]∘swap₊ (sym∼ swap₊∘[f,g]≡[g,f]∘swap₊) 
    } 
  ; iso = λ X → record -- cheat by using the symmetric structure
    { isoˡ = eq swapswap₊ swapswap₊ 
    ; isoʳ = eq swapswap₊ swapswap₊ 
    }
  }

BM⊎ : Braided CPM⊎
BM⊎ = record 
  { braid = x⊎y≈y⊎x 
  ; hexagon₁ = eq hexagon⊎-right hexagon⊎-left 
  ; hexagon₂ = eq hexagon⊎-left hexagon⊎-right 
  }

x×y≈y×x : NaturalIsomorphism ×h.x⊗y ×h.y⊗x
x×y≈y×x = record
  { F⇒G = record
    { η = λ X → swap⋆equiv
    ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl)
    }
  ; F⇐G = record
    { η = λ X → swap⋆equiv
    ; commute = λ f → eq (λ x → P.refl) (λ x → P.refl)
    }
  ; iso = λ X → record -- cheat by using the symmetric structure
    { isoˡ = eq swapswap⋆ swapswap⋆
    ; isoʳ = eq swapswap⋆ swapswap⋆
    }
  }

BM× : Braided CPM×
BM× = record 
  { braid = x×y≈y×x 
  ; hexagon₁ = eq (λ x → P.refl) (λ x → P.refl) 
  ; hexagon₂ = eq (λ x → P.refl) (λ x → P.refl) 
  }

SBM⊎ : Symmetric BM⊎
SBM⊎ = record { symmetry = eq swapswap₊ swapswap₊ }

SBM× : Symmetric BM×
SBM× = record { symmetry = eq swapswap⋆ swapswap⋆ }

module r = BimonoidalHelperFunctors BM⊎ BM×

x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record
  { F⇒G = record
    { η = λ X → distlequiv
    ; commute = λ f → eq distl-commute (λ x → P.sym (factorl-commute x))
    }
  ; F⇐G = record
    { η = λ X → factorlequiv
    ; commute = λ f → eq factorl-commute (λ x → P.sym (distl-commute x))
    }
  ; iso = λ X → record { isoˡ = eq factorl∘distl factorl∘distl
                       ; isoʳ = eq distl∘factorl distl∘factorl }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record
    { η = λ X → distequiv
    ; commute = λ f → eq dist-commute (λ x → P.sym (factor-commute x))
    }
  ; F⇐G = record
    { η = λ X → factorequiv
    ; commute = λ f → eq factor-commute (λ x → P.sym (dist-commute x))
    }
  ; iso = λ X → record { isoˡ = eq factor∘dist factor∘dist
                       ; isoʳ = eq dist∘factor dist∘factor }
  }
  
x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
x⊗0≡0 = record
  { F⇒G = record
    { η = λ X → distzrequiv
    ; commute = λ f → eq (λ { (_ , ()) }) (λ { () })
    }
  ; F⇐G = record
    { η = λ X → factorzrequiv
    ; commute = λ f → eq (λ { () }) (λ { (_ , ()) })
    }
  ; iso = λ X → record
    { isoˡ = eq factorzr∘distzr factorzr∘distzr
    ; isoʳ = eq distzr∘factorzr distzr∘factorzr
    }
  }

0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
0⊗x≡0 = record
  { F⇒G = record
    { η = λ X → distzequiv
    ; commute = λ f → eq (λ { (() , _) }) (λ { () })
    }
  ; F⇐G = record
    { η = λ X → factorzequiv
    ; commute = λ f → eq (λ { () }) (λ { (() , _)})
    }
  ; iso = λ X → record
    { isoˡ = eq factorz∘distz factorz∘distz
    ; isoʳ = eq distz∘factorz distz∘factorz
    }
  }

TERig : RigCategory SBM⊎ SBM×
TERig = record
  { distribₗ = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
  ; distribᵣ = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z]
  ; annₗ = 0⊗x≡0
  ; annᵣ = x⊗0≡0
  ; laplazaI = eq distl-swap₊-lemma factorl-swap₊-lemma
  ; laplazaII = eq dist-swap⋆-lemma factor-swap⋆-lemma
  ; laplazaIV = eq dist-dist-assoc-lemma assoc-factor-factor-lemma
  ; laplazaVI = eq distl-assoc-lemma assoc-factorl-lemma
  ; laplazaX = eq distz0≡distrz0 factorz0≡factorzr0
  ; laplazaXI = eq distz0≡unite₊∘[distz,distz]∘distl factorz0≡factorl∘[factorz,factorz]∘uniti₊
  }

-- Notes from Laplaza, 72
-- All of 2, 9, 10, 15
-- one of each of {1,3}, {4,5}, {6,7}, {9, 12},{13,,14},
--   {19,20,21,22}, {23,24}
-- two-of-three of {16,17,18}
--
-- for natural isos
-- α : A × (B × C) → (A × B) × C
-- γ : A × B → B × A
-- λ : U × A → A  (so that U is 1)
-- ρ : A × U → A
-- λ* : N × A → N (so that N is 0)
-- ρ* : A × n → N
-- and ' versions for ⊕
-- as well as natural monomorphisms
-- δ : A × (B ⊎ C) → (A × B) ⊎ (A × C)
-- δ# : (A ⊎ B) × C → (A × C) ⊎ (B × C)
