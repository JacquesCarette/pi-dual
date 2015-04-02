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

open import Equiv
open import TypeEquiv

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

-- A large number of lemmas below should be in Data.Sum.Properties
-- rather than here.  But they are developped here as needed, and
-- will be moved later.
map⊎idid≡id : {A B : Set} → (x : A ⊎ B) → map⊎ F.id F.id x P.≡ x
map⊎idid≡id (inj₁ x) = P.refl
map⊎idid≡id (inj₂ y) = P.refl

map⊎-∘ : {A B C D E F : Set} → {f : A → C} {g : B → D} {h : C → E} {i : D → F} →
  ∀ x → map⊎ (h F.∘ f) (i F.∘ g) x P.≡ map⊎ h i (map⊎ f g x)
map⊎-∘ (inj₁ x) = P.refl
map⊎-∘ (inj₂ y) = P.refl

map⊎-resp-≡ : {A B C D : Set} → {f₀ g₀ : A → B} {f₁ g₁ : C → D} →
  {e₁ : f₀ ∼ g₀} → {e₂ : f₁ ∼ g₁} →  
  (x : A ⊎ C) → map⊎ f₀ f₁ x P.≡ map⊎ g₀ g₁ x
map⊎-resp-≡ {e₁ = f₀~g₀} (inj₁ x) = P.cong inj₁ (f₀~g₀ x)
map⊎-resp-≡ {e₂ = f₁~g₁} (inj₂ y) = P.cong inj₂ (f₁~g₁ y)

unite₊∘[id,f]≡f∘unite₊ : {A B : Set} {f : A → B} →
  (x : ⊥ ⊎ A) → unite₊ (map⊎ F.id f x) P.≡ f (unite₊ x)
unite₊∘[id,f]≡f∘unite₊ (inj₁ ())
unite₊∘[id,f]≡f∘unite₊ (inj₂ y) = P.refl

unite₊′∘[id,f]≡f∘unite₊′ : {A B : Set} {f : A → B} →
  (x : A ⊎ ⊥) → unite₊′ (map⊎ f F.id x) P.≡ f (unite₊′ x)
unite₊′∘[id,f]≡f∘unite₊′ (inj₁ x) = P.refl
unite₊′∘[id,f]≡f∘unite₊′ (inj₂ ())

inj₂∘unite₊~id : {A : Set} → (x : ⊥ ⊎ A) → inj₂ (unite₊ x) P.≡ x
inj₂∘unite₊~id (inj₁ ())
inj₂∘unite₊~id (inj₂ y) = P.refl

f∘unite₊′≡unite₊′∘[f,id] : {A B : Set} {f : A → B} →
  (x : A ⊎ ⊥) → f (unite₊′ x) P.≡ unite₊′ (map⊎ f F.id x)
f∘unite₊′≡unite₊′∘[f,id] (inj₁ x) = P.refl
f∘unite₊′≡unite₊′∘[f,id] (inj₂ ())

inj₁∘unite₊′~id : {A : Set} → (x : A ⊎ ⊥) → inj₁ (unite₊′ x) P.≡ x
inj₁∘unite₊′~id (inj₁ x) = P.refl
inj₁∘unite₊′~id (inj₂ ())

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

assocr₊∘[[,],] : {A B C D E F : Set} → {f₀ : A → D} {f₁ : B → E} {f₂ : C → F} →
  (x : (A ⊎ B) ⊎ C) →
    assocr₊ (map⊎ (map⊎ f₀ f₁) f₂ x) P.≡ map⊎ f₀ (map⊎ f₁ f₂) (assocr₊ x)
assocr₊∘[[,],] (inj₁ (inj₁ x)) = P.refl
assocr₊∘[[,],] (inj₁ (inj₂ y)) = P.refl
assocr₊∘[[,],] (inj₂ y) = P.refl

[[,],]∘assocl₊ : {A B C D E F : Set} → {f₀ : A → D} {f₁ : B → E} {f₂ : C → F} →
  (x : A ⊎ (B ⊎ C)) →
     map⊎ (map⊎ f₀ f₁) f₂ (assocl₊ x) P.≡ assocl₊ (map⊎ f₀ (map⊎ f₁ f₂) x)
[[,],]∘assocl₊ (inj₁ x) = P.refl
[[,],]∘assocl₊ (inj₂ (inj₁ x)) = P.refl
[[,],]∘assocl₊ (inj₂ (inj₂ y)) = P.refl

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

triangle⊎-right : {A B : Set} → (x : (A ⊎ ⊥) ⊎ B) → map⊎ unite₊′ F.id x P.≡ map⊎ F.id unite₊ (assocr₊ x)
triangle⊎-right (inj₁ (inj₁ x)) = P.refl
triangle⊎-right (inj₁ (inj₂ ()))
triangle⊎-right (inj₂ y) = P.refl

-- note how C is completely arbitrary here (and not ⊥ like in the above)
triangle⊎-left : {A B C : Set} → (x : A ⊎ B) → map⊎ (inj₁ {B = C}) F.id x P.≡ assocl₊ (map⊎ F.id inj₂ x)
triangle⊎-left (inj₁ x) = P.refl
triangle⊎-left (inj₂ y) = P.refl

pentagon⊎-right : {A B C D : Set} → (x : ((A ⊎ B) ⊎ C) ⊎ D) →
  assocr₊ (assocr₊ x) P.≡ map⊎ F.id assocr₊ (assocr₊ (map⊎ assocr₊ F.id x))
pentagon⊎-right (inj₁ (inj₁ (inj₁ x))) = P.refl
pentagon⊎-right (inj₁ (inj₁ (inj₂ y))) = P.refl
pentagon⊎-right (inj₁ (inj₂ y)) = P.refl
pentagon⊎-right (inj₂ y) = P.refl

pentagon⊎-left : {A B C D : Set} → (x : A ⊎ B ⊎ C ⊎ D) →
  assocl₊ (assocl₊ x) P.≡ map⊎ assocl₊ F.id (assocl₊ (map⊎ F.id assocl₊ x))
pentagon⊎-left (inj₁ x) = P.refl
pentagon⊎-left (inj₂ (inj₁ x)) = P.refl
pentagon⊎-left (inj₂ (inj₂ (inj₁ x))) = P.refl
pentagon⊎-left (inj₂ (inj₂ (inj₂ y))) = P.refl

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

swap₊∘[f,g]≡[g,f]∘swap₊ : {A B C D : Set} {f : A → C} {g : B → D} →
  (x : A ⊎ B) → swap₊ (map⊎ f g x) P.≡ map⊎ g f (swap₊ x)
swap₊∘[f,g]≡[g,f]∘swap₊ (inj₁ x) = P.refl
swap₊∘[f,g]≡[g,f]∘swap₊ (inj₂ y) = P.refl

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
  ; iso = λ X → record 
    { isoˡ = eq swapswap₊ swapswap₊ 
    ; isoʳ = eq swapswap₊ swapswap₊ 
    }
  }

BM⊎ : Braided CPM⊎
BM⊎ = record 
  { braid = x⊎y≈y⊎x 
  ; hexagon₁ = eq (λ x → {!!}) (λ x → {!!}) 
  ; hexagon₂ = eq {!!} {!!} 
  }

BM× : Braided CPM×
BM× = record 
  { braid = {!!} 
  ; hexagon₁ = {!!} 
  ; hexagon₂ = {!!} 
  }
