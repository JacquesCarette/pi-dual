{-# OPTIONS --without-K #-}

module TypeEquivEquiv where

open import Equiv 
  using (sym∼; trans∼; sym≃; 
    _⊎≃_; id≃; _≃_; _●_; _×≃_; qinv; gg;
    β⊎₁; β⊎₂; β₁; β₂; cong∘l; cong∘r; cong₂∘)
open import TypeEquiv
  using (unite₊equiv; uniti₊equiv; unite₊′equiv; uniti₊′equiv;
    assocr₊equiv; assocl₊equiv; swap₊equiv;
    unite⋆equiv; uniti⋆equiv; unite⋆′equiv; uniti⋆′equiv;
    assocr⋆equiv; assocl⋆equiv; swap⋆equiv;
    distlequiv; factorlequiv; distequiv; factorequiv;
    distzrequiv; factorzrequiv; distzequiv; factorzequiv)
open import EquivEquiv

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; _×_; proj₁)

open import Data.Sum.Properties
  using (cong₂⊎; id⊎id∼id; ⊎∘∼∘⊎; ⊎→-resp-∼;
    unite₊-coh; uniti₊-coh; unite₊′-coh; uniti₊′-coh;
    assocr₊-wf; assocl₊-wf;
    triangle⊎-left; triangle⊎-right;
    pentagon⊎-right; pentagon⊎-left;
    swap₊-coh; hexagon⊎-right; hexagon⊎-left)

open import Data.Product.Properties
  using (id×id∼id; ×∘∼∘×; ×→-resp-∼;
    unite⋆-coh; uniti⋆-coh; unite⋆′-coh; uniti⋆′-coh;
    assocr⋆-wf; assocl⋆-wf;
    triangle⋆-left; triangle⋆-right;
    pentagon⋆-right; pentagon⋆-left;
    swap⋆-coh; hexagon×-right; hexagon×-left)

open import Data.SumProd.Properties -- TODO: list them

-- some local abbreviations to make life nicer
infixr 10 _⊙_

private
  _⊙_ = trans∼
  !_ = sym∼

-- we define all the equivalences-between-equivalences that hold
-- between type equivalences.

----
-- equivalences for the ⊎ structure

[id,id]≋id : ∀ {A B : Set} → id≃ {A = A} ⊎≃ id≃ {A = B} ≋ id≃
[id,id]≋id = eq (β⊎₁ ⊙ id⊎id∼id) (β⊎₂ ⊙ id⊎id∼id)

-- ● and ⊎≃ commute.
⊎●≋●⊎ : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  (h ● f) ⊎≃ (i ● g) ≋ (h ⊎≃ i) ● (f ⊎≃ g)
⊎●≋●⊎ = 
  eq (β⊎₁ ⊙ cong₂⊎ β₁ β₁ ⊙ ⊎∘∼∘⊎ ⊙ ! cong₂∘ β⊎₁ β⊎₁ ⊙ ! β₁)
       (β⊎₂ ⊙ cong₂⊎ β₂ β₂ ⊙ ⊎∘∼∘⊎ ⊙ ! cong₂∘ β⊎₂ β⊎₂ ⊙ ! β₂)

-- ⊎≃ respects ≋
⊎≃-respects-≋ : {A B C D : Set} {f g : A ≃ B} {h i : C ≃ D} →
  (e₁ : f ≋ g) → (e₂ : h ≋ i) → f ⊎≃ h ≋ g ⊎≃ i
⊎≃-respects-≋ (eq f~g f⁻¹~g⁻¹) (eq h~i h⁻¹~i⁻¹) =
  eq (β⊎₁ ⊙ ⊎→-resp-∼ f~g h~i ⊙ ! β⊎₁) 
       (β⊎₂ ⊙ ⊎→-resp-∼ f⁻¹~g⁻¹ h⁻¹~i⁻¹ ⊙ ! β⊎₂) 

-- Use '-nat' to signify that operation induces a
-- natural transformation, and that the induced operation
-- satisfies the naturality condition thus encoded
unite₊-nat : ∀ {A B} {f : A ≃ B} →
  unite₊equiv ● (id≃ {A = ⊥} ⊎≃ f) ≋ f ● unite₊equiv
unite₊-nat =
  eq (β₁ ⊙ cong∘l (proj₁ unite₊equiv) β⊎₁ ⊙ unite₊-coh ⊙ ! β₁) 
       (β₂ ⊙ cong∘r (gg unite₊equiv) β⊎₂ ⊙ uniti₊-coh ⊙ ! β₂)

uniti₊-nat : ∀ {A B} {f : A ≃ B} →
  uniti₊equiv ● f ≋ (id≃ {A = ⊥} ⊎≃ f) ● uniti₊equiv
uniti₊-nat =  
  eq (β₁ ⊙ ! uniti₊-coh ⊙ ! cong∘r (proj₁ uniti₊equiv) β⊎₁ ⊙ ! β₁) 
       (β₂ ⊙ ! unite₊-coh ⊙ ! cong∘l (gg uniti₊equiv) β⊎₂ ⊙ ! β₂)
{-
unite₊′-nat : ∀ {A B} {f : A ≃ B} →
  unite₊′equiv ● (f ⊎≃ id≃ {A = ⊥}) ≋ f ● unite₊′equiv
unite₊′-nat =
  eq unite₊′∘[f,id]≡f∘unite₊′ [g,id]∘uniti₊′≡uniti₊′∘g

uniti₊′-nat : ∀ {A B} {f : A ≃ B} →
  uniti₊′equiv ● f ≋ (f ⊎≃ id≃ {A = ⊥}) ● uniti₊′equiv
uniti₊′-nat = flip-sym≋ unite₊′-nat

assocr₊-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocr₊equiv ● ((f₀ ⊎≃ f₁) ⊎≃ f₂) ≋ (f₀ ⊎≃ (f₁ ⊎≃ f₂)) ● assocr₊equiv
assocr₊-nat = eq assocr₊∘[[,],] [[,],]∘assocl₊

assocl₊-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocl₊equiv ● (f₀ ⊎≃ (f₁ ⊎≃ f₂)) ≋ ((f₀ ⊎≃ f₁) ⊎≃ f₂) ● assocl₊equiv
assocl₊-nat = flip-sym≋ assocr₊-nat

-- often called 'triangle'
unite-assocr₊-coh : ∀ {A B : Set} →
  unite₊′equiv ⊎≃ id≃ ≋ (id≃ ⊎≃ unite₊equiv) ● assocr₊equiv {A} {⊥} {B}
unite-assocr₊-coh = eq triangle⊎-right triangle⊎-left

-- often called 'pentagon'
assocr₊-coh : ∀ {A B C D : Set} →
  assocr₊equiv {A} {B} {C ⊎ D} ● assocr₊equiv ≋
  (id≃ ⊎≃ assocr₊equiv) ● assocr₊equiv ● (assocr₊equiv ⊎≃ id≃)
assocr₊-coh = eq pentagon⊎-right pentagon⊎-left

swap₊-nat : {A B C D : Set} {f : A ≃ C} {g : B ≃ D} →
  swap₊equiv ● (f ⊎≃ g) ≋ (g ⊎≃ f) ● swap₊equiv
swap₊-nat = eq swap₊-coh (sym∼ swap₊-coh)

-- often called 'hexagon'
assocr₊-swap₊-coh : ∀ {A B C : Set} →
  assocr₊equiv {B} {C} {A} ● swap₊equiv ● assocr₊equiv {A} {B} {C} ≋
  id≃ ⊎≃ swap₊equiv ● assocr₊equiv ● swap₊equiv ⊎≃ id≃
assocr₊-swap₊-coh = eq hexagon⊎-right hexagon⊎-left

-- and in the opposite direction
assocl₊-swap₊-coh : ∀ {A B C : Set} →
  assocl₊equiv {A} {B} {C} ● swap₊equiv ● assocl₊equiv {B} {C} {A} ≋
  swap₊equiv ⊎≃ id≃ ● assocl₊equiv ● id≃ ⊎≃ swap₊equiv
assocl₊-swap₊-coh = eq hexagon⊎-left hexagon⊎-right

----
-- equivalences for the × structure
id×id≋id : ∀ {A B : Set} → id≃ {A = A} ×≃ id≃ {A = B} ≋ id≃
id×id≋id = eq id×id∼id id×id∼id

×●≋●× : {A B C D E F : Set} →
  {f : A ≃ C} {g : B ≃ D} {h : C ≃ E} {i : D ≃ F} →
  (h ● f) ×≃ (i ● g) ≋ (h ×≃ i) ● (f ×≃ g)
×●≋●× {f = f , qinv f′ _ _} {g , qinv g′ _ _} {h , qinv h′ _ _} {i , qinv i′ _ _} =
  eq (×∘∼∘× {f = f} {g} {h} {i}) (×∘∼∘× {f = h′} {i′} {f′} {g′})

×≃-resp-≋ :  ∀ {A B C D : Set} {f g : A ≃ B} {h i : C ≃ D} →
  (e₁ : f ≋ g) → (e₂ : h ≋ i) → f ×≃ h ≋ g ×≃ i
×≃-resp-≋ e₁ e₂ = eq (×→-resp-∼ (f≡ e₁) (f≡ e₂))
                     (×→-resp-∼ (g≡ e₁) (g≡ e₂))
  where open _≋_

unite⋆-nat : ∀ {A B} {f : A ≃ B} →
  unite⋆equiv ● (id≃ {A = ⊤} ×≃ f) ≋ f ● unite⋆equiv
unite⋆-nat = eq unite⋆-coh uniti⋆-coh

uniti⋆-nat : ∀ {A B} {f : A ≃ B} →
  uniti⋆equiv ● f ≋ (id≃ {A = ⊤} ×≃ f) ● uniti⋆equiv
uniti⋆-nat =  flip-sym≋ unite⋆-nat

unite⋆′-nat : ∀ {A B} {f : A ≃ B} →
  unite⋆′equiv ● (f ×≃ id≃ {A = ⊤}) ≋ f ● unite⋆′equiv
unite⋆′-nat = eq unite⋆′-coh uniti⋆′-coh

uniti⋆′-nat : ∀ {A B} {f : A ≃ B} →
  uniti⋆′equiv ● f ≋ (f ×≃ id≃ {A = ⊤}) ● uniti⋆′equiv
uniti⋆′-nat = flip-sym≋ unite⋆′-nat

assocr⋆-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocr⋆equiv ● ((f₀ ×≃ f₁) ×≃ f₂) ≋ (f₀ ×≃ (f₁ ×≃ f₂)) ● assocr⋆equiv
assocr⋆-nat = eq assocr⋆-wf assocl⋆-wf

assocl⋆-nat : ∀ {A B C D E F : Set} →
  {f₀ : A ≃ D} {f₁ : B ≃ E} {f₂ : C ≃ F} →
  assocl⋆equiv ● (f₀ ×≃ (f₁ ×≃ f₂)) ≋ ((f₀ ×≃ f₁) ×≃ f₂) ● assocl⋆equiv
assocl⋆-nat = flip-sym≋ assocr⋆-nat

-- often called 'triangle'
unite-assocr⋆-coh : ∀ {A B : Set} →
  unite⋆′equiv ×≃ id≃ ≋ (id≃ ×≃ unite⋆equiv) ● assocr⋆equiv {A} {⊤} {B}
unite-assocr⋆-coh = eq triangle⋆-right triangle⋆-left

-- often called 'pentagon'
assocr⋆-coh : ∀ {A B C D : Set} →
  assocr⋆equiv {A} {B} {C × D} ● assocr⋆equiv ≋
  (id≃ ×≃ assocr⋆equiv) ● assocr⋆equiv ● (assocr⋆equiv ×≃ id≃)
assocr⋆-coh = eq pentagon⋆-right pentagon⋆-left

swap⋆-nat : {A B C D : Set} {f : A ≃ C} {g : B ≃ D} →
  swap⋆equiv ● (f ×≃ g) ≋ (g ×≃ f) ● swap⋆equiv
swap⋆-nat = eq swap⋆-coh swap⋆-coh

-- often called 'hexagon'
assocr⋆-swap⋆-coh : ∀ {A B C : Set} →
  assocr⋆equiv {B} {C} {A} ● swap⋆equiv ● assocr⋆equiv {A} {B} {C} ≋
  id≃ ×≃ swap⋆equiv ● assocr⋆equiv ● swap⋆equiv ×≃ id≃
assocr⋆-swap⋆-coh = eq hexagon×-right hexagon×-left

-- and in the opposite direction
assocl⋆-swap⋆-coh : ∀ {A B C : Set} →
  assocl⋆equiv {A} {B} {C} ● swap⋆equiv ● assocl⋆equiv {B} {C} {A} ≋
  swap⋆equiv ×≃ id≃ ● assocl⋆equiv ● id≃ ×≃ swap⋆equiv
assocl⋆-swap⋆-coh = eq hexagon×-left hexagon×-right

-------------------
-- distributivity
distl-nat : {A B C D E F : Set} →
  {f : A ≃ D} {g : B ≃ E} {h : C ≃ F} →
  distlequiv ● (f ×≃ (g ⊎≃ h)) ≋ ((f ×≃ g) ⊎≃ (f ×≃ h)) ● distlequiv
distl-nat = eq distl-coh factorl-coh

factorl-nat : {A B C D E F : Set} →
  {f : A ≃ D} {g : B ≃ E} {h : C ≃ F} →
   factorlequiv ● ((f ×≃ g) ⊎≃ (f ×≃ h)) ≋ (f ×≃ (g ⊎≃ h)) ● factorlequiv
factorl-nat = flip-sym≋ distl-nat

dist-nat : {A B C D E F : Set} →
  {f : A ≃ D} {g : B ≃ E} {h : C ≃ F} →
  distequiv ● ((f ⊎≃ g) ×≃ h) ≋ ((f ×≃ h) ⊎≃ (g ×≃ h)) ● distequiv
dist-nat = eq dist-coh factor-coh

factor-nat : {A B C D E F : Set} →
  {f : A ≃ D} {g : B ≃ E} {h : C ≃ F} →
  factorequiv ● ((f ×≃ h) ⊎≃ (g ×≃ h)) ≋ ((f ⊎≃ g) ×≃ h) ● factorequiv
factor-nat = flip-sym≋ dist-nat

-- note how we don't use id≃ but an arbitrary ⊥ ≃ ⊥.
-- because this law under-specifies f and g, we need to
-- be explicit in our calls
distzr-nat : {A B : Set} → {f : A ≃ B} → {g : ⊥ ≃ ⊥} →
  distzrequiv ● (f ×≃ g) ≋ g ● distzrequiv
distzr-nat {f = (f , qinv h _ _)} {(_ , qinv g _ _)} =
  eq (distzr-coh {f = f}) (factorzr-coh {f = h} {g})

factorzr-nat : {A B : Set} → {f : A ≃ B} → {g : ⊥ ≃ ⊥} →
  factorzrequiv ● g ≋ (f ×≃ g) ● factorzrequiv
factorzr-nat {f = f} = flip-sym≋ (distzr-nat {f = sym≃ f})

-- same comment as above
distz-nat : {A B : Set} → {f : A ≃ B} → {g : ⊥ ≃ ⊥} →
  distzequiv ● (g ×≃ f) ≋ g ● distzequiv
distz-nat {f = (f , qinv h _ _)} {(_ , qinv g _ _)} =
  eq (distz-coh {f = f}) (factorz-coh {f = h} {g})

factorz-nat : {A B : Set} → {f : A ≃ B} → {g : ⊥ ≃ ⊥} →
  factorzequiv ● g ≋ (g ×≃ f) ● factorzequiv
factorz-nat {f = f} = flip-sym≋ (distz-nat {f = sym≃ f})

------------------------------------------
-- some equivalences for which there are two 'obvious'
-- programs, but are in fact equivalent.  Named after
-- the types which are witnessed to be equivalent.
A×[B⊎C]≃[A×C]⊎[A×B] : {A B C : Set} →
  distlequiv ● (id≃ {A = A} ×≃ swap₊equiv {B} {C}) ≋ swap₊equiv ● distlequiv
A×[B⊎C]≃[A×C]⊎[A×B] = eq A×[B⊎C]→[A×C]⊎[A×B] [A×C]⊎[A×B]→A×[B⊎C]

[A⊎B]×C≃[C×A]⊎[C×B] : {A B C : Set} →
  (swap⋆equiv ⊎≃ swap⋆equiv) ● distequiv ≋ distlequiv ● swap⋆equiv {A ⊎ B} {C}
[A⊎B]×C≃[C×A]⊎[C×B] = eq [A⊎B]×C→[C×A]⊎[C×B] [C×A]⊎[C×B]→[A⊎B]×C

[A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D : {A B C D : Set} →
  (distequiv ⊎≃ id≃) ● distequiv ● (assocl₊equiv {A} {B} {C} ×≃ id≃ {A = D}) ≋
  assocl₊equiv ● (id≃ ⊎≃ distequiv) ● distequiv
[A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D = eq [A⊎B⊎C]×D→[A×D⊎B×D]⊎C×D [A×D⊎B×D]⊎C×D→[A⊎B⊎C]×D

A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D : {A B C D : Set} →
  distlequiv ● assocl⋆equiv {A} {B} {C ⊎ D} ≋
  (assocl⋆equiv ⊎≃ assocl⋆equiv) ● distlequiv ● (id≃ ×≃ distlequiv)
A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D = eq A×B×[C⊎D]→[A×B]×C⊎[A×B]×D [A×B]×C⊎[A×B]×D→A×B×[C⊎D]

0×0≃0 : distzequiv ≋ distzrequiv
0×0≃0 = eq 0×0→0 0→0×0

0×[A⊎B]≃0 : {A B : Set} →
  distzequiv ≋ unite₊equiv ● (distzequiv ⊎≃ distzequiv) ● distlequiv {⊥} {A} {B}
0×[A⊎B]≃0 = eq 0×[A⊎B]→0 0→0×[A⊎B]

0×1≃0 : unite⋆′equiv  ≋ distzequiv
0×1≃0 = eq 0×1→0 0→0×1

A×0≃0 : {A : Set} → distzrequiv {A} ≋ distzequiv ● swap⋆equiv
A×0≃0 = eq A×0→0 0→A×0

0×A×B≃0 : {A B : Set} →
  distzequiv ≋ distzequiv ● (distzequiv ×≃ id≃) ● assocl⋆equiv {⊥} {A} {B}
0×A×B≃0 = eq 0×A×B→0 0→0×A×B

A×0×B≃0 : {A B : Set} →
  distzrequiv ● (id≃ ×≃ distzequiv)  ≋ 
  distzequiv ● (distzrequiv ×≃ id≃) ● assocl⋆equiv {A} {⊥} {B}
A×0×B≃0 = eq A×0×B→0 0→A×0×B

A×[0+B]≃A×B : {A B : Set} →
  (id≃ {A = A} ×≃ unite₊equiv {B}) ≋ unite₊equiv ● (distzrequiv ⊎≃ id≃) ● distlequiv
A×[0+B]≃A×B = eq A×[0+B]→A×B A×B→A×[0+B]

1×[A⊎B]≃A⊎B : {A B : Set} →
  unite⋆equiv ≋ (unite⋆equiv ⊎≃ unite⋆equiv) ● distlequiv {⊤} {A} {B}
1×[A⊎B]≃A⊎B = eq 1×[A⊎B]→A⊎B A⊎B→1×[A⊎B]

[A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D : {A B C D : Set} →
  assocl₊equiv ● (distequiv ⊎≃ distequiv) ● distlequiv ≋
  (assocl₊equiv ⊎≃ id≃) ● ((id≃ ⊎≃ swap₊equiv) ⊎≃ id≃) ●
     (assocr₊equiv ⊎≃ id≃) ● assocl₊equiv ● 
        (distlequiv ⊎≃ distlequiv) ● distequiv {A} {B} {C ⊎ D}
[A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D = 
  eq [A⊎B]×[C⊎D]→[[A×C⊎B×C]⊎A×D]⊎B×D 
       [[A×C⊎B×C]⊎A×D]⊎B×D→[A⊎B]×[C⊎D]
-}
------------------------------------------------------------------------
-- ≋ has, predictably, an additive structure as well
_⊎≋_ : {A B C D : Set} {f h : A ≃ B} {g i : C ≃ D} → f ≋ h → g ≋ i →
  f ⊎≃ g ≋ h ⊎≃ i
f≋h ⊎≋ g≋i = 
  eq (β⊎₁ ⊙ cong₂⊎ (f≡ f≋h) (f≡ g≋i) ⊙ ! β⊎₁)
     (β⊎₂ ⊙ cong₂⊎ (g≡ f≋h) (g≡ g≋i) ⊙ ! β⊎₂)
  where open _≋_
  
------------------------------------------------------------------------
-- also useful

[g+1]●[1+f]≋g+f : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (g ⊎≃ id≃) ● (id≃ ⊎≃ f) ≋ g ⊎≃ f
[g+1]●[1+f]≋g+f {f = f} {g} = begin (
  (g ⊎≃ id≃) ● (id≃ ⊎≃ f)
    ≋⟨ sym≋ ⊎●≋●⊎ ⟩
  (g ● id≃) ⊎≃ (id≃ ● f)
    ≋⟨ rid≋ ⊎≋ lid≋ ⟩
  g ⊎≃ f ∎)
  where open ≋-Reasoning

-- same proof as above, just written compactly
[1+f]●[g+1]≋g+f : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (id≃ ⊎≃ f) ● (g ⊎≃ id≃) ≋ g ⊎≃ f
[1+f]●[g+1]≋g+f {f = f} {g} =
  trans≋ (sym≋ ⊎●≋●⊎) (lid≋ ⊎≋ rid≋)

-- put then together
[g+1]●[1+f]≋[1+f]●[g+1] : {A B C D : Set} {f : A ≃ B} {g : C ≃ D} →
  (g ⊎≃ id≃) ● (id≃ ⊎≃ f) ≋ (id≃ ⊎≃ f) ● (g ⊎≃ id≃)
[g+1]●[1+f]≋[1+f]●[g+1] = trans≋ [g+1]●[1+f]≋g+f (sym≋ [1+f]●[g+1]≋g+f)

