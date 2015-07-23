{-# OPTIONS --without-K #-}

module Pi1Cat where

-- Proving that Pi with one level of interesting 2 path structure is a
-- symmetric rig 2-groupoid

open import Level using () renaming (zero to lzero)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Function using (flip)

open import Categories.Category using (Category; module Heterogeneous)
open import Categories.Terminal using (OneC; unit)
open import Categories.Groupoid using (Groupoid)
open import Categories.Monoidal using (Monoidal)
open import Categories.Monoidal.Helpers using (module MonoidalHelperFunctors)
open import Categories.Functor using (Functor)
open import Categories.Bifunctor using (Bifunctor)
open import Categories.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Monoidal.Braided using (Braided)
open import Categories.Monoidal.Symmetric using (Symmetric)
open import Categories.RigCategory
  using (RigCategory; module BimonoidalHelperFunctors)
open import Categories.2-Category using (2-Category)

open import PiU using (U; PLUS; ZERO; TIMES; ONE)
open import PiLevel0
  using (_⟷_; id⟷; _◎_;
        !; !!;
        _⊕_; 
        unite₊l; uniti₊l; unite₊r; uniti₊r;
        swap₊;
        assocr₊; assocl₊;
        _⊗_; 
        unite⋆l; uniti⋆l; unite⋆r; uniti⋆r;
        swap⋆;
        assocr⋆; assocl⋆;
        absorbl; absorbr; factorzl; factorzr;
        dist; factor; distl; factorl)

open import PiLevel1 using (_⇔_; ⇔Equiv; triv≡; triv≡Equiv; 2!; 
 id⇔; trans⇔; _⊡_;
 assoc◎l; idr◎l; idl◎l; linv◎l; rinv◎l;
 id⟷⊕id⟷⇔; hom⊕◎⇔; resp⊕⇔;
 unite₊l⇔r; uniti₊l⇔r; unite₊r⇔r; uniti₊r⇔r;
 assocr⊕r; assocl⊕l; triangle⊕l; pentagon⊕l;
 id⟷⊗id⟷⇔; hom⊗◎⇔; resp⊗⇔;
 uniter⋆⇔l; unitir⋆⇔l; uniter⋆⇔r; unitir⋆⇔r;
 assocr⊗r; assocl⊗l; triangle⊗l; pentagon⊗l;
 swapr₊⇔; hexagonr⊕l; hexagonl⊕l;
 swapr⋆⇔; hexagonr⊗l; hexagonl⊗l;
 absorbl⇔l; factorzr⇔l; absorbr⇔l; factorzl⇔l;
 distl⇔l; factorl⇔l; dist⇔l; factor⇔l;
 swap₊distl⇔l; dist-swap⋆⇔l; assocl₊-dist-dist⇔l; assocl⋆-distl⇔l;
 fully-distribute⇔l; absorbr0-absorbl0⇔; absorbr⇔distl-absorb-unite;
 unite⋆r0-absorbr1⇔; absorbl≡swap⋆◎absorbr;
 absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr;
 [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr;
 elim⊥-A[0⊕B]⇔l; elim⊥-1[A⊕B]⇔l
 )

------------------------------------------------------------------------------
-- Pi1 is a category...

Pi1Cat : Category lzero lzero lzero
Pi1Cat = record
  { Obj = U
  ; _⇒_ = _⟷_
  ; _≡_ = _⇔_
  ; id = id⟷
  ; _∘_ = λ y⟷z x⟷y → x⟷y ◎ y⟷z 
  ; assoc = assoc◎l 
  ; identityˡ = idr◎l 
  ; identityʳ = idl◎l 
  ; equiv = ⇔Equiv
  ; ∘-resp-≡ = λ f g → g ⊡ f 
  }

-- and a groupoid ...

Pi1Groupoid : Groupoid Pi1Cat
Pi1Groupoid = record 
  { _⁻¹ = ! 
  ; iso = record { isoˡ = linv◎l ; isoʳ = rinv◎l } 
  }

-- additive bifunctor and monoidal structure

⊕-bifunctor : Bifunctor Pi1Cat Pi1Cat Pi1Cat
⊕-bifunctor = record
  { F₀ = λ {(u , v) → PLUS u v}
  ; F₁ = λ {(x⟷y , z⟷w) → x⟷y ⊕ z⟷w }
  ; identity = id⟷⊕id⟷⇔
  ; homomorphism = hom⊕◎⇔
  ; F-resp-≡ = λ {(x , y) → resp⊕⇔ x y}
  }

module ⊎h = MonoidalHelperFunctors Pi1Cat ⊕-bifunctor ZERO

-- note how powerful linv◎l/rinv◎l are in iso below

0⊕x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊕x≡x = record 
  { F⇒G = record { η = λ X → unite₊l ; commute = λ f → unite₊l⇔r } 
  ; F⇐G = record { η = λ X → uniti₊l ; commute = λ f → uniti₊l⇔r } 
  ; iso = λ X → record { isoˡ = linv◎l; isoʳ = rinv◎l }
  }

x⊕0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊕0≡x = record
  { F⇒G = record { η = λ X → unite₊r ; commute = λ f → unite₊r⇔r }
  ; F⇐G = record { η = λ X → uniti₊r ; commute = λ f → uniti₊r⇔r }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

[x⊕y]⊕z≡x⊕[y⊕z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
[x⊕y]⊕z≡x⊕[y⊕z] = record
  { F⇒G = record
    { η = λ X → assocr₊
    ; commute = λ f → assocr⊕r
    }
  ; F⇐G = record
    { η = λ X → assocl₊
    ; commute = λ f → assocl⊕l
    }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

-- and a monoidal category (additive)

M⊕ : Monoidal Pi1Cat
M⊕ = record
  { ⊗ = ⊕-bifunctor
  ; id = ZERO
  ; identityˡ = 0⊕x≡x
  ; identityʳ = x⊕0≡x
  ; assoc = [x⊕y]⊕z≡x⊕[y⊕z]
  ; triangle = triangle⊕l
  ; pentagon = pentagon⊕l
  }

-- multiplicative bifunctor and monoidal structure

⊗-bifunctor : Bifunctor Pi1Cat Pi1Cat Pi1Cat
⊗-bifunctor = record
  { F₀ = λ {(u , v) → TIMES u v}
  ; F₁ = λ {(x⟷y , z⟷w) → x⟷y ⊗ z⟷w }
  ; identity = id⟷⊗id⟷⇔
  ; homomorphism = hom⊗◎⇔
  ; F-resp-≡ = λ {(x , y) → resp⊗⇔ x y}
  }

module ×h = MonoidalHelperFunctors Pi1Cat ⊗-bifunctor ONE

1⊗x≡x : NaturalIsomorphism ×h.id⊗x ×h.x
1⊗x≡x = record 
  { F⇒G = record
    { η = λ X → unite⋆l
    ; commute = λ f → uniter⋆⇔l } 
  ; F⇐G = record
    { η = λ X → uniti⋆l
    ; commute = λ f → unitir⋆⇔l } 
  ; iso = λ X → record { isoˡ = linv◎l; isoʳ = rinv◎l }
  }

x⊗1≡x : NaturalIsomorphism ×h.x⊗id ×h.x
x⊗1≡x = record
  { F⇒G = record
    { η = λ X → unite⋆r 
    ; commute = λ f → uniter⋆⇔r
    }
  ; F⇐G = record
    { η = λ X → uniti⋆r
    ; commute = λ f → unitir⋆⇔r 
    }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

[x⊗y]⊗z≡x⊗[y⊗z] : NaturalIsomorphism ×h.[x⊗y]⊗z ×h.x⊗[y⊗z]
[x⊗y]⊗z≡x⊗[y⊗z] = record
  { F⇒G = record
    { η = λ X → assocr⋆
    ; commute = λ f → assocr⊗r
    }
  ; F⇐G = record
    { η = λ X → assocl⋆
    ; commute = λ f → assocl⊗l
    }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

-- and a monoidal category (multiplicative)

M⊗ : Monoidal Pi1Cat
M⊗ = record
  { ⊗ = ⊗-bifunctor
  ; id = ONE
  ; identityˡ = 1⊗x≡x
  ; identityʳ = x⊗1≡x
  ; assoc = [x⊗y]⊗z≡x⊗[y⊗z]
  ; triangle = triangle⊗l
  ; pentagon = pentagon⊗l
  }

x⊕y≡y⊕x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
x⊕y≡y⊕x = record 
  { F⇒G = record { η = λ X → swap₊ ; commute = λ f → swapr₊⇔ } 
  ; F⇐G = record { η = λ X → swap₊ ; commute = λ f → swapr₊⇔ } 
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l } }

BM⊕ : Braided M⊕
BM⊕ = record
  { braid = x⊕y≡y⊕x
  ; hexagon₁ = hexagonr⊕l
  ; hexagon₂ = hexagonl⊕l
  }

x⊗y≡y⊗x : NaturalIsomorphism ×h.x⊗y ×h.y⊗x
x⊗y≡y⊗x = record 
  { F⇒G = record { η = λ X → swap⋆ ; commute = λ f → swapr⋆⇔ } 
  ; F⇐G = record { η = λ X → swap⋆ ; commute = λ f → swapr⋆⇔ } 
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l } }

BM⊗ : Braided M⊗
BM⊗ = record
  { braid = x⊗y≡y⊗x
  ; hexagon₁ = hexagonr⊗l
  ; hexagon₂ = hexagonl⊗l
  }

-- with both monoidal structures being symmetric

SBM⊕ : Symmetric BM⊕
SBM⊕ = record { symmetry = linv◎l }

SBM⊗ : Symmetric BM⊗
SBM⊗ = record { symmetry = rinv◎l }

module r = BimonoidalHelperFunctors BM⊕ BM⊗

x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
x⊗0≡0 = record 
  { F⇒G = record
    { η = λ X → absorbl
    ; commute = λ f → absorbl⇔l
    } 
  ; F⇐G = record
    { η = λ X → factorzr
    ; commute = λ f → factorzr⇔l
    } 
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l } 
  }

0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
0⊗x≡0 = record
  { F⇒G = record { η = λ X → absorbr ; commute = λ f → absorbr⇔l }
  ; F⇐G = record { η = λ X → factorzl ; commute = λ f → factorzl⇔l }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record
  { F⇒G = record { η = λ _ → distl ; commute = λ f → distl⇔l }
  ; F⇐G = record { η = λ _ → factorl ; commute = λ f → factorl⇔l }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record { η = λ X → dist ; commute = λ f → dist⇔l }
  ; F⇐G = record { η = λ X → factor ; commute = λ f → factor⇔l }
  ; iso = λ X → record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }

-- and the multiplicative structure distributing over the additive one

Pi1Rig : RigCategory SBM⊕ SBM⊗
Pi1Rig = record 
  { distribₗ = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
  ; distribᵣ = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z] 
  ; annₗ = 0⊗x≡0 
  ; annᵣ = x⊗0≡0
  ; laplazaI = swap₊distl⇔l
  ; laplazaII = dist-swap⋆⇔l
  ; laplazaIV = assocl₊-dist-dist⇔l
  ; laplazaVI = assocl⋆-distl⇔l
  ; laplazaIX = fully-distribute⇔l
  ; laplazaX = absorbr0-absorbl0⇔
  ; laplazaXI = absorbr⇔distl-absorb-unite
  ; laplazaXIII = unite⋆r0-absorbr1⇔
  ; laplazaXV = absorbl≡swap⋆◎absorbr
  ; laplazaXVI =  absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr
  ; laplazaXVII = [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr
  ; laplazaXIX = elim⊥-A[0⊕B]⇔l 
  ; laplazaXXIII = elim⊥-1[A⊕B]⇔l
  }

------------------------------------------------------------------------------
-- The morphisms of the Pi1 category have structure; they form a
-- category, something like another Symmetric Rig Groupoid but more
-- general

⟷Cat : (t₁ t₂ : U) → Category lzero lzero lzero
⟷Cat t₁ t₂ = record
  { Obj = t₁ ⟷ t₂
  ; _⇒_ = _⇔_
  ; _≡_ = triv≡
  ; id = id⇔
  ; _∘_ = flip trans⇔
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; equiv = triv≡Equiv
  ; ∘-resp-≡ = λ _ _ → tt
  }

⟷Groupoid : (t₁ t₂ : U) → Groupoid (⟷Cat t₁ t₂)
⟷Groupoid t₁ t₂ = record 
  { _⁻¹ = 2! 
  ; iso = record { isoˡ = tt ; isoʳ = tt }
  }

-- These feel like the right notions of bifunctor but of course they
-- are relating different categories so the rest of the development to
-- RigCategory would need to be generalized if we were to use these
-- definitions of bifunctors.

⊕⟷-bifunctor : (t₁ t₂ t₃ t₄ : U) →
  Bifunctor (⟷Cat t₁ t₂) (⟷Cat t₃ t₄) (⟷Cat (PLUS t₁ t₃) (PLUS t₂ t₄))
⊕⟷-bifunctor t₁ t₂ t₃ t₄ = record
  { F₀ = λ {(f , g) → f ⊕ g } 
  ; F₁ = λ {(α , β) → resp⊕⇔ α β } 
  ; identity = tt 
  ; homomorphism = tt 
  ; F-resp-≡ = λ _ → tt
  }

⊗⟷-bifunctor : (t₁ t₂ t₃ t₄ : U) →
  Bifunctor (⟷Cat t₁ t₂) (⟷Cat t₃ t₄) (⟷Cat (TIMES t₁ t₃) (TIMES t₂ t₄))
⊗⟷-bifunctor t₁ t₂ t₃ t₄ = record
  { F₀ = λ {(f , g) → f ⊗ g }
  ; F₁ = λ {(α , β) → resp⊗⇔ α β }
  ; identity = tt
  ; homomorphism = tt
  ; F-resp-≡ = λ _ → tt
  }

------------------------------------------------------------------------------
-- We have a 2-category but NOT a strict one. Again we need to
-- generalize so that equality is up to ⇔ instead of ≡ 

idF : {t : U} → Functor {lzero} {lzero} {lzero} OneC (⟷Cat t t)
idF {t} = record
  { F₀ = λ _ → id⟷ {t} 
  ; F₁ = λ _ → id⇔ 
  ; identity = tt 
  ; homomorphism = tt 
  ; F-resp-≡ = λ _ → tt 
  }

∘-bifunctor : {t₁ t₂ t₃ : U} → Bifunctor (⟷Cat t₂ t₃) (⟷Cat t₁ t₂) (⟷Cat t₁ t₃)
∘-bifunctor = record
  { F₀ = λ {(f , g) → g ◎ f} 
  ; F₁ = λ {(α , β) → β ⊡ α} 
  ; identity = tt 
  ; homomorphism = tt 
  ; F-resp-≡ = λ _ → tt 
  }

{--
This is where the strict version fails:

Pi1-2Cat : 2-Category lzero lzero lzero lzero
Pi1-2Cat = record
  { Obj = U
  ; _⇒_ = ⟷Cat
  ; id = idF
  ; —∘— = ∘-bifunctor
  ; assoc =
    λ { {A} {B} {C} {D} {(CD₁ , BC₁ , AB₁)} {(CD₂ , BC₂ , AB₂)} (f₁ , f₂ , f₃) →
      let module m = Heterogeneous (⟷Cat A D) in
      {!m.≡⇒∼ tt!}}
  ; identityˡ =
    λ { {A} {B} (unit , β) →
      let module m = Heterogeneous (⟷Cat A B) in
      {!!}}
  ; identityʳ =
    λ { {A} {B} (α , unit) →
      let module m = Heterogeneous (⟷Cat A B) in
      {!!}} -- would like to use (a lifted version of idl◎l)
  }

For hole 2, we essentially want to show that the two functors 
(α -∘- id) and α are related by:
  
data _∼_ {A B} (f : A ⇒ B) : ∀ {X Y} → (X ⇒ Y) → Set (ℓ ⊔ e) where
    ≡⇒∼ : {g : A ⇒ B} → .(f ≡ g) → f ∼ g

(defined in Category.Heteregenous)

The problem is that the definition of ~ has ≡ hardwired. We have
instead ⇔ are our equality relation.

--}

------------------------------------------------------------------------------
