{-# OPTIONS --without-K #-}

module TypeEquivCat where

-- We will define a rig category whose objects are types and whose
-- morphisms are type equivalences; and where the equivalence of
-- morphisms ≋ is extensional

open import Level renaming (zero to lzero; suc to lsuc)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; _×_; uncurry)

import Relation.Binary.PropositionalEquality as P
  using (sym)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Monoidal using (Monoidal)
open import Categories.Monoidal.Helpers using (module MonoidalHelperFunctors)
open import Categories.Bifunctor using (Bifunctor)
open import Categories.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Monoidal.Braided using (Braided)
open import Categories.Monoidal.Symmetric using (Symmetric)
open import Categories.RigCategory
  using (RigCategory; module BimonoidalHelperFunctors)

open import Equiv
  using (_≃_; id≃; sym≃; _●_; _⊎≃_; _×≃_)
open import EquivEquiv
  using (_≋_; eq; id≋; sym≋; trans≋; ●-assoc; _◎_;
    linv≋; rinv≋; lid≋; rid≋; flip-sym≋)

-- list all explicitly, but these are all equivalences
open import TypeEquiv
  using (unite₊equiv; uniti₊equiv; unite₊′equiv; uniti₊′equiv;
         assocr₊equiv; assocl₊equiv;
         unite⋆equiv; uniti⋆equiv; unite⋆′equiv; uniti⋆′equiv;
         assocr⋆equiv; assocl⋆equiv; swap₊equiv; swapswap₊;
         swapswap⋆; swap⋆equiv;
         distequiv; factorequiv; factor∘dist; dist∘factor; 
         distlequiv; factorlequiv; factorl∘distl; distl∘factorl;
         distzequiv; factorzequiv; factorz∘distz; distz∘factorz;
         distzrequiv; factorzrequiv; factorzr∘distzr; distzr∘factorzr)

open import TypeEquivEquiv -- need them all!

open import Data.SumProd.Properties
  using (dist-commute; factor-commute; distl-commute; factorl-commute;
         dist-swap⋆-lemma; factor-swap⋆-lemma; 
         distl-swap₊-lemma; factorl-swap₊-lemma;
         dist-dist-assoc-lemma; assoc-factor-factor-lemma;
         distl-assoc-lemma; assoc-factorl-lemma;
         fully-distribute; fully-factor;
         distz0≡distrz0; factorz0≡factorzr0;
         distz0≡unite₊∘[distz,distz]∘distl;
         factorz0≡factorl∘[factorz,factorz]∘uniti₊;
         unite⋆r0≡absorb1; uniti⋆r0≡factorz;
         absorbl≡absorbr∘swap⋆; factorzr≡swap⋆∘factorz;
         absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr;
         factorz⇔factorz◎[factorz⊗id]◎assocr⋆;
         elim-middle-⊥; insert-middle-⊥;
         elim⊥-A[0⊕B]; insert⊕⊥-AB;
         elim⊤-1[A⊕B]; insert⊤l⊗-A⊕B)

------------------------------------------------------------------------------
-- We show that types with type equivalences are a commutative rig
-- groupoid

-- First it is a category

TypeEquivCat : Category (lsuc lzero) lzero lzero
TypeEquivCat = record
  { Obj = Set
  ; _⇒_ = _≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = _●_
  ; assoc = λ { {f = f} {g} {h} → ●-assoc {f = f} {g} {h} }
  ; identityˡ = lid≋
  ; identityʳ = rid≋
  ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ }
  ; ∘-resp-≡ = _◎_
  }

-- The category has inverses and hence a groupoid

TypeEquivGroupoid : Groupoid TypeEquivCat
TypeEquivGroupoid = record 
  { _⁻¹ = sym≃ 
  ; iso = λ { {f = A≃B} → record
    { isoˡ = linv≋ A≃B
    ; isoʳ = rinv≋ A≃B
    } }
  }


-- The additive structure is monoidal

⊎-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
⊎-bifunctor = record
  { F₀ = uncurry _⊎_
  ; F₁ = uncurry _⊎≃_
  ; identity = [id,id]≋id
  ; homomorphism = ⊎●≋●⊎
  ; F-resp-≡ = uncurry ⊎≃-respects-≋
  }
  
module ⊎h = MonoidalHelperFunctors TypeEquivCat ⊎-bifunctor ⊥

0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊎x≡x = record 
  { F⇒G = record
    { η = λ _ → unite₊equiv
    ; commute = λ f → unite₊-nat }
  ; F⇐G = record
    { η = λ _ → uniti₊equiv
    ; commute = λ f →  uniti₊-nat } 
  ; iso = λ _ → record
    { isoˡ = linv≋ unite₊equiv
    ; isoʳ = rinv≋ unite₊equiv
    }
  }

x⊎0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊎0≡x = record
  { F⇒G = record
    { η = λ _ → unite₊′equiv
    ; commute = λ f → unite₊′-nat
    }
  ; F⇐G = record
    { η = λ X → uniti₊′equiv
    ; commute = λ f → uniti₊′-nat
    }
  ; iso = λ X → record
    { isoˡ = linv≋ unite₊′equiv
    ; isoʳ = rinv≋ unite₊′equiv
    }
  }

[x⊎y]⊎z≡x⊎[y⊎z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
[x⊎y]⊎z≡x⊎[y⊎z] = record
  { F⇒G = record
    { η = λ _ → assocr₊equiv
    ; commute = λ f → assocr₊-nat
    }
  ; F⇐G = record
    { η = λ _ → assocl₊equiv
    ; commute = λ f → assocl₊-nat
    }
  ; iso = λ X → record
    { isoˡ = linv≋ assocr₊equiv
    ; isoʳ = rinv≋ assocr₊equiv
    }
  }

CPM⊎ : Monoidal TypeEquivCat
CPM⊎ = record
  { ⊗ = ⊎-bifunctor
   ; id = ⊥
   ; identityˡ = 0⊎x≡x
   ; identityʳ = x⊎0≡x
   ; assoc = [x⊎y]⊎z≡x⊎[y⊎z]
   ; triangle = unite-assocr₊-coh
   ; pentagon = assocr₊-coh
   }

-- The multiplicative structure is also monoidal

-- below, we will have a lot of things which belong in
-- Data.Product.Properties.  In fact, some of them are ``free'', in
-- that β-reduction is enough.  However, it might be a good idea to
-- fully mirror all the ones needed for ⊎.

×-bifunctor : Bifunctor TypeEquivCat TypeEquivCat TypeEquivCat
×-bifunctor = record
  { F₀ = uncurry _×_
  ; F₁ = uncurry _×≃_
  ; identity = id×id≋id
      -- the following would have unresolved metas without the extra precision
  ; homomorphism = λ { {f = (f , g)} {h , i} → ×●≋●× {f = f} {g} {h} {i}}
  ; F-resp-≡ = uncurry ×≃-resp-≋
  }

module ×h = MonoidalHelperFunctors TypeEquivCat ×-bifunctor ⊤

-- again because of η for products, lots of the following have trivial proofs

1×y≡y : NaturalIsomorphism ×h.id⊗x ×h.x
1×y≡y = record
  { F⇒G = record
    { η = λ X → unite⋆equiv
    ; commute = λ f → unite⋆-nat
    }
  ; F⇐G = record
    { η = λ X → uniti⋆equiv
    ; commute = λ f → uniti⋆-nat
    }
  ; iso = λ X → record
    { isoˡ = linv≋ unite⋆equiv
    ; isoʳ = rinv≋ unite⋆equiv
    }
  }

y×1≡y : NaturalIsomorphism ×h.x⊗id ×h.x
y×1≡y = record
  { F⇒G = record 
    { η = λ X → unite⋆′equiv 
    ;  commute = λ f → unite⋆′-nat
    }
  ; F⇐G = record 
    { η = λ X → uniti⋆′equiv 
    ; commute = λ f → uniti⋆′-nat
    }
  ; iso = λ X → record 
    { isoˡ = linv≋ unite⋆′equiv
    ; isoʳ = rinv≋ unite⋆′equiv
    }
  }

[x×y]×z≡x×[y×z] : NaturalIsomorphism ×h.[x⊗y]⊗z ×h.x⊗[y⊗z]
[x×y]×z≡x×[y×z] = record
  { F⇒G = record
    { η = λ X → assocr⋆equiv
    ; commute = λ f → assocr⋆-nat }
  ; F⇐G = record
    { η = λ X → assocl⋆equiv
    ; commute = λ f → assocl⋆-nat }
  ; iso = λ X → record
    { isoˡ = linv≋ assocr⋆equiv
    ; isoʳ = rinv≋ assocr⋆equiv }
  }

CPM× : Monoidal TypeEquivCat
CPM× = record
  { ⊗ = ×-bifunctor
  ; id = ⊤
  ; identityˡ = 1×y≡y
  ; identityʳ = y×1≡y
  ; assoc = [x×y]×z≡x×[y×z]
  ; triangle = unite-assocr⋆-coh
  ; pentagon = assocr⋆-coh
  }

-- The monoidal structures are symmetric

x⊎y≈y⊎x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
x⊎y≈y⊎x = record 
  { F⇒G = record 
    { η = λ X → swap₊equiv 
    ; commute = λ f → swap₊-nat
    } 
  ; F⇐G = record 
    { η = λ X → sym≃ swap₊equiv
    ; commute = λ f → swap₊-nat
    } 
  ; iso = λ X → record
    { isoˡ = linv≋ swap₊equiv 
    ; isoʳ = rinv≋ swap₊equiv 
    }
  }

BM⊎ : Braided CPM⊎
BM⊎ = record 
  { braid = x⊎y≈y⊎x 
  ; hexagon₁ = assocr₊-swap₊-coh 
  ; hexagon₂ = assocl₊-swap₊-coh 
  }

x×y≈y×x : NaturalIsomorphism ×h.x⊗y ×h.y⊗x
x×y≈y×x = record
  { F⇒G = record
    { η = λ X → swap⋆equiv
    ; commute = λ _ → swap⋆-nat
    }
  ; F⇐G = record
    { η = λ X → sym≃ swap⋆equiv
    ; commute = λ f → swap⋆-nat
    }
  ; iso = λ X → record
    { isoˡ = linv≋ swap⋆equiv
    ; isoʳ = rinv≋ swap⋆equiv
    }
  }

BM× : Braided CPM×
BM× = record 
  { braid = x×y≈y×x 
  ; hexagon₁ = assocr⋆-swap⋆-coh
  ; hexagon₂ = assocl⋆-swap⋆-coh 
  }

SBM⊎ : Symmetric BM⊎
SBM⊎ = record { symmetry = linv≋ swap₊equiv }

SBM× : Symmetric BM×
SBM× = record { symmetry = linv≋ swap⋆equiv }

-- And finally the multiplicative structure distributes over the
-- additive one

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
  ; iso = λ X → record { isoˡ = linv≋ distlequiv
                       ; isoʳ = rinv≋ distlequiv }
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
  ; iso = λ X → record { isoˡ = linv≋ distequiv
                       ; isoʳ = rinv≋ distequiv }
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
    { isoˡ = linv≋ distzrequiv
    ; isoʳ = rinv≋ distzrequiv
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
    { isoˡ = linv≋ distzequiv
    ; isoʳ = rinv≋ distzequiv
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
  ; laplazaIX = eq fully-distribute fully-factor
  ; laplazaX = eq distz0≡distrz0 factorz0≡factorzr0
  ; laplazaXI = eq
                 distz0≡unite₊∘[distz,distz]∘distl
                 factorz0≡factorl∘[factorz,factorz]∘uniti₊
  ; laplazaXIII = eq unite⋆r0≡absorb1 uniti⋆r0≡factorz
  ; laplazaXV = eq absorbl≡absorbr∘swap⋆ factorzr≡swap⋆∘factorz
  ; laplazaXVI = eq
                  absorbr⇔assocl⋆◎[absorbr⊗id]◎absorbr
                  factorz⇔factorz◎[factorz⊗id]◎assocr⋆
  ; laplazaXVII = eq elim-middle-⊥ insert-middle-⊥
  ; laplazaXIX = eq elim⊥-A[0⊕B] insert⊕⊥-AB
  ; laplazaXXIII = eq elim⊤-1[A⊕B] insert⊤l⊗-A⊕B
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

------------------------------------------------------------------------------
