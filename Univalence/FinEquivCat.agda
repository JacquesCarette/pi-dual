{-# OPTIONS --without-K #-}

module FinEquivCat where

-- We will define a rig category whose objects are Fin types and whose
-- morphisms are type equivalences; and where the equivalence of
-- morphisms ≋ is extensional

open import Level using () renaming (zero to lzero; suc to lsuc)

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Unit using ()
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Data.Product
  using (_,_; proj₁; proj₂;_×_; Σ; uncurry)
  renaming (map to map×)
import Function as F using (_∘_; id)

import Relation.Binary.PropositionalEquality as P
  using (refl; trans; cong)

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

open import Equiv using (id≃; sym≃; _∼_; sym∼; _●_)
open import EquivEquiv
  using (_≋_; eq; id≋; sym≋; trans≋; _◎_; ●-assoc; lid≋; rid≋;
         linv≋; rinv≋; module _≋_)

open import FinEquivTypeEquiv
  using (_fin≃_; module PlusE; module TimesE; module PlusTimesE)
open PlusE using (_+F_; unite+; unite+r; uniti+; uniti+r;
                  swap+; sswap+; assocl+; assocr+)
open TimesE using (_*F_; unite*; uniti*; unite*r; uniti*r; 
                  swap*; sswap*; assocl*; assocr*)
open PlusTimesE using (distz; factorz; distzr; factorzr;
                       dist; factor; distl; factorl)
open import FinEquivEquivPlus using (
    [id+id]≋id; +●≋●+; _+≋_;
    unite₊-nat; unite₊r-nat; uniti₊-nat; uniti₊r-nat;
    assocr₊-nat; assocl₊-nat; unite-assocr₊-coh; assocr₊-coh;
    swap₊-nat; sswap₊-nat; assocr₊-swap₊-coh; assocl₊-swap₊-coh)
open import FinEquivEquivTimes using (
    id*id≋id; *●≋●*; _*≋_;
    unite*-nat; unite*r-nat; uniti*-nat; uniti*r-nat;
    assocr*-nat; assocl*-nat; unite-assocr*-coh; assocr*-coh;
    swap*-nat; sswap*-nat; assocr*-swap*-coh; assocl*-swap*-coh)
open import FinEquivEquivPlusTimes using (
    distl-nat; factorl-nat; dist-nat; factor-nat;
    distzr-nat; factorzr-nat; distz-nat; factorz-nat;
    A×[B⊎C]≃[A×C]⊎[A×B]; 
    [A⊎B]×C≃[C×A]⊎[C×B]; 
    [A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D; 
    A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D; 
    [A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D;
    0×0≃0;
    0×[A⊎B]≃0;
    0×1≃0;
    A×0≃0;
    0×A×B≃0;
    A×0×B≃0;
    A×[0+B]≃A×B;
    1×[A⊎B]≃A⊎B)

------------------------------------------------------------------------------
-- Fin and type equivalences are a category
-- note how all of the 'higher structure' (i.e. ≋ equations) are all
-- generic, i.e. they are true of all equivalences, not just _fin≃_.

FinEquivCat : Category lzero lzero lzero
FinEquivCat = record
  { Obj = ℕ
  ; _⇒_ = _fin≃_
  ; _≡_ = _≋_
  ; id = id≃
  ; _∘_ = _●_ 
  ; assoc = λ { {f = f} {g} {h} → ●-assoc {f = f} {g} {h} }
  ; identityˡ = lid≋
  ; identityʳ = rid≋ 
  ; equiv = record { refl = id≋ ; sym = sym≋ ; trans = trans≋ } 
  ; ∘-resp-≡ = _◎_
  }

FinEquivGroupoid : Groupoid FinEquivCat
FinEquivGroupoid = record 
  { _⁻¹ = sym≃ 
  ; iso = λ { {f = A≃B} → record
    { isoˡ = linv≋ A≃B
    ; isoʳ = rinv≋ A≃B
    } }
  }

-- The additive structure is monoidal

⊎-bifunctor : Bifunctor FinEquivCat FinEquivCat FinEquivCat
⊎-bifunctor = record
  { F₀ = uncurry _+_ 
  ; F₁ = uncurry _+F_
  ; identity = [id+id]≋id
  ; homomorphism = +●≋●+
  ; F-resp-≡ = uncurry _+≋_
  }

module ⊎h = MonoidalHelperFunctors FinEquivCat ⊎-bifunctor 0

0⊎x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊎x≡x = record 
  { F⇒G = record
    { η = λ _ → unite+  
    ; commute = λ _ → unite₊-nat }
  ; F⇐G = record
    { η = λ _ → uniti+ 
    ; commute = λ _ →  uniti₊-nat }
  ; iso = λ _ → record
    { isoˡ = linv≋ unite+
    ; isoʳ = rinv≋ unite+
    }
  }

x⊎0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊎0≡x = record
  { F⇒G = record
    { η = λ _ → unite+r 
    ; commute = λ _ → unite₊r-nat }
  ; F⇐G = record
    { η = λ _ → uniti+r 
    ; commute = λ _ → uniti₊r-nat 
    }
  ; iso = λ X → record
    { isoˡ = linv≋ unite+r
    ; isoʳ = rinv≋ unite+r
    }
  }

[x⊎y]⊎z≡x⊎[y⊎z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
[x⊎y]⊎z≡x⊎[y⊎z] = record
  { F⇒G = record
    { η = λ X → assocr+ {m = X zero}
    ; commute = λ _ → assocr₊-nat 
    }
  ; F⇐G = record
    { η = λ X → assocl+ {m = X zero}
    ; commute = λ _ → assocl₊-nat 
    }
  ; iso = λ X → record
    { isoˡ = linv≋ assocr+
    ; isoʳ = rinv≋ assocr+
    }
  }

CPM⊎ : Monoidal FinEquivCat
CPM⊎ = record
  { ⊗ = ⊎-bifunctor
   ; id = 0
   ; identityˡ = 0⊎x≡x
   ; identityʳ = x⊎0≡x
   ; assoc = [x⊎y]⊎z≡x⊎[y⊎z]
   ; triangle = unite-assocr₊-coh
   ; pentagon = assocr₊-coh
   }

-- The multiplicative structure is monoidal

×-bifunctor : Bifunctor FinEquivCat FinEquivCat FinEquivCat
×-bifunctor = record
  { F₀ = uncurry _*_ 
  ; F₁ = uncurry _*F_
  ; identity = id*id≋id
  ; homomorphism = *●≋●*
  ; F-resp-≡ = uncurry _*≋_
  }

module ×h = MonoidalHelperFunctors FinEquivCat ×-bifunctor 1

1×y≡y : NaturalIsomorphism ×h.id⊗x ×h.x
1×y≡y = record
  { F⇒G = record
    { η = λ _ → unite* 
    ; commute = λ _ → unite*-nat
    }
  ; F⇐G = record
    { η = λ _ → uniti* 
    ; commute = λ _ → uniti*-nat
    }
  ; iso = λ X → record
    { isoˡ = linv≋ unite*
    ; isoʳ = rinv≋ unite*
    }
  }

y×1≡y : NaturalIsomorphism ×h.x⊗id ×h.x
y×1≡y = record
  { F⇒G = record 
    { η = λ X → unite*r 
    ;  commute = λ _ → unite*r-nat
    }
  ; F⇐G = record 
    { η = λ X → uniti*r 
    ; commute = λ _ → uniti*r-nat
    }
  ; iso = λ X → record 
    { isoˡ = linv≋ unite*r
    ; isoʳ = rinv≋ unite*r
    }
  }

[x×y]×z≡x×[y×z] : NaturalIsomorphism ×h.[x⊗y]⊗z ×h.x⊗[y⊗z]
[x×y]×z≡x×[y×z] = record
  { F⇒G = record
    { η = λ X → assocr* {m = X zero}
    ; commute = λ _ → assocr*-nat }
  ; F⇐G = record
    { η = λ X → assocl* {m = X zero}
    ; commute = λ _ → assocl*-nat }
  ; iso = λ X → record
    { isoˡ = linv≋ assocr*
    ; isoʳ = rinv≋ assocr* }
  }

CPM× : Monoidal FinEquivCat
CPM× = record
  { ⊗ = ×-bifunctor
  ; id = 1
  ; identityˡ = 1×y≡y
  ; identityʳ = y×1≡y
  ; assoc = [x×y]×z≡x×[y×z]
  ; triangle = unite-assocr*-coh
  ; pentagon = assocr*-coh
  }

-- The monoidal structures are symmetric

x⊎y≈y⊎x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
x⊎y≈y⊎x = record 
  { F⇒G = record 
    { η = λ X → swap+ {m = X zero}
    ; commute = λ _ → swap₊-nat
    } 
  ; F⇐G = record 
    { η = λ X → sswap+ {m = X zero} {n = X (suc zero)}
    ; commute = λ _ → sswap₊-nat 
    } 
  ; iso = λ X → record
    { isoˡ = linv≋ swap+ 
    ; isoʳ = rinv≋ swap+ 
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
    { η = λ X → swap* {m = X zero}
    ; commute = λ _ → swap*-nat 
    }
  ; F⇐G = record
    { η = λ X → sswap* {m = X zero} 
    ; commute = λ _ → sswap*-nat 
    }
  ; iso = λ X → record
    { isoˡ = linv≋ swap* 
    ; isoʳ = rinv≋ swap* 
    }
  }

BM× : Braided CPM×
BM× = record 
  { braid = x×y≈y×x 
  ; hexagon₁ = assocr*-swap*-coh 
  ; hexagon₂ = assocl*-swap*-coh 
  }

SBM⊎ : Symmetric BM⊎
SBM⊎ = record { symmetry = linv≋ sswap+ }

SBM× : Symmetric BM×
SBM× = record { symmetry = linv≋ sswap* }

-- And finally the multiplicative structure distributes over the
-- additive one

module r = BimonoidalHelperFunctors BM⊎ BM×

x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record
  { F⇒G = record
    { η = λ X → distl {m = X zero}
    ; commute = λ _ → distl-nat
    }
  ; F⇐G = record
    { η = λ X → factorl {m = X zero}
    ; commute = λ _ → factorl-nat
    }
  ; iso = λ X → record { isoˡ = linv≋ distl 
                       ; isoʳ = rinv≋ distl }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record
    { η = λ X → dist {m = X zero}
    ; commute = λ _ → dist-nat
    }
  ; F⇐G = record
    { η = λ X → factor {m = X zero}
    ; commute = λ _ → factor-nat
    }
  ; iso = λ X → record { isoˡ = linv≋ dist
                       ; isoʳ = rinv≋ dist }
  }

x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
x⊗0≡0 = record
  { F⇒G = record
    { η = λ X → distzr {m = X zero}
    ; commute = λ _ → distzr-nat
    }
  ; F⇐G = record
    { η = λ X → factorzr {n = X zero}
    ; commute = λ _ → factorzr-nat
    }
  ; iso = λ X → record
    { isoˡ = linv≋ distzr 
    ; isoʳ = rinv≋ distzr 
    }
  }

0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
0⊗x≡0 = record
  { F⇒G = record
    { η = λ X → distz {m = X zero}
    ; commute = λ _ → distz-nat
    }
  ; F⇐G = record
    { η = λ X → factorz {m = X zero}
    ; commute = λ _ → factorz-nat
    }
  ; iso = λ X → record
    { isoˡ = linv≋ distz
    ; isoʳ = rinv≋ distz
    }
  }

TERig : RigCategory SBM⊎ SBM×
TERig = record
  { distribₗ = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
  ; distribᵣ = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z]
  ; annₗ = 0⊗x≡0
  ; annᵣ = x⊗0≡0
  ; laplazaI = A×[B⊎C]≃[A×C]⊎[A×B]
  ; laplazaII = [A⊎B]×C≃[C×A]⊎[C×B]
  ; laplazaIV = [A⊎B⊎C]×D≃[A×D⊎B×D]⊎C×D
  ; laplazaVI = A×B×[C⊎D]≃[A×B]×C⊎[A×B]×D
  ; laplazaIX = [A⊎B]×[C⊎D]≃[[A×C⊎B×C]⊎A×D]⊎B×D
  ; laplazaX = 0×0≃0
  ; laplazaXI = 0×[A⊎B]≃0
  ; laplazaXIII = 0×1≃0
  ; laplazaXV = A×0≃0
  ; laplazaXVI = 0×A×B≃0
  ; laplazaXVII = A×0×B≃0
  ; laplazaXIX = A×[0+B]≃A×B
  ; laplazaXXIII = 1×[A⊎B]≃A⊎B
  }

------------------------------------------------------------------------------
