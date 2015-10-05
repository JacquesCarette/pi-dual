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
open PlusE using (_+F_; unite+; unite+r; uniti+; uniti+r; swap+;
                  assocl+; assocr+)
open TimesE using (_*F_; unite*; uniti*; unite*r; uniti*r; swap*;
                   assocl*; assocr*)
open PlusTimesE using (distz; factorz; distzr; factorzr;
                       dist; factor; distl; factorl)
open import FinEquivEquiv
  using ([id+id]≋id; +●≋●+; _+≋_;
         unite₊-nat; unite₊r-nat; uniti₊-nat; uniti₊r-nat;
         assocr₊-nat; assocl₊-nat; unite-assocr₊-coh; assocr₊-coh; 
         id*id≋id; *●≋●*; _*≋_;
         unite*-nat; unite*r-nat; uniti*-nat; uniti*r-nat;
         assocr*-nat; assocl*-nat; unite-assocr*-coh; assocr*-coh)

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

{--

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

--}

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
    ; commute = λ f → {!!} -- unite*-nat 
    }
  ; F⇐G = record
    { η = λ _ → uniti* 
    ; commute = λ f → {!!} -- unite*r-nat
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
    ;  commute = λ f → {!!} -- uniti*-nat
    }
  ; F⇐G = record 
    { η = λ X → uniti*r 
    ; commute = λ f → {!!} -- uniti*r-nat
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

{--
-- The monoidal structures are symmetric

x⊎y≈y⊎x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
x⊎y≈y⊎x = record 
  { F⇒G = record 
    { η = λ X → swap+ {m = X zero}
    ; commute = {!!} 
    } 
  ; F⇐G = record 
    { η = λ X → swap+ {m = X (suc zero)}
    ; commute = {!!} 
    } 
  ; iso = λ X → record
    { isoˡ = {!!} 
    ; isoʳ = {!!} 
    }
  }

BM⊎ : Braided CPM⊎
BM⊎ = record 
  { braid = x⊎y≈y⊎x 
  ; hexagon₁ = {!!} 
  ; hexagon₂ = {!!} 
  }

x×y≈y×x : NaturalIsomorphism ×h.x⊗y ×h.y⊗x
x×y≈y×x = record
  { F⇒G = record
    { η = λ X → swap* {m = X zero}
    ; commute = {!!} 
    }
  ; F⇐G = record
    { η = λ X → swap* {m = X (suc zero)} 
    ; commute = {!!} 
    }
  ; iso = λ X → record
    { isoˡ = {!!} 
    ; isoʳ = {!!} 
    }
  }

BM× : Braided CPM×
BM× = record 
  { braid = x×y≈y×x 
  ; hexagon₁ = {!!} 
  ; hexagon₂ = {!!} 
  }

SBM⊎ : Symmetric BM⊎
SBM⊎ = record { symmetry = {!!} }

SBM× : Symmetric BM×
SBM× = record { symmetry = {!!} }

-- And finally the multiplicative structure distributes over the
-- additive one

module r = BimonoidalHelperFunctors BM⊎ BM×

x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record
  { F⇒G = record
    { η = λ X → distl {m = X zero}
    ; commute = {!!}
    }
  ; F⇐G = record
    { η = λ X → factorl {m = X zero}
    ; commute = {!!}
    }
  ; iso = λ X → record { isoˡ = {!!} 
                       ; isoʳ = {!!} }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record
    { η = λ X → dist {m = X zero}
    ; commute = {!!}
    }
  ; F⇐G = record
    { η = λ X → factor {m = X zero}
    ; commute = {!!}
    }
  ; iso = λ X → record { isoˡ = {!!}
                       ; isoʳ = {!!} }
  }

x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
x⊗0≡0 = record
  { F⇒G = record
    { η = λ X → distzr {m = X zero}
    ; commute = {!!}
    }
  ; F⇐G = record
    { η = λ X → factorzr {n = X zero}
    ; commute = {!!}
    }
  ; iso = λ X → record
    { isoˡ = {!!} 
    ; isoʳ = {!!} 
    }
  }

0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
0⊗x≡0 = record
  { F⇒G = record
    { η = λ X → distz {m = X zero}
    ; commute = {!!}
    }
  ; F⇐G = record
    { η = λ X → factorz {m = X zero}
    ; commute = {!!}
    }
  ; iso = λ X → record
    { isoˡ = {!!}
    ; isoʳ = {!!}
    }
  }

TERig : RigCategory SBM⊎ SBM×
TERig = record
  { distribₗ = x⊗[y⊕z]≡[x⊗y]⊕[x⊗z]
  ; distribᵣ = [x⊕y]⊗z≡[x⊗z]⊕[y⊗z]
  ; annₗ = 0⊗x≡0
  ; annᵣ = x⊗0≡0
  ; laplazaI = {!!}
  ; laplazaII = {!!}
  ; laplazaIV = {!!}
  ; laplazaVI = {!!}
  ; laplazaIX = {!!}
  ; laplazaX = {!!}
  ; laplazaXI = {!!}
  ; laplazaXIII = {!!}
  ; laplazaXV = {!!}
  ; laplazaXVI = {!!}
  ; laplazaXVII = {!!}
  ; laplazaXIX = {!!}
  ; laplazaXXIII = {!!}
  }

--}

------------------------------------------------------------------------------
