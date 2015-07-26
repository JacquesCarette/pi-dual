{-# OPTIONS --without-K #-}

module CPermCat where

open import Level using (zero)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using () renaming (zero to 0F) 
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; sym; cong₂; isEquivalence)

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

--

open import ConcretePermutation
  using (CPerm; idp; symp; transp; _⊎p_; _×p_;
         unite+p; uniti+p; unite+rp; uniti+rp)

open import ConcretePermutationProperties
  using (assocp; lidp; ridp; linv; rinv;
         1p⊎1p≡1p; 1p×1p≡1p;
         ⊎p-distrib; ×p-distrib;
         unite+p∘[0⊎x]≡x∘unite+p; uniti+p∘x≡[0⊎x]∘uniti+p)

------------------------------------------------------------------------------
-- CPerm is is a category
-- Permutations can be compared by strict propositional equality

CPermCat : Category zero zero zero
CPermCat = record
  { Obj = ℕ
  ; _⇒_ = CPerm
  ; _≡_ = P._≡_ 
  ; id = idp
  ; _∘_ = transp
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → P.sym (assocp {p₁ = h} {g} {f})
  ; identityˡ = lidp
  ; identityʳ = ridp
  ; equiv = P.isEquivalence
  ; ∘-resp-≡ = λ { {_} {_} {_} {f} {.f} {g} {.g} P.refl P.refl → P.refl}
  }

-- ... and a groupoid

CPermGroupoid : Groupoid CPermCat
CPermGroupoid = record 
  { _⁻¹ = symp 
  ; iso = λ {_} {_} {f} → record { isoˡ = rinv f ; isoʳ = linv f } 
  }

-- additive bifunctor and monoidal structure

⊎p-bifunctor : Bifunctor CPermCat CPermCat CPermCat
⊎p-bifunctor = record
  { F₀ = λ { (n , m) → n + m }
  ; F₁ = λ { (p₁ , p₂) → p₁ ⊎p p₂ }
  ; identity = λ { {m , n} → 1p⊎1p≡1p {m} {n}}
  ; homomorphism = λ { {m₁ , m₂} {n₁ , n₂} {o₁ , o₂} {p₁ , p₂} {q₁ , q₂} →
      P.sym (⊎p-distrib {n₁} {n₂} {m₁} {m₂} {o₁} {o₂} {q₁} {q₂} {p₁} {p₂}) }
  ; F-resp-≡ = λ { (p₁≡p₃ , p₂≡p₄) → P.cong₂ _⊎p_ p₁≡p₃ p₂≡p₄ }
  }

-- the 0 below is the id from CPermMonoidal

module ⊎h = MonoidalHelperFunctors CPermCat ⊎p-bifunctor 0

0⊕x≡x : NaturalIsomorphism ⊎h.id⊗x ⊎h.x
0⊕x≡x = record
  { F⇒G = record { η = λ _ → unite+p
                 ; commute = λ f → unite+p∘[0⊎x]≡x∘unite+p (f 0F)
                 }
  ; F⇐G = record { η = λ _ → uniti+p
                  ; commute = λ f → uniti+p∘x≡[0⊎x]∘uniti+p (f 0F)
                  }
  ; iso = λ X → record { isoˡ = linv uniti+p ; isoʳ = linv unite+p }
  }

x⊕0≡x : NaturalIsomorphism ⊎h.x⊗id ⊎h.x
x⊕0≡x = record
  { F⇒G = record { η = λ _ → uniti+rp
                 ; commute = {!!}
                 } 
  ; F⇐G = record { η = λ _ → unite+rp
                 ; commute = {!!}
                 }
  ; iso = λ X → record { isoˡ = linv unite+rp ; isoʳ = linv uniti+rp }
  }

{--
[x⊕y]⊕z≡x⊕[y⊕z] : NaturalIsomorphism ⊎h.[x⊗y]⊗z ⊎h.x⊗[y⊗z]
[x⊕y]⊕z≡x⊕[y⊕z] = record
  { F⇒G = record
    { η = {!!} 
    ; commute = {!!} 
    }
  ; F⇐G = record
    { η = {!!} 
    ; commute = {!!} 
    }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  }

-- and a monoidal category (additive)

M⊕ : Monoidal CPermCat
M⊕ = record
  { ⊗ = ⊎p-bifunctor
  ; id = 0
  ; identityˡ = 0⊕x≡x
  ; identityʳ = x⊕0≡x
  ; assoc = [x⊕y]⊕z≡x⊕[y⊕z]
  ; triangle = {!!}
  ; pentagon = {!!}
  }

-- multiplicative bifunctor and monoidal structure

×p-bifunctor : Bifunctor CPermCat CPermCat CPermCat
×p-bifunctor = record
  { F₀ = λ { (m , n) → m * n}
  ; F₁ = λ { (p₁ , p₂) → p₁ ×p p₂ }
  ; identity = λ { {m , n} → 1p×1p≡1p {m} }
  ; homomorphism = λ { {_} {_} {_} {p₁ , p₂} {q₁ , q₂} →
      ×p-distrib {p₁ = q₁} {q₂} {p₁} {p₂}}
  ; F-resp-≡ = λ {(p₁≡p₃ , p₂≡p₄) → P.cong₂ _×p_ p₁≡p₃ p₂≡p₄ }
  }

module ×h = MonoidalHelperFunctors CPermCat ×p-bifunctor 1

1⊗x≡x : NaturalIsomorphism ×h.id⊗x ×h.x
1⊗x≡x = record 
  { F⇒G = record
    { η = {!!} 
    ; commute = {!!}
    }
  ; F⇐G = record
    { η = {!!} 
    ; commute = {!!}
    }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  }

x⊗1≡x : NaturalIsomorphism ×h.x⊗id ×h.x
x⊗1≡x = record
  { F⇒G = record
    { η = {!!} 
    ; commute = {!!} 
    }
  ; F⇐G = record
    { η = {!!} 
    ; commute = {!!} 
    }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  }

[x⊗y]⊗z≡x⊗[y⊗z] : NaturalIsomorphism ×h.[x⊗y]⊗z ×h.x⊗[y⊗z]
[x⊗y]⊗z≡x⊗[y⊗z] = record
  { F⇒G = record
    { η = {!!} 
    ; commute = {!!} 
    }
  ; F⇐G = record
    { η = {!!}
    ; commute = {!!} 
    }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  }

-- and a monoidal category (multiplicative)

M⊗ : Monoidal CPermCat
M⊗ = record
  { ⊗ = ×p-bifunctor
  ; id = 1
  ; identityˡ = 1⊗x≡x
  ; identityʳ = x⊗1≡x
  ; assoc = [x⊗y]⊗z≡x⊗[y⊗z]
  ; triangle = {!!}
  ; pentagon = {!!}
  }

x⊕y≡y⊕x : NaturalIsomorphism ⊎h.x⊗y ⊎h.y⊗x
x⊕y≡y⊕x = record 
  { F⇒G = record { η = {!!} ; commute = {!!} }
  ; F⇐G = record { η = {!!} ; commute = {!!} }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} } }

BM⊕ : Braided M⊕
BM⊕ = record
  { braid = x⊕y≡y⊕x
  ; hexagon₁ = {!!}
  ; hexagon₂ = {!!}
  }

x⊗y≡y⊗x : NaturalIsomorphism ×h.x⊗y ×h.y⊗x
x⊗y≡y⊗x = record 
  { F⇒G = record { η = {!!} ; commute = {!!} }
  ; F⇐G = record { η = {!!} ; commute = {!!} }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} } }

BM⊗ : Braided M⊗
BM⊗ = record
  { braid = x⊗y≡y⊗x
  ; hexagon₁ = {!!} 
  ; hexagon₂ = {!!} 
  }

-- with both monoidal structures being symmetric

SBM⊕ : Symmetric BM⊕
SBM⊕ = record { symmetry = {!!} }

SBM⊗ : Symmetric BM⊗
SBM⊗ = record { symmetry = {!!} }

module r = BimonoidalHelperFunctors BM⊕ BM⊗

x⊗0≡0 : NaturalIsomorphism r.x⊗0 r.0↑
x⊗0≡0 = record 
  { F⇒G = record
    { η = {!!} 
    ; commute = {!!} 
    } 
  ; F⇐G = record
    { η = {!!} 
    ; commute = {!!} 
    } 
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} } 
  }

0⊗x≡0 : NaturalIsomorphism r.0⊗x r.0↑
0⊗x≡0 = record
  { F⇒G = record { η = {!!} ; commute = {!!} }
  ; F⇐G = record { η = {!!} ; commute = {!!} }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  }

x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] : NaturalIsomorphism r.x⊗[y⊕z] r.[x⊗y]⊕[x⊗z]
x⊗[y⊕z]≡[x⊗y]⊕[x⊗z] = record
  { F⇒G = record { η = {!!} ; commute = {!!} }
  ; F⇐G = record { η = {!!} ; commute = {!!} }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  }

[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] : NaturalIsomorphism r.[x⊕y]⊗z r.[x⊗z]⊕[y⊗z]
[x⊕y]⊗z≡[x⊗z]⊕[y⊗z] = record
  { F⇒G = record { η = {!!} ; commute = {!!} }
  ; F⇐G = record { η = {!!} ; commute = {!!} }
  ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
  }

-- and the multiplicative structure distributing over the additive one

Pi1Rig : RigCategory SBM⊕ SBM⊗
Pi1Rig = record 
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
  ; laplazaXVI =  {!!} 
  ; laplazaXVII = {!!} 
  ; laplazaXIX = {!!} 
  ; laplazaXXIII = {!!} 
  }

--}
------------------------------------------------------------------------------
