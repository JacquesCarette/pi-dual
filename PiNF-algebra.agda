module PiNF-algebra where

-- open import Data.Nat hiding (_⊔_; suc; _+_; _*_)
-- open import Data.Vec 
-- open import Data.Empty
-- open import Data.Unit
-- open import Data.Sum hiding (map)
open import Data.Product hiding (map)
-- open import Function
open import Level
-- open import Relation.Binary.PropositionalEquality hiding (sym)
open import Relation.Binary.Core
open import Algebra
import Algebra.FunctionProperties as FunctionProperties
open import Algebra.FunctionProperties.Core 
open import Algebra.Structures

open import PiNF-syntax

------------------------------------------------------------------------------
-- Establish that Pi syntactically is a commutative semiring

⟷IsEquivalence : IsEquivalence _⟷_
⟷IsEquivalence = record {
    refl = id⟷ ;
    sym = sym  ;
    trans = _◎_ 
  } 

+IsSemigroup : IsSemigroup _⟷_ PLUS
+IsSemigroup = record {
    isEquivalence = ⟷IsEquivalence ;
    assoc = λ x y z → assocr₊ {x} {y} {z} ;
    ∙-cong = _⊕_
  }

+0IsMonoid : IsMonoid _⟷_ PLUS ZERO
+0IsMonoid = record {
    isSemigroup = +IsSemigroup ;
    identity = ((λ x → unite₊ {x}) , 
                (λ x → swap₊ ◎ unite₊ {x}))
  }

+0IsCommutativeMonoid : IsCommutativeMonoid _⟷_ PLUS ZERO
+0IsCommutativeMonoid = record {
    isSemigroup = +IsSemigroup ;
    identityˡ = λ x → unite₊ {x} ;
    comm = λ x y → swap₊ {x} {y} 
  }

+0CommutativeMonoid : CommutativeMonoid _ _
+0CommutativeMonoid = record {
  Carrier = B ;
  _≈_ = _⟷_ ; 
  _∙_ = PLUS ;
  ε = ZERO ;
  isCommutativeMonoid = +0IsCommutativeMonoid  
  }

-- 

⋆IsSemigroup : IsSemigroup _⟷_ TIMES
⋆IsSemigroup = record {
    isEquivalence = ⟷IsEquivalence ;
    assoc = λ x y z → assocr⋆ {x} {y} {z} ;
    ∙-cong = _⊗_
  }

⋆1IsMonoid : IsMonoid _⟷_ TIMES ONE
⋆1IsMonoid = record {
    isSemigroup = ⋆IsSemigroup ;
    identity = ((λ x → unite⋆ {x}) , 
                (λ x → swap⋆ ◎ unite⋆ {x}))
  }  

⋆1IsCommutativeMonoid : IsCommutativeMonoid _⟷_ TIMES ONE
⋆1IsCommutativeMonoid = record {
    isSemigroup = ⋆IsSemigroup ;
    identityˡ = λ x → unite⋆ {x} ;
    comm = λ x y → swap⋆ {x} {y} 
  }  

⋆1CommutativeMonoid : CommutativeMonoid _ _ 
⋆1CommutativeMonoid = record {
  Carrier = B ;
  _≈_ = _⟷_ ; 
  _∙_ = TIMES ;
  ε = ONE ;
  isCommutativeMonoid = ⋆1IsCommutativeMonoid
  }

record IsCommutativeSemiringWithoutAnnihilatingZero
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (0# 1# : A) 
       : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    *-isCommutativeMonoid : IsCommutativeMonoid ≈ * 1#
    distrib               : * DistributesOver +

record CommutativeSemiringWithoutAnnihilatingZero c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    _+_ : Op₂ Carrier
    _*_ : Op₂ Carrier
    0# : Carrier
    1# : Carrier
    isCommutativeSemiringWithoutAnnihilatingZero : 
      IsCommutativeSemiringWithoutAnnihilatingZero _≈_ _+_ _*_ 0# 1#

B-isCommutativeSemiringWithoutAnnihilatingZero
    : IsCommutativeSemiringWithoutAnnihilatingZero _⟷_ PLUS TIMES ZERO ONE
B-isCommutativeSemiringWithoutAnnihilatingZero = record {
    +-isCommutativeMonoid = +0IsCommutativeMonoid ;
    *-isCommutativeMonoid = ⋆1IsCommutativeMonoid ;
    distrib = ( (λ x y z → dist' {x} {y} {z}) ,
                (λ x y z → dist {y} {z} {x} ))
    }

------------------------------------------------------------------------------
-- Establish that Pi+negatives+fractionals syntactically is a meadow

+0-IsGroup : IsGroup _⟷_ PLUS ZERO NEG
+0-IsGroup = record {
  isMonoid = +0IsMonoid ; 
  inverse = ( (λ x → swap₊ ◎ ε₊ {x}) , 
              (λ x → ε₊ {x}) );
  ⁻¹-cong = neg
  }

+0-IsAbelianGroup : IsAbelianGroup _⟷_ PLUS ZERO NEG
+0-IsAbelianGroup = record {
    isGroup = +0-IsGroup ; 
    comm = λ x y → swap₊ {x} {y} 
  }

B-IsRing : IsRing _⟷_ PLUS TIMES NEG ZERO ONE
B-IsRing = record {
    +-isAbelianGroup = +0-IsAbelianGroup ; 
    *-isMonoid = ⋆1IsMonoid ;
    distrib = ( (λ x y z → dist' {x} {y} {z}) ,
                (λ x y z → dist {y} {z} {x} ))
  }

B-IsCommutativeRing : IsCommutativeRing _⟷_ PLUS TIMES NEG ZERO ONE
B-IsCommutativeRing = record {
    isRing = B-IsRing ;
    *-comm = λ x y → swap⋆ {x} {y} 
  }

-- 

B-CommutativeRing : CommutativeRing _ _
B-CommutativeRing = record {
    Carrier = B ;
    _≈_ = _⟷_ ; 
    _+_ = PLUS ;
    _*_ = TIMES ;
    -_ = NEG ;
    0# = ZERO ;
    1# = ONE ;
    isCommutativeRing = B-IsCommutativeRing
  } 

-- 

record IsMeadow
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (- r : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +*-isCommutativeRing : IsCommutativeRing ≈ + * - 0# 1#
    *-refl-l : ∀ x → ≈ (r (r x)) x
    *-refl-r : ∀ x → ≈ x (r (r x))
    *-ril-l : ∀ x → ≈ (* x (* x (r x))) x
    *-ril-r : ∀ x → ≈ x (* x (* x (r x)))
    r-cong : ∀ x y → ≈ x y → ≈ (r x) (r y)

record Meadow c ℓ : Set (suc (c ⊔ ℓ)) where
  field 
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    _+_ : Op₂ Carrier
    _*_ : Op₂ Carrier
    -_ : Op₁ Carrier
    r  : Op₁ Carrier
    0# : Carrier
    1# : Carrier
    isMeadow : IsMeadow _≈_ _+_ _*_ -_ r 0# 1#

B-/IsMeadow : IsMeadow _⟷_ PLUS TIMES NEG RECIP ZERO ONE
B-/IsMeadow = record {
    +*-isCommutativeRing = B-IsCommutativeRing ;
    *-refl-l = λ x → refe⋆ {x} ;
    *-refl-r = λ x → sym (refe⋆ {x}) ;
    *-ril-l = λ x → sym (rili⋆ {x}) ;
    *-ril-r = λ x → rili⋆ {x} ;
    r-cong = λ x y → recip {x} {y} 
  }

B-/Meadow : Meadow _ _
B-/Meadow = record {
    Carrier = B ;
    _≈_ = _⟷_ ;
    _+_ = PLUS ;
    _*_ = TIMES ; 
    -_ = NEG ;
    r  = RECIP ;
    0# = ZERO ;
    1# = ONE ;
    isMeadow = B-/IsMeadow
  }

------------------------------------------------------------------------------
