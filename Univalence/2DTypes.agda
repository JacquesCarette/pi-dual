{-# OPTIONS --without-K #-}

module 2DTypes where

-- open import Level renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary using (Setoid)
open import Data.Nat using (ℕ) renaming (suc to ℕsuc; _+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; lookup; _∷_; []; zipWith)
open import Data.Integer hiding (suc)

open import VectorLemmas using (_!!_)
open import PiU
open import PiLevel0 hiding (!!)
open import PiEquiv
open import PiLevel1
open import Equiv
open import EquivEquiv using (_≋_; module _≋_)

open import Categories.Category
open import Categories.Groupoid
open import Categories.Equivalence.Strong

-- This exists somewhere, but I can't find it
⊎-inj : ∀ {ℓ} {A B : Set ℓ} {a : A} {b : B} → inj₁ a ≡ inj₂ b → ⊥
⊎-inj ()

-- should probably make this level-polymorphic
record Typ : Set where
  constructor typ
  field
    carr : U
    len : ℕ -- number of non-trivial automorphisms
    auto : Vec (carr ⟷ carr) (ℕsuc len) -- the real magic goes here

    -- normally the stuff below is "global", but here
    -- we attach it to a type.
    id : id⟷ ⇔ (auto !! zero)
    _⊙_ : Fin (ℕsuc len) → Fin (ℕsuc len) → Fin (ℕsuc len)
    coh : ∀ (i j : Fin (ℕsuc len)) → -- note the flip !!!
        ((auto !! i) ◎ (auto !! j) ⇔ (auto !! (j ⊙ i))) 
    -- to get groupoid, we need inverse knowledge, do later
    
open Typ

-- The above 'induces' a groupoid structure, which
-- we need to show in detail.
-- First, a useful container for the info we need:
record Hm (t : Typ) (a b : ⟦ carr t ⟧) : Set where
  constructor hm
  field
    eq : carr t ⟷ carr t
    good : Σ (Fin (ℕsuc (len t))) (λ n → eq ⇔ (auto t !! n))
    fwd : proj₁ (c2equiv eq) a ≡ b
    bwd : isqinv.g (proj₂ (c2equiv eq)) b ≡ a
    
-- note how (auto t) is not actually used!
-- also: not sure e₁ and e₂ always used coherently, as types are not enough
--  to decide which one to use...
induceCat : Typ → Category _ _ _
induceCat t = record
  { Obj =  ⟦ carr t ⟧
  ; _⇒_ = Hm t
  ; _≡_ = λ { (hm e₁ g₁ _ _) → λ { (hm e₂ g₂ _ _) → e₁ ⇔ e₂} }
  ; id = hm id⟷ (zero , id t) refl refl
  ; _∘_ = λ { {A} {B} {C} (hm e₁ (n₁ , p₁) fwd₁ bwd₁) (hm e₂ (n₂ , p₂) fwd₂ bwd₂) →  
   let pf₁ = (begin (
        proj₁ (c2equiv e₁ ● c2equiv e₂) A
          ≡⟨ β₁ A ⟩
        (proj₁ (c2equiv e₁) ∘ (proj₁ (c2equiv e₂))) A
          ≡⟨ cong (proj₁ (c2equiv e₁)) fwd₂ ⟩
        proj₁ (c2equiv e₁) B
          ≡⟨ fwd₁ ⟩
        C ∎ ))
       -- same as above (in opposite direction), just compressed
       pf₂ = trans (β₂ C)
            (trans (cong (isqinv.g (proj₂ (c2equiv e₂))) bwd₁)
                   bwd₂)
       n₃ = _⊙_ t n₁ n₂
       compos = n₃ , trans⇔ (p₂ ⊡ p₁) (coh t n₂ n₁)
   in
        hm (e₂ ◎ e₁) compos pf₁ pf₂ }
  ; assoc = assoc◎l
  ; identityˡ = idr◎l
  ; identityʳ = idl◎l
  ; equiv = record { refl = id⇔ ; sym = 2! ; trans = trans⇔ }
  ; ∘-resp-≡ = λ f g → g ⊡ f
  }
  where open Typ
        open ≡-Reasoning

{- 
 -- to get the Groupoid structure, there is stuff in the type that is
 -- missing; see the hole.
induceG : (t : Typ)  → Groupoid (induceCat t)
induceG t = record
  { _⁻¹ = λ { {A} {B} (hm e g fw bw) →
    hm (! e) {!!} (trans (f≡ (!≡sym≃ e) B) bw) (trans (g≡ (!≡sym≃ e) A) fw) }
  ; iso = record { isoˡ = linv◎l ; isoʳ = rinv◎l }
  }
  where open _≋_
-}

-- some useful functions for defining the type 1T
private
  mult : Fin 1 → Fin 1 → Fin 1
  mult zero zero = zero
  mult _ (suc ())
  mult (suc ()) _

  triv : Vec (ONE ⟷ ONE) 1
  triv = id⟷ ∷ []
  
  mult-coh : ∀ (i j : Fin 1) →
        ((triv !! i) ◎ (triv !! j) ⇔ (triv !! (mult j i)))
  mult-coh zero zero = idl◎l -- note how this is non-trivial!
  mult-coh _ (suc ())
  mult-coh (suc ()) _
  
1T : Typ
1T = record
  { carr = ONE
  ; len = 0
  ; auto = triv
  ; id = id⇔
  ; _⊙_ = mult
  ; coh = mult-coh
  }

BOOL : U
BOOL = PLUS ONE ONE

-- some useful functions for defining the type 1T′
private
  mult′ : Fin 2 → Fin 2 → Fin 2
  mult′ zero zero = zero
  mult′ zero (suc zero) = suc zero
  mult′ _ (suc (suc ()))
  mult′ (suc zero) zero = suc zero
  mult′ (suc zero) (suc zero) = zero
  mult′ (suc (suc ())) _

  sw : Vec (BOOL ⟷ BOOL) 2
  sw = id⟷ ∷ swap₊ ∷ []

  sw-coh :  ∀ (i j : Fin 2) →
        ((sw !! i) ◎ (sw !! j) ⇔ (sw !! (mult′ j i)))
  sw-coh zero zero = idl◎l
  sw-coh zero (suc zero) = idl◎l
  sw-coh _ (suc (suc ()))
  sw-coh (suc zero) zero = idr◎l
  sw-coh (suc zero) (suc zero) = linv◎l
  sw-coh (suc (suc ())) _
  
1T′ : Typ
1T′ = record
  { carr = BOOL
  ; len = 1
  ; auto = sw
  ; id = id⇔
  ; _⊙_ = mult′
  ; coh = sw-coh
  }

-- useful utilities
private
  collapse : ⊤ ⊎ ⊤ → ⊤
  collapse (inj₁ a) = a
  collapse (inj₂ b) = b

  collapse-coh : ∀ {A B : ⊤ ⊎ ⊤} → collapse A ≡ collapse B
  collapse-coh {inj₁ tt} {inj₁ tt} = refl
  collapse-coh {inj₁ tt} {inj₂ tt} = refl
  collapse-coh {inj₂ tt} {inj₁ tt} = refl
  collapse-coh {inj₂ tt} {inj₂ tt} = refl
  
-- let's do it on categories only.
-- The important thing here is that we only have
-- access to id⟷ and (auto 1T′) as things of type
-- (carr 1T′ ⟷ carr 1T′).
1T≃1T′ : StrongEquivalence (induceCat 1T) (induceCat 1T′)
1T≃1T′ =
  record
  -- from 1T to 1T′, we really do want to map down to id⟷ onto inj₁
  { F = record
    { F₀ = inj₁
    ; F₁ = λ { {tt} {tt} (hm e g fwd bwd) → hm id⟷ (zero , id⇔) refl refl}
    ; identity = id⇔
    ; homomorphism = idl◎r
    ; F-resp-≡ = λ _ → id⇔
    }
  -- and here, everything should be collapsed
  ; G = record
    { F₀ = collapse
    ; F₁ = λ { {A} {B} (hm e g fwd bwd) →
        hm id⟷ (zero , id⇔) (collapse-coh {A} {B}) (collapse-coh {B} {A})}
    ; identity = id⇔
    ; homomorphism = idl◎r
    ; F-resp-≡ = λ _ → id⇔
    }
  -- and here is where (auto 1T′) is needed, else this is false!!
  ; weak-inverse = record
    { F∘G≅id = record
      { F⇒G = record
        { η = λ { (inj₁ a) → hm id⟷ (zero , id⇔) refl refl;
                  (inj₂ b) → hm swap₊ (suc zero , id⇔) refl refl }
        ; commute = 
          λ { {inj₁ tt} {inj₁ tt} (hm c (zero , x) _ _) →  trans⇔ idl◎l (trans⇔ (2! x) idl◎r) ;
              {inj₁ tt} {inj₁ tt} (hm c (suc zero , x) a b) →
                  ⊥-elim (⊎-inj (
                    trans (sym a) (
                    trans (sym (lemma0 c (inj₁ tt)))
                          (≋⇒≡ x (inj₁ tt))))) ;
              {inj₁ tt} {inj₁ tt} (hm c (suc (suc ()), _) _ _);
              {inj₁ tt} {inj₂ tt} (hm c (zero , x) a b) → 
                ⊥-elim (⊎-inj (
                  trans (sym (≋⇒≡ x (inj₁ tt))) (
                  trans (lemma0 c (inj₁ tt))
                         a ) ) );
              {inj₁ tt} {inj₂ tt} (hm c (suc zero , x) _ _) →
                trans⇔ idl◎l (trans⇔ (2! x) idl◎r) ;
              {inj₁ tt} {inj₂ tt} (hm c (suc (suc ()), _) _ _);
              {inj₂ tt} {inj₁ tt} (hm c (zero , x) a b) → 
                ⊥-elim (⊎-inj (
                  trans (sym a) (
                  trans (sym (lemma0 c (inj₂ tt)))
                        (≋⇒≡ x (inj₂ tt)) ) ) );
              {inj₂ tt} {inj₁ tt} (hm c (suc (suc ()), _) _ _);
              {inj₂ tt} {inj₂ tt} (hm c (zero , x) _ _) → 
                trans⇔ idl◎l (trans⇔ idr◎r (id⇔ ⊡ (2! x)));
              {inj₂ tt} {inj₁ tt} (hm c (suc zero , x) _ _) → 
                trans⇔ idl◎l (trans⇔ linv◎r (id⇔ ⊡ (2! x)));
              {inj₂ tt} {inj₂ tt} (hm c (suc zero , x) a b) → 
                ⊥-elim (⊎-inj (
                  trans (sym (≋⇒≡ x (inj₂ tt))) (
                   trans (lemma0 c (inj₂ tt)) a) ) ) ;
              {inj₂ tt} {inj₂ tt} (hm c (suc (suc ()), _) _ _) 
            }
          }
      ; F⇐G = record
        { η = λ { (inj₁ a) → hm id⟷ (zero , id⇔) refl refl;
                  (inj₂ b) → hm swap₊ ((suc zero , id⇔)) refl refl }
        ; commute = λ
          { {inj₁ tt} {inj₁ tt} (hm a (zero , e) c d) → e ⊡ id⇔
          ; {inj₁ tt} {inj₂ tt} (hm a (zero , e) c d) → {!!}
          ; {inj₂ tt} {inj₁ tt} (hm a (zero , e) c d) → {!!}
          ; {inj₂ tt} {inj₂ tt} (hm a (zero , e) c d) → trans⇔ (e ⊡ id⇔) (trans⇔ idl◎l idr◎r)
          ; {inj₁ tt} {inj₁ tt} (hm a (suc zero , e) c d) → {!!}
          ; {inj₁ tt} {inj₂ tt} (hm a (suc zero , e) c d) → {!!}
          ; {inj₂ tt} {inj₁ tt} (hm a (suc zero , e) c d) → {!!}
          ; {inj₂ tt} {inj₂ tt} (hm a (suc zero , e) c d) → {!!}
          ; (hm a (suc (suc ()) , _) _ _) }
        }
      ; iso = λ { (inj₁ tt) → record { isoˡ = idl◎l ; isoʳ = idl◎l };
                  (inj₂ tt) → record { isoˡ = linv◎l ; isoʳ = linv◎l } }
      }
    ; G∘F≅id = record
      { F⇒G = record
        { η = λ {tt → hm id⟷ (zero , id⇔) refl refl}
        ; commute =
          λ { {tt} {tt} (hm eq (zero , e) _ _) → id⇔ ⊡ (2! e)
            ; {tt} {tt} (hm eq (suc () , _) _ _) }
        }
      ; F⇐G = record
        { η = λ {tt → hm id⟷ (zero , id⇔) refl refl}
        ; commute =
          λ { {tt} {tt} (hm c (zero , e) _ _) → e ⊡ id⇔
            ; {tt} {tt} (hm c (suc () , _) _ _) }
        }
      ; iso = λ {tt → record { isoˡ = linv◎l ; isoʳ = linv◎l } }
      }
    }
  }

-- And so 1T′ is equivalent to 1T.  This can be interpreted to mean
-- that swap₊ (perhaps more precisely, id⟷ ∷ swap₊ ∷ [] ) is the
-- representation of a 'negative type'.

---------------
-- Cardinality function
card : Typ → ℤ
card (typ carr len _ _ _ _) = (+ size carr) - (+ len)

-- check
card-1T : card 1T ≡ + 1
card-1T = refl

card-1T′ : card 1T′ ≡ + 1
card-1T′ = refl

--------------
-- Conjecture...

-- to make this work, we're going to postulate another loop
-- and that it is idempotent:
postulate
  loop : ZERO ⟷ ZERO
  idemp : loop ◎ loop ⇔ loop
  
private
  cc : Fin 2 → Fin 2 → Fin 2
  cc zero zero = zero
  cc zero (suc zero) = suc zero
  cc (suc zero) zero = suc zero
  cc (suc zero) (suc zero) = suc zero
  cc (suc (suc ())) _
  cc _ (suc (suc ()))

  two-loops : Vec (ZERO ⟷ ZERO) 2
  two-loops = id⟷ ∷ loop ∷ []

  tl-coh :   ∀ (i j : Fin 2) →
        ((two-loops !! i) ◎ (two-loops !! j) ⇔ (two-loops !! (cc j i)))
  tl-coh zero zero = idl◎l
  tl-coh zero (suc zero) = idl◎l
  tl-coh (suc zero) zero = idr◎l
  tl-coh (suc zero) (suc zero) = {!idemp!}
  tl-coh (suc (suc ())) _
  tl-coh _ (suc (suc ()))
  
-1T : Typ
-1T = typ ZERO 1 two-loops id⇔ cc tl-coh

card--1T : card -1T ≡ -[1+ 0 ] -- indeed -1 ...
card--1T = refl

{--
Here is my current thinking:

* A type is a package of:
 - a carrier (that comes with the trivial automorphism)
 - a collection of non-trivial automorphisms that have a groupoid structure
 Let’s denote this package by ‘R A (Auto A)'

* The collection of non-trivial automorphisms could very well be
  missing (i.e., empty) and we then recover plain sets like Bool etc.

* Now here is the interesting bit: the carrier itself could be
  missing, i.e., a parameter. In that case we get something like:

 A -> R A (Auto A)

 That thing could be treated as outside the universe of types but we
 are proposing to enlarge the universe of type to also include it as a
 fractional type. Of course we need a way to combine such a fractional
 type with a carrier to get a regular type so we need another
 operation _[_] to do the instantiation.

* So to revise, a type is:

 T ::= R A (Auto A)    |    /\ A . T    |     T[A] 

To make sure this behaves like fractional types, we want /\ A. T and
T[A] to behave like a product. It is a product of course but a
dependent one.
--}

-- Parameterized type
-- Frac supposed to 1/t
-- instantiate Frac with u to get u/t
-- make sure t/t is 1
-- define eta and epsilon and check axioms

{-- Syntax of types --}

Auto : (u : U) → Set
Auto u = Σ[ n ∈ ℕ ] (Vec (u ⟷ u) n)

trivA : (u : U) → Auto u
trivA u = (1 , id⟷ ∷ [])

data T : (u₁ : U) → {u₂ : U} → Auto u₂ → Set where
  UT : (u : U) → T u (trivA u) -- regular sets
  FT : (u₁ u₂ : U) → (auto₂ : Auto u₂) → T u₁ auto₂

-- Regular sets

ZT : T ZERO (trivA ZERO)
ZT = UT ZERO

OT : T ONE (trivA ONE)
OT = UT ONE

-- one third

2U : U
2U = PLUS ONE ONE

3U : U
3U = PLUS ONE (PLUS ONE ONE)

3T : T 3U (trivA 3U)
3T = UT 3U

-- could add the remaining two but these are sufficient I think
all3A : Auto 3U
all3A = (4 , id⟷ ∷
             (id⟷ ⊕ swap₊) ∷
             (assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊) ∷
             ((id⟷ ⊕ swap₊) ◎ (assocl₊ ◎ (swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)) ∷
             [])

1/3T : T ONE all3A 
1/3T = FT ONE 3U all3A

-- notice that a/b + c/b = (a+c) / b
-- So 1/3T + 1/3T is

2/3T : T 2U all3A
2/3T = FT 2U 3U all3A

-- one more

3/3T : T 3U all3A
3/3T = FT 3U 3U all3A

-- Now eta applied to 3/3T should match the carrier with the autos and produce the plain OT



