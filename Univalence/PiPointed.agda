{-# OPTIONS --without-K #-}

module PiPointed where

open import Level using (_⊔_) renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Functor using (Functor)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Relation.Binary.PropositionalEquality as P
open import Function using (flip)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Data.Integer using (ℤ;+_;-[1+_]) renaming (suc to ℤsuc; -_ to ℤ-; _+_ to _ℤ+_)

open import Data.List using (List; foldr; replicate; _++_) renaming (map to Lmap; [] to nil; _∷_ to _∷:_)
open import Data.List.Any using (module Membership-≡; here; there)
open Membership-≡
open import Data.List.Properties using ()

open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid using () renaming (Product to GProduct)

open import PiU using (U; ZERO; ONE; PLUS; TIMES; toℕ)
open import PiLevel0
open import PiLevel1
open import PiEquiv renaming (eval to ap; evalB to apB)
open import Equiv

infix 40 _^_

data Pointed (t : U) : Set where
  ∙ : ⟦ t ⟧ → Pointed t

-- yes, re-use name eval on purpose here
eval : {t₁ t₂ : U} → (t₁ ⟷ t₂) → Pointed t₁ → Pointed t₂
eval c (∙ x) = ∙ (ap c x)

-- all our values will be 'subtypes' of this:
record V (t : U) : Set where
  constructor v
  field
    pt : ⟦ t ⟧
    auto : t ⟷ t

evalV : {t₁ t₂ : U} → (t₁ ⟷ t₂) → V t₁ → V t₂
evalV c (v pt auto) = v (ap c pt) (! c ◎ auto ◎ c)

-- V equivalence
record _≈_ {t : U} (a : V t) (b : V t) : Set where
  constructor veq
  field
    pt-eq : V.pt a P.≡ V.pt b
    auto-eq : V.auto a ⇔ V.auto b
    
-- and in general, all our morphisms will be 'subtypes' of
record H {s t : U} (a : V s) (b : V t) : Set where
  constructor mor
  field
    transp : s ⟷ t
    t-eq : evalV transp a ≈ b

--- Generating sets: lists of combinators over a type
GenSet : U → Set
GenSet t = List (t ⟷ t)

-- We will need to use a choice between 3 things.  Don't want
-- to abuse ⊎.  The 3 things can be understood as
-- Forward, Backward and Neutral.  So we name it ⇕.
infix 30 _⇕_

data _⇕_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  Fwd : (x : A) → A ⇕ B
  Bwd : (y : B) → A ⇕ B
  Neu :           A ⇕ B
  
-- note that this uses ≡ (inside ∈), not ⇔.  On purpose.
inGS : {t : U} → GenSet t → Set
inGS {t} S = Σ (t ⟷ t) (λ p → (p ∈ S) ⇕ (p ∈ S))

-- flip a ⇕
flip⇕ : ∀ {a b} {A : Set a} {B : Set b} → A ⇕ B → B ⇕ A
flip⇕ (Fwd x) = Bwd x
flip⇕ (Bwd y) = Fwd y
flip⇕ Neu = Neu

-- type of sequences of applications from GenSet
CombS : {t : U} → GenSet t → Set
CombS {t} S = List ( inGS S )

extract : {t : U} {S : GenSet t} → inGS S → (t ⟷ t)
extract (p , Fwd x) = p
extract (p , Bwd y) = ! p
extract (p , Neu  ) = id⟷

interp : {t : U} {S : GenSet t} → CombS S → (t ⟷ t)
interp l = foldr _◎_ id⟷ (Lmap extract l)

-- the combinator (CombS S) acts as a sort of reference point
data U↑ : Set where
  ↑ : U → U↑
  # : {τ : U} → (S : GenSet τ) → CombS S → U↑
  1/ : {τ : U} → (S : GenSet τ) → CombS S → U↑
  _⊞_ : U↑ → U↑ → U↑
  _⊠_ : U↑ → U↑ → U↑
  
infix 40 _⇿_

data _⇿_ : U↑ → U↑ → Set where
  ↑ : {t₁ t₂ : U} → t₁ ⟷ t₂  → ↑ t₁ ⇿ ↑ t₂
  ev : {t₁ : U} {S : GenSet t₁} → (q : CombS S) → ((# S q) ⊠ (1/ S q)) ⇿ ↑ ONE
  coev : {t₁ : U} {S : GenSet t₁} → (q : CombS S) → ↑ ONE ⇿ ((# S q) ⊠ (1/ S q))
  id⇿ : {t₁ : U↑} → t₁ ⇿ t₁ -- needed for coev of ⊠

UG : Universe l0 (lsuc l0)
UG = record {
    U = U↑
 ;  El = λ T → Σ[ ℂ ∈ Category l0 l0 l0 ] (Groupoid ℂ)
 }

-- for convenience, create some types which are embedable into V
D : U → Set
D t = ⟦ t ⟧

embedD : {t : U} → D t → V t
embedD w = v w id⟷

-- and D equality lifts to ≈
embedDeq : {τ : U} → (s t : D τ) → s ≡ t → embedD s ≈ embedD t
embedDeq s .s P.refl = veq P.refl id⇔

-- even more to the point, it lifts to describing Hom sets
-- note how we can't use embedDeq directly!
embedDHom : {τ : U} → (s t : D τ) → s ≡ t → H (embedD s) (embedD t)
embedDHom s .s P.refl = mor id⟷ (veq P.refl (trans⇔ idl◎l idl◎l))

-- this is the same as in 2DTypes/groupoid
discreteC : U → Category _ _ _
discreteC t = record {
     Obj = D t
    ; _⇒_ = λ s₁ s₂ → s₁ P.≡ s₂ -- see embedDHom
    ; _≡_ = λ _ _ → ⊤ -- hard-code proof-irrelevance
    ; id = P.refl 
    ; _∘_ = flip P.trans
    ; assoc = tt 
    ; identityˡ = tt 
    ; identityʳ = tt
    ; equiv = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }  
    ; ∘-resp-≡ = λ _ _ → tt
    }
-- ditto
discreteG : (t : U) → Groupoid (discreteC t)
discreteG S = record
  { _⁻¹ = λ { {A} {.A} refl → P.refl }
  ; iso = record { isoˡ = tt; isoʳ = tt }
  }

-----------

--- Structure theorems for ⇕
extract-GS[]≡id⟷ : ∀ {t : U} → (gs : GenSet t) → gs ≡ nil →
  (∀ (y : inGS gs) → extract y ≡ id⟷)
extract-GS[]≡id⟷ .nil refl (p , Fwd ())
extract-GS[]≡id⟷ .nil refl (p , Bwd ())
extract-GS[]≡id⟷ .nil refl (p , Neu) = refl

_^_ : {τ : U} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = id⟷
p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

-- useful properties of ^
-- because ^ is iterated composition of the same thing,
-- then by associativity, we can hive off compositions
-- from left or right

assoc1 : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  (p ◎ (p ^ (+ m))) ⇔ ((p ^ (+ m)) ◎ p)
assoc1 ℕ.zero = trans⇔ idr◎l idl◎r
assoc1 (suc m) = trans⇔ (id⇔ ⊡ assoc1 m) assoc◎l

assoc1- : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  ((! p) ◎ (p ^ -[1+ m ])) ⇔ ((p ^ -[1+ m ]) ◎ (! p))
assoc1- ℕ.zero = id⇔
assoc1- (suc m) = trans⇔ (id⇔ ⊡ assoc1- m) assoc◎l

-- Property of ^: negating exponent is same as
-- composing in the other direction, then reversing.
^⇔! : {τ : U} → {p : τ ⟷ τ} → (k : ℤ) →
  (p ^ (ℤ- k)) ⇔ ! (p ^ k)
^⇔! (+_ ℕ.zero) = id⇔
-- need to dig deeper, as we end up negating
^⇔! (+_ (suc ℕ.zero)) = idl◎r
^⇔! (+_ (suc (suc n))) = trans⇔ (assoc1- n) (^⇔! (+ suc n) ⊡ id⇔)
^⇔! {p = p} (-[1+_] ℕ.zero) = trans⇔ idr◎l (2! !!⇔id) -- (!!⇔id {c = p})
^⇔! {p = p} (-[1+_] (suc n)) =
  trans⇔ (assoc1 (suc n)) ((^⇔! -[1+ n ]) ⊡ 2! !!⇔id) -- (!!⇔id p))

-- first match on m, n, then proof is purely PiLevel1
lower : {τ : U} {p : τ ⟷ τ} (m n : ℤ) →
  p ^ (m ℤ+ n) ⇔ ((p ^ m) ◎ (p ^ n))
lower (+_ ℕ.zero) (+_ n) = idl◎r
lower (+_ ℕ.zero) (-[1+_] n) = idl◎r
lower (+_ (suc m)) (+_ n) =
  trans⇔ (id⇔ ⊡ lower (+ m) (+ n)) assoc◎l
lower {p = p} (+_ (suc m)) (-[1+_] ℕ.zero) = 
  trans⇔ idr◎r (trans⇔ (id⇔ ⊡ linv◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔)))  -- p ^ ((m + 1) -1)
lower (+_ (suc m)) (-[1+_] (suc n)) = -- p ^ ((m + 1) -(1+1+n)
  trans⇔ (lower (+ m) (-[1+ n ])) (
  trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ linv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔))))) 
lower (-[1+_] m) (+_ ℕ.zero) = idr◎r
lower (-[1+_] ℕ.zero) (+_ (suc n)) = 2! (trans⇔ assoc◎l (
  trans⇔ (rinv◎l ⊡ id⇔) idl◎l))
lower (-[1+_] (suc m)) (+_ (suc n)) = -- p ^ (-(1+m) + (n+1))
  trans⇔ (lower (-[1+ m ]) (+ n)) (
    trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ rinv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l ((2! (assoc1- m)) ⊡ id⇔)))))
lower (-[1+_] ℕ.zero) (-[1+_] n) = id⇔
lower (-[1+_] (suc m)) (-[1+_] n) = -- p ^ (-(1+1+m) - (1+n))
  trans⇔ (id⇔ ⊡ lower (-[1+ m ]) (-[1+ n ])) assoc◎l

-- i.e. Perm is: for all i, any p' such that
-- p' ⇔ p ^ i

record Perm {τ : U} (p : τ ⟷ τ) : Set where
  constructor perm
  field
    iter : ℤ
    p' : τ ⟷ τ
    p'⇔p^i : p' ⇔ (p ^ iter)

-- Equality of Perm. 
record _≡c_ {τ : U} {p : τ ⟷ τ} (q r : Perm p) : Set where
  constructor eqc
  field
    iter≡ : Perm.iter q ≡ Perm.iter r
    p⇔ : Perm.p' q ⇔ Perm.p' r

private
  Perm→CombS :  ∀ {τ : U} (c : τ ⟷ τ) → Perm c → CombS (c ∷: nil)
  Perm→CombS p (perm (+_ n) _ _) = replicate n (p , Fwd (here refl))
  Perm→CombS p (perm (-[1+_] n) _ _) = replicate (suc n) (p , Bwd (here refl))

  CombS→Perm : ∀ {τ : U} (c : τ ⟷ τ) → CombS (c ∷: nil) → Perm c
  CombS→Perm p nil = perm (+ 0) id⟷ id⇔
  CombS→Perm p (x ∷: xs) with CombS→Perm p xs
  CombS→Perm p ((.p , Fwd (here refl)) ∷: xs) | perm i q pf =
      perm (ℤsuc i) (p ◎ q) (trans⇔ (id⇔ ⊡ pf)
        (trans⇔ (idr◎r ⊡ id⇔) (2! (lower (+ 1) i))))
  CombS→Perm p ((p' , Fwd (there ())) ∷: xs) | perm i q pf
  CombS→Perm p ((.p , Bwd (here refl)) ∷: xs) | perm i q pf =
     perm (i ℤ+ -[1+ 0 ]) (q ◎ (! p))
       (trans⇔ (pf ⊡ id⇔) (2! (lower i -[1+ 0 ])))
  CombS→Perm p ((p' , Bwd (there ())) ∷: xs) | perm i q pf
  CombS→Perm p ((p' , Neu) ∷: xs) | perm i q pf = perm i q pf

  -- split Fwd case from Bwd
  preserve-iter : ∀ {τ : U} (c : τ ⟷ τ) → (n : ℕ) →
    let p = CombS→Perm c (replicate n (c , Fwd (here refl))) in
    Perm.iter p ≡ + n
  preserve-iter c zero = refl
  preserve-iter c (suc n) = cong ℤsuc (preserve-iter c n)

  preserve-iterB : ∀ {τ : U} (c : τ ⟷ τ) → (n : ℕ) →
    let p = CombS→Perm c (replicate (suc n) (c , Bwd (here refl))) in
    Perm.iter p ≡ -[1+ n ]
  preserve-iterB c zero = refl
  preserve-iterB c (suc i) = P.trans
    (cong (λ z → z ℤ+ -[1+ 0 ]) (preserve-iterB c i))
    (cong (λ z → -[1+ (suc z) ]) (+-right-identity i))

  P2C2P : ∀ {τ : U} (c : τ ⟷ τ) → (p : Perm c) → (CombS→Perm c (Perm→CombS c p)) ≡c p
  P2C2P c (perm (+_ zero) p' p'⇔p^i) = eqc refl (2! p'⇔p^i)
  P2C2P c (perm (+_ (suc n)) p' p'⇔p^i) with CombS→Perm c (replicate n (c , Fwd (here refl))) | P.inspect (λ nn → CombS→Perm c (replicate nn (c , Fwd (here refl)))) n
  ... | perm i q pf | [ eq ] =
    let i=n = (P.trans (cong Perm.iter (P.sym eq)) (preserve-iter c n)) in
    eqc (cong ℤsuc i=n) (trans⇔ (id⇔ {c = c} ⊡ pf)
        (trans⇔ (id⇔ ⊡ P.subst (λ j → c ^ i ⇔ c ^ j) i=n (id⇔ {c = c ^ i})) (2! p'⇔p^i)))
  P2C2P c (perm (-[1+_] n) p' p'⇔p^i) with CombS→Perm c (replicate (suc n) (c , Bwd (here refl))) | P.inspect (λ nn → CombS→Perm c (replicate (suc nn) (c , Bwd (here refl)))) n
  ... | perm i q pf | [ eq ] = 
    let i=n = P.trans (cong Perm.iter (P.sym eq)) (preserve-iterB c n) in
    eqc i=n (trans⇔ (P.subst (λ j → q ⇔ c ^ j) i=n pf) (2! p'⇔p^i))

  C2P2C :  ∀ {τ : U} (c : τ ⟷ τ) → (q : CombS (c ∷: nil)) →
    interp (Perm→CombS c (CombS→Perm c q)) ⇔ interp q
  C2P2C c nil = id⇔
  C2P2C c (x ∷: q) with CombS→Perm c q | (C2P2C c) q
  C2P2C c ((.c , Fwd (here refl)) ∷: q) | perm (+_ n) p' pf | pf2 = id⇔ ⊡ pf2
  C2P2C c ((.c , Fwd (here refl)) ∷: q) | perm (-[1+_] zero) p' pf | pf2 =
    trans⇔ (linv◎r {c = c}) (id⇔ ⊡ trans⇔ idr◎r pf2) 
  C2P2C c ((.c , Fwd (here refl)) ∷: q) | perm (-[1+_] (suc n)) p' pf | pf2 =
    trans⇔ (trans⇔ idl◎r (linv◎r ⊡ id⇔)) (trans⇔ assoc◎r (id⇔ ⊡ pf2))
  C2P2C c ((comb , Fwd (there ())) ∷: q) | perm i p' pf | pf2
  C2P2C c ((.c , Bwd (here refl)) ∷: q) | perm (+_ zero) p' pf | pf2 = id⇔ ⊡ pf2
  C2P2C c ((.c , Bwd (here refl)) ∷: q) | perm (+_ (suc n)) p' pf | pf2 = 
    trans⇔ (trans⇔ idl◎r (rinv◎r ⊡ id⇔)) (trans⇔ assoc◎r (id⇔ ⊡ pf2))
  C2P2C c ((.c , Bwd (here refl)) ∷: q) | perm (-[1+_] n) p' pf | pf2 =
    id⇔ {c = ! c} ⊡ (P.subst (λ j → ! c ◎ foldr _◎_ id⟷ (Lmap extract (replicate j (c , Bwd (here refl)))) ⇔ foldr _◎_ id⟷ (Lmap extract q)) (P.sym (+-right-identity n)) pf2)
  C2P2C c ((comb , Bwd (there ())) ∷: q) | perm i p' pf | pf2
  C2P2C c ((comb , Neu) ∷: q) | perm i p' pf | pf2 = trans⇔ pf2 idl◎r
  
-- we would like to say:
--    Perm[p]≃CombS[p] : ∀ {τ : U} (p : τ ⟷ τ) → Perm p ≃ CombS (p ∷: nil)
-- but the homotopies have the wrong type (≡ rather than ≡c and ⇔).

-----------
-- Generalization of # p to # S.

orderC : {τ : U} → (S : GenSet τ) → Category _ _ _
orderC {τ} S = record {
     Obj = CombS S
   ; _⇒_ = λ q₁ q₂ → interp q₁ ⇔ interp q₂
   ; _≡_ = λ _ _ → ⊤ 
   ; id = id⇔
   ; _∘_ = flip trans⇔
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt 
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }
   ; ∘-resp-≡ = λ _ _ → tt
   }

orderG : {τ : U} → (S : GenSet τ) → Groupoid (orderC S)
orderG {τ} S = record {
    _⁻¹ = 2!
  ; iso = record {
        isoˡ = tt
      ; isoʳ = tt
      }
  }

commute-interp-++ : ∀ {τ : U} {S : GenSet τ} (f g : CombS S) →
  interp (f ++ g) ⇔ interp f ◎ interp g
commute-interp-++ nil g = idl◎r
commute-interp-++ (x ∷: f) g = trans⇔ (id⇔ ⊡ commute-interp-++ f g) assoc◎l

1/orderC : {τ : U} → (S : GenSet τ) → Category _ _ _
1/orderC S = record {
    Obj = ⊤
  ; _⇒_ = λ _ _ → CombS S
  ; _≡_ = λ p q → interp p ⇔ interp q
  ; id = nil
  ; _∘_ = _++_
  ; assoc = λ { {f = f} {g} {h} → trans⇔ (commute-interp-++ (h ++ g) f) (
      trans⇔ (commute-interp-++ h g ⊡ id⇔) (
      trans⇔ assoc◎r (
      trans⇔ (id⇔ ⊡ (2! (commute-interp-++ g f))) (
              2! (commute-interp-++ h (g ++ f)))))) }
  ; identityˡ = id⇔ -- could also use idl◎l like below
  ; identityʳ = λ { {f = f} → trans⇔ (commute-interp-++ f nil) idr◎l }
  ; equiv = record { refl = id⇔ ; sym = 2! ; trans = trans⇔ }
  ; ∘-resp-≡ = λ { {f = f} {h} {g} {i} f⇔h g⇔i →
      trans⇔ (commute-interp-++ f g) (trans⇔ (f⇔h ⊡ g⇔i) (2! (commute-interp-++ h i))) }
  }

flipGS : {τ : U} {S : GenSet τ} → inGS S → inGS S
flipGS (c , pf) = c , flip⇕ pf

invert-CombS : {τ : U} {S : GenSet τ} → CombS S → CombS S
invert-CombS pl = Data.List.map flipGS (Data.List.reverse pl)

-- sometimes we need to do some list manipulations under interp 
lift-≡ : {t₁ t₂ : U} {p q : t₁ ⟷ t₂} → p ≡ q → p ⇔ q
lift-≡ refl = id⇔

interp-invert : {τ : U} {S : GenSet τ} → (x : inGS S) → (f : CombS S) →
  interp (invert-CombS (x ∷: f)) ⇔ interp (invert-CombS f) ◎ extract (flipGS x)
interp-invert (c , Fwd x) f = {!!}
interp-invert (c , Bwd y) f = {!!}
interp-invert (c , Neu) f = {!!}

extract-flipGS : {τ : U} {S : GenSet τ} → (x : inGS S) → extract (flipGS x) ⇔ ! (extract x)
extract-flipGS (proj₁ , Fwd x) = id⇔
extract-flipGS (proj₁ , Bwd y) = 2! !!⇔id
extract-flipGS (proj₁ , Neu) = id⇔

private
  left-invCS : {τ : U} {S : GenSet τ} (f : CombS S) → interp (invert-CombS f ++ f) ⇔ id⟷
  left-invCS nil = id⇔
  left-invCS (x ∷: f) = trans⇔
    (commute-interp-++ (invert-CombS (x ∷: f)) (x ∷: f)) (trans⇔
    (interp-invert x f ⊡ id⇔) (trans⇔
    assoc◎r (trans⇔
    (id⇔ ⊡ assoc◎l) (trans⇔
    (id⇔ ⊡ trans⇔ (trans⇔ (extract-flipGS x ⊡ id⇔) rinv◎l ⊡ id⇔) idl◎l) (trans⇔
    (2! (commute-interp-++ (invert-CombS f) f)) (left-invCS f))))))

  right-invCS : {τ : U} {S : GenSet τ} (f : CombS S) → interp (f ++ invert-CombS f) ⇔ id⟷
  right-invCS l = {!!}
  
1/orderG : {τ : U} → (S : GenSet τ) → Groupoid (1/orderC S)
1/orderG s = record {
    _⁻¹ = invert-CombS
  ; iso = λ {_} {_} {f} → record {
      isoˡ = left-invCS f
    ; isoʳ = right-invCS f
    }
  }
  
-----------
--- Our semantics into groupoids
⟦_⟧↑ : (T : U↑) → Universe.El UG T
⟦ ↑ S ⟧↑ = , discreteG S
⟦ # S q ⟧↑ = , orderG S -- the base point doesn't matter here?
⟦ 1/ S q ⟧↑ = , 1/orderG S -- ditto?
⟦ x ⊞ y ⟧↑ with ⟦ x ⟧↑ | ⟦ y ⟧↑
... | (_ , G₁) | (_ , G₂) = , GSum G₁ G₂
⟦ x ⊠ y ⟧↑ with ⟦ x ⟧↑ | ⟦ y ⟧↑
... | (_ , G₁) | (_ , G₂) = , GProduct G₁ G₂

record W (t : U↑) : Set where
  constructor w
  field
    pt : Category.Obj (proj₁ ⟦ t ⟧↑)
    auto : Category._⇒_ (proj₁ ⟦ t ⟧↑) pt pt

evalW : {s t : U↑} → s ⇿ t → W s → W t
evalW (↑ x) (w pt auto) = w (ap x pt) refl
evalW (ev q) (w (cc , tt) (cc⇔cc-pf , cc')) = w tt refl -- this is cheating, cc <=> cc' ??
evalW (coev q) (w tt refl) = w (q , tt) (id⇔ , q) -- but this isn't.
evalW id⇿ (w pt auto) = w pt auto

-- This should actually be Hom-set inhabitation, aka categorical equivalence
-- (as we are in a groupoid setting).
ObjEq : (t : U↑) → Category.Obj (proj₁ ⟦ t ⟧↑) → Category.Obj (proj₁ ⟦ t ⟧↑) → Set
ObjEq (↑ x) a b = a P.≡ b
ObjEq (# S x) a b = interp a ⇔ interp b
ObjEq (1/ S x) a b = ⊤
ObjEq (s ⊞ t) (inj₁ x) (inj₁ y) = ObjEq s x y
ObjEq (s ⊞ t) (inj₁ x) (inj₂ y) = ⊥
ObjEq (s ⊞ t) (inj₂ y) (inj₁ x) = ⊥
ObjEq (s ⊞ t) (inj₂ x) (inj₂ y) = ObjEq t x y
ObjEq (s ⊠ t) (a , b) (c , d) = ObjEq s a c × ObjEq t b d

HomEq : (t : U↑) → (a b : Category.Obj (proj₁ ⟦ t ⟧↑)) →
  Category._⇒_ (proj₁ ⟦ t ⟧↑) a b → Category._⇒_ (proj₁ ⟦ t ⟧↑) a b → Set
HomEq (↑ x) a b h1 h2 = ⊤ -- this is basically proof-irrelevance h1 h2
HomEq (# S x) a b h1 h2 = ⊤ -- because h1 and h2 are the exact same ⇔
HomEq (1/ S x) tt tt h1 h2 = interp h1 ⇔ interp h2 -- here!
HomEq (s ⊞ t) (inj₁ x) (inj₁ x₁) h1 h2 = HomEq s x x₁ h1 h2
HomEq (s ⊞ t) (inj₁ x) (inj₂ y) (Level.lift ()) h2
HomEq (s ⊞ t) (inj₂ y) (inj₁ x) (Level.lift ()) h2
HomEq (s ⊞ t) (inj₂ y) (inj₂ y₁) h1 h2 = HomEq t y y₁ h1 h2
HomEq (s ⊠ t) (a , b) (c , d) (a⇒c , b⇒d) (a⇒c' , b⇒d') =
  HomEq s a c a⇒c a⇒c' × HomEq t b d b⇒d b⇒d'

-- W equivalence; note that transp is restricted to be the Homs of cat
--   we might want to restrict that more.
record _≈W_ {t : U↑} (a : W t) (b : W t) : Set where
  constructor weq
  cat = proj₁ ⟦ t ⟧↑
  gpd = proj₂ ⟦ t ⟧↑
  _∘_ = Category._∘_ cat
  field
    pt-eq : ObjEq t (W.pt a) (W.pt b)
    transp : Category._⇒_ cat (W.pt a) (W.pt b)
    auto-eq : HomEq t (W.pt a) (W.pt b) (W.auto b ∘ (transp ∘ (W.auto a))) transp
