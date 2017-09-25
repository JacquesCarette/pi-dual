{-# OPTIONS --without-K #-}

module TheSame where

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
open import Data.Integer using (+_)

open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid.Product using () renaming (Product to GProduct)

open import PiU using (U; ZERO; ONE; PLUS; TIMES; toℕ)
open import PiLevel0
open import PiLevel1
open import PiEquiv
open import Equiv

open import PiIter

-- our values come in three flavours, base, up and down (i.e. #p and 1/# p)
data Flavour : Set where
  base up down : Flavour
  
-- all our values will be 'subtypes' of this:
record V (fl : Flavour) (t₀ t₁ : U) (p : t₁ ⟷ t₁) : Set where
  constructor v
  field
    pt : ⟦ t₀ ⟧
    auto : Iter p

-- we need t₀ and t₁ to potentially be different to embed
-- #p and 1/#p.  The values of these are the same, but
-- the homomorphisms will be different, and thus how to count them.

-- We can embed our (current) values into V easily: 
embedBase : {t : U} → ⟦ t ⟧ → V base t ONE id⟷
embedBase w = v w (iter (+ 0) id⟷ id⇔)

embed#p : {t : U} → {p : t ⟷ t} → Iter p → V up ONE t p
embed#p it = v tt it

embed1/#p : {t : U} → {p : t ⟷ t} → Iter p → V down ONE t p
embed1/#p it = v tt it

-- We can then define combinators on V as two actions, one on each part
record C (s₀ s₁ t₀ t₁ : U) : Set where
  constructor cc
  field
    comb : s₀ ⟷ t₀
    transp : s₁ ⟷ t₁

-- evaluation is then straightforward, just follow the types: 
evalV : {s₀ s₁ t₀ t₁ : U} {fl : Flavour} {p₀ : s₁ ⟷ s₁} →
  (c : C s₀ s₁ t₀ t₁) → (val : V fl s₀ s₁ p₀) →
  V fl t₀ t₁ (! (C.transp c) ◎ p₀ ◎ (C.transp c))
evalV {p₀ = p} (cc comb transp) (v pt (iter i q α)) =
  v (eval comb pt) (iter i (! transp ◎ (q ◎ transp)) {!!}) -- 

-- we should go backwards too
evalVB : {s₀ s₁ t₀ t₁ : U} {fl : Flavour} {p₁ : t₁ ⟷ t₁} →
  (c : C s₀ s₁ t₀ t₁) → (val : V fl t₀ t₁ p₁) →
    V fl s₀ s₁ ((C.transp c) ◎ p₁ ◎ ! (C.transp c))
evalVB (cc comb transp) (v pt (iter i q α)) =
  v (evalB comb pt) (iter (+ 1) (transp ◎ (q ◎ ! transp)) {!!})

-- Next comes the (generic) type of morphisms. Note that this type is
-- 'too big', in practice we use particular sub-types. 
record H {s₀ s₁ t₀ t₁ : U} {fl : Flavour} {p : s₁ ⟷ s₁} {q : t₁ ⟷ t₁}
  (a : V fl s₀ s₁ p) (b : V fl t₀ t₁ q) : Set where
  constructor mor
  open V
  field
    combi : C s₀ s₁ t₀ t₁

  vb = evalV combi a
  
  field
    pt-eq : pt vb P.≡ pt b
    t-eq : Iter.p' (auto vb) ⇔ Iter.p' (auto b)
    -- should p transport to ⇔ q ?

-- The above gives, implicitly, a notion of equality, which can
-- be extracted as below.  Note how we insist on the types being
-- the same.  This is basically the same as H when combi is id⟷ id⟷
record _≡V_ {s₀ s₁ : U} {fl : Flavour} {p q : s₁ ⟷ s₁} 
  (a : V fl s₀ s₁ p) (b : V fl s₀ s₁ q) : Set where
  constructor veq
  open V
  field
    pt-eq : pt a P.≡ pt b
    t-eq : Iter.p' (auto a) ⇔ Iter.p' (auto b)
    p⇔q : p ⇔ q

-- And now we can say what back-and-forth do:
evBF : {s₀ s₁ t₀ t₁ : U} {fl : Flavour} {p₀ : s₁ ⟷ s₁} →
  (c : C s₀ s₁ t₀ t₁) → (val : V fl s₀ s₁ p₀) →
  evalVB c (evalV c val) ≡V val
evBF (cc comb transp) (v pt (iter i p' α)) =
  veq (P.trans (lemma1 comb (eval comb pt)) (
       P.trans (P.cong (proj₁ (sym≃ (c2equiv comb))) (lemma0 comb pt))
               (isqinv.β (proj₂ (c2equiv comb)) pt)))
      {!!} {!!}

-- and Homs.  Note how the range of this is quite restricted
embedBaseHom : {τ : U} → (s t : ⟦ τ ⟧) → s ≡ t → H (embedBase s) (embedBase t)
embedBaseHom s .s P.refl = mor (cc id⟷ id⟷) P.refl (trans⇔ idl◎l idr◎l )

-- for #p.  The only Homs are when p ^ i ⇔ p ^ j
embed#pHom : {τ : U} → {p : τ ⟷ τ} → (v₀ v₁ : Iter p) → (Iter.p' v₀) ⇔ (Iter.p' v₁) →
  H (embed#p v₀) (embed#p v₁)
embed#pHom {_} {p} (iter i q α) (iter j r β) iso = mor (cc id⟷ p) P.refl (
  trans⇔ (id⇔ ⊡ (α ⊡ id⇔)) (trans⇔ (trans⇔ (id⇔ ⊡ (2! (assoc1g i)))
  (trans⇔ assoc◎l (trans⇔ (rinv◎l ⊡ (2! α)) idl◎l))) iso)) 

-- for 1/#p; a bit lazy here, q should be Iter p, but the core of the
-- idea remains the same.  
embed1/#pHom : {τ : U} → (p : τ ⟷ τ) → (q : Iter p) → 
  H (embed1/#p q) (embed1/#p q)
embed1/#pHom p (iter i q α) = mor (cc id⟷ p) P.refl (trans⇔
  (id⇔ ⊡ (α ⊡ id⇔)) (trans⇔ (id⇔ ⊡ 2! (assoc1g i)) (trans⇔
  assoc◎l (trans⇔ (rinv◎l ⊡ id⇔) (trans⇔ idl◎l (2! α))))))

-- infix 40 _⇿_
infixl 50 ↑_

-- let's make the relationship much clearer
data U↑ : Set where
  ↑_ : U → U↑
  -- we need to do a more complicated lift of 1
  𝟙 : {t : U} → (p : t ⟷ t) → U↑
  #p   : {t : U} → (p : t ⟷ t) → U↑
  1/#p : {t : U} → (p : t ⟷ t) → U↑

-- This corresponds exactly to Obj (proj₁ ⟦ t ⟧ ) from 2D/Frac.agda
⟦_⟧↑ : U↑ → Set
⟦ ↑ x ⟧↑ = ⟦ x ⟧
⟦ 𝟙 p ⟧↑ = {!!}
⟦ #p p ⟧↑ = Iter p
⟦ 1/#p p ⟧↑ = ⊤

flavour : U↑ → Flavour
flavour (↑ _) = base
flavour (𝟙 p) = {!!}
flavour (#p _) = up
flavour (1/#p _) = down

t₀↑ : U↑ → U
t₀↑ (↑ t) = t
t₀↑ (𝟙 p) = {!!}
t₀↑ (#p p) = ONE
t₀↑ (1/#p p) = ONE

t₁↑ : U↑ → U
t₁↑ (↑ t) = ONE
t₁↑ (𝟙 p) = {!!}
t₁↑ (#p {t} _) = t
t₁↑ (1/#p {t} _) = t

auto↑ : (t : U↑) → (t₁↑ t ⟷ t₁↑ t)
auto↑ (↑ x) = id⟷
auto↑ (𝟙 p) = {!!}
auto↑ (#p p) = p
auto↑ (1/#p p) = id⟷

iter↑ : (t : U↑) → Iter (auto↑ t)
iter↑ (↑ x) = iter (+ 0) id⟷ id⇔
iter↑ (𝟙 p) = {!!}
iter↑ (#p p) = iter (+ 1) p idr◎r
iter↑ (1/#p p) = iter (+ 0) id⟷ id⇔

⟦_⟧V : (t : U↑)  → Set
⟦ t ⟧V = V (flavour t) (t₀↑ t) (t₁↑ t) (auto↑ t)

fwd : {t : U↑} → ⟦ t ⟧↑ → ⟦ t ⟧V
fwd {↑ x} val = embedBase val
fwd {𝟙 p} val = {!!}
fwd {#p p} val = embed#p val
fwd {1/#p p} tt = embed1/#p (iter (+ 0) id⟷ id⇔)

bwd : {t : U↑} → ⟦ t ⟧V → ⟦ t ⟧↑
bwd {↑ x} val = V.pt val
bwd {𝟙 p} val = {!!}
bwd {#p p} val = V.auto val
bwd {1/#p p} val = tt

-- (This should be packed up to use ≡V)
fwdbwd≈id : {t : U↑} → (x : ⟦ t ⟧V) → V.pt (fwd {t} (bwd x)) P.≡ V.pt x
fwdbwd≈id {↑ x} (v pt auto) = P.refl
fwdbwd≈id {𝟙 p} (v pt auto) = {!!}
fwdbwd≈id {#p p} (v tt auto) = P.refl
fwdbwd≈id {1/#p p} (v tt auto) = P.refl

fb-auto : {t : U↑} → (x : ⟦ t ⟧V) → Iter.p' (V.auto (fwd {t} (bwd x))) ⇔ Iter.p' (V.auto x)
fb-auto {↑ x} (v pt (iter i p' α)) = 2! (trans⇔ α (id^i≡id i))
fb-auto {𝟙 p} vv = {!!}
fb-auto {#p p} (v pt (iter i p' α)) = id⇔
fb-auto {1/#p p} (v pt (iter i p' α)) = 2! (trans⇔ α (id^i≡id i))

bf-x : {t : U↑} → (x : ⟦ t ⟧↑) → bwd (fwd {t} x) P.≡ x
bf-x {↑ x} x₁ = P.refl
bf-x {𝟙 p} x = {!!}
bf-x {#p p} x = P.refl
bf-x {1/#p p} tt = P.refl

{-
data _⇿_ : U↑ → U↑ → Set where
  prim : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (↑ t₁ ⇿ ↑ t₂)
-}
  
