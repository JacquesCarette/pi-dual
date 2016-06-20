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
open import PiEquiv renaming (eval to ap; evalB to apB)
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
embed1/#p (iter i q α) = v tt (iter i q α)

-- We can then define combinators on V as two actions, one on each part
record C (s₀ s₁ t₀ t₁ : U) : Set where
  constructor cc
  field
    comb : s₀ ⟷ t₀
    transp : s₁ ⟷ t₁

-- evaluation is then straightforward, just follow the types: 
evalV : {s₀ s₁ t₀ t₁ : U} {fl : Flavour} {p₀ : s₁ ⟷ s₁} →
  (c : C s₀ s₁ t₀ t₁) → (val : V fl s₀ s₁ p₀) →
  V fl t₀ t₁ (! (C.transp c) ◎ (Iter.p' (V.auto val)) ◎ (C.transp c))
evalV (cc comb transp) (v pt (iter i q α)) =
  v (ap comb pt) (iter (+ 1) (! transp ◎ (q ◎ transp)) idr◎r) -- 

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
  #p   : {t : U} → (p : t ⟷ t) → U↑
  1/#p : {t : U} → (p : t ⟷ t) → U↑

-- This corresponds exactly to Obj (proj₁ ⟦ t ⟧ ) from 2D/Frac.agda
⟦_⟧↑ : U↑ → Set
⟦ ↑ x ⟧↑ = ⟦ x ⟧
⟦ #p p ⟧↑ = Iter p
⟦ 1/#p p ⟧↑ = ⊤

flavour : U↑ → Flavour
flavour (↑ _) = base
flavour (#p _) = up
flavour (1/#p _) = down

t₀↑ : U↑ → U
t₀↑ (↑ t) = t
t₀↑ (#p p) = ONE
t₀↑ (1/#p p) = ONE

t₁↑ : U↑ → U
t₁↑ (↑ t) = ONE
t₁↑ (#p {t} _) = t
t₁↑ (1/#p {t} _) = t

auto↑ : (t : U↑) → (t₁↑ t ⟷ t₁↑ t)
auto↑ (↑ x) = id⟷
auto↑ (#p p) = p
auto↑ (1/#p p) = id⟷

iter↑ : (t : U↑) → Iter (auto↑ t)
iter↑ (↑ x) = iter (+ 0) id⟷ id⇔
iter↑ (#p p) = iter (+ 1) p idr◎r
iter↑ (1/#p p) = iter (+ 0) id⟷ id⇔

⟦_⟧V : (t : U↑)  → Set
⟦ t ⟧V = V (flavour t) (t₀↑ t) (t₁↑ t) (auto↑ t)

fwd : {t : U↑} → ⟦ t ⟧↑ → ⟦ t ⟧V
fwd {↑ x} val = embedBase val
fwd {#p p} val = embed#p val
fwd {1/#p p} tt = embed1/#p (iter (+ 0) id⟷ id⇔)

bwd : {t : U↑} → ⟦ t ⟧V → ⟦ t ⟧↑
bwd {↑ x} val = V.pt val
bwd {#p p} val = V.auto val
bwd {1/#p p} val = tt

-- we can at least show the point is preserved:
fwdbwd≈id : {t : U↑} → (x : ⟦ t ⟧V) → V.pt (fwd {t} (bwd x)) P.≡ V.pt x
fwdbwd≈id {↑ x} (v pt auto) = P.refl
fwdbwd≈id {#p p} (v tt auto) = P.refl
fwdbwd≈id {1/#p p} (v tt auto) = P.refl

fb-auto : {t : U↑} → (x : ⟦ t ⟧V) → Iter.p' (V.auto (fwd {t} (bwd x))) ⇔ Iter.p' (V.auto x)
fb-auto {↑ x} (v pt (iter i p' α)) = 2! (trans⇔ α (id^i≡id i))
fb-auto {#p p} (v pt (iter i p' α)) = id⇔
fb-auto {1/#p p} (v pt (iter i p' α)) = 2! (trans⇔ α (id^i≡id i))

{-
data _⇿_ : U↑ → U↑ → Set where
  prim : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (↑ t₁ ⇿ ↑ t₂)
-}
  
