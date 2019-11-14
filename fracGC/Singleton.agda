{-# OPTIONS --without-K --safe #-}

-- Singleton type and its 'inverse'

module Singleton where

open import Data.Unit using (⊤; tt)
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong ; cong₂)
-- open import Level
--   using (zero)
-- open import Axiom.Extensionality.Propositional
--   using (Extensionality)

is-contr : Set → Set
is-contr A = Σ A (λ a → (x : A) → a ≡ x)

is-prop : Set → Set
is-prop A = (x y : A) → x ≡ y

is-set : Set → Set
is-set A = (x y : A) → is-prop (x ≡ y)

contr-prop : {A : Set} → is-contr A → is-prop A
contr-prop (a , ϕ) x y = trans (sym (ϕ x)) (ϕ y)

apd : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) {x y} → (p : x ≡ y) → subst B p (f x) ≡ f y
apd f refl = refl

prop-set : {A : Set} → is-prop A → is-set A
prop-set {A} ϕ x y p q = trans (l p) (sym (l q))
  where g : (z : A) → x ≡ z
        g z = ϕ x z
        unitr : {y z : A} (p : y ≡ z) → refl ≡ trans (sym p) p
        unitr refl = refl
        l : {y z : A} (p : y ≡ z) → p ≡ trans (sym (g y)) (g z)
        l refl = unitr (g _)

prop-contr : {A : Set} → is-prop A → A → is-contr A
prop-contr ϕ a = a , ϕ a

------------------------------------------------------------------------------
-- Singleton type: A type with a distinguished point
--  The 'interesting' part is that the point is both a parameter
--  and a field.

{--
record Singleton (A : Set) (v : A) : Set where
  constructor ⇑
  field
    ● : A
    v≡● : v ≡ ●

open Singleton public
--}

Singleton : (A : Set) → (v : A) → Set
Singleton A v = ∃ (λ ● → v ≡ ●)

-- Singleton types are contractible:
pointed-contr : {A : Set} {v : A} → is-contr (Singleton A v)
--pointed-contr {A} {v} = ⇑ v refl , λ { (⇑ ● refl) → refl }
pointed-contr {A} {v} = (v , refl) , λ { ( ● , refl) → refl }

-- and thus have all paths between them:
pointed-all-paths : {A : Set} {v : A} {p q : Singleton A v} → p ≡ q
pointed-all-paths = contr-prop pointed-contr _ _

-- What does Singleton of Singleton do?
-- Values of type Singleton A v are of the form (w , p) where p : v ≡ w
-- Values of type Singleton (Singleton A v) x

ssv : (A : Set) (v : A) (x : Singleton A v) → Singleton (Singleton A v) x
ssv A v (.v , refl) = (v , refl) , refl

{--
ss=s : (A : Set) (v : A) (x : Singleton A v) → Singleton (Singleton A v) x ≡ Singleton A v
ss=s A v (.v , refl) with pointed-contr {A} {v}
... | (.v , refl) , f = let p = f (v , refl) in {!!} -- ??
--}
------------------------------------------------------------------------------
-- The 'reciprocal' of a Singleton type is a function that accepts exactly
-- that point, and returns no information. It acts as a 'witness' that
-- the right point has been fed to it.
{--
Recip : (A : Set) → (v : A) → Set
Recip A v = (w : A) → (v ≡ w) → ⊤
--}

Recip : (A : Set) → (v : A) → Set
Recip A v = Singleton A v → ⊤

-- Recip A v = Singleton A v → ⊤

-- Recip is also contractible, if we're thinking of homotopy types.
-- We need funext to prove it which is not --safe

-- posulate
--   funext : Extensionality zero zero

-- recip-contr : {A : Set} {v : A} → is-contr (Recip A v)
-- recip-contr = (λ _ _ → tt) , λ r → funext λ _ → funext λ _ → refl


------------------------------------------------------------------------------

-- Recip' : {A : Set} {v : A} → Singleton A v → Set
-- Recip' {A} {v} (⇑ w v≡w) = v ≡ w

-- Recip'-ptd : {A : Set} {v : A} → (p : Singleton A v) → Singleton (Recip' p) (v≡● p)
-- Recip'-ptd (⇑ w v≡w) = ⇑ v≡w refl

-- family of path types from arbitrary w to a fixed v

Recip' : (A : Set) → (v : A) → Set
Recip' A v = (w : A) → v ≡ w

-- If A is a n-type, Recip' is a (n-1)-type

-- recip'-contr : {A : Set} {v : A} → is-prop A → is-contr (Recip' A v)
-- recip'-contr {A} {v} ϕ = (λ w → ϕ v w) , λ r → funext λ x → prop-set ϕ v x (ϕ v x) (r x)

-- recip'-prop : {A : Set} {v : A} → is-set A → is-prop (Recip' A v)
-- recip'-prop ϕ r s = funext (λ x → ϕ _ x (r x) (s x))

------------------------------------------------------------------------------
-- Singleton is an idempotent bimonad on pointed sets
-- (need to check some coherences)

∙Set = Σ Set (λ X → X)

∙Set[_,_] : ∙Set → ∙Set → Set
∙Set[ (A , a) , (B , b) ] = Σ (A → B) λ f → f a ≡ b

_∙×_ : ∙Set → ∙Set → ∙Set
(A , a) ∙× (B , b) = (A × B) , (a , b)

-- left version, there's also a right version
-- note that this isn't a coproduct
-- wedge sum is the coproduct
_∙+_ : ∙Set → ∙Set → ∙Set
(A , a) ∙+ (B , b) = (A ⊎ B) , inj₁ a

∙id : ∀{∙A} → ∙Set[ ∙A , ∙A ]
∙id = (λ a → a) , refl

_∘_ : ∀ {∙A ∙B ∙C} → ∙Set[ ∙A , ∙B ] → ∙Set[ ∙B , ∙C ] → ∙Set[ ∙A , ∙C ]
(f , p) ∘ (g , q) = (λ x → g (f x)) , trans (cong g p) q

record ∙Iso[_,_] (∙A ∙B : ∙Set) : Set where
  constructor iso
  field
    ∙f : ∙Set[ ∙A , ∙B ]
    ∙g : ∙Set[ ∙B , ∙A ]
  f = ∙f .proj₁
  g = ∙g .proj₁
  field
    f-g : ∀ b → f (g b) ≡ b
    g-f : ∀ a → g (f a) ≡ a

open ∙Iso[_,_]

∙Iso⁻¹ : ∀ {∙A ∙B} → ∙Iso[ ∙A , ∙B ] → ∙Iso[ ∙B , ∙A ]
∙Iso⁻¹ (iso ∙f ∙g f-g g-f) = iso ∙g ∙f g-f f-g

Sing : ∙Set → ∙Set
Sing (A , a) = Singleton A a , a , refl

Sing[_,_] : ∀ ∙A ∙B → ∙Set[ ∙A , ∙B ] → ∙Set[ Sing ∙A , Sing ∙B  ]
Sing[ (A , a) , (B , .(f a)) ] (f , refl) = (λ { (x , refl) → f x , refl }) , refl

-- monad
η[_] : ∀ ∙A → ∙Set[ ∙A , Sing ∙A ]
η[ (A , a) ] = (λ x → a , refl) , refl

μ[_] : ∀ ∙A → ∙Iso[ Sing (Sing ∙A) , Sing ∙A ]
μ[ (A , a) ] = iso ((λ { (.(a , refl) , refl) → a , refl }) , refl)
                   ((λ { (a , refl) → (a , refl) , refl }) , refl)
                   (λ { (a , refl) → refl})
                   (λ { ((a , refl) , refl) → refl })

-- check
Sη-μ : ∀ {∙A} → ((Sing[ ∙A , Sing ∙A ] η[ ∙A ] ∘ (μ[ ∙A ] .∙f)) .proj₁) (∙A .proj₂ , refl) ≡ (∙A .proj₂ , refl)
Sη-μ = refl

ηS-μ : ∀ {∙A} → ((Sing[ Sing ∙A , Sing (Sing ∙A) ] η[ Sing ∙A ] ∘ (μ[ Sing ∙A ] .∙f)) .proj₁) ((∙A .proj₂ , refl) , refl) ≡ ((∙A .proj₂ , refl) , refl)
ηS-μ = refl

-- strength
σ×[_,_] : ∀ ∙A ∙B → ∙Set[ Sing ∙A ∙× ∙B , Sing (∙A ∙× ∙B) ]
σ×[ (A , a) , (B , b) ] = (λ { ((a , refl) , _) → (a , b) , refl }) , refl

τ×[_,_] : ∀ ∙A ∙B → ∙Set[ ∙A ∙× Sing ∙B , Sing (∙A ∙× ∙B) ]
τ×[ (A , a) , (B , b) ] = (λ { (_ , (b , refl)) → (a , b) , refl }) , refl

σ+[_,_] : ∀ ∙A ∙B → ∙Set[ Sing ∙A ∙+ ∙B , Sing (∙A ∙+ ∙B) ]
σ+[ (A , a) , (B , b) ] = (λ _ → inj₁ a , refl) , refl

τ+[_,_] : ∀ ∙A ∙B → ∙Set[ ∙A ∙+ Sing ∙B , Sing (∙A ∙+ ∙B) ]
τ+[ (A , a) , (B , b) ] = (λ _ → inj₁ a , refl) , refl

-- comonad
ε[_] : ∀ ∙A → ∙Set[ Sing ∙A , ∙A ]
ε[ (A , a) ] = (λ { (x , refl) → x }) , refl

δ[_] : ∀ ∙A → ∙Iso[ Sing ∙A , Sing (Sing ∙A) ]
δ[ ∙A ] = ∙Iso⁻¹ μ[ ∙A ]

-- check
δ-Sε : ∀ {∙A} → ((δ[ ∙A ] .∙f ∘ Sing[ Sing ∙A , ∙A ] ε[ ∙A ]) .proj₁) (∙A .proj₂ , refl) ≡ (∙A .proj₂ , refl)
δ-Sε = refl

δ-εS : ∀ {∙A} → ((δ[ Sing ∙A ] .∙f ∘ Sing[ Sing (Sing ∙A) , Sing ∙A ] ε[ Sing ∙A ]) .proj₁) ((∙A .proj₂ , refl) , refl) ≡ ((∙A .proj₂ , refl) , refl)
δ-εS = refl

-- costrength
σ'×[_,_] : ∀ ∙A ∙B → ∙Set[ Sing (∙A ∙× ∙B) , Sing ∙A ∙× ∙B ]
σ'×[ (A , a) , (B , b) ] = (λ { (.(a , b) , refl) → (a , refl) , b }) , refl

τ'×[_,_] : ∀ ∙A ∙B → ∙Set[ Sing (∙A ∙× ∙B) , ∙A ∙× Sing ∙B ]
τ'×[ (A , a) , (B , b) ] = (λ { (.(a , b) , refl) → a , (b , refl) }) , refl

σ'+[_,_] : ∀ ∙A ∙B → ∙Set[ Sing (∙A ∙+ ∙B) , Sing ∙A ∙+ ∙B ]
σ'+[ (A , a) , (B , b) ] = (λ _ → inj₁ (a , refl)) , refl

τ'+[_,_] : ∀ ∙A ∙B → ∙Set[ Sing (∙A ∙+ ∙B) , ∙A ∙+ Sing ∙B ]
τ'+[ (A , a) , (B , b) ] = (λ _ → inj₁ a) , refl

-- even better, strong monoidal functor
ν×[_,_] : ∀ ∙A ∙B → ∙Iso[ Sing ∙A ∙× Sing ∙B , Sing (∙A ∙× ∙B) ]
ν×[ (A , a) , (B , b) ] = iso ((λ _ → (a , b) , refl) , refl)
                              ((λ _ → (a , refl) , b , refl) , refl)
                              (λ { (.(a , b) , refl) → refl })
                              (λ { ((a , refl) , (b , refl)) → refl })

-- this one is only lax
ν+[_,_] : ∀ ∙A ∙B → ∙Set[ Sing ∙A ∙+ Sing ∙B , Sing (∙A ∙+ ∙B) ]
ν+[ (A , a) , (B , b) ] = (λ _ → inj₁ a , refl) , refl
