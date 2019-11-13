{-# OPTIONS --without-K --safe #-}

-- Singleton type and its 'inverse'

module Singleton where

open import Data.Unit using (⊤; tt)
open import Data.Product 
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong₂)
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

Sing : ∙Set → ∙Set
Sing (A , a) = Singleton A a , a , refl

Sing[_,_] : ∀ ∙A ∙B → ∙Set[ ∙A , ∙B ] → ∙Set[ Sing ∙A , Sing ∙B  ]
Sing[ (A , a) , (B , .(f a)) ] (f , refl) = (λ { (x , refl) → f x , refl }) , refl

η[_] : ∀ ∙A → ∙Set[ ∙A , Sing ∙A ]
η[ (A , a) ] = (λ x → a , refl) , refl

ε[_] : ∀ ∙A → ∙Set[ Sing ∙A , ∙A ]
ε[ (A , a) ] = (λ { (x , refl) → x }) , refl

μ[_] : ∀ ∙A → ∙Set[ Sing (Sing ∙A) , Sing ∙A ]
μ[ (A , a) ] = (λ x → a , refl) , refl

δ[_] : ∀ ∙A → ∙Set[ Sing ∙A , Sing (Sing ∙A) ]
δ[ (A , a) ]  = (λ x → (a , refl) , refl) , refl
