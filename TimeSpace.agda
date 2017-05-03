
module TimeSpace where

open import Prelude as P
  hiding
    ( [_]
    ; id
    ; _∘_
    ; _***_
    )
open import Container.List
open import Pi.Util

{-
A universe of finite types.
-}
data U : Set where
  𝟘 𝟙     : U
  _⊕_ _⊗_ : U → U → U
infixr 6 _⊕_
infixr 7 _⊗_

{-
A collection of "primitive" isomorphisms.
Selection was based on accepted definitions of categorical structures.
Monoidal categories have left and right unitors, and associators;
braided monoidal categories have commutators.

While the left/right unitor pairs might be considered redundant in light of the commutative morphism,
I decided to keep them. By matching the morphisms of relevant categorical structures, we can
examine the various categorical coherence laws for time/space tradeoffs. This isn't necessary,
but I want to test the effects of the change on the structure of the proofs.
-}
data _≅_ : U → U → Set where
  -- Coproduct monoid
  ⊕λ : ∀ {A}
     → 𝟘 ⊕ A ≅ A
  ⊕ρ : ∀ {A}
     → A ⊕ 𝟘 ≅ A
  ⊕σ : ∀ {A B}
     → A ⊕ B ≅ B ⊕ A
  ⊕α : ∀ {A B C}
     → (A ⊕ B) ⊕ C ≅ A ⊕ (B ⊕ C)
  -- Product monoid
  ⊗λ : ∀ {A}
     → 𝟙 ⊗ A ≅ A
  ⊗ρ : ∀ {A}
     → A ⊗ 𝟙 ≅ A
  ⊗σ : ∀ {A B}
     → A ⊗ B ≅ B ⊗ A
  ⊗α : ∀ {A B C}
     → (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)
  -- Distributivity
  δ  : ∀ {A B C}
     → A ⊗ (B ⊕ C) ≅ (A ⊗ B) ⊕ (A ⊗ C)
infix 1 _≅_
{- Naming conventions:
  *λ : left unitor     : ε ∙ x ≅ x
  *ρ : right unitor    : x ∙ ε ≅ x
  *α : associator      : (x ∙ y) ∙ z ≅ x ∙ (y ∙ z)
  *σ : braid           : x ∙ y ≅ y ∙ x
  ⊗* : multiplicative variant, (𝟙 , ⊗)
  ⊕* : additive variant,       (𝟘 , ⊕)
  δ  : distributor     : x ⊗ (y ⊕ z) ≅ (x ⊗ y) ⊕ (x ⊗ z)
-}

infixr 5 _∘_
infix 1 _⟷_
data _⟷_ : U → U → Set where
  [_] : ∀ {A B}
      → A ≅ B
      → A ⟷ B
  id : ∀ {A}
    → A ⟷ A
  _⁻¹ : ∀ {A B}
    → A ⟷ B
    → B ⟷ A
  _∘_ : ∀ {A B C}
      → B ⟷ C
      → A ⟷ B
      → A ⟷ C
  _⊗_ : ∀ {A B C D}
      → A ⟷ B
      → C ⟷ D
      → A ⊗ C ⟷ B ⊗ D
  _⊕_ : ∀ {A B C D}
      → A ⟷ B
      → C ⟷ D
      → A ⊕ C ⟷ B ⊕ D

El : U → Set
El 𝟘       = ⊥
El 𝟙       = ⊤
El (A ⊕ B) = Either (El A) (El B)
El (A ⊗ B) = El A × El B

{-
bwd/fwd relate to the unitary morphisms,
while ap/ap⁻¹ relate to arbitrary morphisms.
-}

fwd : ∀ {A B}
    → A ≅ B
    → El A → El B
bwd : ∀ {A B}
    → A ≅ B
    → El B → El A

fwd ⊕λ (left ())
fwd ⊕λ (right x)        = x
fwd ⊕ρ (left x)         = x
fwd ⊕ρ (right ())
fwd ⊕σ (left x)         = right x
fwd ⊕σ (right x)        = left x
fwd ⊕α (left (left x))  = left x
fwd ⊕α (left (right x)) = right (left x)
fwd ⊕α (right x)        = right (right x)
fwd ⊗λ (tt , x)         = x
fwd ⊗ρ (x , tt)         = x
fwd ⊗σ (x , y)          = y , x
fwd ⊗α ((x , y) , z)    = x , y , z
fwd δ (x , left y)      = left (x , y)
fwd δ (x , right y)     = right (x , y)

bwd ⊕λ x                 = right x
bwd ⊕ρ x                 = left x
bwd ⊕σ (left x)          = right x
bwd ⊕σ (right x)         = left x
bwd ⊕α (left x)          = left (left x)
bwd ⊕α (right (left x))  = left (right x)
bwd ⊕α (right (right x)) = right x
bwd ⊗λ x                 = tt , x
bwd ⊗ρ x                 = x , tt
bwd ⊗σ (x , y)           = y , x
bwd ⊗α (x , y , z)       = (x , y) , z
bwd δ (left  (x , y))    = x , left y
bwd δ (right (x , y))    = x , right y

fwd-bwd : ∀ {A B}
        → (f : A ≅ B)
        → bwd f P.∘ fwd f ≃ P.id

fwd-bwd ⊕λ (left ())
fwd-bwd ⊕λ (right x)        = P.refl
fwd-bwd ⊕ρ (left x)         = P.refl
fwd-bwd ⊕ρ (right ())
fwd-bwd ⊕σ (left x)         = P.refl
fwd-bwd ⊕σ (right x)        = P.refl
fwd-bwd ⊕α (left (left x))  = P.refl
fwd-bwd ⊕α (left (right x)) = P.refl
fwd-bwd ⊕α (right x)        = P.refl
fwd-bwd ⊗λ (tt , x)         = P.refl
fwd-bwd ⊗ρ (x , tt)         = P.refl
fwd-bwd ⊗σ (x , y)          = P.refl
fwd-bwd ⊗α ((x , y) , z)    = P.refl
fwd-bwd δ (x , left y)      = P.refl
fwd-bwd δ (x , right y)     = P.refl

bwd-fwd : ∀ {A B}
        → (f : A ≅ B)
        → fwd f P.∘ bwd f ≃ P.id
bwd-fwd ⊕λ x                 = P.refl
bwd-fwd ⊕ρ x                 = P.refl
bwd-fwd ⊕σ (left x)          = P.refl
bwd-fwd ⊕σ (right x)         = P.refl
bwd-fwd ⊕α (left x)          = P.refl
bwd-fwd ⊕α (right (left x))  = P.refl
bwd-fwd ⊕α (right (right x)) = P.refl
bwd-fwd ⊗λ x                 = P.refl
bwd-fwd ⊗ρ x                 = P.refl
bwd-fwd ⊗σ (x , y)           = P.refl
bwd-fwd ⊗α (x , y , z)       = P.refl
bwd-fwd δ (left (x , y))     = P.refl
bwd-fwd δ (right (x , y))    = P.refl

infixr 1 ap ap⁻¹

ap : ∀ {A B}
   → A ⟷ B
   → El A → El B
ap⁻¹ : ∀ {A B}
     → A ⟷ B
     → El B → El A

ap [ f ]   = fwd f
ap id      = P.id
ap (f ⁻¹)  = ap⁻¹ f
ap (g ∘ f) = ap g P.∘ ap f
ap (f ⊗ g) = ap f *** ap g
ap (f ⊕ g) = ap f +++ ap g

ap⁻¹ [ f ]   = bwd f
ap⁻¹ id      = P.id
ap⁻¹ (f ⁻¹)  = ap f
ap⁻¹ (g ∘ f) = ap⁻¹ f P.∘ ap⁻¹ g
ap⁻¹ (f ⊗ g) = ap⁻¹ f *** ap⁻¹ g
ap⁻¹ (f ⊕ g) = ap⁻¹ f +++ ap⁻¹ g

ap-inv : ∀ {A B}
       → (f : A ⟷ B)
       → ap⁻¹ f P.∘ ap f ≃ P.id
inv-ap : ∀ {A B}
       → (f : A ⟷ B)
       → ap f P.∘ ap⁻¹ f ≃ P.id

ap-inv [ f ]   x = fwd-bwd f x
ap-inv id      x = P.refl
ap-inv (f ⁻¹)  x = inv-ap f x
ap-inv (g ∘ f) x =
  ap⁻¹ f $≡ ap-inv g (ap f x)
  ⟨≡⟩ ap-inv f x
ap-inv (f ⊗ g) (x , y) = cong₂ _,_ (ap-inv f x) (ap-inv g y)
ap-inv (f ⊕ g) (left x)  = left  $≡ ap-inv f x
ap-inv (f ⊕ g) (right x) = right $≡ ap-inv g x

inv-ap [ f ]   x = bwd-fwd f x
inv-ap id      x = P.refl
inv-ap (f ⁻¹)  x = ap-inv f x
inv-ap (g ∘ f) x =
  ap g $≡ inv-ap f (ap⁻¹ g x)
  ⟨≡⟩ inv-ap g x
inv-ap (f ⊗ g) (x , y) = cong₂ _,_ (inv-ap f x) (inv-ap g y)
inv-ap (f ⊕ g) (left x)  = left  $≡ inv-ap f x
inv-ap (f ⊕ g) (right x) = right $≡ inv-ap g x

syntax fwd  f x = f ♯ x
syntax bwd  f x = f ♭ x

syntax ap   f x = f ▸ x
syntax ap⁻¹ f x = f ◂ x

{-
The size of a type A is a natural number equal to the lub to any element of A. 
We can also measure the size of an individual element of A, which may differ
for elements when there are sums present in A.
-}

size : U → Nat
size 𝟘 = 0
size 𝟙 = 1
size (A ⊕ B) = max (size A) (size B)
size (A ⊗ B) = size A + size B

sizeEl : ∀ A → El A → Nat
sizeEl 𝟘       ()
sizeEl 𝟙       tt        = 1
sizeEl (A ⊕ B) (left x)  = sizeEl A x
sizeEl (A ⊕ B) (right x) = sizeEl B x
sizeEl (A ⊗ B) (x , y)   = sizeEl A x + sizeEl B y

{-
`path-length` calculates the total number of computation steps required,
according to a given valuation of the primitive isomorphisms. (see _≅_ type defn)

For any (f : A ⟷ B), the number of steps taken to transform an (x : El A) to (ap f x : El B)
depends on the value of `x`, due to the difference in steps between the two possible cases
of `path-length (f ⊕ g)`.

-}

module _ (t : ∀ {A B} → A ≅ B → El A → Nat) where
  path-length : ∀ {A B} → A ⟷ B → El A → Nat
  --| in the primitive case, we use the supplied valuation.
  path-length [ f ]             = t f
  --| `id` has unit length. Although it does no work, an abstract machine processing
  --  the morphism (f ∘ id) might still need to decompose the task into processing `f`,
  --  and processing `id`.
  path-length id      _         = 1
  --| the inverse of a morphism f takes the same number of steps to compute
  --  as does f.
  path-length (f ⁻¹)  x         = path-length f (ap⁻¹ f x)
  --| composition is sequential, and so time is added.
  path-length (g ∘ f) x         = path-length f x + path-length g (ap f x)
  --| the product tensor runs two processes in parallel, and so takes
  --  the max time of the individual processes.
  path-length (f ⊗ g) (x , y)   = max (path-length f x) (path-length g y)
  --| The coproduct tensor of two processes may take different amounts of
  --  time to run, depending on from which side of the disjoint union
  --  a particular input element is drawn.
  path-length (f ⊕ g) (left x)  = path-length f x
  path-length (f ⊕ g) (right x) = path-length g x

{-
`circuit-length` is an upper bound of `path-length`, across all possible (x : El A).
Consequently, it is independent of any particular element (x : El A).

Here, a circuit is a spatial layout of a program in two dimensions, the "width" representing
"size", or memory usage, or storage requirements of a program, and the "length" representing
the stage of execution of the program.
-}

module _ (t : ∀ {A B} → A ≅ B → Nat) where
  circuit-length : ∀ {A B} → A ⟷ B → Nat
  circuit-length [ f ]   = t f
  circuit-length id      = 1
  circuit-length (f ⁻¹)  = circuit-length f
  circuit-length (g ∘ f) = circuit-length f + circuit-length g
  circuit-length (f ⊗ g) = max (circuit-length f) (circuit-length g)
  circuit-length (f ⊕ g) = max (circuit-length f) (circuit-length g)

{-
`circuit-width` measures the maximum width of the circuit described. viz. The maximum of the widths of all cross-section types.
-}

module _ (w : ∀ {A B} → A ≅ B → Nat) where
  circuit-width : ∀ {A B} → A ⟷ B → Nat
  circuit-width [ f ]   = w f
  circuit-width {A} id  = size A
  circuit-width (f ⁻¹)  = circuit-width f
  circuit-width (g ∘ f) = max (circuit-width f) (circuit-width g)
  circuit-width (f ⊗ g) = circuit-width f + circuit-width g
  circuit-width (f ⊕ g) = max (circuit-width f) (circuit-width g)

{-
Proposition: For any morphism f : A ⟷ B, (circuit-length f) is the least upper bound of (path-length f x), for any x.
-}

Max : ∀ A → (El A → Nat) → Nat
Max 𝟘 f = 0
Max 𝟙 f = f tt
Max (A ⊕ B) f = max (Max A (f P.∘ left)) (Max B (f P.∘ right))
Max (A ⊗ B) f = Max A λ a → Max B λ b → f (a , b)

Maximum : ∀ A (f : El A → Nat) (x : El A) → f x ≤ Max A f
Maximum 𝟘 f ()
Maximum 𝟙 f tt = diff! 0
Maximum (A ⊕ B) f (left x) = prf
  where
  MA : f (left x) ≤ Max A (f P.∘ left)
  MA = Maximum A (f P.∘ left) x
  prf : f (left x) ≤ max (Max A (f P.∘ left)) (Max B (f P.∘ right))
  prf = {!!}
Maximum (A ⊕ B) f (right x) = prf
  where
  MB : f (right x) ≤ Max B (f P.∘ right)
  MB = Maximum B (f P.∘ right) x
  prf : f (right x) ≤ max (Max A (f P.∘ left)) (Max B (f P.∘ right))
  prf = {!!}
Maximum (A ⊗ B) f (x , y) = {!!}

{-
Lemma: The max of a constant function is the value of the function.
-}
MaxConst : ∀ n A → El A → Max A (λ _ → n) ≡ n
MaxConst n 𝟘 ()
MaxConst n 𝟙 tt = P.refl
MaxConst n (A ⊕ B) (left x) = {!!}
MaxConst n (A ⊕ B) (right x) = {!!}
MaxConst n (A ⊗ B) (x , y) = {!!}

module _ (t : ∀ {A B} → A ≅ B → Nat) where
  path≤circuit : ∀ {A B} 
               → (f : A ⟷ B)
               → Max A (path-length (λ f _ → t f) f) ≤ circuit-length t f
  path≤circuit [ f ]   = {!!}
  path≤circuit id      = {!!}
  path≤circuit (f ⁻¹)  = {!!}
  path≤circuit (g ∘ f) = {!!}
  path≤circuit (f ⊗ g) = {!!}
  path≤circuit (f ⊕ g) = {!!}

{-
Future work:
* Continue the literature search. Much of the underpinnings of this work are speculative,
  such as the definitions of 'width' and 'length'.
* Continue the search for time/space invariants, and other properties of equivalence classes
  of morphisms.
* Derive circuit-length circuit-width explicitly as LUBs
  over element dependent metrics path-length and path-width (currently undefined).
* Find examples! The primitive objects and morphisms used here will only produce
  straight-line programs.
* c.f. lit on complexity analysis and tradeoffs re. straight-line programs.
-}

-- These are the canonical equivalences arising from the categorical structure of a symmetric monoidal category.
-- I thought they might be a good place to start looking for nonzero time/space tradeoffs.

-- Should we investigate at all toward some form of distribuitive monoidal category?

{-
∘idₗ : ∀ {A B} (f : A ⟷ B) → id ∘ f ≅ f

∘idᵣ : ∀ {A B} (f : A ⟷ B) → f ∘ id ≅ f

∘invₗ : ∀ {A B} (f : A ⟷ B)
      → f ⁻¹ ∘ f ≅ id

∘invᵣ : ∀ {A B} (f : A ⟷ B)
      → f ∘ f ⁻¹ ≅ id

∘assoc : ∀ {A B C D}
       → (f : A ⟷ B) (g : B ⟷ C) (h : C ⟷ D)
       → (h ∘ g) ∘ f ≅ h ∘ (g ∘ f)

⁻¹cong : ∀ {A B}
       → {f g : A ⟷ B} → f ≅ g
       → f ⁻¹ ≅ g ⁻¹

∘cong : ∀ {A B C}
      → {f g : A ⟷ B} → f ≅ g
      → {h i : B ⟷ C} → h ≅ i
      → h ∘ f ≅ i ∘ g

⊗cong : ∀ {A B C D}
      → {f g : A ⟷ B} → f ≅ g
      → {h i : C ⟷ D} → h ≅ i
      → f ⊗ h ≅ g ⊗ i

⊕cong : ∀ {A B C D}
      → {f g : A ⟷ B} → f ≅ g
      → {h i : C ⟷ D} → h ≅ i
      → f ⊕ h ≅ g ⊕ i

∘/⁻¹ : ∀ {A B C}
     → (f : A ⟷ B) (g : B ⟷ C)
     → (g ∘ f) ⁻¹ ≅ f ⁻¹ ∘ g ⁻¹

⊗tri : ∀ {A B}
     → (id ⊗ [ ⊗λ ]) ∘ [ ⊗α ] ≅ [ ⊗ρ ] ⊗ id ∶ (A ⊗ 𝟙) ⊗ B ⟷ A ⊗ B

⊕tri : ∀ {A B}
     → (id ⊕ [ ⊕λ ]) ∘ [ ⊕α ] ≅ [ ⊕ρ ] ⊕ id ∶ (A ⊕ 𝟘) ⊕ B ⟷ A ⊕ B

⊕pent : ∀ {A B C D}
      → [ ⊕α ] ∘ [ ⊕α ] ≅ (id ⊕ [ ⊕α ]) ∘ [ ⊕α ] ∘ ([ ⊕α ] ⊕ id) ∶ ((A ⊕ B) ⊕ C) ⊕ D ⟷ A ⊕ (B ⊕ (C ⊕ D))

⊗pent : ∀ {A B C D}
      → [ ⊗α ] ∘ [ ⊗α ] ≅ (id ⊗ [ ⊗α ]) ∘ [ ⊗α ] ∘ ([ ⊗α ] ⊗ id) ∶ ((A ⊗ B) ⊗ C) ⊗ D ⟷ A ⊗ (B ⊗ (C ⊗ D))

⊗hex : ∀ {A B C}
     → (id ⊗ [ ⊗σ ]) ∘ [ ⊗α ] ∘ ([ ⊗σ ] ⊗ id) ≅ [ ⊗α ] ∘ [ ⊗σ ] ∘ [ ⊗α ] ∶ (A ⊗ B) ⊗ C ⟷ B ⊗ (C ⊗ A)

⊕hex : ∀ {A B C}
     → (id ⊕ [ ⊕σ ]) ∘ [ ⊕α ] ∘ ([ ⊕σ ] ⊕ id) ≅ [ ⊕α ] ∘ [ ⊕σ ] ∘ [ ⊕α ] ∶ (A ⊕ B) ⊕ C ⟷ B ⊕ (C ⊕ A)

⊗hex⁻¹ : ∀ {A B C}
       → ([ ⊗σ ] ⊗ id) ∘ [ ⊗α ] ⁻¹ ∘ (id ⊗ [ ⊗σ ]) ≅ [ ⊗α ] ⁻¹ ∘ [ ⊗σ ] ∘ [ ⊗α ] ⁻¹ ∶ A ⊗ (B ⊗ C) ⟷ (C ⊗ A) ⊗ B

⊕hex⁻¹ : ∀ {A B C}
       → ([ ⊕σ ] ⊕ id) ∘ [ ⊕α ] ⁻¹ ∘ (id ⊕ [ ⊕σ ]) ≅ [ ⊕α ] ⁻¹ ∘ [ ⊕σ ] ∘ [ ⊕α ] ⁻¹ ∶ A ⊕ (B ⊕ C) ⟷ (C ⊕ A) ⊕ B
-}
