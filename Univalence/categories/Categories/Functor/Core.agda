{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category

module Categories.Functor.Core where

open import Level
open import Categories.Support.EqReasoning

record Functor {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    {F₁} : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]

    .{identity} : ∀ {A} → D [ F₁ (C.id {A}) ≡ D.id ]
    .{homomorphism} : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                  → D [ F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ] ]
    .{F-resp-≡} : ∀ {A B} {F G : C [ A , B ]} → C [ F ≡ G ] → D [ F₁ F ≡ F₁ G ]

  op : Functor C.op D.op
  op = record 
    { F₀ = F₀
    ; F₁ = F₁
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≡ = F-resp-≡
    }


Endofunctor : ∀ {o ℓ e} → Category o ℓ e → Set _
Endofunctor C = Functor C C

Contravariant : ∀ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Set _
Contravariant C D = Functor C.op D
  where module C = Category C

id : ∀ {o ℓ e} {C : Category o ℓ e} → Endofunctor C
id {C = C} = record 
  { F₀ = λ x → x
  ; F₁ = λ x → x
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≡ = λ x → x
  }
  where open Category.Equiv C

infixr 9 _∘_

_∘_ : ∀ {o ℓ e} {o′ ℓ′ e′} {o′′ ℓ′′ e′′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o′′ ℓ′′ e′′} 
    → Functor D E → Functor C D → Functor C E
_∘_ {C = C} {D = D} {E = E} F G = record 
  { F₀ = λ x → F₀ (G₀ x)
  ; F₁ = λ f → F₁ (G₁ f)
  ; identity = identity′
  ; homomorphism = homomorphism′
  ; F-resp-≡ = ∘-resp-≡′
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≡ to G-resp-≡)

  .identity′ : ∀ {A} → E [ F₁ (G₁ (C.id {A})) ≡ E.id ]
  identity′ = begin
                F₁ (G₁ C.id)
              ≈⟨ F-resp-≡ G.identity ⟩
                F₁ D.id
              ≈⟨ F.identity ⟩
                E.id
              ∎
    where
    open SetoidReasoning E.hom-setoid

  .homomorphism′ : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                 → E [ F₁ (G₁ (C [ g ∘ f ])) ≡ E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ]
  homomorphism′ {f = f} {g = g} = begin
                                    F₁ (G₁ (C [ g ∘ f ]))
                                  ≈⟨ F-resp-≡ G.homomorphism ⟩
                                    F₁ (D [ G₁ g ∘ G₁ f ])
                                  ≈⟨ F.homomorphism ⟩
                                    (E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ])
                                  ∎
    where
    open SetoidReasoning E.hom-setoid

  .∘-resp-≡′ : ∀ {A B} {F G : C [ A , B ]} 
            → C [ F ≡ G ] → E [ F₁ (G₁ F) ≡ F₁ (G₁ G) ]
  ∘-resp-≡′ = λ x → F-resp-≡ (G-resp-≡ x)
