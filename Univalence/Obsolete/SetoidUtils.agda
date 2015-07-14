{-
-- an ≃ equivalence of types can be lifted to a ≃S equivalence 
-- (over their ≡-Setoids)
-- NOT NEEDED
lift≃ : ∀ {ℓ} → {A B : Set ℓ} → A ≃ B → (≡-Setoid A) ≃S (≡-Setoid B)
lift≃ {_} {A} {B} (f , mkqinv g α β) = equiv AS BS α' β'
  where
    module AA = Setoid (≡-Setoid A)
    module BB = Setoid (≡-Setoid B)
    AS : ≡-Setoid A ⟶ ≡-Setoid B
    AS = →to⟶ f
    BS : ≡-Setoid B ⟶ ≡-Setoid A
    BS = →to⟶ g
    α' : {x y : B} → P._≡_ x y → P._≡_ (f (g x)) y
    α' = λ {x} {y} p → BB.trans (α x) p
    β' : {x y : A} → P._≡_ x y → P._≡_ (g (f x)) y
    β' = λ {x} {y} p → AA.trans (β x) p

-}
