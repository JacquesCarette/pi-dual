{-# OPTIONS --without-K #-}

module Pi1Examples where

open import PiU using (U; ONE) 
open import PiLevel0 using (_⟷_; _◎_; _⊗_; id⟷;
  swap₊; unite⋆l; unite⋆r;
  swap⋆; uniti⋆l; uniti⋆r)
open import Pi0Examples using (BOOL)
open import PiLevel1 using (_⇔_; id⇔; trans⇔; _⊡_;
  assoc◎l; swapl⋆⇔; assoc◎r; linv◎l; idl◎l; idr◎l; unitil⋆⇔l)

------------------------------------------------------------------------------
-- Better syntax for writing 2paths

infix  2  _▤       
infixr 2  _⇔⟨_⟩_   

_⇔⟨_⟩_ : {t₁ t₂ : U} (c₁ : t₁ ⟷ t₂) {c₂ : t₁ ⟷ t₂} {c₃ : t₁ ⟷ t₂} → 
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
_ ⇔⟨ α ⟩ β = trans⇔ α β

_▤ : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → (c ⇔ c)
_▤ c = id⇔

------------------------------------------------------------------------------
-- a nice example of 2 paths

neg₁ neg₂ neg₃ neg₄ neg₅ : BOOL ⟷ BOOL
neg₁ = swap₊
neg₂ = id⟷ ◎ swap₊
neg₃ = swap₊ ◎ swap₊ ◎ swap₊
neg₄ = swap₊ ◎ id⟷
neg₅ = uniti⋆l ◎ swap⋆ ◎ (swap₊ ⊗ id⟷) ◎ swap⋆ ◎ unite⋆l
neg₆ = uniti⋆r ◎ (swap₊ {ONE} {ONE} ⊗ id⟷) ◎ unite⋆r

negEx : neg₅ ⇔ neg₁
negEx = uniti⋆l ◎ (swap⋆ ◎ ((swap₊ ⊗ id⟷) ◎ (swap⋆ ◎ unite⋆l)))
          ⇔⟨ id⇔ ⊡ assoc◎l ⟩
        uniti⋆l ◎ ((swap⋆ ◎ (swap₊ ⊗ id⟷)) ◎ (swap⋆ ◎ unite⋆l))
          ⇔⟨ id⇔ ⊡ (swapl⋆⇔ ⊡ id⇔) ⟩
        uniti⋆l ◎ (((id⟷ ⊗ swap₊) ◎ swap⋆) ◎ (swap⋆ ◎ unite⋆l))
          ⇔⟨ id⇔ ⊡ assoc◎r ⟩
        uniti⋆l ◎ ((id⟷ ⊗ swap₊) ◎ (swap⋆ ◎ (swap⋆ ◎ unite⋆l)))
          ⇔⟨ id⇔ ⊡ (id⇔ ⊡ assoc◎l) ⟩
        uniti⋆l ◎ ((id⟷ ⊗ swap₊) ◎ ((swap⋆ ◎ swap⋆) ◎ unite⋆l))
          ⇔⟨ id⇔ ⊡ (id⇔ ⊡ (linv◎l ⊡ id⇔)) ⟩
        uniti⋆l ◎ ((id⟷ ⊗ swap₊) ◎ (id⟷ ◎ unite⋆l))
          ⇔⟨ id⇔ ⊡ (id⇔ ⊡ idl◎l) ⟩
        uniti⋆l ◎ ((id⟷ ⊗ swap₊) ◎ unite⋆l)
          ⇔⟨ assoc◎l ⟩
        (uniti⋆l ◎ (id⟷ ⊗ swap₊)) ◎ unite⋆l
          ⇔⟨ unitil⋆⇔l ⊡ id⇔ ⟩
        (swap₊ ◎ uniti⋆l) ◎ unite⋆l
          ⇔⟨ assoc◎r ⟩
        swap₊ ◎ (uniti⋆l ◎ unite⋆l)
          ⇔⟨ id⇔ ⊡ linv◎l ⟩
        swap₊ ◎ id⟷
          ⇔⟨ idr◎l ⟩
        swap₊ ▤

------------------------------------------------------------------------------
