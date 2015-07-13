{-# OPTIONS --without-K #-}

module Pif where

open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂; setoid; 
        proof-irrelevance; module ≡-Reasoning)
open import Data.Nat.Properties using (m≢1+m+n; i+j≡0⇒i≡0; i+j≡0⇒j≡0)
open import Data.Nat.Properties.Simple 
  using (+-right-identity; +-suc; +-assoc; +-comm; 
        *-assoc; *-comm; *-right-zero; distribʳ-*-+)
open import Relation.Binary.Core using (Transitive)

open import Data.String using (String)
  renaming (_++_ to _++S_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; false; true; _∧_; _∨_)
open import Data.Nat using (ℕ; suc; _+_; _∸_; _*_; _<_; _≮_; _≤_; _≰_; 
  z≤n; s≤s; _≟_; _≤?_; module ≤-Reasoning)
open import Data.Fin 
  using (Fin; zero; suc; toℕ; fromℕ; _ℕ-_; _≺_;
         raise; inject+; inject₁; inject≤; _≻toℕ_) 
  renaming (_+_ to _F+_)

open import Data.Vec 
  using (Vec; tabulate; []; _∷_ ; tail; lookup; zip; zipWith; splitAt;
         _[_]≔_; allFin; toList)
  renaming (_++_ to _++V_; map to mapV; concat to concatV)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import PiLevel0
open import Cauchy
open import Perm
open import Proofs
open import CauchyProofs
open import CauchyProofsT
open import CauchyProofsS
open import Groupoid

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes a permutation.

c2cauchy : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Cauchy (size t₁)
-- the cases that do not inspect t₁ and t₂ should be at the beginning
-- so that Agda would unfold them
c2cauchy (c₁ ◎ c₂) = 
  scompcauchy 
    (c2cauchy c₁) 
    (subst Cauchy (size≡! c₁) (c2cauchy c₂)) 
c2cauchy (c₁ ⊕ c₂) = pcompcauchy (c2cauchy c₁) (c2cauchy c₂) 
c2cauchy (c₁ ⊗ c₂) = tcompcauchy (c2cauchy c₁) (c2cauchy c₂)  
c2cauchy {PLUS ZERO t} unite₊ = idcauchy (size t)
c2cauchy {t} uniti₊ = idcauchy (size t)
c2cauchy {PLUS t₁ t₂} swap₊ = swap+cauchy (size t₁) (size t₂)
c2cauchy {PLUS t₁ (PLUS t₂ t₃)} assocl₊ = 
  idcauchy (size t₁ + (size t₂ + size t₃))
c2cauchy {PLUS (PLUS t₁ t₂) t₃} assocr₊ = 
  idcauchy ((size t₁ + size t₂) + size t₃)
c2cauchy {TIMES ONE t} unite⋆ = 
  subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t))
c2cauchy {t} uniti⋆ = idcauchy (size t)
c2cauchy {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = swap⋆cauchy (size t₁) (size t₂)
c2cauchy {TIMES t₁ (TIMES t₂ t₃)} assocl⋆ = 
  idcauchy (size t₁ * (size t₂ * size t₃))
c2cauchy {TIMES (TIMES t₁ t₂) t₃} assocr⋆ = 
  idcauchy ((size t₁ * size t₂) * size t₃)
c2cauchy {TIMES ZERO t} distz = []
c2cauchy factorz = []
c2cauchy {TIMES (PLUS t₁ t₂) t₃} dist = 
  idcauchy ((size t₁ + size t₂) * size t₃)
c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} factor = 
  idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))
c2cauchy {t} id⟷  = idcauchy (size t)

c2perm : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → Permutation (size t₁)
-- the cases that do not inspect t₁ and t₂ should be at the beginning
-- so that Agda would unfold them
c2perm (c₁ ◎ c₂) = 
  scompperm 
    (c2perm c₁) 
    (subst Permutation (size≡! c₁) (c2perm c₂)) 
c2perm (c₁ ⊕ c₂) = pcompperm (c2perm c₁) (c2perm c₂) 
c2perm (c₁ ⊗ c₂) = tcompperm (c2perm c₁) (c2perm c₂)  
c2perm unfoldBool = idperm 2
c2perm foldBool   = idperm 2
c2perm {PLUS ZERO t} unite₊ = idperm (size t)
c2perm {t} uniti₊ = idperm (size t)
c2perm {PLUS t₁ t₂} swap₊ = swap+perm (size t₁) (size t₂)
c2perm {PLUS t₁ (PLUS t₂ t₃)} assocl₊ = 
  idperm (size t₁ + (size t₂ + size t₃))
c2perm {PLUS (PLUS t₁ t₂) t₃} assocr₊ = 
  idperm ((size t₁ + size t₂) + size t₃)
c2perm {TIMES ONE t} unite⋆ = 
  subst Permutation (sym (+-right-identity (size t))) (idperm (size t))
c2perm {t} uniti⋆ = idperm (size t)
c2perm {TIMES t₁ t₂} {TIMES .t₂ .t₁} swap⋆ = swap⋆perm (size t₁) (size t₂) 
c2perm {TIMES t₁ (TIMES t₂ t₃)} assocl⋆ = 
  idperm (size t₁ * (size t₂ * size t₃))
c2perm {TIMES (TIMES t₁ t₂) t₃} assocr⋆ = 
  idperm ((size t₁ * size t₂) * size t₃)
c2perm {TIMES ZERO t} distz = emptyperm
c2perm factorz = emptyperm
c2perm {TIMES (PLUS t₁ t₂) t₃} dist = 
  idperm ((size t₁ + size t₂) * size t₃)
c2perm {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} factor = 
  idperm ((size t₁ * size t₃) + (size t₂ * size t₃))
c2perm {t} id⟷  = idperm (size t)

-- Looking forward to Sec. 2.2 (Functions are functors). The
-- corresponding statement to Lemma 2.2.1 in our setting would be the
-- following. Given any *size preserving* function f : U → U, it is
-- the case that a combinator (path) c : t₁ ⟷ t₂ maps to a combinator
-- (path) ap_f(c) : f(t₁) ⟷ f(t₂).

------------------------------------------------------------------------------
-- Extensional equivalence of combinators

-- Two combinators are equivalent if they denote the same
-- permutation. Generally we would require that the two permutations
-- map the same value x to values y and z that have a path between
-- them, but because the internals of each type are discrete
-- groupoids, this reduces to saying that y and z are identical, and
-- hence that the permutations are identical.

infix  10  _∼_  

_∼_ : {t₁ t₂ : U} → (c₁ c₂ : t₁ ⟷ t₂) → Set
c₁ ∼ c₂ = (c2cauchy c₁ ≡ c2cauchy c₂)

-- The relation ~ is an equivalence relation

refl∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ∼ c)
refl∼ = refl 

sym∼ : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₁)
sym∼ = sym

trans∼ : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ∼ c₂) → (c₂ ∼ c₃) → (c₁ ∼ c₃)
trans∼ = trans

assoc∼ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
         c₁ ◎ (c₂ ◎ c₃) ∼ (c₁ ◎ c₂) ◎ c₃
assoc∼ {t₁} {t₂} {t₃} {t₄} {c₁} {c₂} {c₃} = 
  begin (c2cauchy (c₁ ◎ (c₂ ◎ c₃))
           ≡⟨ refl ⟩ 
         scompcauchy
           (c2cauchy c₁)
           (subst Cauchy (size≡! c₁)
             (scompcauchy
               (c2cauchy c₂)
               (subst Cauchy (size≡! c₂) (c2cauchy c₃))))
           ≡⟨ cong 
                (scompcauchy (c2cauchy c₁))
                (subst-dist 
                  scompcauchy 
                  (size≡! c₁) 
                  (c2cauchy c₂)
                  (subst Cauchy (size≡! c₂) (c2cauchy c₃))) ⟩ 
         scompcauchy
           (c2cauchy c₁)
           (scompcauchy
             (subst Cauchy (size≡! c₁) (c2cauchy c₂))
             (subst Cauchy (size≡! c₁)
               (subst Cauchy (size≡! c₂) (c2cauchy c₃))))
           ≡⟨ cong (λ x → 
                scompcauchy 
                  (c2cauchy c₁)
                  (scompcauchy 
                    (subst Cauchy (size≡! c₁) (c2cauchy c₂))
                    x))
                (subst-trans (size≡! c₁) (size≡! c₂) (c2cauchy c₃)) ⟩ 
         scompcauchy
           (c2cauchy c₁)
           (scompcauchy
             (subst Cauchy (size≡! c₁) (c2cauchy c₂))
             (subst Cauchy (trans (size≡! c₂) (size≡! c₁)) (c2cauchy c₃)))
           ≡⟨ scompassoc 
                (c2cauchy c₁) 
                (subst Cauchy (size≡! c₁) (c2cauchy c₂)) 
                (subst Cauchy (trans (size≡! c₂) (size≡! c₁)) (c2cauchy c₃)) ⟩
         scompcauchy 
           (scompcauchy 
             (c2cauchy c₁)
             (subst Cauchy (size≡! c₁) (c2cauchy c₂)))
           (subst Cauchy (trans (size≡! c₂) (size≡! c₁)) (c2cauchy c₃))
           ≡⟨ refl ⟩ 
         c2cauchy ((c₁ ◎ c₂) ◎ c₃) ∎)
  where open ≡-Reasoning

-- The combinators c : t₁ ⟷ t₂ are paths; we can transport
-- size-preserving properties across c. In particular, for some
-- appropriate P we want P(t₁) to map to P(t₂) via c.

-- The relation ~ validates the groupoid laws

c◎id∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ id⟷ ∼ c
c◎id∼c {t₁} {t₂} {c} = 
  begin (c2cauchy (c ◎ id⟷)
           ≡⟨ refl ⟩ 
        scompcauchy 
          (c2cauchy c)
          (subst Cauchy (size≡! c) (allFin (size t₂)))
           ≡⟨ cong (λ x → scompcauchy (c2cauchy c) x) 
              (congD! {B = Cauchy} allFin (size≡! c)) ⟩ 
        scompcauchy (c2cauchy c) (allFin (size t₁))
           ≡⟨ scomprid (c2cauchy c) ⟩ 
         c2cauchy c ∎)
  where open ≡-Reasoning

id◎c∼c : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ◎ c ∼ c
id◎c∼c {t₁} {t₂} {c} = 
  begin (c2cauchy (id⟷ ◎ c)
           ≡⟨ refl ⟩ 
        scompcauchy 
          (allFin (size t₁))
          (subst Cauchy refl (c2cauchy c))
           ≡⟨ refl ⟩ 
        scompcauchy (allFin (size t₁)) (c2cauchy c)
           ≡⟨ scomplid (c2cauchy c) ⟩ 
         c2cauchy c ∎)
  where open ≡-Reasoning

linv∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ◎ ! c ∼ id⟷
linv∼ {PLUS ZERO t} {.t} {unite₊} = 
  begin (c2cauchy {PLUS ZERO t} (unite₊ ◎ uniti₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {PLUS ZERO t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {t} {PLUS ZERO .t} {uniti₊} = 
  begin (c2cauchy {t} (uniti₊ ◎ unite₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS t₁ t₂} {PLUS .t₂ .t₁} {swap₊} =
  begin (c2cauchy {PLUS t₁ t₂} (swap₊ ◎ swap₊)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (swap+cauchy (size t₁) (size t₂))
           (subst Cauchy (+-comm (size t₂) (size t₁)) 
             (swap+cauchy (size t₂) (size t₁)))
           ≡⟨ swap+idemp (size t₁) (size t₂) ⟩ 
         c2cauchy {PLUS t₁ t₂} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} {assocl₊} = 
  begin (c2cauchy {PLUS t₁ (PLUS t₂ t₃)} (assocl₊ ◎ assocr₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃)))
           (subst Cauchy (+-assoc (size t₁) (size t₂) (size t₃))
             (idcauchy ((size t₁ + size t₂) + size t₃)))
           ≡⟨ cong 
               (scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃))))
               (congD! idcauchy (+-assoc (size t₁) (size t₂) (size t₃))) ⟩ 
         scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃)))
           (idcauchy (size t₁ + (size t₂ + size t₃)))
           ≡⟨ scomplid (idcauchy (size t₁ + (size t₂ + size t₃))) ⟩ 
         c2cauchy {PLUS t₁ (PLUS t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} {assocr₊} = 
  begin (c2cauchy {PLUS (PLUS t₁ t₂) t₃} (assocr₊ ◎ assocl₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃))
           (subst Cauchy (sym (+-assoc (size t₁) (size t₂) (size t₃)))
             (idcauchy (size t₁ + (size t₂ + size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃)))
                (congD! idcauchy (sym (+-assoc (size t₁) (size t₂) (size t₃)))) ⟩
         scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃))
           (idcauchy ((size t₁ + size t₂) + size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ + size t₂) + size t₃)) ⟩ 
         c2cauchy {PLUS (PLUS t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES ONE t} {.t} {unite⋆} = 
  begin (c2cauchy {TIMES ONE t} (unite⋆ ◎ uniti⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t)))
           (subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t)))
           ≡⟨ cong  
                (λ x → scompcauchy x x) 
                (congD! idcauchy (sym (+-right-identity (size t)))) ⟩ 
         scompcauchy (idcauchy (size t + 0)) (idcauchy (size t + 0))
           ≡⟨ scomplid (idcauchy (size t + 0)) ⟩ 
         c2cauchy {TIMES ONE t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {t} {TIMES ONE .t} {uniti⋆} = 
  begin (c2cauchy {t} (uniti⋆ ◎ unite⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy (+-right-identity (size t))
             (subst Cauchy (sym (+-right-identity (size t))) 
               (idcauchy (size t))))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t)))
                (subst-trans 
                  (+-right-identity (size t))
                  (sym (+-right-identity (size t))) 
                  (idcauchy (size t))) ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy (trans (sym (+-right-identity (size t)))
                                (+-right-identity (size t)))
               (idcauchy (size t)))
           ≡⟨ cong 
                 (λ x → scompcauchy 
                          (idcauchy (size t))
                          (subst Cauchy x (idcauchy (size t))))
                 (trans-syml (+-right-identity (size t))) ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy refl (idcauchy (size t)))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES t₁ t₂} {TIMES .t₂ .t₁} {swap⋆} = 
  begin (c2cauchy {TIMES t₁ t₂} (swap⋆ ◎ swap⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (swap⋆cauchy (size t₁) (size t₂))
           (subst Cauchy (*-comm (size t₂) (size t₁)) 
             (swap⋆cauchy (size t₂) (size t₁)))
           ≡⟨ swap⋆idemp (size t₁) (size t₂) ⟩
         c2cauchy {TIMES t₁ t₂} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} {assocl⋆} = 
  begin (c2cauchy {TIMES t₁ (TIMES t₂ t₃)} (assocl⋆ ◎ assocr⋆)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃)))
           (subst Cauchy (*-assoc (size t₁) (size t₂) (size t₃))
             (idcauchy ((size t₁ * size t₂) * size t₃)))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃))))
                (congD! idcauchy (*-assoc (size t₁) (size t₂) (size t₃))) ⟩ 
         scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃)))
           (idcauchy (size t₁ * (size t₂ * size t₃)))
           ≡⟨ scomplid (idcauchy (size t₁ * (size t₂ * size t₃))) ⟩ 
         c2cauchy {TIMES t₁ (TIMES t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES (TIMES t₁ t₂) t₃} {TIMES .t₁ (TIMES .t₂ .t₃)} {assocr⋆} = 
  begin (c2cauchy {TIMES (TIMES t₁ t₂) t₃} (assocr⋆ ◎ assocl⋆)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃))
           (subst Cauchy (sym (*-assoc (size t₁) (size t₂) (size t₃)))
             (idcauchy (size t₁ * (size t₂ * size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃)))
                (congD! idcauchy (sym (*-assoc (size t₁) (size t₂) (size t₃)))) ⟩
         scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃))
           (idcauchy ((size t₁ * size t₂) * size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ * size t₂) * size t₃)) ⟩ 
         c2cauchy {TIMES (TIMES t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES ZERO t} {ZERO} {distz} = refl
linv∼ {ZERO} {TIMES ZERO t} {factorz} = refl
linv∼ {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} {dist} = 
  begin (c2cauchy {TIMES (PLUS t₁ t₂) t₃} (dist ◎ factor)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃))
           (subst Cauchy (sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂)))
             (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃)))
                (congD! idcauchy 
                  (sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂)))) ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃))
           (idcauchy ((size t₁ + size t₂) * size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ + size t₂) * size t₃)) ⟩ 
         c2cauchy {TIMES (PLUS t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} {TIMES (PLUS .t₁ .t₂) .t₃} {factor} = 
  begin (c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)} (factor ◎ dist)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           (subst Cauchy (distribʳ-*-+ (size t₃) (size t₁) (size t₂))
             (idcauchy ((size t₁ + size t₂) * size t₃)))
           ≡⟨ cong 
                (scompcauchy 
                  (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))))
                (congD! idcauchy 
                  (distribʳ-*-+ (size t₃) (size t₁) (size t₂))) ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           ≡⟨ scomplid (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))) ⟩ 
         c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {t} {.t} {id⟷} = 
  begin (c2cauchy {t} (id⟷ ◎ id⟷)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {t₁} {t₃} {_◎_ {t₂ = t₂} c₁ c₂} = 
  begin (c2cauchy {t₁} ((c₁ ◎ c₂) ◎ ((! c₂) ◎ (! c₁)))
           ≡⟨ refl ⟩ 
         scompcauchy 
           (scompcauchy 
              (c2cauchy c₁) 
              (subst Cauchy (size≡! c₁) (c2cauchy c₂)))
           (subst Cauchy (trans (size≡! c₂) (size≡! c₁))
              (scompcauchy 
                (c2cauchy (! c₂)) 
                (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))
           ≡⟨ sym (scompassoc 
                    (c2cauchy c₁)
                    (subst Cauchy (size≡! c₁) (c2cauchy c₂))
                    (subst Cauchy (trans (size≡! c₂) (size≡! c₁))
                      (scompcauchy
                        (c2cauchy (! c₂))
                        (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))))  ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (scompcauchy 
              (subst Cauchy (size≡! c₁) (c2cauchy c₂))
              (subst Cauchy (trans (size≡! c₂) (size≡! c₁))
                (scompcauchy
                  (c2cauchy (! c₂))
                  (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (scompcauchy 
                           (subst Cauchy (size≡! c₁) (c2cauchy c₂))
                           x))
                (sym (subst-trans (size≡! c₁) (size≡! c₂)
                       (scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (scompcauchy 
              (subst Cauchy (size≡! c₁) (c2cauchy c₂))
              (subst Cauchy (size≡! c₁) 
                (subst Cauchy (size≡! c₂)
                  (scompcauchy
                    (c2cauchy (! c₂))
                    (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))))
           ≡⟨ cong 
                (scompcauchy (c2cauchy c₁))
                (sym (subst-dist scompcauchy (size≡! c₁)
                       (c2cauchy c₂)
                       (subst Cauchy (size≡! c₂)
                         (scompcauchy
                           (c2cauchy (! c₂))
                           (subst Cauchy (size≡! (! c₂)) 
                             (c2cauchy (! c₁))))))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (scompcauchy 
               (c2cauchy c₂)
               (subst Cauchy (size≡! c₂)
                 (scompcauchy
                   (c2cauchy (! c₂))
                   (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁)
                           (scompcauchy (c2cauchy c₂) x)))
                (subst-dist scompcauchy (size≡! c₂)
                  (c2cauchy (! c₂))
                  (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (scompcauchy 
               (c2cauchy c₂)
                 (scompcauchy
                   (subst Cauchy (size≡! c₂) (c2cauchy (! c₂)))
                   (subst Cauchy (size≡! c₂) 
                     (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) x))
                (scompassoc 
                  (c2cauchy c₂)
                  (subst Cauchy (size≡! c₂) (c2cauchy (! c₂)))
                  (subst Cauchy (size≡! c₂) 
                    (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (scompcauchy 
               (scompcauchy
                 (c2cauchy c₂)
                 (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
               (subst Cauchy (size≡! c₂) 
                 (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁)
                           (scompcauchy 
                             x
                             (subst Cauchy (size≡! c₂)
                               (subst Cauchy (size≡! (! c₂)) 
                                 (c2cauchy (! c₁)))))))
                (linv∼ {t₂} {t₃} {c₂}) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (scompcauchy 
               (allFin (size t₂))
               (subst Cauchy (size≡! c₂) 
                 (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))))
           ≡⟨ cong 
                (λ x → scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) x))
                (scomplid
                  (subst Cauchy (size≡! c₂) 
                    (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (subst Cauchy (size≡! c₂) 
               (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))))
           ≡⟨ cong 
                (λ x → scompcauchy 
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) x))
                (subst-trans (size≡! c₂) (size≡! (! c₂))
                  (c2cauchy (! c₁))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) 
             (subst Cauchy (trans (size≡! (! c₂)) (size≡! c₂))
               (c2cauchy (! c₁))))
           ≡⟨ cong 
                (λ x → scompcauchy 
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) 
                           (subst Cauchy x (c2cauchy (! c₁)))))
                (trans 
                  (cong (λ y → trans y (size≡! c₂)) (size≡!! c₂)) 
                  (trans-syml (size≡! c₂))) ⟩ 
         scompcauchy 
           (c2cauchy c₁) 
           (subst Cauchy (size≡! c₁) (c2cauchy (! c₁)))
           ≡⟨ linv∼ {t₁} {t₂} {c₁} ⟩ 
         c2cauchy {t₁} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS t₁ t₂} {PLUS t₃ t₄} {c₁ ⊕ c₂} = 
  begin (c2cauchy {PLUS t₁ t₂} ((c₁ ⊕ c₂) ◎ ((! c₁) ⊕ (! c₂)))
           ≡⟨ refl ⟩ 
         scompcauchy
           (pcompcauchy (c2cauchy c₁) (c2cauchy c₂))
           (subst Cauchy (cong₂ _+_ (size≡! c₁) (size≡! c₂))
             (pcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂))))
           ≡⟨ cong 
                (scompcauchy (pcompcauchy (c2cauchy c₁) (c2cauchy c₂)))
                (subst₂+ 
                  (size≡! c₁) (size≡! c₂) 
                  (c2cauchy (! c₁)) (c2cauchy (! c₂))
                  pcompcauchy) ⟩
         scompcauchy
           (pcompcauchy (c2cauchy c₁) (c2cauchy c₂))
           (pcompcauchy 
             (subst Cauchy (size≡! c₁) (c2cauchy (! c₁)))
             (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
           ≡⟨ pcomp-dist 
               (c2cauchy c₁) 
               (subst Cauchy (size≡! c₁) (c2cauchy (! c₁)))
               (c2cauchy c₂) (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))) ⟩
         pcompcauchy 
           (scompcauchy 
             (c2cauchy c₁) 
             (subst Cauchy (size≡! c₁) (c2cauchy (! c₁))))
           (scompcauchy 
             (c2cauchy c₂) 
             (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
           ≡⟨ cong₂ pcompcauchy (linv∼ {t₁} {t₃} {c₁}) (linv∼ {t₂} {t₄} {c₂}) ⟩
         pcompcauchy (c2cauchy {t₁} id⟷) (c2cauchy {t₂} id⟷)
           ≡⟨ pcomp-id {size t₁} {size t₂} ⟩ 
         c2cauchy {PLUS t₁ t₂} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {TIMES t₁ t₂} {TIMES t₃ t₄} {c₁ ⊗ c₂} = 
  begin (c2cauchy {TIMES t₁ t₂} ((c₁ ⊗ c₂) ◎ ((! c₁) ⊗ (! c₂)))
           ≡⟨ refl ⟩ 
         scompcauchy
           (tcompcauchy (c2cauchy c₁) (c2cauchy c₂))
           (subst Cauchy (cong₂ _*_ (size≡! c₁) (size≡! c₂))
             (tcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂))))
           ≡⟨ cong 
                (scompcauchy (tcompcauchy (c2cauchy c₁) (c2cauchy c₂)))
                (subst₂*
                  (size≡! c₁) (size≡! c₂)
                  (c2cauchy (! c₁)) (c2cauchy (! c₂))
                  tcompcauchy) ⟩ 
         scompcauchy 
           (tcompcauchy (c2cauchy c₁) (c2cauchy c₂))
           (tcompcauchy
             (subst Cauchy (size≡! c₁) (c2cauchy (! c₁)))
             (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
           ≡⟨ tcomp-dist
                (c2cauchy c₁)
                (subst Cauchy (size≡! c₁) (c2cauchy (! c₁))) 
                (c2cauchy c₂)
                (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))) ⟩
         tcompcauchy
           (scompcauchy 
             (c2cauchy c₁)
             (subst Cauchy (size≡! c₁) (c2cauchy (! c₁))))
           (scompcauchy 
             (c2cauchy c₂)
             (subst Cauchy (size≡! c₂) (c2cauchy (! c₂))))
           ≡⟨ cong₂ tcompcauchy (linv∼ {t₁} {t₃} {c₁}) (linv∼ {t₂} {t₄} {c₂}) ⟩ 
         tcompcauchy (c2cauchy {t₁} id⟷) (c2cauchy {t₂} id⟷)
            ≡⟨ tcomp-id {size t₁} {size t₂} ⟩
         c2cauchy {TIMES t₁ t₂} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {PLUS ONE ONE} {BOOL} {foldBool} = 
  begin (c2cauchy {PLUS ONE ONE} (foldBool ◎ unfoldBool)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy 2) (idcauchy 2)
           ≡⟨ scomplid (idcauchy 2) ⟩ 
         c2cauchy {PLUS ONE ONE} id⟷ ∎)
  where open ≡-Reasoning
linv∼ {BOOL} {PLUS ONE ONE} {unfoldBool} = 
  begin (c2cauchy {BOOL} (unfoldBool ◎ foldBool)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy 2) (idcauchy 2)
           ≡⟨ scomplid (idcauchy 2) ⟩ 
         c2cauchy {BOOL} id⟷ ∎)
  where open ≡-Reasoning

rinv∼ : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! c ◎ c ∼ id⟷
rinv∼ {PLUS ZERO t} {.t} {unite₊} = 
  begin (c2cauchy {t} (uniti₊ ◎ unite₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {t} {PLUS ZERO .t} {uniti₊} = 
  begin (c2cauchy {PLUS ZERO t} (unite₊ ◎ uniti₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {PLUS ZERO t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS t₁ t₂} {PLUS .t₂ .t₁} {swap₊} =
  begin (c2cauchy {PLUS t₂ t₁} (swap₊ ◎ swap₊)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (swap+cauchy (size t₂) (size t₁))
           (subst Cauchy (+-comm (size t₁) (size t₂)) 
             (swap+cauchy (size t₁) (size t₂)))
           ≡⟨ swap+idemp (size t₂) (size t₁) ⟩ 
         c2cauchy {PLUS t₂ t₁} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS t₁ (PLUS t₂ t₃)} {PLUS (PLUS .t₁ .t₂) .t₃} {assocl₊} = 
  begin (c2cauchy {PLUS (PLUS t₁ t₂) t₃} (assocr₊ ◎ assocl₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃))
           (subst Cauchy (sym (+-assoc (size t₁) (size t₂) (size t₃)))
             (idcauchy (size t₁ + (size t₂ + size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃)))
                (congD! idcauchy (sym (+-assoc (size t₁) (size t₂) (size t₃)))) ⟩
         scompcauchy (idcauchy ((size t₁ + size t₂) + size t₃))
           (idcauchy ((size t₁ + size t₂) + size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ + size t₂) + size t₃)) ⟩ 
         c2cauchy {PLUS (PLUS t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS (PLUS t₁ t₂) t₃} {PLUS .t₁ (PLUS .t₂ .t₃)} {assocr₊} = 
  begin (c2cauchy {PLUS t₁ (PLUS t₂ t₃)} (assocl₊ ◎ assocr₊)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃)))
           (subst Cauchy (+-assoc (size t₁) (size t₂) (size t₃))
             (idcauchy ((size t₁ + size t₂) + size t₃)))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃))))
                (congD! idcauchy (+-assoc (size t₁) (size t₂) (size t₃))) ⟩ 
         scompcauchy (idcauchy (size t₁ + (size t₂ + size t₃)))
           (idcauchy (size t₁ + (size t₂ + size t₃)))
           ≡⟨ scomplid (idcauchy (size t₁ + (size t₂ + size t₃))) ⟩ 
         c2cauchy {PLUS t₁ (PLUS t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES ONE t} {.t} {unite⋆} = 
  begin (c2cauchy {t} (uniti⋆ ◎ unite⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy (+-right-identity (size t))
             (subst Cauchy (sym (+-right-identity (size t))) 
               (idcauchy (size t))))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t)))
                (subst-trans 
                  (+-right-identity (size t))
                  (sym (+-right-identity (size t))) 
                  (idcauchy (size t))) ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy (trans (sym (+-right-identity (size t)))
                                (+-right-identity (size t)))
               (idcauchy (size t)))
           ≡⟨ cong 
                 (λ x → scompcauchy 
                          (idcauchy (size t))
                          (subst Cauchy x (idcauchy (size t))))
                 (trans-syml (+-right-identity (size t))) ⟩ 
         scompcauchy 
           (idcauchy (size t))
           (subst Cauchy refl (idcauchy (size t)))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {t} {TIMES ONE .t} {uniti⋆} = 
  begin (c2cauchy {TIMES ONE t} (unite⋆ ◎ uniti⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t)))
           (subst Cauchy (sym (+-right-identity (size t))) (idcauchy (size t)))
           ≡⟨ cong  
                (λ x → scompcauchy x x) 
                (congD! idcauchy (sym (+-right-identity (size t)))) ⟩ 
         scompcauchy (idcauchy (size t + 0)) (idcauchy (size t + 0))
           ≡⟨ scomplid (idcauchy (size t + 0)) ⟩ 
         c2cauchy {TIMES ONE t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES t₁ t₂} {TIMES .t₂ .t₁} {swap⋆} =
  begin (c2cauchy {TIMES t₂ t₁} (swap⋆ ◎ swap⋆)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (swap⋆cauchy (size t₂) (size t₁))
           (subst Cauchy (*-comm (size t₁) (size t₂)) 
             (swap⋆cauchy (size t₁) (size t₂)))
           ≡⟨ swap⋆idemp (size t₂) (size t₁) ⟩
         c2cauchy {TIMES t₂ t₁} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES t₁ (TIMES t₂ t₃)} {TIMES (TIMES .t₁ .t₂) .t₃} {assocl⋆} = 
  begin (c2cauchy {TIMES (TIMES t₁ t₂) t₃} (assocr⋆ ◎ assocl⋆)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃))
           (subst Cauchy (sym (*-assoc (size t₁) (size t₂) (size t₃)))
             (idcauchy (size t₁ * (size t₂ * size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃)))
                (congD! idcauchy (sym (*-assoc (size t₁) (size t₂) (size t₃)))) ⟩
         scompcauchy (idcauchy ((size t₁ * size t₂) * size t₃))
           (idcauchy ((size t₁ * size t₂) * size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ * size t₂) * size t₃)) ⟩ 
         c2cauchy {TIMES (TIMES t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES (TIMES t₁ t₂) t₃} {TIMES .t₁ (TIMES .t₂ .t₃)} {assocr⋆} = 
  begin (c2cauchy {TIMES t₁ (TIMES t₂ t₃)} (assocl⋆ ◎ assocr⋆)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃)))
           (subst Cauchy (*-assoc (size t₁) (size t₂) (size t₃))
             (idcauchy ((size t₁ * size t₂) * size t₃)))
           ≡⟨ cong 
                (scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃))))
                (congD! idcauchy (*-assoc (size t₁) (size t₂) (size t₃))) ⟩ 
         scompcauchy (idcauchy (size t₁ * (size t₂ * size t₃)))
           (idcauchy (size t₁ * (size t₂ * size t₃)))
           ≡⟨ scomplid (idcauchy (size t₁ * (size t₂ * size t₃))) ⟩ 
         c2cauchy {TIMES t₁ (TIMES t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES ZERO t} {ZERO} {distz} = refl
rinv∼ {ZERO} {TIMES ZERO t} {factorz} = refl
rinv∼ {TIMES (PLUS t₁ t₂) t₃} {PLUS (TIMES .t₁ .t₃) (TIMES .t₂ .t₃)} {dist} = 
  begin (c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)} (factor ◎ dist)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           (subst Cauchy (distribʳ-*-+ (size t₃) (size t₁) (size t₂))
             (idcauchy ((size t₁ + size t₂) * size t₃)))
           ≡⟨ cong 
                (scompcauchy 
                  (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))))
                (congD! idcauchy 
                  (distribʳ-*-+ (size t₃) (size t₁) (size t₂))) ⟩ 
         scompcauchy (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃)))
           ≡⟨ scomplid (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))) ⟩ 
         c2cauchy {PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS (TIMES t₁ t₃) (TIMES t₂ .t₃)} {TIMES (PLUS .t₁ .t₂) .t₃} {factor} = 
  begin (c2cauchy {TIMES (PLUS t₁ t₂) t₃} (dist ◎ factor)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃))
           (subst Cauchy (sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂)))
             (idcauchy ((size t₁ * size t₃) + (size t₂ * size t₃))))
           ≡⟨ cong 
                (scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃)))
                (congD! idcauchy 
                  (sym (distribʳ-*-+ (size t₃) (size t₁) (size t₂)))) ⟩ 
         scompcauchy (idcauchy ((size t₁ + size t₂) * size t₃))
           (idcauchy ((size t₁ + size t₂) * size t₃))
           ≡⟨ scomplid (idcauchy ((size t₁ + size t₂) * size t₃)) ⟩ 
         c2cauchy {TIMES (PLUS t₁ t₂) t₃} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {t} {.t} {id⟷} = 
  begin (c2cauchy {t} (id⟷ ◎ id⟷)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy (size t)) (idcauchy (size t))
           ≡⟨ scomplid (idcauchy (size t)) ⟩ 
         c2cauchy {t} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {t₁} {t₃} {_◎_ {t₂ = t₂} c₁ c₂} = 
  begin (c2cauchy {t₃} (((! c₂) ◎ (! c₁)) ◎ (c₁ ◎ c₂))
           ≡⟨ refl ⟩ 
         scompcauchy
           (scompcauchy
              (c2cauchy (! c₂))
              (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁))))
           (subst Cauchy (trans (size≡! (! c₁)) (size≡! (! c₂)))
             (scompcauchy
               (c2cauchy c₁)
               (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))
           ≡⟨ sym (scompassoc
                     (c2cauchy (! c₂))
                     (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))
                     (subst Cauchy (trans (size≡! (! c₁)) (size≡! (! c₂)))
                       (scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (scompcauchy
              (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))
              (subst Cauchy (trans (size≡! (! c₁)) (size≡! (! c₂)))
                (scompcauchy
                  (c2cauchy c₁)
                  (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (scompcauchy
                           (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))
                           x))
                (sym (subst-trans (size≡! (! c₂)) (size≡! (! c₁))
                       (scompcauchy
                         (c2cauchy c₁)
                         (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (scompcauchy
              (subst Cauchy (size≡! (! c₂)) (c2cauchy (! c₁)))
              (subst Cauchy (size≡! (! c₂))
                (subst Cauchy (size≡! (! c₁))
                  (scompcauchy
                    (c2cauchy c₁)
                    (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))))
           ≡⟨ cong
                (scompcauchy (c2cauchy (! c₂)))
                (sym (subst-dist scompcauchy (size≡! (! c₂))
                       (c2cauchy (! c₁))
                       (subst Cauchy (size≡! (! c₁))
                         (scompcauchy
                           (c2cauchy c₁)
                           (subst Cauchy (size≡! c₁) (c2cauchy c₂)))))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (scompcauchy
               (c2cauchy (! c₁))
               (subst Cauchy (size≡! (! c₁))
                 (scompcauchy
                   (c2cauchy c₁)
                   (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))))
           ≡⟨ cong 
                (λ x → scompcauchy 
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂))
                           (scompcauchy (c2cauchy (! c₁)) x)))
                (subst-dist scompcauchy (size≡! (! c₁))
                  (c2cauchy c₁)
                  (subst Cauchy (size≡! c₁) (c2cauchy  c₂))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (scompcauchy
               (c2cauchy (! c₁))
                 (scompcauchy
                   (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
                   (subst Cauchy (size≡! (! c₁))
                     (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))))
           ≡⟨ cong
                (λ x → scompcauchy 
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂)) x))
                (scompassoc
                  (c2cauchy (! c₁))
                  (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
                  (subst Cauchy (size≡! (! c₁))
                    (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))) ⟩
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (scompcauchy
               (scompcauchy
                 (c2cauchy (! c₁))
                 (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁)))
               (subst Cauchy (size≡! (! c₁))
                 (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂))
                           (scompcauchy 
                             x
                             (subst Cauchy (size≡! (! c₁))
                               (subst Cauchy (size≡! c₁) (c2cauchy  c₂))))))
                (rinv∼ {t₁} {t₂} {c₁}) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (scompcauchy
               (allFin (size t₂))
               (subst Cauchy (size≡! (! c₁))
                 (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂)) x))
                (scomplid
                  (subst Cauchy (size≡! (! c₁))
                    (subst Cauchy (size≡! c₁) (c2cauchy  c₂)))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (subst Cauchy (size≡! (! c₁))
               (subst Cauchy (size≡! c₁) (c2cauchy c₂))))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂)) x))
                (subst-trans (size≡! (! c₁)) (size≡! c₁) (c2cauchy c₂)) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂))
             (subst Cauchy (trans (size≡! c₁) (size≡! (! c₁))) 
               (c2cauchy c₂)))
           ≡⟨ cong
                (λ x → scompcauchy
                         (c2cauchy (! c₂))
                         (subst Cauchy (size≡! (! c₂))
                           (subst Cauchy x (c2cauchy c₂))))
                (trans
                  (cong (λ y → trans (size≡! c₁) y) (size≡!! c₁))
                  (trans-symr (size≡! c₁))) ⟩ 
         scompcauchy
           (c2cauchy (! c₂))
           (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂))
           ≡⟨ rinv∼ {t₂} {t₃} {c₂} ⟩ 
         c2cauchy {t₃} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS t₁ t₂} {PLUS t₃ t₄} {c₁ ⊕ c₂} =
  begin (c2cauchy {PLUS t₃ t₄} (((! c₁) ⊕ (! c₂)) ◎ (c₁ ⊕ c₂))
           ≡⟨ refl ⟩ 
         scompcauchy
           (pcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂)))
           (subst Cauchy (cong₂ _+_ (size≡! (! c₁)) (size≡! (! c₂)))
             (pcompcauchy (c2cauchy c₁) (c2cauchy c₂)))
           ≡⟨ cong 
                (scompcauchy (pcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂))))
                (subst₂+ 
                  (size≡! (! c₁)) (size≡! (! c₂))
                  (c2cauchy c₁) (c2cauchy c₂)
                  pcompcauchy) ⟩
         scompcauchy
           (pcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂)))
           (pcompcauchy 
             (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
             (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)))
           ≡⟨ pcomp-dist 
               (c2cauchy (! c₁))
               (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
               (c2cauchy (! c₂)) (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)) ⟩
         pcompcauchy 
           (scompcauchy 
             (c2cauchy (! c₁))
             (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁)))
           (scompcauchy 
             (c2cauchy (! c₂))
             (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)))
           ≡⟨ cong₂ pcompcauchy (rinv∼ {t₁} {t₃} {c₁}) (rinv∼ {t₂} {t₄} {c₂}) ⟩
         pcompcauchy (c2cauchy {t₃} id⟷) (c2cauchy {t₄} id⟷)
           ≡⟨ pcomp-id {size t₃} {size t₄} ⟩ 
         c2cauchy {PLUS t₃ t₄} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {TIMES t₁ t₂} {TIMES t₃ t₄} {c₁ ⊗ c₂} =
  begin (c2cauchy {TIMES t₃ t₄} (((! c₁) ⊗ (! c₂)) ◎ (c₁ ⊗ c₂))
           ≡⟨ refl ⟩ 
         scompcauchy
           (tcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂)))
           (subst Cauchy (cong₂ _*_ (size≡! (! c₁)) (size≡! (! c₂)))
             (tcompcauchy (c2cauchy c₁) (c2cauchy c₂)))
           ≡⟨ cong 
                (scompcauchy (tcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂))))
                (subst₂*
                  (size≡! (! c₁)) (size≡! (! c₂))
                  (c2cauchy c₁) (c2cauchy c₂)
                  tcompcauchy) ⟩ 
         scompcauchy 
           (tcompcauchy (c2cauchy (! c₁)) (c2cauchy (! c₂)))
           (tcompcauchy
             (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
             (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)))
           ≡⟨ tcomp-dist
                (c2cauchy (! c₁))
                (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁))
                (c2cauchy (! c₂))
                (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)) ⟩
         tcompcauchy
           (scompcauchy 
             (c2cauchy (! c₁))
             (subst Cauchy (size≡! (! c₁)) (c2cauchy c₁)))
           (scompcauchy 
             (c2cauchy (! c₂))
             (subst Cauchy (size≡! (! c₂)) (c2cauchy c₂)))
           ≡⟨ cong₂ tcompcauchy (rinv∼ {t₁} {t₃} {c₁}) (rinv∼ {t₂} {t₄} {c₂}) ⟩ 
         tcompcauchy (c2cauchy {t₃} id⟷) (c2cauchy {t₄} id⟷)
            ≡⟨ tcomp-id {size t₃} {size t₄} ⟩
         c2cauchy {TIMES t₃ t₄} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {PLUS ONE ONE} {BOOL} {foldBool} = 
  begin (c2cauchy {BOOL} (unfoldBool ◎ foldBool)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy 2) (idcauchy 2)
           ≡⟨ scomplid (idcauchy 2) ⟩ 
         c2cauchy {BOOL} id⟷ ∎)
  where open ≡-Reasoning
rinv∼ {BOOL} {PLUS ONE ONE} {unfoldBool} = 
  begin (c2cauchy {PLUS ONE ONE} (foldBool ◎ unfoldBool)
           ≡⟨ refl ⟩ 
         scompcauchy (idcauchy 2) (idcauchy 2)
           ≡⟨ scomplid (idcauchy 2) ⟩ 
         c2cauchy {PLUS ONE ONE} id⟷ ∎)
  where open ≡-Reasoning

resp∼ : {t₁ t₂ t₃ : U} {c₁ c₂ : t₁ ⟷ t₂} {c₃ c₄ : t₂ ⟷ t₃} → 
        (c₁ ∼ c₂) → (c₃ ∼ c₄) → (c₁ ◎ c₃ ∼ c₂ ◎ c₄)
resp∼ {t₁} {t₂} {t₃} {c₁} {c₂} {c₃} {c₄} c₁∼c₂ c₃∼c₄ = 
  begin (c2cauchy (c₁ ◎ c₃)
           ≡⟨ refl ⟩ 
         scompcauchy 
           (c2cauchy c₁)
           (subst Cauchy (size≡! c₁) (c2cauchy c₃))
           ≡⟨ cong₂ 
                (λ x y → scompcauchy x (subst Cauchy (size≡! c₁) y))
                c₁∼c₂ c₃∼c₄ ⟩ 
         scompcauchy 
           (c2cauchy c₂)
           (subst Cauchy (size≡! c₁) (c2cauchy c₄))
           ≡⟨ cong 
                (λ x → scompcauchy (c2cauchy c₂) (subst Cauchy x (c2cauchy c₄)))
                (size∼! c₁ c₂) ⟩ 
         scompcauchy 
           (c2cauchy c₂)
           (subst Cauchy (size≡! c₂) (c2cauchy c₄))
           ≡⟨ refl ⟩ 
         c2cauchy (c₂ ◎ c₄) ∎)
  where open ≡-Reasoning

-- The equivalence ∼ of paths makes U a 1groupoid: the points are
-- types (t : U); the 1paths are ⟷; and the 2paths between them are
-- based on extensional equivalence ∼

G : 1Groupoid
G = record
        { set = U
        ; _↝_ = _⟷_
        ; _≈_ = _∼_
        ; id  = id⟷
        ; _∘_ = λ p q → q ◎ p
        ; _⁻¹ = !
        ; lneutr = λ c → c◎id∼c {c = c}
        ; rneutr = λ c → id◎c∼c {c = c}
        ; assoc  = λ c₃ c₂ c₁ → assoc∼ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}  
        ; equiv = record { 
            refl  = λ {c} → refl∼ {c = c}
          ; sym   = λ {c₁} {c₂} → sym∼ {c₁ = c₁} {c₂ = c₂}
          ; trans = λ {c₁} {c₂} {c₃} → trans∼ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} 
          }
        ; linv = λ c → linv∼ {c = c} 
        ; rinv = λ c → rinv∼ {c = c} 
        ; ∘-resp-≈ = λ {t₁} {t₂} {t₃} {p} {q} {r} {s} p∼q r∼s → 
                    resp∼ {t₁} {t₂} {t₃} {r} {s} {p} {q} r∼s p∼q 
        }

-- There are additional laws that should hold:
-- 
-- assoc⊕∼ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
--           {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
--           c₁ ⊕ (c₂ ⊕ c₃) ∼ assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊
-- 
-- assoc⊗∼ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
--           {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
--           c₁ ⊗ (c₂ ⊗ c₃) ∼ assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆
-- 
-- but we will turn our attention to completeness below (in Pif2) in a more
-- systematic way.

------------------------------------------------------------------------------
