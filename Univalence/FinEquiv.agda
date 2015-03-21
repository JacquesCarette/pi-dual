{-# OPTIONS --without-K #-}

module FinEquiv where

open import Relation.Nullary.Core using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning; inspect; [_])
open import Data.Fin
  using (Fin; zero; suc; inject+; raise; toℕ; fromℕ≤; reduce≥)
open import Data.Fin.Properties
  using (bounded; inject+-lemma; toℕ-raise; toℕ-injective; toℕ-fromℕ≤)
open import Data.Nat.Properties using (≰⇒>; 1+n≰n; m≤m+n; ¬i+1+j≤i)
open import Data.Nat.Properties.Simple
  using (+-suc; +-comm; +-assoc; +-right-identity; *-right-zero; *-assoc;  distribʳ-*-+)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to mapSum)
open import Data.Product using (_,_; _×_; proj₁; proj₂) renaming (map to mapTimes)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _≥_; ≤-pred; _≤?_; module ≤-Reasoning)
open import Data.Nat.DivMod using (_divMod_; result)
open import Function using (_∘_; id)
open import Data.Unit using (⊤; tt)

open import Equiv using (_∼_; _≃_; module qinv; mkqinv; id≃; sym≃; trans≃)
open import TypeEquivalences using (swap₊; swapswap₊; swap⋆; swapswap⋆)
open import Proofs
  using (_<?_; inj₁-≡; inj₂-≡; inject+-injective; raise-injective; subst-subst; sym-sym;
        cong+r≤; cong+l≤; cong*r≤; sinj≤)

-- generally useful, leave this at top:
Fin0-⊥ : Fin 0 → ⊥
Fin0-⊥ ()

F0≃⊥ : Fin 0 ≃ ⊥
F0≃⊥ = f , mkqinv g α β
  where
    f : Fin 0 → ⊥
    f ()
    g : ⊥ → Fin 0
    g ()
    α : f ∘ g ∼ id
    α ()
    β : g ∘ f ∼ id
    β ()

Fin1≃⊤ : Fin 1 ≃ ⊤
Fin1≃⊤ = f , mkqinv g α β
  where
    f : Fin 1 → ⊤
    f zero = tt
    f (suc ())
    g : ⊤ → Fin 1
    g tt = zero
    α : f ∘ g ∼ id
    α tt = refl
    β : g ∘ f ∼ id
    β zero = refl
    β (suc ())

id-iso : {m : ℕ} → Fin m ≃ Fin m
id-iso = id≃ 

trans-iso : {m n o : ℕ} → (Fin m ≃ Fin n) → (Fin n ≃ Fin o) → (Fin m ≃ Fin o) 
trans-iso = trans≃ 

-- Divide into 3 modules
module Plus where
  private
    fwd : {m n : ℕ} → (Fin m ⊎ Fin n) → Fin (m + n)
    fwd {m} {n} (inj₁ x) = inject+ n x
    fwd {m} {n} (inj₂ y) = raise m y

    bwd : {m n : ℕ} → Fin (m + n) → (Fin m ⊎ Fin n)
    bwd {m} {n} i with toℕ i <? m
    ... | yes p = inj₁ (fromℕ≤ p)
    ... | no ¬p = inj₂ (reduce≥ i (≤-pred (≰⇒> ¬p)))

    fwd∘bwd~id : {m n : ℕ} → fwd {m} {n} ∘ bwd ∼ id
    fwd∘bwd~id {m} i with toℕ i <? m
    fwd∘bwd~id i | yes p = sym (inj₁-≡ i p)
    fwd∘bwd~id i | no ¬p = sym (inj₂-≡ i (≤-pred (≰⇒> ¬p)))

    bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
    bwd∘fwd~id {m} {n} (inj₁ x) with toℕ (inject+ n x) <? m 
    bwd∘fwd~id {n = n} (inj₁ x) | yes p = 
       cong inj₁ (inject+-injective (fromℕ≤ p) x (sym (inj₁-≡ (inject+ n x) p)))
    bwd∘fwd~id {m} {n} (inj₁ x) | no ¬p = ⊥-elim (1+n≰n pf)
     where
       open ≤-Reasoning
       pf : suc (toℕ x) ≤ toℕ x
       pf = let q =  (≤-pred (≰⇒> ¬p)) in 
              begin (
                suc (toℕ x)
                  ≤⟨ bounded x ⟩
                m
                  ≤⟨ q ⟩
                toℕ (inject+ n x)
                  ≡⟨ sym (inject+-lemma n x) ⟩
                toℕ x ∎ )

    bwd∘fwd~id {m} {n} (inj₂ y) with toℕ (raise m y) <? m 
    bwd∘fwd~id {m} {n} (inj₂ y) | yes p = ⊥-elim (1+n≰n pf)
     where
       open ≤-Reasoning
       pf : suc m ≤ m
       pf = begin (
               suc m
                   ≤⟨ m≤m+n (suc m) (toℕ y) ⟩
               suc (m + toℕ y)
                   ≡⟨ cong suc (sym (toℕ-raise m y)) ⟩
               suc (toℕ (raise m y))
                   ≤⟨ p ⟩
               m ∎)
    bwd∘fwd~id {m} {n} (inj₂ y) | no ¬p = 
       cong inj₂ (raise-injective {m} (reduce≥ (raise m y) (≤-pred (≰⇒> ¬p))) 
                    y (sym (inj₂-≡ (raise m y) (≤-pred (≰⇒> ¬p)))))

  -- this corresponds to _⊕_
  fwd-iso : {m n : ℕ} → (Fin m ⊎ Fin n) ≃ Fin (m + n)
  fwd-iso {m} {n} = fwd , mkqinv bwd (fwd∘bwd~id {m}) (bwd∘fwd~id {m})

  -- swap+
  swapper : (m n : ℕ) → Fin (m + n) → Fin (n + m)
  swapper m n = fwd ∘ swap₊ ∘ bwd {m} {n} 

  swap-inv : (m n : ℕ) → ∀ i → swapper n m (swapper m n i) ≡ i
  swap-inv m n i = 
    begin (
      fwd (swap₊ (bwd {n} {m} (fwd (swap₊ (bwd {m} {n} i)))))
        ≡⟨ cong (λ x → fwd (swap₊ x)) (bwd∘fwd~id {n} {m} (swap₊ (bwd i))) ⟩
      fwd (swap₊ (swap₊ (bwd {m} i)))
        ≡⟨ cong fwd (swapswap₊ (bwd {m} i)) ⟩
      fwd (bwd {m} {n} i)
        ≡⟨ fwd∘bwd~id {m} i ⟩
      i ∎ )
    where open ≡-Reasoning
    
  -- unite+
  unite+ : {m : ℕ} → Fin (0 + m) ≃ Fin m
  unite+ = id-iso

  -- uniti+
  uniti+ : {m : ℕ} → Fin m ≃ Fin (0 + m)
  uniti+ = id-iso

  -- swap₊
  swap+ : {m n : ℕ} → Fin (m + n) ≃ Fin (n + m)
  swap+ {m} {n} = (swapper m n , mkqinv (swapper n m) (swap-inv n m) (swap-inv m n))

  assocl+ : {m n o : ℕ} → Fin (m + (n + o)) ≃ Fin ((m + n) + o)
  assocl+ {m} {n} {o} =
    let eq = +-assoc m n o in
    subst Fin (sym eq) ,
    mkqinv (subst Fin eq)
               (subst-subst (sym eq) eq sym-sym)
               (subst-subst eq (sym eq) (cong sym refl))

  assocr+ : {m n o : ℕ} → Fin ((m + n) + o) ≃ Fin (m + (n + o))
  assocr+ {m} {n} {o} = sym≃ (assocl+ {m})

  cong+-iso : {m n o p : ℕ} → (Fin m ≃ Fin n) → (Fin o ≃ Fin p) → Fin (m + o) ≃ Fin (n + p)
  cong+-iso {m} {n} {o} {p} (f , feq) (g , geq) = 
    fwd {n} {p} ∘ mapSum f g ∘ bwd {m} {o} , 
    mkqinv
      (fwd {m} {o} ∘ mapSum fm.g gm.g ∘ bwd {n} {p})
      (λ i →
        begin (fwd {n} {p} (mapSum f g (bwd {m} {o} 
                 (fwd {m} {o} (mapSum fm.g gm.g (bwd {n} {p} i)))))
               ≡⟨ cong
                    (λ x → fwd {n} {p} (mapSum f g x))
                    (bwd∘fwd~id {m} {o} (mapSum fm.g gm.g (bwd {n} {p} i))) ⟩ 
               fwd {n} {p} (mapSum f g (mapSum fm.g gm.g (bwd {n} {p} i)))
               ≡⟨ {!!} ⟩
               fwd {n} {p} (bwd {n} {p} i)
               ≡⟨ fwd∘bwd~id {n} {p} i ⟩
               i ∎))
      (λ i →
        begin (fwd {m} {o} (mapSum fm.g gm.g (bwd {n} {p}
                 (fwd {n} {p} (mapSum f g (bwd {m} {o} i)))))
               ≡⟨ cong
                    (λ x → fwd {m} {o} (mapSum fm.g gm.g x))
                    (bwd∘fwd~id {n} {p} (mapSum f g (bwd {m} {o} i))) ⟩
               fwd {m} {o} (mapSum fm.g gm.g (mapSum f g (bwd {m} {o} i)))
               ≡⟨ {!!} ⟩
               fwd {m} {o} (bwd {m} {o} i)
               ≡⟨ fwd∘bwd~id {m} {o} i ⟩
               i ∎))
    where module fm = qinv feq
          module gm = qinv geq
          open ≡-Reasoning

module Times where
  open import DivModUtils using (addMul-lemma)
  
  fwd : {m n : ℕ} → (Fin m × Fin n) → Fin (m * n)
--   fwd {m} {n} (i , k) = inject≤ (fromℕ (toℕ i * n + toℕ k)) (i*n+k≤m*n i k)
  fwd {suc m} {n} (zero , k) = inject+ (m * n) k
  fwd          {n = n} (suc i , k) = raise n (fwd (i , k))

  private
    soundness : ∀ {m n} (i : Fin m) (j : Fin n) → toℕ (fwd (i , j)) ≡ toℕ i * n + toℕ j
    soundness {suc m} {n} zero     j = sym (inject+-lemma (m * n) j)
    soundness {n = n} (suc i) j rewrite toℕ-raise n (fwd (i , j)) | soundness i j 
      = sym (+-assoc n (toℕ i * n) (toℕ j))

    absurd-quotient : (m n q : ℕ) (r : Fin (suc n)) (k : Fin (m * suc n)) 
         (k≡r+q*sn : toℕ k ≡ toℕ r + q * suc n) (p : m ≤ q) → ⊥
    absurd-quotient m n q r k k≡r+q*sn p = ¬i+1+j≤i (toℕ k) {toℕ r} k≥k+sr
      where k≥k+sr : toℕ k ≥ toℕ k + suc (toℕ r)
            k≥k+sr = begin (toℕ k + suc (toℕ r)
                       ≡⟨ +-suc (toℕ k) (toℕ r) ⟩
                     suc (toℕ k) + toℕ r
                       ≤⟨ cong+r≤ (bounded k) (toℕ r) ⟩ 
                     (m * suc n) + toℕ r
                       ≡⟨ +-comm (m * suc n) (toℕ r) ⟩ 
                     toℕ r + (m * suc n)
                       ≡⟨ refl ⟩ 
                     toℕ r + m * suc n
                       ≤⟨ cong+l≤ (cong*r≤ p (suc n)) (toℕ r) ⟩ 
                     toℕ r + q * suc n
                       ≡⟨ sym k≡r+q*sn ⟩
                     toℕ k ∎)
                      where open ≤-Reasoning

    elim-right-zero : ∀ {ℓ} {Whatever : Set ℓ} (m : ℕ) → Fin (m * 0) → Whatever
    elim-right-zero m i = ⊥-elim (Fin0-⊥ (subst Fin (*-right-zero m) i))
    
  -- this was fin-project in Perm.agda
  bwd : {m n : ℕ} → Fin (m * n) → (Fin m × Fin n)
  bwd {m} {0} k = elim-right-zero m k
  bwd {m} {suc n} k with (toℕ k) divMod (suc n)
  ... | result q r k≡r+q*sn = (fromℕ≤ {q} {m} (q<m) , r)
    where 
          q<m : q < m
          q<m with suc q ≤? m 
          ... | no ¬p = ⊥-elim (absurd-quotient m n q r k k≡r+q*sn (sinj≤ (≰⇒> ¬p)))
          ... | yes p = p

  fwd∘bwd~id : {m n : ℕ} → fwd {m} {n} ∘ bwd ∼ id
  fwd∘bwd~id {m} {zero} i = elim-right-zero m i
  fwd∘bwd~id {m} {suc n} i with (toℕ i) divMod (suc n)
  ... | result q r k≡r+q*sn with suc q ≤? m
  ... | yes p = toℕ-injective ((
      begin (
        toℕ (fwd (fromℕ≤ p , r))
          ≡⟨ soundness (fromℕ≤ p) r ⟩
        toℕ (fromℕ≤ p) * (suc n) + toℕ r
          ≡⟨ cong (λ x → x * (suc n) + toℕ r) (toℕ-fromℕ≤ p) ⟩
        q * (suc n) + toℕ r
          ≡⟨ +-comm _ (toℕ r) ⟩
         toℕ r  + q * (suc n)
          ≡⟨ sym (k≡r+q*sn) ⟩
        toℕ i ∎)))
    where open ≡-Reasoning
  ... | no ¬p = ⊥-elim (absurd-quotient m n q r i k≡r+q*sn (sinj≤ (≰⇒> ¬p)))
     
  bwd∘fwd~id : {m n : ℕ} → bwd {m} {n} ∘ fwd ∼ id
  bwd∘fwd~id {n = zero} (b , ())
  bwd∘fwd~id {m} {suc n} (b , d) with fwd (b , d) | inspect fwd (b , d)
  ... | k | [ eq ] with (toℕ k) divMod (suc n)
  ... | result q r pf with suc q ≤? m
  ... | no ¬p = ⊥-elim (absurd-quotient m n q r k pf (sinj≤ (≰⇒> ¬p)))
  ... | yes p = cong₂ _,_  pf₁ (proj₁ same-quot)
    where
      open ≡-Reasoning
      eq' : toℕ d + toℕ b * suc n ≡ toℕ r + q * suc n
      eq' = begin (
        toℕ d + toℕ b * suc n
          ≡⟨ +-comm (toℕ d) _ ⟩
        toℕ b * suc n + toℕ d
          ≡⟨ trans (sym (soundness b d)) (cong toℕ eq) ⟩
        toℕ k
          ≡⟨ pf ⟩
        toℕ r + q * suc n ∎ )
      same-quot : (r ≡ d) × (q ≡ toℕ b)
      same-quot = addMul-lemma q (toℕ b) n r d ( sym eq' )
      pf₁ = (toℕ-injective (trans (toℕ-fromℕ≤ p) (proj₂ same-quot)))

  fwd-iso : {m n : ℕ} → (Fin m × Fin n) ≃ Fin (m * n)
  fwd-iso {m} {n} = fwd , mkqinv bwd (fwd∘bwd~id {m}) (bwd∘fwd~id {m})

  swapper : (m n : ℕ) → Fin (m * n) → Fin (n * m)
  swapper m n = fwd ∘ swap⋆ ∘ bwd {m} {n} 

  swap-inv : (m n : ℕ) → ∀ i → swapper n m (swapper m n i) ≡ i
  swap-inv m n i = 
    begin (
      fwd (swap⋆ (bwd {n} {m} (fwd (swap⋆ (bwd {m} {n} i)))))
        ≡⟨ cong (λ x → fwd (swap⋆ x)) (bwd∘fwd~id {n} {m} (swap⋆ (bwd i))) ⟩
      fwd (swap⋆ (swap⋆ (bwd {m} i)))
        ≡⟨ cong fwd (swapswap⋆ (bwd {m} i)) ⟩
      fwd (bwd {m} {n} i)
        ≡⟨ fwd∘bwd~id {m} i ⟩
      i ∎ )
    where open ≡-Reasoning
    
  -- unite*
  unite* : {m : ℕ} → Fin (1 * m) ≃ Fin m
  unite* {m} =
    let eq = +-right-identity m in
    subst Fin eq ,
    mkqinv (subst Fin (sym eq))
               (subst-subst eq (sym eq) (cong sym refl))
               (subst-subst (sym eq) eq sym-sym)

  -- uniti*
  uniti* : {m : ℕ} → Fin m ≃ Fin (1 * m)
  uniti* = sym≃ unite*

  -- swap*
  swap* : {m n : ℕ} → Fin (m * n) ≃ Fin (n * m)
  swap* {m} {n} = (swapper m n , mkqinv (swapper n m) (swap-inv n m) (swap-inv m n))

  assocl* : {m n o : ℕ} → Fin (m * (n * o)) ≃ Fin ((m * n) * o)
  assocl* {m} {n} {o} = subst Fin (sym (*-assoc m n o)) ,
    mkqinv ((subst Fin (*-assoc m n o)) ) 
                (λ x → subst-subst (sym (*-assoc m n o)) (*-assoc m n o) sym-sym x)
               (λ x → subst-subst (*-assoc m n o) (sym (*-assoc m n o)) (cong sym refl) x)

  assocr* : {m n o : ℕ} → Fin ((m * n) * o) ≃ Fin (m * (n * o))
  assocr* {m} {n} {o} = sym≃ (assocl* {m})

  distz : {m : ℕ} → Fin (0 * m) ≃ Fin 0
  distz {m} = id-iso 

  factorz : {m : ℕ} → Fin 0 ≃ Fin (0 * m)
  factorz {m} = id-iso 

  cong*-iso : {m n o p : ℕ} → (Fin m ≃ Fin n) → (Fin o ≃ Fin p) → Fin (m * o) ≃ Fin (n * p)
  cong*-iso {m} {n} {o} {p} (f , feq) (g , geq) = 
    fwd {n} {p} ∘ mapTimes f g ∘ bwd {m} {o} , 
    mkqinv
      (fwd {m} {o} ∘ mapTimes fm.g gm.g ∘ bwd {n} {p})
      (λ i →
        begin (fwd {n} {p} (mapTimes f g (bwd {m} {o}
                (fwd {m} {o} (mapTimes fm.g gm.g (bwd {n} {p} i)))))
               ≡⟨ cong
                    (λ x → fwd {n} {p} (mapTimes f g x))
                    (bwd∘fwd~id {m} {o} (mapTimes fm.g gm.g (bwd {n} {p} i))) ⟩ 
               fwd {n} {p} (mapTimes f g (mapTimes fm.g gm.g (bwd {n} {p} i)))
               ≡⟨ {!!} ⟩
               fwd {n} {p} (bwd {n} {p} i)
               ≡⟨ fwd∘bwd~id {n} {p} i ⟩
               i ∎))
      (λ i →
        begin (fwd {m} {o} (mapTimes fm.g gm.g (bwd {n} {p}
                 (fwd {n} {p} (mapTimes f g (bwd {m} {o} i)))))
               ≡⟨ cong
                    (λ x → fwd {m} {o} (mapTimes fm.g gm.g x))
                    (bwd∘fwd~id {n} {p} (mapTimes f g (bwd {m} {o} i))) ⟩ 
               fwd {m} {o} (mapTimes fm.g gm.g (mapTimes f g (bwd {m} {o} i)))
               ≡⟨ {!!} ⟩
               fwd {m} {o} (bwd {m} {o} i)
               ≡⟨ fwd∘bwd~id {m} {o} i ⟩
               i ∎))
    where module fm = qinv feq
          module gm = qinv geq
          open ≡-Reasoning

-- for distributivity

module PlusTimes where

  dist : {m n o : ℕ} → Fin ((m + n) * o) ≃ Fin ((m * o) + (n * o))
  dist {m} {n} {o} = subst Fin (distribʳ-*-+ o m n) ,
                     mkqinv
                       (subst Fin (sym (distribʳ-*-+ o m n)) )
                       (subst-subst
                         (distribʳ-*-+ o m n)
                         (sym (distribʳ-*-+ o m n))
                         refl)
                       (subst-subst
                         (sym (distribʳ-*-+ o m n))
                         (distribʳ-*-+ o m n)
                         sym-sym) 

  factor : {m n o : ℕ} → Fin ((m * o) + (n * o)) ≃ Fin ((m + n) * o) 
  factor {m} {n} {o} = sym≃ (dist {m} {n} {o}) 

