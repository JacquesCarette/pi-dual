{-# OPTIONS --without-K #-}

module FinVecProperties where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin; zero; suc; inject+; raise; toℕ)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Product using (_×_; proj₁; proj₂; _,′_)

open import Data.Nat.Properties.Simple using (+-right-identity)
open import Data.Fin.Properties using (toℕ-injective; inject+-lemma)

open import Data.Vec
   using (Vec; []; _∷_; tabulate; allFin)
   renaming (_++_ to _++V_; concat to concatV; map to mapV)
open import Data.Vec.Properties
    using (tabulate∘lookup; lookup∘tabulate; lookup-allFin;
           lookup-++-inject+; tabulate-∘)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Function using (_∘_; id)

--

open import Equiv using (_∼_; p∘!p≡id)
open import FinEquiv using (module Plus; module Times; module PlusTimes)
open import FinVec using (FinVec; 0C; 1C; _∘̂_; _⊎c_; _×c_;
  unite+; uniti+; unite+r; uniti+r;
  unite+r'; -- alternative definition of unite+r using equivalences
  swap+cauchy; assocl+; assocr+;
  unite*; uniti*; unite*r; uniti*r;
  swap⋆cauchy; assocl*; assocr*;
  dist*+; factor*+; distl*+; factorl*+;
  right-zero*l; right-zero*r
  ) 

open import Proofs using (
  -- FiniteFunctions
       finext; 
  -- VectorLemmas
       _!!_; lookupassoc; unSplit; lookup-++-raise; tabulate-split; 
       concat-map; left!!; right!!; map-map-map; lookup-map; map-∘;
       lookup-subst;
  -- FinNatLemmas
      toℕ-fin
     )

------------------------------------------------------------------------------
-- Two ways for reasoning about permutations: we use whichever is more
-- convenient in each context

-- I: we can reason about permutations by looking at their action at
-- every index. This exposes the underlying raw vectors...

infix 4 _∼p_

_∼p_ : {n m : ℕ} (p₁ p₂ : Vec (Fin m) n) → Set
_∼p_ {n} p₁ p₂ = (i : Fin n) → p₁ !! i ≡ p₂ !! i

∼p⇒≡ : {n : ℕ} {p₁ p₂ : Vec (Fin n) n} → (p₁ ∼p p₂) → p₁ ≡ p₂
∼p⇒≡ {n} {p₁} {p₂} eqv = 
  begin (
    p₁                            ≡⟨ sym (tabulate∘lookup p₁) ⟩
    tabulate (_!!_ p₁)            ≡⟨ finext eqv ⟩
    tabulate (_!!_ p₂)            ≡⟨ tabulate∘lookup p₂ ⟩
    p₂ ∎)
  where open ≡-Reasoning

cauchyext : {m n : ℕ} (π : FinVec m n) → tabulate (_!!_ π) ≡ π
-- this is just tabulate∘lookup, but it hides the details; should this
-- be called 'join' or 'flatten' ?
cauchyext π = tabulate∘lookup π

1C!!i≡i : ∀ {m} {i : Fin m} → 1C {m} !! i ≡ i
1C!!i≡i = lookup∘tabulate id _

!!⇒∘̂ : {n₁ n₂ n₃ : ℕ} →
        (π₁ : Vec (Fin n₁) n₂) → (π₂ : Vec (Fin n₂) n₃) → (i : Fin n₃) →
        π₁ !! (π₂ !! i) ≡ (π₂ ∘̂ π₁) !! i
!!⇒∘̂ π₁ π₂ i = 
  begin (
    π₁ !! (π₂ !! i)
          ≡⟨ sym (lookup∘tabulate (λ j → (π₁ !! (π₂ !! j))) i) ⟩
    tabulate (λ i → π₁ !! (π₂ !! i)) !! i
          ≡⟨ refl ⟩
    (π₂ ∘̂ π₁) !! i ∎)
    where open ≡-Reasoning

-- II: we can relate compositions of permutations of type equivalences
-- and pull back properties of permutations from properties of
-- equivalences

∘̂⇒∘ : {m n o : ℕ} → (f : Fin m → Fin n) → (g : Fin n → Fin o) → 
      tabulate f ∘̂ tabulate g ∼p tabulate (g ∘ f)
      -- note the flip!
∘̂⇒∘ f g i = 
  begin (
    (tabulate f ∘̂ tabulate g) !! i
      ≡⟨ lookup∘tabulate _ i ⟩
    (tabulate g) !! (tabulate f !! i)
      ≡⟨ lookup∘tabulate _ (tabulate f !! i) ⟩
    g (tabulate f !! i)
      ≡⟨ cong g (lookup∘tabulate f i) ⟩
    g (f i)
      ≡⟨ sym (lookup∘tabulate (g ∘ f) i) ⟩
    tabulate (g ∘ f) !! i ∎)
  where open ≡-Reasoning

-- we could go through ~p, but this works better in practice

~⇒≡ : {m n : ℕ} {f : Fin m → Fin n} {g : Fin n → Fin m} → 
           (f ∘ g ∼ id) → (tabulate g ∘̂ tabulate f ≡ 1C)
~⇒≡ {f = f} {g} β =
  ∼p⇒≡ (λ i → trans (∘̂⇒∘ g f i) (cong (λ x → x !! i) (finext β)))

------------------------------------------------------------------------------
-- A permutation and its inverse compose to the identity
--
-- Here we just exploit the connection to type equivalences to get all
-- the properties for free.

-- additives

unite+∘̂uniti+~id : ∀ {m} → (unite+ {m}) ∘̂ uniti+ ≡ 1C {m}
unite+∘̂uniti+~id {m} = ~⇒≡ {m} {n = m} (p∘!p≡id {p = Plus.unite+ {m}})

uniti+∘̂unite+~id : ∀ {m} → (uniti+ {m}) ∘̂ unite+ ≡ 1C {m}
uniti+∘̂unite+~id {m} = ~⇒≡ {m} {n = m} (p∘!p≡id {p = Plus.uniti+})

unite+r∘̂uniti+r~id : ∀ {m} → (unite+r {m}) ∘̂ uniti+r ≡ 1C {m + 0}
unite+r∘̂uniti+r~id {m} = ~⇒≡ {m} (p∘!p≡id {p = Plus.unite+r {m}})

uniti+r∘̂unite+r~id : ∀ {m} → (uniti+r {m}) ∘̂ unite+r ≡ 1C {m}
uniti+r∘̂unite+r~id {m} = ~⇒≡ (p∘!p≡id {p = Plus.uniti+r})

swap+-inv : ∀ {m n} → swap+cauchy m n ∘̂ swap+cauchy n m ≡ 1C
swap+-inv {m} {n} = ~⇒≡ (Plus.swap-inv m n)

assocl+∘̂assocr+~id : ∀ {m n o} → assocl+ {m} {n} {o} ∘̂ assocr+ {m} ≡ 1C
assocl+∘̂assocr+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = Plus.assocl+ {m}})

assocr+∘̂assocl+~id : ∀ {m n o} → assocr+ {m} {n} {o} ∘̂ assocl+ {m} ≡ 1C
assocr+∘̂assocl+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = Plus.assocr+ {m}})

-- multiplicatives

unite*∘̂uniti*~id : ∀ {m} → (unite* {m}) ∘̂ uniti* ≡ 1C {1 * m}
unite*∘̂uniti*~id {m} = ~⇒≡ {m} {n = 1 * m} (p∘!p≡id {p = Times.unite* {m}})

uniti*∘̂unite*~id : ∀ {m} → (uniti* {m}) ∘̂ unite* ≡ 1C {m}
uniti*∘̂unite*~id {m} = ~⇒≡ {1 * m} {n = m} (p∘!p≡id {p = Times.uniti* {m}})

unite*r∘̂uniti*r~id : ∀ {m} → (unite*r {m}) ∘̂ uniti*r ≡ 1C {m * 1}
unite*r∘̂uniti*r~id {m} = ~⇒≡ {m} {n = m * 1} (p∘!p≡id {p = Times.unite*r {m}})

uniti*r∘̂unite*r~id : ∀ {m} → (uniti*r {m}) ∘̂ unite*r ≡ 1C {m}
uniti*r∘̂unite*r~id {m} = ~⇒≡ {m * 1} {n = m} (p∘!p≡id {p = Times.uniti*r {m}})

swap*-inv : ∀ {m n} → swap⋆cauchy m n ∘̂ swap⋆cauchy n m ≡ 1C
swap*-inv {m} {n} = ~⇒≡ (Times.swap-inv m n)

assocl*∘̂assocr*~id : ∀ {m n o} → assocl* {m} {n} {o} ∘̂ assocr* {m} ≡ 1C
assocl*∘̂assocr*~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = Times.assocl* {m}})

assocr*∘̂assocl*~id : ∀ {m n o} → assocr* {m} {n} {o} ∘̂ assocl* {m} ≡ 1C
assocr*∘̂assocl*~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = Times.assocr* {m}})

-- Distributivity

right-zero*l∘̂right-zero*r~id : ∀ {m} →
  right-zero*l {m} ∘̂ right-zero*r {m} ≡ 1C {m * 0}
right-zero*l∘̂right-zero*r~id {m} =
  ~⇒≡ {f = proj₁ (PlusTimes.factorzr {m})} (p∘!p≡id {p = PlusTimes.distzr {m}})

right-zero*r∘̂right-zero*l~id : ∀ {m} → right-zero*r {m} ∘̂ right-zero*l {m} ≡ 1C
right-zero*r∘̂right-zero*l~id {m} =
  ~⇒≡ { f = proj₁ (PlusTimes.factorz {m})} (p∘!p≡id {p = PlusTimes.distz {m}})

dist*+∘̂factor*+~id : ∀ {m n o} → dist*+ {m} {n} {o} ∘̂ factor*+ {m} ≡ 1C
dist*+∘̂factor*+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = PlusTimes.dist {m}})

factor*+∘̂dist*+~id : ∀ {m n o} → factor*+ {m} {n} {o} ∘̂ dist*+ {m} ≡ 1C
factor*+∘̂dist*+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = PlusTimes.factor {m}})

distl*+∘̂factorl*+~id : ∀ {m n o} → distl*+ {m} {n} {o} ∘̂ factorl*+ {m} ≡ 1C
distl*+∘̂factorl*+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = PlusTimes.distl {m}})

factorl*+∘̂distl*+~id : ∀ {m n o} → factorl*+ {m} {n} {o} ∘̂ distl*+ {m} ≡ 1C
factorl*+∘̂distl*+~id {m} {_} {o} = ~⇒≡ (p∘!p≡id {p = PlusTimes.factorl {m}})

------------------------------------------------------------------------------
-- Properties of sequential composition 

0C∘̂0C≡0C : 1C {0} ∘̂ 1C {0} ≡ 1C {0}
0C∘̂0C≡0C = refl
    
∘̂-assoc : {m₁ m₂ m₃ m₄ : ℕ} →
         (a : Vec (Fin m₂) m₁) (b : Vec (Fin m₃) m₂) (c : Vec (Fin m₄) m₃) → 
         a ∘̂ (b ∘̂ c) ≡ (a ∘̂ b) ∘̂ c
∘̂-assoc a b c = finext (lookupassoc a b c)

∘̂-rid : {m n : ℕ} → (π : Vec (Fin m) n) → π ∘̂ 1C ≡ π
∘̂-rid π = trans (finext (λ i → lookup-allFin (π !! i))) (cauchyext π)

∘̂-lid : {m n : ℕ} → (π : Vec (Fin m) n) → 1C ∘̂ π ≡ π
∘̂-lid π = trans (finext (λ i → cong (_!!_ π) (lookup-allFin i))) (cauchyext π)

------------------------------------------------------------------------------
-- Properties of additive composition

1C₀⊎x≡x : ∀ {m n} {x : FinVec m n} → 1C {0} ⊎c x ≡ x
1C₀⊎x≡x {x = x} = cauchyext x

1C⊎1C≡1C : ∀ {m n} → 1C {m} ⊎c 1C {n} ≡ 1C
1C⊎1C≡1C {m} {n} = 
  begin (
     tabulate {m} (inject+ n ∘ _!!_ 1C) ++V tabulate {n} (raise m ∘ _!!_ 1C)
       ≡⟨ cong₂ (_++V_ {m = m})
           (finext (λ i → cong (inject+ n) (lookup-allFin i)))
           (finext (λ i → cong (raise m) (lookup-allFin i))) ⟩
     tabulate {m} (inject+ n) ++V tabulate {n} (raise m)
       ≡⟨ unSplit {m} id ⟩
     tabulate {m + n} id ∎)
  where open ≡-Reasoning

-- interactions with sequential composition

unite+∘[0⊎x]≡x∘unite+ : ∀ {m n} {x : FinVec m n} →
  unite+ ∘̂ (1C {0} ⊎c x) ≡ x ∘̂ unite+
unite+∘[0⊎x]≡x∘unite+ {m} {n} {x} = finext pf
  where
    pf : (i : Fin n) → (0C ⊎c x) !! (unite+ !! i) ≡ unite+ !! (x !! i)
    pf i = 
      begin (
        tabulate (λ y → x !! y) !! (tabulate id !! i)
          ≡⟨ cong (λ j → tabulate (λ y → x !! y) !! j) (lookup∘tabulate id i) ⟩
        tabulate (λ y → x !! y) !! i
          ≡⟨ lookup∘tabulate (_!!_ x) i ⟩
        x !! i
          ≡⟨ sym (lookup∘tabulate id (x !! i)) ⟩
        tabulate id !! (x !! i) ∎)
      where open ≡-Reasoning
            
uniti+∘x≡[0⊎x]∘uniti+ : ∀ {m n} {x : FinVec m n} →
  uniti+ ∘̂ x ≡ (1C {0} ⊎c x) ∘̂ uniti+
uniti+∘x≡[0⊎x]∘uniti+ {m} {n} {x} = finext pf
  where
    pf : (i : Fin n) → x !! (uniti+ !! i) ≡ uniti+ !! ((0C ⊎c x) !! i)
    pf i = begin (
      x !! (tabulate id !! i)
        ≡⟨ cong (_!!_ x) (lookup∘tabulate id i) ⟩
      x !! i
        ≡⟨ sym (lookup∘tabulate (λ y → x !! y) i) ⟩
      tabulate (λ y → x !! y) !! i
        ≡⟨ sym (lookup∘tabulate id _) ⟩
      tabulate id !! (tabulate (λ y → x !! y) !! i) ∎)
      where open ≡-Reasoning

private
  n+0≡inject+0 : (n : ℕ) → (i : Fin n) → (eq : n ≡ n + 0) →
    subst Fin eq i ≡ inject+ 0 i
  n+0≡inject+0 n i eq = toℕ-injective pf
    where
      open ≡-Reasoning
      pf : toℕ (subst Fin eq i) ≡ toℕ (inject+ 0 i)
      pf = begin (
        toℕ (subst Fin eq i)
          ≡⟨ toℕ-fin n (n + 0) eq i ⟩
        toℕ i
          ≡⟨ inject+-lemma {n} 0 i ⟩
        toℕ (inject+ 0 i) ∎)
  
uniti+r∘[x⊎0]≡x∘uniti+r : ∀ {m n} {x : FinVec m n} →
    uniti+r ∘̂ (x ⊎c 1C {0}) ≡ x ∘̂ uniti+r
uniti+r∘[x⊎0]≡x∘uniti+r {m} {n} {x} = finext pf
  where
    pf : (i : Fin n) → (x ⊎c 1C {0}) !! (uniti+r !! i) ≡
         uniti+r !! (x !! i)
    pf i = begin (
      (x ⊎c 1C {0}) !! ((tabulate (proj₁ Plus.uniti+r)) !! i)
        ≡⟨ cong (_!!_ (x ⊎c 1C {0})) (lookup∘tabulate (proj₁ Plus.uniti+r) i) ⟩
      (x ⊎c 1C {0}) !! (proj₁ Plus.uniti+r i)
        ≡⟨ cong (_!!_ (x ⊎c 1C {0})) (n+0≡inject+0 n i (sym (+-right-identity n))) ⟩
      (x ⊎c 1C {0}) !! (inject+ 0 i)
        ≡⟨ left!! i (λ z → inject+ 0 (x !! z)) {λ {()}}⟩
      inject+ 0 (x !! i)
        ≡⟨ sym (n+0≡inject+0 m (x !! i) (sym (+-right-identity m))) ⟩
      subst Fin (sym (+-right-identity m)) (x !! i)
        ≡⟨ sym (lookup∘tabulate (subst Fin (sym (+-right-identity m))) (x !! i) ) ⟩
      uniti+r !! (x !! i) ∎)
      where open ≡-Reasoning

unite+r∘[x⊎0]≡x∘unite+r : ∀ {m n} {x : FinVec m n} →
    unite+r ∘̂ x ≡ (x ⊎c 1C {0}) ∘̂ unite+r
unite+r∘[x⊎0]≡x∘unite+r {m} {n} {x} = {!!} 

unite+r'∘[x⊎0]≡x∘unite+r' : ∀ {m n} {x : FinVec m n} →
    unite+r' ∘̂ x ≡ (x ⊎c 1C {0}) ∘̂ unite+r'
unite+r'∘[x⊎0]≡x∘unite+r' {m} {n} {x} =
  finext xxx
  where
        open ≡-Reasoning
        xxx : (_!!_ x) ∘ (_!!_ unite+r') ∼ (_!!_ unite+r') ∘ (_!!_ (x ⊎c 1C))
        xxx i = begin
                  (x !! (unite+r' !! i))
                  ≡⟨ {!!} ⟩
                  (unite+r' !! ((x ⊎c 1C) !! i)) ∎

-- unite+r' : FinVec m (m + 0)
-- unite+r' = tabulate (proj₁ Plus.unite+r')
--
-- Plus.unite+r' : {m : ℕ} → Fin (m + 0) ≃ Fin m
-- Plus.unite+r' {m} = swapper m 0 ,
--                     mkqinv (swapper 0 m) (swap-inv 0 m) (swap-inv m 0) 



idˡ⊕ : ∀ {m n} {x : FinVec m n} → uniti+ ∘̂ (1C {0} ⊎c x) ≡ x ∘̂ uniti+
idˡ⊕ {m} {n} {x} = finext pf
  where
    open ≡-Reasoning
    pf : (i : Fin n) → (1C {0} ⊎c x) !! (uniti+ !! i) ≡ (uniti+ !! (x !! i))
    pf i =  begin (
      tabulate (λ y → x !! y) !! (tabulate id !! i)
        ≡⟨ cong (_!!_ (tabulate λ y → x !! y)) (lookup∘tabulate id i) ⟩
      (tabulate (λ y → x !! y)) !! i
        ≡⟨ lookup∘tabulate (λ y → x !! y) i ⟩
      x !! i
        ≡⟨ sym (lookup∘tabulate id (x !! i)) ⟩
      tabulate id !! (x !! i) ∎)

private

  left⊎⊎!! :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → (p₁ : FinVec m₁ n₁) → (p₂ : FinVec m₂ n₂)
    → (p₃ : FinVec m₃ m₁) → (p₄ : FinVec m₄ m₂) → (i : Fin n₁) → 
    (p₃ ⊎c p₄) !! ( (p₁ ⊎c p₂) !! inject+ n₂ i ) ≡ inject+ m₄ ( (p₁ ∘̂ p₃) !! i) 
  left⊎⊎!! {m₁} {m₂} {_} {m₄} {_} {n₂} p₁ p₂ p₃ p₄ i =
    let pp = p₃ ⊎c p₄ in
    let qq = p₁ ⊎c p₂ in
    begin (
        pp !! (qq !! inject+ n₂ i)
          ≡⟨ cong
               (_!!_ pp)
               (lookup-++-inject+
                 (tabulate (inject+ m₂ ∘ _!!_ p₁)) 
                 (tabulate (raise m₁ ∘ _!!_ p₂))
                 i) ⟩ 
       pp !! (tabulate (inject+ m₂ ∘ _!!_ p₁ ) !! i)
          ≡⟨ cong (_!!_ pp) (lookup∘tabulate _ i) ⟩
       pp !! (inject+ m₂ (p₁ !! i))
          ≡⟨ left!! (p₁ !! i) (inject+ m₄ ∘ (_!!_ p₃)) ⟩
        inject+ m₄ (p₃ !! (p₁ !! i))
          ≡⟨ cong (inject+ m₄) (sym (lookup∘tabulate _ i)) ⟩
        inject+ m₄ ((p₁ ∘̂ p₃) !! i) ∎ )
      where open ≡-Reasoning

  right⊎⊎!! :  ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → (p₁ : FinVec m₁ n₁) → (p₂ : FinVec m₂ n₂)
    → (p₃ : FinVec m₃ m₁) → (p₄ : FinVec m₄ m₂) → (i : Fin n₂) → 
    (p₃ ⊎c p₄) !! ( (p₁ ⊎c p₂) !! raise n₁ i ) ≡ raise m₃ ( (p₂ ∘̂ p₄) !! i) 
  right⊎⊎!! {m₁} {m₂} {m₃} {_} {n₁} {_} p₁ p₂ p₃ p₄ i =
    let pp = p₃ ⊎c p₄ in
    let qq = p₁ ⊎c p₂ in
    begin (
      pp !! (qq !! raise n₁ i)
        ≡⟨ cong
             (_!!_ pp)
             (lookup-++-raise
               (tabulate (inject+ m₂ ∘ _!!_ p₁))
               (tabulate (raise m₁ ∘ _!!_ p₂))
               i) ⟩
      pp !! (tabulate (raise m₁ ∘ _!!_ p₂) !! i)
        ≡⟨ cong (_!!_ pp) (lookup∘tabulate _ i) ⟩
      pp !! raise m₁ (p₂ !! i)
        ≡⟨ right!! {m₁} (p₂ !! i) (raise m₃ ∘ (_!!_ p₄)) ⟩
      raise m₃ (p₄ !! (p₂ !! i))
        ≡⟨ cong (raise m₃) (sym (lookup∘tabulate _ i)) ⟩
      raise m₃ ((p₂ ∘̂ p₄) !! i) ∎ )
      where open ≡-Reasoning

⊎c-distrib : ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : FinVec m₁ n₁} → {p₂ : FinVec m₂ n₂}
  → {p₃ : FinVec m₃ m₁} → {p₄ : FinVec m₄ m₂} →
    (p₁ ⊎c p₂) ∘̂ (p₃ ⊎c p₄) ≡ (p₁ ∘̂ p₃) ⊎c (p₂ ∘̂ p₄)
⊎c-distrib {m₁} {m₂} {m₃} {m₄} {n₁} {n₂} {p₁} {p₂} {p₃} {p₄} =
  let p₃₄ = p₃ ⊎c p₄ in let p₁₂ = p₁ ⊎c p₂ in
  let lhs = λ i → p₃₄ !! (p₁₂ !! i) in
  begin (
    tabulate lhs
      ≡⟨ tabulate-split {n₁} {n₂} ⟩
    tabulate {n₁} (lhs ∘ inject+ n₂) ++V tabulate {n₂} (lhs ∘ raise n₁)
      ≡⟨ cong₂ _++V_
          (finext (left⊎⊎!! p₁ _ _ _))
          (finext (right⊎⊎!! p₁ _ _ _)) ⟩
    tabulate {n₁} (λ i → inject+ m₄ ((p₁ ∘̂ p₃) !! i)) ++V 
    tabulate {n₂} (λ i → raise m₃ ((p₂ ∘̂ p₄) !! i))
      ≡⟨ refl ⟩
    (p₁ ∘̂ p₃) ⊎c (p₂ ∘̂ p₄) ∎)
    where open ≡-Reasoning

------------------------------------------------------------------------------
-- Properties of multiplicative composition

private
  
  concat!! : {A : Set} {m n : ℕ} → (a : Fin m) → (b : Fin n) →
    (xss : Vec (Vec A n) m) →
    concatV xss !! (Times.fwd (a ,′ b)) ≡ (xss !! a) !! b
  concat!! zero b (xs ∷ xss) = lookup-++-inject+ xs (concatV xss) b
  concat!! (suc a) b (xs ∷ xss) = 
    trans
      (lookup-++-raise xs (concatV xss) (Times.fwd (a ,′ b)))
      (concat!! a b xss)

  ×c-equiv : {m₁ m₂ n₁ n₂ : ℕ} (p₁ : FinVec m₁ n₁) (p₂ : FinVec m₂ n₂) →
    (p₁ ×c p₂) ≡
    concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y ,′ x) p₂)) p₁)
  ×c-equiv p₁ p₂ =
    let zss = mapV  (λ b → mapV (λ x → b ,′ x) p₂) p₁ in
    begin (
      (p₁ ×c p₂)
        ≡⟨ refl ⟩
      mapV Times.fwd (concatV zss)
        ≡⟨ sym (concat-map zss Times.fwd) ⟩
      concatV (mapV (mapV Times.fwd) zss)
        ≡⟨ cong concatV
            (map-map-map Times.fwd (λ b → mapV (λ x → b ,′ x) p₂) p₁) ⟩
       concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y ,′ x) p₂)) p₁) ∎)
      where open ≡-Reasoning

  lookup-2d : {A : Set} (m n : ℕ) → (k : Fin (m * n)) →
     {f : Fin m × Fin n → A} →
     concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i ,′ j)))) !! k ≡
     f (Times.bwd k)
  lookup-2d m n k {f} =
    let lhs = concatV (tabulate {m} (λ i → tabulate {n} (λ j → f (i ,′ j))))
        a = proj₁ (Times.bwd {m} {n} k) 
        b = proj₂ (Times.bwd {m} {n} k) in
    begin (
      lhs !! k 
        ≡⟨ cong (_!!_ lhs) (sym (Times.fwd∘bwd~id {m} k)) ⟩
      lhs !! (Times.fwd (a ,′ b))
        ≡⟨ concat!! a b _ ⟩
      (tabulate {m} (λ i → tabulate {n} (λ j → f (i ,′ j))) !! a) !! b
        ≡⟨ cong (λ x → x !! b) (lookup∘tabulate _ a) ⟩
      tabulate {n} (λ j → f (a ,′ j)) !! b
        ≡⟨ lookup∘tabulate _ b ⟩
      f (a ,′ b)
        ≡⟨ refl ⟩
      f (Times.bwd k) ∎)
      where open ≡-Reasoning

  ×c!! : {m₁ m₂ n₁ n₂ : ℕ} (p₁ : FinVec m₁ n₁) (p₂ : FinVec m₂ n₂)
    (k : Fin (n₁ * n₂)) →
    (p₁ ×c p₂) !! k ≡
    Times.fwd (p₁ !! proj₁ (Times.bwd k) ,′ p₂ !! proj₂ (Times.bwd {n₁} k))
  ×c!! {n₁ = n₁} p₁ p₂ k =
    let a = proj₁ (Times.bwd {n₁} k) in
    let b = proj₂ (Times.bwd {n₁} k) in
    begin (
      (p₁ ×c p₂) !! k
        ≡⟨ cong₂ _!!_ (×c-equiv p₁ p₂) (sym (Times.fwd∘bwd~id {n₁} k)) ⟩
      concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y ,′ x) p₂)) p₁) !!
      Times.fwd (a ,′ b)
        ≡⟨ concat!! a b _ ⟩
      ((mapV (λ y → mapV Times.fwd (mapV (λ x → y ,′ x) p₂)) p₁) !! a) !! b
        ≡⟨ cong (λ x → x !! b) (lookup-map a _ p₁) ⟩
      mapV Times.fwd (mapV (λ x → p₁ !! a ,′ x) p₂) !! b
        ≡⟨ cong (λ x → x !! b) (sym (map-∘ Times.fwd _ p₂)) ⟩
      mapV (Times.fwd ∘ (λ x → p₁ !! a ,′ x)) p₂ !! b
        ≡⟨ lookup-map b _ p₂ ⟩
      Times.fwd (p₁ !! a ,′ p₂ !! b) ∎)
      where open ≡-Reasoning

1C×1C≡1C : ∀ {m n} → (1C {m} ×c 1C {n}) ≡ 1C {m * n}
1C×1C≡1C {m} {n} = 
  begin (
    1C {m} ×c 1C
      ≡⟨ ×c-equiv 1C 1C ⟩
    concatV (mapV (λ y → mapV Times.fwd (mapV (_,′_ y) (1C {n}))) (1C {m}))
      ≡⟨ cong (concatV {n = m}) (sym (tabulate-∘ _ id)) ⟩
    concatV {n = m} (tabulate (λ y → mapV Times.fwd (mapV (_,′_ y) (1C {n}))))
      ≡⟨ cong (concatV {n = m})
          (finext (λ y → sym (map-∘ Times.fwd (λ x → y ,′ x) 1C))) ⟩
    concatV (tabulate {n = m} (λ y → mapV (Times.fwd ∘ (_,′_ y)) (1C {n})))
      ≡⟨ cong
          (concatV {m = n} {m})
          (finext (λ y → sym (tabulate-∘ (Times.fwd ∘ (_,′_ y)) id))) ⟩
    concatV (tabulate {n = m}
              (λ a → tabulate {n = n} (λ b → Times.fwd (a ,′ b))))
      ≡⟨ sym (tabulate∘lookup _) ⟩
    tabulate (λ k →
    concatV (tabulate {n = m}
              (λ a → tabulate {n = n} (λ b → Times.fwd (a ,′ b)))) !! k)
      ≡⟨ finext (λ k → lookup-2d m n k) ⟩
    tabulate (λ k → Times.fwd {m} {n} (Times.bwd k))
      ≡⟨ finext (Times.fwd∘bwd~id {m} {n}) ⟩
    1C {m * n} ∎ )
    where open ≡-Reasoning        

×c-distrib : ∀ {m₁ m₂ m₃ m₄ n₁ n₂} → {p₁ : FinVec m₁ n₁} → {p₂ : FinVec m₂ n₂}
  → {p₃ : FinVec m₃ m₁} → {p₄ : FinVec m₄ m₂} →
    (p₁ ×c p₂) ∘̂ (p₃ ×c p₄) ≡ (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄)
×c-distrib {m₁} {m₂} {m₃} {m₄} {n₁} {n₂} {p₁} {p₂} {p₃} {p₄} =
  let p₃₄ = p₃ ×c p₄ in let p₁₂ = p₁ ×c p₂ in
  let p₂₄ = p₂ ∘̂ p₄ in let p₁₃ = p₁ ∘̂ p₃ in
  let lhs = λ i → p₃₄ !! (p₁₂ !! i) in
  let zss = mapV  (λ b → mapV (λ x → b ,′ x) (p₂ ∘̂ p₄)) (p₁ ∘̂ p₃) in
  begin (
     tabulate {n₁ * n₂} (λ i → p₃₄ !! (p₁₂ !! i))
       ≡⟨ finext (λ j → cong (_!!_ p₃₄) (×c!! p₁ p₂ j)) ⟩
     tabulate {n₁ * n₂}
       (λ i → p₃₄ !! Times.fwd (p₁ !! proj₁ (Times.bwd i) ,′
              p₂ !! proj₂ (Times.bwd i)))
       ≡⟨ finext (λ j → ×c!! p₃ p₄ _) ⟩
     tabulate (λ i →
       let k = Times.fwd (p₁ !! proj₁ (Times.bwd i) ,′
                          p₂ !! proj₂ (Times.bwd i)) in
       Times.fwd (p₃ !! proj₁ (Times.bwd k) ,′ p₄ !! proj₂ (Times.bwd k)))
       ≡⟨ finext (λ i → cong₂
                         (λ x y → Times.fwd (p₃ !! proj₁ x ,′ p₄ !! proj₂ y))
                 (Times.bwd∘fwd~id {m₁} {m₂} (p₁ !! proj₁ (Times.bwd i) ,′ _))
                 (Times.bwd∘fwd~id (_ ,′ p₂ !! proj₂ (Times.bwd i)))) ⟩
     tabulate (λ i → Times.fwd (p₃ !! (p₁ !! proj₁ (Times.bwd i)) ,′
                                (p₄ !! (p₂ !! proj₂ (Times.bwd i)))))
       ≡⟨ finext (λ k → sym (lookup-2d n₁ n₂ k)) ⟩
     tabulate (λ k →
       concatV (tabulate {n₁} (λ z →
                tabulate {n₂} (λ w →
                Times.fwd ((p₃ !! (p₁ !! z)) ,′ (p₄ !! (p₂ !! w))))))
       !! k)
        ≡⟨ tabulate∘lookup _ ⟩
     concatV (tabulate {n₁} (λ z →
              tabulate {n₂} (λ w →
              Times.fwd ((p₃ !! (p₁ !! z)) ,′ (p₄ !! (p₂ !! w))))))
       ≡⟨ cong
           concatV
           (finext (λ i →
             tabulate-∘ Times.fwd
               (λ w → ((p₃ !! (p₁ !! i)) ,′ (p₄ !! (p₂ !! w)))))) ⟩
     concatV (tabulate (λ z →
              mapV Times.fwd
                (tabulate (λ w → (p₃ !! (p₁ !! z)) ,′ (p₄ !! (p₂ !! w))))))
       ≡⟨ cong
           concatV
           (finext (λ i →
             cong
               (mapV Times.fwd)
               (tabulate-∘
                 (λ x → (p₃ !! (p₁ !! i)) ,′ x)
                 (_!!_ p₄ ∘ _!!_ p₂)))) ⟩
     concatV
       (tabulate
         (λ z → mapV Times.fwd (mapV (λ x → (p₃ !! (p₁ !! z)) ,′ x) p₂₄)))
       ≡⟨ cong concatV (tabulate-∘ _ (_!!_ p₃ ∘ _!!_ p₁)) ⟩
     concatV (mapV (λ y → mapV Times.fwd (mapV (λ x → y ,′ x) p₂₄)) p₁₃)
       ≡⟨ sym (×c-equiv p₁₃ p₂₄) ⟩
     (p₁ ∘̂ p₃) ×c (p₂ ∘̂ p₄) ∎)
     where open ≡-Reasoning

------------------------------------------------------------------------------
-- A few "reveal" functions, to let us peek into the representation

reveal1C : ∀ {m} → allFin m ≡ 1C
reveal1C = refl

reveal0C : [] ≡ 1C {0}
reveal0C = refl

reveal⊎c :  ∀ {m₁ n₁ m₂ n₂} → {α : FinVec m₁ m₂} → {β : FinVec n₁ n₂} →
  α ⊎c β ≡
    tabulate (Plus.fwd ∘ inj₁ ∘ _!!_ α) ++V
    tabulate (Plus.fwd {m₁} ∘ inj₂ ∘ _!!_ β)
reveal⊎c = refl
    
------------------------------------------------------------------------------
