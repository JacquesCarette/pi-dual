module Sane where

import Level as U
import Data.Fin as F
import Data.List as L
--
open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Data.Vec
open import Function renaming (_∘_ to _○_) hiding (flip)

infixl 10 _◎_
infixr 8  _∘_     -- path composition
infix  4  _≡_     -- propositional equality
infix  4  _∼_     -- homotopy between two functions 
infix  4  _≃_     -- type of equivalences
infix  2  _∎      -- equational reasoning for paths
infixr 2  _≡⟨_⟩_  -- equational reasoning for paths

------------------------------------------------------------------------------
-- Finite types

data FT : Set where
  ZERO  : FT
  ONE   : FT
  PLUS  : FT → FT → FT
  TIMES : FT → FT → FT

⟦_⟧ : FT → Set
⟦ ZERO ⟧ = ⊥
⟦ ONE ⟧ = ⊤
⟦ PLUS B₁ B₂ ⟧ = ⟦ B₁ ⟧ ⊎ ⟦ B₂ ⟧
⟦ TIMES B₁ B₂ ⟧ = ⟦ B₁ ⟧ × ⟦ B₂ ⟧

------------------------------------------------------------------------------
-- Generalized paths are pi-combinators

data _⇛_ : FT → FT → Set where
  -- additive structure
  unite₊⇛  : { b : FT } → PLUS ZERO b ⇛ b
  uniti₊⇛  : { b : FT } → b ⇛ PLUS ZERO b
  swap₊⇛   : { b₁ b₂ : FT } → PLUS b₁ b₂ ⇛ PLUS b₂ b₁
  assocl₊⇛ : { b₁ b₂ b₃ : FT } → PLUS b₁ (PLUS b₂ b₃) ⇛ PLUS (PLUS b₁ b₂) b₃
  assocr₊⇛ : { b₁ b₂ b₃ : FT } → PLUS (PLUS b₁ b₂) b₃ ⇛ PLUS b₁ (PLUS b₂ b₃)
  -- multiplicative structure
  unite⋆⇛  : { b : FT } → TIMES ONE b ⇛ b
  uniti⋆⇛  : { b : FT } → b ⇛ TIMES ONE b
  swap⋆⇛   : { b₁ b₂ : FT } → TIMES b₁ b₂ ⇛ TIMES b₂ b₁
  assocl⋆⇛ : { b₁ b₂ b₃ : FT } → 
             TIMES b₁ (TIMES b₂ b₃) ⇛ TIMES (TIMES b₁ b₂) b₃
  assocr⋆⇛ : { b₁ b₂ b₃ : FT } → 
             TIMES (TIMES b₁ b₂) b₃ ⇛ TIMES b₁ (TIMES b₂ b₃)
  -- distributivity
  distz⇛   : { b : FT } → TIMES ZERO b ⇛ ZERO
  factorz⇛ : { b : FT } → ZERO ⇛ TIMES ZERO b
  dist⇛    : { b₁ b₂ b₃ : FT } → 
            TIMES (PLUS b₁ b₂) b₃ ⇛ PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) 
  factor⇛  : { b₁ b₂ b₃ : FT } → 
            PLUS (TIMES b₁ b₃) (TIMES b₂ b₃) ⇛ TIMES (PLUS b₁ b₂) b₃
  -- congruence
  id⇛    : { b : FT } → b ⇛ b
  sym⇛   : { b₁ b₂ : FT } → (b₁ ⇛ b₂) → (b₂ ⇛ b₁)
  _◎_    : { b₁ b₂ b₃ : FT } → (b₁ ⇛ b₂) → (b₂ ⇛ b₃) → (b₁ ⇛ b₃)
  _⊕_    : { b₁ b₂ b₃ b₄ : FT } → 
           (b₁ ⇛ b₃) → (b₂ ⇛ b₄) → (PLUS b₁ b₂ ⇛ PLUS b₃ b₄)
  _⊗_    : { b₁ b₂ b₃ b₄ : FT } → 
           (b₁ ⇛ b₃) → (b₂ ⇛ b₄) → (TIMES b₁ b₂ ⇛ TIMES b₃ b₄)

-- just flip.  It is he caller's responsibility to do other things

flip : {b₁ b₂ : FT} → b₂ ⇛ b₁ → b₁ ⇛ b₂
flip unite₊⇛ = uniti₊⇛
flip uniti₊⇛ = unite₊⇛
flip swap₊⇛ = swap₊⇛
flip assocl₊⇛ = assocr₊⇛
flip assocr₊⇛ = assocl₊⇛
flip unite⋆⇛ = uniti⋆⇛
flip uniti⋆⇛ = unite⋆⇛
flip swap⋆⇛ = swap⋆⇛
flip assocl⋆⇛ = assocr⋆⇛
flip assocr⋆⇛ = assocl⋆⇛
flip distz⇛ = factorz⇛
flip factorz⇛ = distz⇛
flip dist⇛ = factor⇛
flip factor⇛ = dist⇛
flip id⇛ = id⇛
flip (sym⇛ p) = p
flip (p ◎ q) = flip q ◎ flip p
flip (p ⊕ q) = flip p ⊕ flip q
flip (p ⊗ q) = flip p ⊗ flip q

------------------------------------------------------------------------------
-- Equivalences a la HoTT (using HoTT paths and path induction)

-- Our own version of refl that makes 'a' explicit

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → (a ≡ a)

-- J
pathInd : ∀ {u ℓ} → {A : Set u} → 
          (C : {x y : A} → x ≡ y → Set ℓ) → 
          (c : (x : A) → C (refl x)) → 
          ({x y : A} (p : x ≡ y) → C p)
pathInd C c (refl x) = c x

! : ∀ {u} → {A : Set u} {x y : A} → (x ≡ y) → (y ≡ x)
! = pathInd (λ {x} {y} _ → y ≡ x) refl

_∘_ : ∀ {u} → {A : Set u} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {u} {A} {x} {y} {z} p q = 
  pathInd {u}
    (λ {x} {y} p → ((z : A) → (q : y ≡ z) → (x ≡ z)))
    (λ x z q → pathInd (λ {x} {z} _ → x ≡ z) refl {x} {z} q)
    {x} {y} p z q

ap : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} {x y : A} → 
     (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {ℓ} {ℓ'} {A} {B} {x} {y} f p = 
  pathInd -- on p
    (λ {x} {y} p → f x ≡ f y) 
    (λ x → refl (f x))
    {x} {y} p

-- Abbreviations for path compositions

_≡⟨_⟩_ : ∀ {u} → {A : Set u} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_ ≡⟨ p ⟩ q = p ∘ q

_∎ : ∀ {u} → {A : Set u} (x : A) → x ≡ x
_∎ x = refl x

-- Equivalences

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {P : A → Set ℓ'} → 
      (f g : (x : A) → P x) → Set (ℓ U.⊔ ℓ')
_∼_ {ℓ} {ℓ'} {A} {P} f g = (x : A) → f x ≡ g x

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ U.⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ○ g) ∼ id
    h : B → A
    β : (h ○ f) ∼ id

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ U.⊔ ℓ')
A ≃ B = Σ (A → B) isequiv

------------------------------------------------------------------
-- Finite Types and the natural numbers are intimately related.
--
-- Basically, this is because both of them are models of 
-- unital semirings, and the natural numbers are the initial object
-- in the category of unital semirings.  In this case, things are
-- deeper still, and so we record many of these facts here.
--
-- And, of course, as Pi records the proof-theory of semirings in
-- a fairly explicit manner, we can use all this to link up 
-- normalization of natural-numbers expressions and Pi-based paths.

fromℕ : ℕ → FT
fromℕ zero = ZERO
fromℕ (suc n) = PLUS ONE (fromℕ n)

-- normalize a finite type to (1 + (1 + (1 + ... + (1 + 0) ... )))
-- a bunch of ones ending with zero with left biased + in between

⟦_⟧ℕ : ℕ → Set
⟦ zero ⟧ℕ = ⊥
⟦ suc n ⟧ℕ = ⊤ ⊎ ⟦ n ⟧ℕ

fromNormalNat : (n : ℕ) → ⟦ n ⟧ℕ → F.Fin n
fromNormalNat zero ()
fromNormalNat (suc n) (inj₁ tt) = F.zero
fromNormalNat (suc n) (inj₂ x) = F.suc (fromNormalNat n x)

toNormalNat : (n : ℕ) → F.Fin n → ⟦ n ⟧ℕ
toNormalNat zero ()
toNormalNat (suc n) F.zero = inj₁ tt
toNormalNat (suc n) (F.suc f) = inj₂ (toNormalNat n f)

equivToVec : {n : ℕ} → ⟦ n ⟧ℕ ≃ ⟦ n ⟧ℕ → Vec (F.Fin n) n
equivToVec {n} (f , _) = tabulate ((fromNormalNat n) ○ f ○ (toNormalNat n))

-- TODO: vecToEquiv needs an extra proof that the vector is in fact "normal"
-- in order to define it correctly Or we could just only use indices i such
-- that vec[i] > i, like in vecToComb...should work
--
--vecToEquiv : {n : ℕ} → Vec (F.Fin n) n → ⟦ n ⟧ℕ ≃ ⟦ n ⟧ℕ
--vecToEquiv = {!!}

swapi : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapi {zero} ()
swapi {suc n} F.zero = assocl₊⇛ ◎ swap₊⇛ ⊕ id⇛ ◎ assocr₊⇛
swapi {suc n} (F.suc i) = id⇛ ⊕ swapi {n} i

-- swapUpTo i permutes the combinator left by one up to i 
-- if possible values are X a b c Y d e, swapUpTo 3's possible outputs 
-- are a b c X Y d e
swapUpTo : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapUpTo F.zero = id⇛
swapUpTo (F.suc i) = swapi F.zero ◎ id⇛ ⊕ swapUpTo i

-- swapDownFrom i permutes the combinator right by one up to i (the reverse
-- of swapUpTo)
swapDownFrom : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapDownFrom F.zero = id⇛
swapDownFrom (F.suc i) = id⇛ ⊕ swapUpTo i ◎ swapi F.zero  

-- TODO: verify that this is actually correct
-- Idea: To swap n < m with each other, swap n, n + 1, ... , m - 1, m, then
-- go back down, so that m and n are swapped and everything else is in the
-- same spot
swapmn : {lim : ℕ} → (m : F.Fin lim) → F.Fin′ m → (fromℕ lim) ⇛ (fromℕ lim)
swapmn F.zero ()
swapmn (F.suc m) (F.zero) = swapUpTo m ◎ swapi m ◎ swapDownFrom m
swapmn (F.suc m) (F.suc n) = id⇛ ⊕ swapmn m n

-- makeSingleComb {combinator size} (arrayElement) (arrayIndex)
makeSingleComb : {n : ℕ} → F.Fin n → F.Fin n → (fromℕ n) ⇛ (fromℕ n)
makeSingleComb j i with F.compare i j
makeSingleComb .j .(F.inject i) | F.less j i = swapmn j i
makeSingleComb j i | _ = id⇛

-- upTo n returns [0, 1, ..., n-1] as Fins
upTo : (n : ℕ) → Vec (F.Fin n) n
upTo n = tabulate {n} id

vecToComb : {n : ℕ} → Vec (F.Fin n) n → (fromℕ n) ⇛ (fromℕ n)
vecToComb {n} vec = 
  foldr (λ i → fromℕ n ⇛ fromℕ n) _◎_ id⇛ (zipWith makeSingleComb vec (upTo n))

evalComb : {a b : FT} → a ⇛ b → ⟦ a ⟧ → ⟦ b ⟧
evalComb unite₊⇛ (inj₁ ())
evalComb unite₊⇛ (inj₂ y) = y
evalComb uniti₊⇛ v = inj₂ v
evalComb swap₊⇛ (inj₁ x) = inj₂ x
evalComb swap₊⇛ (inj₂ y) = inj₁ y
evalComb assocl₊⇛ (inj₁ x) = inj₁ (inj₁ x)
evalComb assocl₊⇛ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalComb assocl₊⇛ (inj₂ (inj₂ y)) = inj₂ y
evalComb assocr₊⇛ (inj₁ (inj₁ x)) = inj₁ x
evalComb assocr₊⇛ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalComb assocr₊⇛ (inj₂ y) = inj₂ (inj₂ y)
evalComb unite⋆⇛ (tt , proj₂) = proj₂
evalComb uniti⋆⇛ v = tt , v
evalComb swap⋆⇛ (proj₁ , proj₂) = proj₂ , proj₁
evalComb assocl⋆⇛ (proj₁ , proj₂ , proj₃) = (proj₁ , proj₂) , proj₃
evalComb assocr⋆⇛ ((proj₁ , proj₂) , proj₃) = proj₁ , proj₂ , proj₃
evalComb distz⇛ (() , proj₂)
evalComb factorz⇛ ()
evalComb dist⇛ (inj₁ x , proj₂) = inj₁ (x , proj₂)
evalComb dist⇛ (inj₂ y , proj₂) = inj₂ (y , proj₂)
evalComb factor⇛ (inj₁ (proj₁ , proj₂)) = inj₁ proj₁ , proj₂
evalComb factor⇛ (inj₂ (proj₁ , proj₂)) = inj₂ proj₁ , proj₂
evalComb id⇛ v = v
evalComb (sym⇛ c) v = evalComb (flip c) v -- TODO: use a backwards interpreter
evalComb (c ◎ c₁) v = evalComb c₁ (evalComb c v)
evalComb (c ⊕ c₁) (inj₁ x) = inj₁ (evalComb c x)
evalComb (c ⊕ c₁) (inj₂ y) = inj₂ (evalComb c₁ y)
evalComb (c ⊗ c₁) (proj₁ , proj₂) = evalComb c proj₁ , evalComb c₁ proj₂

finToVal : {n : ℕ} → F.Fin n → ⟦ fromℕ n ⟧
finToVal F.zero = inj₁ tt
finToVal (F.suc n) = inj₂ (finToVal n)

valToFin : {n : ℕ} → ⟦ fromℕ n ⟧ → F.Fin n
valToFin {zero} ()
valToFin {suc n} (inj₁ tt) = F.zero
valToFin {suc n} (inj₂ v) = F.suc (valToFin v)

combToVec : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (F.Fin n) n
combToVec c = tabulate (valToFin ○ (evalComb c) ○ finToVal)

evalVec : {n : ℕ} → Vec (F.Fin n) n → F.Fin n → ⟦ fromℕ n ⟧
evalVec vec i = finToVal (lookup i vec)

-- Correctness proofs for normal combinators, to be used in a univalence proof

-- TODO: define the "meaning" of a combinator (ideally somewhere else) There
-- seem to be a few functions that evaluate a combinator; we should probably
-- just choose one and call it "evalComb" or something so we have something
-- to work with here.

-- To show: equivToVec and vecToEquiv preserve meaning
-- To show: equivToVec ∘ vecToEquiv is the identity, on the nose
-- To show: a similar property for the composition in the other direction?

-- To show: vecToComb and combToVec preserve meaning (so normalizing like
-- this is safe)

lookupTab : {A : Set} → {n : ℕ} → {f : F.Fin n → A} → 
  (i : F.Fin n) → lookup i (tabulate f) ≡ (f i)
lookupTab {f = f} F.zero = refl (f F.zero)
lookupTab (F.suc i) = lookupTab i

finToValToFin : {n : ℕ} → (v : ⟦ fromℕ n ⟧) → finToVal (valToFin v) ≡ v
finToValToFin {zero} ()
finToValToFin {suc n} (inj₁ tt)  = refl (inj₁ tt)
finToValToFin {suc n} (inj₂ v) = ap inj₂ (finToValToFin v)

--  Might want to take a ⟦ fromℕ n ⟧ instead of a Fin n as the second
--  argument here?
combToVecWorks : {n : ℕ} → (c : (fromℕ n) ⇛ (fromℕ n)) → 
  (i : F.Fin n) → (evalComb c (finToVal i)) ≡ evalVec (combToVec c) i
combToVecWorks c i = (! (finToValToFin _)) ∘ (ap finToVal (! (lookupTab i)))

-- The trickier one

_!!_ : {A : Set} → {n : ℕ} → Vec A n → F.Fin n → A
_!!_ v i = lookup i v

map!! : {A B : Set} → {n : ℕ} → (f : A → B) → (v : Vec A n) → (i : F.Fin n) → 
        (map f v) !! i ≡ f (v !! i)
map!! {n = zero} f [] ()
map!! {n = suc n} f (x ∷ xs) F.zero = refl (f x)
map!! {n = suc n} f (x ∷ xs) (F.suc i) = map!! f xs i

foldrWorks : {A : Set} → {m : ℕ} → 
             (B : ℕ → Set) → (P : (n : ℕ) → Vec A n → B n → Set)
           → (_⊕_ : {n : ℕ} → A → B n → B (suc n)) → (base : B zero)
           → ({n : ℕ} → (a : A) → (v : Vec A n) → (b : B n) → P n v b
              → P (suc n) (a ∷ v) (a ⊕ b))
           → P zero [] base
           → (v : Vec A m)
           → P m v (foldr B _⊕_ base v)
foldrWorks B P combine base pcombine pbase [] = pbase
foldrWorks B P combine base pcombine pbase (x ∷ v) =
  pcombine x v (foldr B combine base v) 
    (foldrWorks B P combine base pcombine pbase v)

-- IDEA: reformulate evaluation as a relation between a combinator and its
-- output vector?  Would simplify the correctness condition we're trying to
-- prove

-- Correctness specifically for the subset of combinators used in vecToComb
-- Should be able to use these to build up all the important lemmas for the
-- final proof, then use vecRepWorks to finish it off
data vecRep : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (F.Fin n) n → Set where
  vr-id    : {n : ℕ} → vecRep (id⇛ {fromℕ n}) (upTo n)
  vr-swap  : 
    {n : ℕ} → 
    vecRep {suc (suc n)} (swapi {suc n} F.zero)
      ((F.suc F.zero) ∷ F.zero ∷ 
       (Data.Vec.map (λ i → F.suc (F.suc i)) (upTo n)))
  vr-comp  : 
    {n : ℕ} → {c₁ c₂ : (fromℕ n) ⇛ (fromℕ n)} → {v₁ v₂ : Vec (F.Fin n) n} → 
    vecRep c₁ v₁ → vecRep c₂ v₂ → 
    vecRep (c₁ ◎ c₂) (tabulate {n} (λ i → (lookup (lookup i v₂) v₁)))
  vr-plus : {n : ℕ} → {c : (fromℕ n) ⇛ (fromℕ n)} → {v : Vec (F.Fin n) n} → 
    vecRep {n} c v → 
    vecRep {suc n} (id⇛ ⊕ c) (F.zero ∷ (Data.Vec.map F.suc v))

vecRepWorks : {n : ℕ} → {c : (fromℕ n) ⇛ (fromℕ n)} → {v : Vec (F.Fin n) n} → 
  vecRep c v → (i : F.Fin n) → (evalVec v i) ≡ (evalComb c (finToVal i))
vecRepWorks vr-id i = {!!} -- ap finToVal (lookupTab i)
vecRepWorks vr-swap i = {!!}
vecRepWorks (vr-comp vr vr₁) i = {!!}
vecRepWorks {suc n} (vr-plus vr) F.zero = {!!} -- refl (inj₁ tt)
vecRepWorks (vr-plus {c = c} {v = v} vr) (F.suc i) = {!!} 
{--
  evalVec (F.zero ∷ map F.suc v) (F.suc i) ≡⟨ ap finToVal (map!! F.suc v i) ⟩
  inj₂ (finToVal (v !! i)) ≡⟨ ap inj₂ (vecRepWorks vr i) ⟩
  (evalComb (id⇛ ⊕ c) (finToVal (F.suc i)) ∎)
--}

-- XXX: the predicate here should probably return a vecRep, and the proof
-- should get finished off by vecRepWorks; might want to break that out into
-- separate lemmas
vecToCombWorks : {n : ℕ} → 
  (v : Vec (F.Fin n) n) → (i : F.Fin n) → 
  (evalVec v i) ≡ (evalComb (vecToComb v) (finToVal i))
vecToCombWorks {n} v = {!!} 
{--
  foldrWorks
    {fromℕ n ⇛ fromℕ n}
    {n}
    (λ i → fromℕ n ⇛ fromℕ n)
    -- I think we need to rewrite vecToComb using an indexed fold to have all
    -- the information here that we need for the correctness proof [Z]
    (λ n′ v c → (i : F.Fin n′) → {!!}) 
    -- (evalVec {n′} v i) ≡ (evalComb c (finToVal i)))
    _◎_
    id⇛
    {!!} -- combination lemma
    {!!} -- base case lemma
    (zipWith makeSingleComb v (upTo n))
--}
