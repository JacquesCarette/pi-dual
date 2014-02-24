module Sane where

import Data.Fin as F
--
open import Data.Empty
open import Data.Unit
open import Data.Unit.Core
open import Data.Nat renaming (_⊔_ to _⊔ℕ_)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product renaming (map to _×→_)
open import Data.Vec
open import Function renaming (_∘_ to _○_) 

-- start re-splitting things up, as this is getting out of hand
open import FT -- Finite Types
open import SimpleHoTT using (_≡_ ; refl ; pathInd ; ! ; _∘_ ; ap ; _≡⟨_⟩_ ; _∎ ; hetType)
open import VecHelpers
open import NatSimple

-- construct a combinator which represents the swapping of the i-th and 
-- (i+1)-th 'bit' of a finite type.  
-- Best to think of this as an 'elementary permutation', in the same way
-- we have 'elementary matrices' (which turn out to be permutations when they
-- are unitary).
swapi : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapi {zero}  ()
swapi {suc n} F.zero    = assocl₊⇛ ◎ swap₊⇛ ⊕ id⇛ ◎ assocr₊⇛
swapi {suc n} (F.suc i) = id⇛ ⊕ swapi {n} i

-- swapUpTo i permutes the combinator left by one up to i 
-- if possible values are X a b c Y d e, swapUpTo 3's possible outputs 
-- are a b c X Y d e
swapUpTo : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapUpTo F.zero    = id⇛
swapUpTo (F.suc i) = (id⇛ ⊕ swapUpTo i) ◎ swapi F.zero  

-- swapDownFrom i permutes the combinator right by one up to i (the reverse
-- of swapUpTo)
swapDownFrom : {n : ℕ} → F.Fin n → (fromℕ (suc n)) ⇛ (fromℕ (suc n))
swapDownFrom F.zero    = id⇛
swapDownFrom (F.suc i) = swapi F.zero ◎ (id⇛ ⊕ swapDownFrom i)

-- TODO: verify that this is actually correct
-- Idea: To swap n < m with each other, swap n, n + 1, ... , m - 1, m, then
-- go back down, so that m and n are swapped and everything else is in the
-- same spot
-- makeSingleComb {combinator size} (arrayElement) (arrayIndex),
-- gives a combinator which 'does' that, assuming i<j, else id⇛
makeSingleComb : {n : ℕ} → F.Fin n → F.Fin n → (fromℕ n) ⇛ (fromℕ n)
makeSingleComb F.zero   F.zero     = id⇛
makeSingleComb F.zero   (F.suc i)  = id⇛
makeSingleComb (F.suc j) F.zero   = swapDownFrom j ◎ swapi j ◎ swapUpTo j
makeSingleComb (F.suc j) (F.suc i) = id⇛ ⊕ makeSingleComb j i

-- Correctness: after putting together i indices, the partial combinator c' is
-- represented by the vector [1, 2, ... , n - (i +1)] ++ (last i v)
--
-- Might want to bake in the correctness proof here---have the output be a
-- combinator c, a vector v, and a proof that vecRep c v, then we just prove
-- that the vector at the end is just the vector from the beginning
--
-- Or just put them together and prove that they're related by vecRep with
-- foldrWorks and that the end vector is the input vector; this is probably simpler
-- (and is the approach currently reflected in the code below)

-- swapInd i j returns a vector v′ where v′[i] = j, v′[j] = i, and v′[k] = k
-- where k != j and k != i

zeroIfEq : {n n′ : ℕ} → F.Fin n → F.Fin n → F.Fin (suc n′) → F.Fin (suc n′)
zeroIfEq F.zero    F.zero   ret = F.zero
zeroIfEq F.zero   (F.suc j) ret = ret
zeroIfEq (F.suc i) F.zero   ret = ret
zeroIfEq (F.suc i) (F.suc j) ret = zeroIfEq i j ret

swapIndFn : {n : ℕ} → F.Fin n → F.Fin n → (F.Fin n → F.Fin n)
swapIndFn                       F.zero     j              F.zero   = j
swapIndFn                       (F.suc i)  F.zero     F.zero   = F.suc i
swapIndFn                       (F.suc i) (F.suc j)    F.zero   = F.zero
swapIndFn                       F.zero     F.zero    (F.suc x) = F.suc x
swapIndFn {suc zero}     F.zero   (F.suc ()) (F.suc x)
swapIndFn {suc (suc n)} F.zero   (F.suc j)  (F.suc x) = zeroIfEq j x (F.suc x)
swapIndFn                       (F.suc i)  F.zero    (F.suc x) = zeroIfEq i x (F.suc x)
swapIndFn                       (F.suc i) (F.suc j)  (F.suc x) = F.suc (swapIndFn i j x)

swapInd : {n : ℕ} → F.Fin n → F.Fin n → Vec (F.Fin n) n
swapInd i j = tabulate (swapIndFn i j)

swapIndVec : {n : ℕ} → F.Fin n → F.Fin n → Vec (F.Fin n) n → Vec (F.Fin n) n
swapIndVec i j v = tabulate (λ k → v !! swapIndFn i j k)

-- vecRep c v relates a combinator c over normal types to the output
-- vector it results in. This works only over a subset of combinators
-- used in decompilation.
data vecRep : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (F.Fin n) n → Set where
  vr-id    : {n : ℕ} → vecRep (id⇛ {fromℕ n}) (upTo n)
  vr-swap  :   {n : ℕ} → 
    vecRep {suc (suc n)} (swapi {suc n} F.zero)
      ((F.suc F.zero) ∷ F.zero ∷ 
       (tabulate (λ i → F.suc (F.suc i)) ))
  vr-comp  : {n : ℕ} → {c₁ c₂ : (fromℕ n) ⇛ (fromℕ n)} → {v₁ v₂ : Vec (F.Fin n) n} → 
    vecRep c₁ v₁ → vecRep c₂ v₂ → 
    vecRep (c₁ ◎ c₂) (v₁ ∘̬ v₂)
  vr-plus : {n : ℕ} → {c : (fromℕ n) ⇛ (fromℕ n)} → {v : Vec (F.Fin n) n} → 
    vecRep {n} c v → 
    vecRep {suc n} (id⇛ ⊕ c) (F.zero ∷ (vmap F.suc v))

-- Record for keeping a combinator, a vector, and a proof that they compute
-- the same function.
record Compiled (n : ℕ) : Set where
  constructor
    _►_⟨_⟩
  field
    comb   : (fromℕ n) ⇛ (fromℕ n)
    vec    : Vec (F.Fin n) n
    proof  : vecRep comb vec

{-- For reference

swapmn : {lim : ℕ} → (m : F.Fin lim) → F.Fin′ m → (fromℕ lim) ⇛ (fromℕ lim)
swapmn F.zero ()
swapmn (F.suc m) (F.zero) = swapUpTo m ◎ swapi m ◎ swapDownFrom m
swapmn (F.suc m) (F.suc n) = id⇛ ⊕ swapmn m n                              
--}

swapIndIdAfterOne : {n : ℕ} → (i : F.Fin n) →
                    (F.suc (F.suc i)) ≡ (swapIndFn F.zero (F.suc F.zero) (F.suc (F.suc i)))
swapIndIdAfterOne i = refl _ -- yesss finally it just works!
  
swap≡ind₀ : {n : ℕ} →
            ((F.suc F.zero) ∷ F.zero ∷ (vmap (λ i → F.suc (F.suc i)) (upTo n)))
            ≡ (swapInd F.zero (F.suc F.zero))
swap≡ind₀ {n} = ap (λ v → F.suc F.zero ∷ F.zero ∷ v)
               ((vmap (λ i → F.suc (F.suc i)) (upTo n)) ≡⟨ mapTab _ _ ⟩
               (tabulate (id ○ (λ i → F.suc (F.suc i)))) ≡⟨ tabf∼g _ _ swapIndIdAfterOne ⟩
               ((tabulate (((swapIndFn F.zero (F.suc F.zero)) ○ F.suc) ○ F.suc)) ∎))

swapIndSucDist : {n : ℕ} → (i j x : F.Fin n) →
                 (F.suc (swapIndFn i j x)) ≡
                 (swapIndFn (F.suc i) (F.suc j) (F.suc x))
swapIndSucDist i j x = refl _

swap≡ind₁ : {n : ℕ} → (i : F.Fin n) →
            F.zero ∷ vmap F.suc (swapInd (F.inject₁ i) (F.suc i)) ≡
            swapInd (F.inject₁ (F.suc i)) (F.suc (F.suc i))
swap≡ind₁ {n} i =
  F.zero ∷ (vmap F.suc (swapInd (F.inject₁ i) (F.suc i)))
    ≡⟨ ap (_∷_ F.zero)
      (vmap F.suc (swapInd (F.inject₁ i) (F.suc i))
        ≡⟨ mapTab F.suc (swapIndFn (F.inject₁ i) (F.suc i)) ⟩
         tabulate (F.suc ○ swapIndFn (F.inject₁ i) (F.suc i))
           ≡⟨ tabf∼g _ _ (swapIndSucDist (F.inject₁ i) (F.suc i)) ⟩
         (tabulate
          (swapIndFn (F.inject₁ (F.suc i)) (F.suc (F.suc i)) ○ F.suc)
          ∎)) ⟩
  ((swapInd (F.inject₁ (F.suc i)) (F.suc (F.suc i))) ∎)
               
-- TODO: there might be a better vector to put in the vecRep here
-- we'll need to see what's most amenable to proving swapUpToWorks
swapiWorks : {n : ℕ} → (i : F.Fin n) → vecRep (swapi i) (swapInd (F.inject₁ i) (F.suc i))
swapiWorks {zero} ()
swapiWorks {suc n} F.zero = vr-swap
swapiWorks {suc n} (F.suc i) =
  hetType (vr-plus (swapiWorks i)) (ap (vecRep (id⇛ ⊕ swapi i)) (swap≡ind₁ i)) 

-- permutations on vectors for specifying swapUpTo/DownFrom
  
data _<F_ : {n : ℕ} → F.Fin n → F.Fin n → Set where
  zero-leq : {n : ℕ} → {i : F.Fin n} → F.zero <F (F.suc i)
  suc-leq  : {n : ℕ} → {i j : F.Fin n} → i <F j → (F.suc i) <F (F.suc j)

<suc : {n : ℕ} → (i j : F.Fin n) → (F.suc i) <F (F.suc j) → i <F j
<suc i j (suc-leq p) = p
  
dec<F : {n : ℕ} → (i j : F.Fin n) → Dec (i <F j)
dec<F F.zero    F.zero   = no (λ ())
dec<F F.zero   (F.suc j) = yes zero-leq
dec<F (F.suc i) F.zero   = no (λ ())
dec<F (F.suc i) (F.suc j) with dec<F i j
dec<F (F.suc i) (F.suc j) | yes x = yes (suc-leq x)
dec<F (F.suc i) (F.suc j) | no x = no (λ p → x (<suc i j p))

-- swap args of F.inject+
inj+ : {m n : ℕ} → F.Fin m → F.Fin (n + m)
inj+ {m} {n} i = hetType (F.inject+ n i) (ap F.Fin (+-comm m n))

-- the library definition of + on Fin isn't what we want here, ugh
_+F_ : {m n : ℕ} → F.Fin (suc m) → F.Fin n → F.Fin (m + n)
_+F_ {m} {zero} F.zero ()
_+F_ {m} {suc n} F.zero j = inj+ {suc n} {m} j
_+F_ {zero} {n} (F.suc ()) _
_+F_ {suc m} {n} (F.suc i) j = F.suc (i +F j)

-- Second argument is an accumulator
-- plf′ max i acc = (i + acc) + 1 mod (max + acc) if (i + acc) <= (max + acc), (max + acc) ow
-- This is the simplest way I could come up with to do this without
-- using F.compare or something similar
{-
plf′ : {m n : ℕ} → F.Fin (suc m) → F.Fin (suc m) → F.Fin n → F.Fin (m + n)
plf′ {n = zero}    F.zero           F.zero          ()
plf′ {m} {suc n}   F.zero           F.zero          acc =
  hetType F.zero (ap F.Fin (! (m+1+n≡1+m+n m _))) -- m mod m == 0
plf′               F.zero          (F.suc i)        acc = (F.suc i) +F acc -- above the threshold, so just id
plf′              (F.suc {zero} ()) _               _
plf′              (F.suc {suc m} max) F.zero        acc =  -- we're in range, so take succ of acc
  hetType (inj+ {n = m} (F.suc acc)) (ap F.Fin (m+1+n≡1+m+n m _))
plf′              (F.suc {suc m} max) (F.suc i)     acc = -- we don't know what to do yet, so incr acc & recur
  hetType (plf′ max i (F.suc acc))
          (ap F.Fin ((m+1+n≡1+m+n m _)))
-}
data _h≡_ {A : Set} : {B : Set} → A → B → Set₁ where
  hrefl : (x : A) → _h≡_ {A} {A} x x

hetTypeIsID : {A B : Set} → (x : A) → (p : A ≡ B) → (hetType x p) h≡ x
hetTypeIsID x (refl _) = hrefl x
          
-- Permute the first i elements of v to the right one
-- Should correspond with swapDownFrom
-- permuteRight : {n : ℕ} → (i : F.Fin n) → Vec (F.Fin n) n → Vec (F.Fin n) n
-- permuteRight i v = tabulate (permRightFn v i)

permuteRight : {n : ℕ} → (i : F.Fin n) → Vec (F.Fin n) n
permuteRight {zero} ()
permuteRight {suc n} F.zero = upTo _
permuteRight {suc zero} (F.suc ())
permuteRight {suc (suc n)} (F.suc i) with permuteRight {suc n} i
permuteRight {suc (suc n)} (F.suc i) | x ∷ xs = F.suc x ∷ F.zero ∷ vmap F.suc xs

-- redundant helper
permRightID : {n : ℕ} → F.Fin n → Vec (F.Fin n) n
permRightID i = permuteRight i

-- The opposite of permuteRight; should correspond with swapUpTo
pl′ : {m n : ℕ} → F.Fin m → Vec (F.Fin n) m → F.Fin n → Vec (F.Fin n) (suc m)
pl′ {m = zero} () _ _
pl′ {m = suc m} F.zero (x ∷ xs) first = x ∷ first ∷ xs
pl′ (F.suc i) (x ∷ xs) first = x ∷ (pl′ i xs first)

permuteLeft : {n : ℕ} → (i : F.Fin n) → Vec (F.Fin n) n → Vec (F.Fin n) n
permuteLeft {zero} () _
permuteLeft {suc n} F.zero v = v
permuteLeft {suc zero} (F.suc ()) _
permuteLeft {suc (suc n)} (F.suc i) (a ∷ b ∷ rest) = pl′ i (b ∷ rest) a

permLeftID : {n : ℕ} → F.Fin n → Vec (F.Fin n) n
permLeftID i = permuteLeft i (upTo _)

permLeftId₀ : {n : ℕ} → (upTo (suc n)) ≡ permuteLeft F.zero (upTo (suc n))
permLeftId₀ {n} = refl (F.zero ∷ tabulate F.suc)

permLeftIdPasti : {n : ℕ} → (v : Vec (F.Fin (suc (suc n))) (suc (suc n))) →
                  (i : F.Fin n) →
                  permuteLeft (F.suc F.zero) v !! (F.suc (F.suc i)) ≡ v !! (F.suc (F.suc i))
permLeftIdPasti (x ∷ x₁ ∷ x₂ ∷ v) F.zero = refl _
permLeftIdPasti (x ∷ x₁ ∷ x₂ ∷ v) (F.suc i) = refl _

swapUp₀ : {n : ℕ} → (i : F.Fin (suc (suc (suc n)))) →
          ((F.zero ∷ vmap F.suc ((permuteLeft F.zero) (upTo (suc (suc n)))))
          ∘̬ (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)))) !! i
          ≡
          permuteLeft (F.suc F.zero) (upTo (suc (suc (suc n)))) !! i
swapUp₀ {n} F.zero =
          ((F.zero ∷ vmap F.suc ((permuteLeft F.zero) (upTo (suc (suc n)))))
          ∘̬ (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo (suc n)))) !! F.zero
            ≡⟨ refl (F.suc F.zero) ⟩
          F.suc F.zero
            ≡⟨ refl (F.suc F.zero) ⟩
          permuteLeft (F.suc F.zero) (upTo (suc (suc (suc n))))
            !! F.zero ∎
swapUp₀ {n} (F.suc F.zero) =
        ((F.zero ∷ vmap F.suc (permuteLeft F.zero (upTo (suc (suc n)))))
        ∘̬ (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo (suc n)))) !! F.suc F.zero
          ≡⟨ refl _ ⟩
        (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo (suc n))) !!
        (((F.zero ∷ vmap F.suc (permuteLeft F.zero (upTo (suc (suc n))))) !! F.suc F.zero))
          ≡⟨ refl _ ⟩
        (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo (suc n))) !!
        (((vmap F.suc (permuteLeft F.zero (upTo (suc (suc n))))) !! F.zero))
          ≡⟨ ap
               (λ x →
                  (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo (suc n))) !!
                  (vmap F.suc x !! F.zero))
               (! permLeftId₀) ⟩
        (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo (suc n))) !!
        (((vmap F.suc (upTo (suc (suc n)))) !! F.zero))
          ≡⟨ ap
               (λ x →
                  (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo (suc n))) !! x)
               (map!! F.suc (upTo _) F.zero) -- F.suc (upTo (suc (suc n))) F.zero)
               ⟩
        (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo (suc n))) !! (F.suc F.zero)
          ≡⟨ refl F.zero ⟩
        F.zero
          ≡⟨ ! (lookupTab {f = id} F.zero) ⟩
        (upTo (suc (suc (suc n)))) !! F.zero
          ≡⟨ refl F.zero ⟩
        permuteLeft (F.suc F.zero) (upTo (suc (suc (suc n)))) !! F.suc F.zero ∎
         
swapUp₀ {n} (F.suc (F.suc i)) =
  ((F.zero ∷ vmap F.suc (permuteLeft F.zero (upTo (suc (suc n))))) ∘̬
     (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)) ))
    !! F.suc (F.suc i)
    ≡⟨ lookupTab
         {f = λ x →
                (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i))) !!
                  ((F.zero ∷ vmap F.suc (permuteLeft F.zero (upTo (suc (suc n))))) !! x)}
         (F.suc (F.suc i)) ⟩
  (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)) ) !!
    ((F.zero ∷ vmap F.suc (permuteLeft F.zero (upTo (suc (suc n))))) !! F.suc (F.suc i))
    ≡⟨ ap (λ x →
             (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)) ) !!
               ((F.zero ∷ vmap F.suc x) !! F.suc (F.suc i)))
           (! permLeftId₀) ⟩
  (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)) ) !!
     ((F.zero ∷ vmap F.suc (upTo (suc (suc n)))) !! F.suc (F.suc i))
    ≡⟨ ap
         (λ x →
            (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)) ) !! x)
         (map!! F.suc (upTo (suc (suc n))) (F.suc i)) ⟩
  (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)) ) !!
    F.suc (upTo (suc (suc n)) !! F.suc i)
    ≡⟨ ap
         (λ x →
            (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)) ) !!
            F.suc x)
         (lookupTab {f = id} (F.suc i)) ⟩
  (tabulate (λ i → F.suc (F.suc i)) ) !! i
--    ≡⟨ lookupTab {f = id} (F.suc (F.suc i)) ⟩
--  F.suc (F.suc i)
--    ≡⟨ ! (lookupTab {f = id} (F.suc (F.suc i))) ⟩
--  upTo (suc (suc (suc n))) !! (F.suc (F.suc i))  
    ≡⟨ ! (permLeftIdPasti (upTo (suc (suc (suc n)))) i) ⟩
  permuteLeft (F.suc F.zero) (upTo (suc (suc (suc n)))) !! F.suc (F.suc i) ∎

{--
pl′ : {m n : ℕ} → F.Fin m → Vec (F.Fin n) m → F.Fin n → Vec (F.Fin n) (suc m)
pl′ {m = zero} () _ _
pl′ {m = suc m} F.zero (x ∷ xs) first = x ∷ first ∷ xs
pl′ (F.suc i) (x ∷ xs) first = x ∷ (pl′ i xs first)

permuteLeft : {n : ℕ} → (i : F.Fin n) → Vec (F.Fin n) n → Vec (F.Fin n) n
permuteLeft {zero} () _
permuteLeft {suc n} F.zero v = v
permuteLeft {suc zero} (F.suc ()) _
permuteLeft {suc (suc n)} (F.suc i) (a ∷ b ∷ rest) = pl′ i (b ∷ rest) a
--}

plcomp : {n : ℕ} → (i : F.Fin n) →
         ((vmap F.suc (pl′ (F.inject₁ i) (tabulate (F.suc ○ F.suc)) F.zero)) ∘̬′
           (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷ (tabulate {suc n} (F.suc ○ F.suc ○ F.suc))))
         ≡
         pl′ (F.inject₁ i) (tabulate (F.suc ○ F.suc ○ F.suc)) F.zero
plcomp {suc n} F.zero =
  ((vmap F.suc (pl′ (F.inject₁ F.zero) (tabulate (F.suc ○ F.suc)) F.zero)) ∘̬′
    (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷ (tabulate {suc (suc n)} (F.suc ○ F.suc ○ F.suc))))
    ≡⟨ refl _ ⟩
  ((vmap F.suc (F.suc (F.suc F.zero) ∷ F.zero ∷ tabulate (F.suc ○ F.suc ○ F.suc))) ∘̬′
    (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷ (tabulate {suc (suc n)} (F.suc ○ F.suc ○ F.suc))))
    ≡⟨ refl _ ⟩
  ((F.suc (F.suc (F.suc F.zero)) ∷ F.suc F.zero ∷ vmap F.suc (tabulate (F.suc ○ F.suc ○ F.suc))) ∘̬′
    (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷ (tabulate {suc (suc n)} (F.suc ○ F.suc ○ F.suc))))
    ≡⟨ ap
         (λ x →
           ((F.suc (F.suc (F.suc F.zero)) ∷ F.suc F.zero ∷ x) ∘̬′
             (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷
               (tabulate {suc (suc n)} (F.suc ○ F.suc ○ F.suc)))))
         (mapTab F.suc (F.suc ○ F.suc ○ F.suc)) ⟩
  ((F.suc (F.suc (F.suc F.zero)) ∷ F.suc F.zero ∷
    (tabulate (F.suc ○ F.suc ○ F.suc ○ F.suc))) ∘̬′
  (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷
    (tabulate {suc (suc n)} (F.suc ○ F.suc ○ F.suc))))
    ≡⟨ refl _ ⟩
  F.suc (F.suc (F.suc F.zero)) ∷ F.zero ∷
  (((tabulate (F.suc ○ F.suc ○ F.suc ○ F.suc))) ∘̬′
  (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷
    (tabulate {suc (suc n)} (F.suc ○ F.suc ○ F.suc))))
    ≡⟨ {!!} ⟩    
  F.suc (F.suc (F.suc F.zero)) ∷ F.zero ∷ tabulate (F.suc ○ F.suc ○ F.suc ○ F.suc)
    ≡⟨ refl _ ⟩    
  pl′ (F.inject₁ F.zero) (tabulate (F.suc ○ F.suc ○ F.suc)) F.zero ∎  
plcomp (F.suc i) = {!!}         

permLeft₁ : {n : ℕ} → (i : F.Fin n) →
            permuteLeft (F.inject₁ (F.suc (F.suc i))) (upTo (suc (suc (suc n)))) ≡
            F.suc F.zero ∷ pl′ (F.inject₁ i) (tail (tail (upTo (suc (suc (suc n)))))) F.zero
permLeft₁ i = refl _            

-- makes sure we have at least two elements on the front of permLeft to reason about
permLeft₂ : {n : ℕ} → (i : F.Fin n) →
            F.suc F.zero ∷ F.suc (F.suc F.zero) ∷
              pl′ (F.inject₁ i) (tail (tail (tail (upTo (suc (suc (suc (suc n)))))))) F.zero ≡
            permuteLeft (F.inject₁ (F.suc (F.suc (F.suc i)))) (upTo (suc (suc (suc (suc n)))))
permLeft₂ F.zero = refl _
permLeft₂ (F.suc i) = refl _            
  
swapUpCompWorks : {n : ℕ} → (i : F.Fin n) →
                  (F.zero ∷ vmap F.suc (permuteLeft (F.inject₁ i) (upTo (suc n))))
                  ∘̬ (F.suc F.zero ∷ F.zero ∷ tabulate (λ i → F.suc (F.suc i)))
                  ≡ permuteLeft (F.inject₁ (F.suc i)) (upTo (suc (suc n)))
swapUpCompWorks {suc n} F.zero = lookup∼vec _ _ swapUp₀
swapUpCompWorks (F.suc F.zero) = {!!}
swapUpCompWorks {suc (suc n)} (F.suc (F.suc i)) =
  (F.zero ∷ vmap F.suc (permuteLeft (F.inject₁ (F.suc (F.suc i))) (upTo (suc (suc (suc n))))))
  ∘̬ (F.suc F.zero ∷ F.zero ∷ tabulate (F.suc ○ F.suc))
    ≡⟨ ap (λ x →
               (F.zero ∷ vmap F.suc x) ∘̬
               (F.suc F.zero ∷ F.zero ∷ tabulate (F.suc ○ F.suc))) (permLeft₁ i) ⟩
  (F.zero ∷ vmap F.suc (F.suc F.zero ∷
                        pl′ (F.inject₁ i) (tail (tail (upTo (suc (suc (suc n)))))) F.zero))
    ∘̬ (F.suc F.zero ∷ F.zero ∷ tabulate (F.suc ○ F.suc))
    ≡⟨ refl _ ⟩
  (F.zero ∷ F.suc (F.suc F.zero) ∷
          vmap F.suc (pl′ (F.inject₁ i) (tail (tail (upTo (suc (suc (suc n)))))) F.zero))
    ∘̬ (F.suc F.zero ∷ F.zero ∷ tabulate {suc (suc n)} (F.suc ○ F.suc))
    ≡⟨ refl _ ⟩
  (F.zero ∷ F.suc (F.suc F.zero) ∷ vmap F.suc (pl′ (F.inject₁ i) (tail (tail (upTo (suc (suc (suc n)))))) F.zero))
    ∘̬ (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷ (tabulate {suc n} (F.suc ○ F.suc ○ F.suc)))
    ≡⟨ ∘̬≡∘̬′ (F.zero ∷ F.suc (F.suc F.zero) ∷ vmap F.suc (pl′ (F.inject₁ i) (tail (tail (upTo (suc (suc (suc n)))))) F.zero))
            (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷ (tabulate {suc n} (F.suc ○ F.suc ○ F.suc))) ⟩
  (F.zero ∷ F.suc (F.suc F.zero) ∷ vmap F.suc (pl′ (F.inject₁ i) (tail (tail (upTo (suc (suc (suc n)))))) F.zero))
    ∘̬′ (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷ (tabulate {suc n} (F.suc ○ F.suc ○ F.suc)))
    ≡⟨ refl _ ⟩
  F.suc F.zero ∷ F.suc (F.suc F.zero) ∷
    ((vmap F.suc (pl′ (F.inject₁ i) (tabulate (F.suc ○ F.suc)) F.zero)) ∘̬′
      (F.suc F.zero ∷ F.zero ∷ F.suc (F.suc F.zero) ∷ (tabulate {suc n} (F.suc ○ F.suc ○ F.suc))))
    ≡⟨ ap (λ x → F.suc F.zero ∷ F.suc (F.suc F.zero) ∷ x) (plcomp i) ⟩
   F.suc F.zero ∷ F.suc (F.suc F.zero) ∷
    pl′ (F.inject₁ i) (tabulate (F.suc ○ F.suc ○ F.suc)) F.zero
    ≡⟨ permLeft₂ i ⟩
  permuteLeft (F.inject₁ (F.suc (F.suc (F.suc i)))) (upTo (suc (suc (suc (suc n))))) ∎

         
-- NB: I added the F.inject₁ in calls to permuteLeft/Right to get it to work
-- with swapUpTo/DownFrom; I'm not sure that this is correct? It might
-- be a sign that the type of the swap functions is too specific, instead.
-- (though now it looks like it will at least make the type of shuffle a bit nicer) [Z]
swapUpToWorks : {n : ℕ} → (i : F.Fin n) →
                vecRep (swapUpTo i) (permuteLeft (F.inject₁ i) (upTo (suc n)))
swapUpToWorks F.zero = vr-id
swapUpToWorks (F.suc i) = hetType (vr-comp (vr-plus (swapUpToWorks i)) vr-swap)
                         (ap (vecRep (swapUpTo (F.suc i))) (swapUpCompWorks i))
-- swapUpToWorks (F.suc i) = {!(vr-comp (vr-plus (swapUpToWorks i)) vr-swap)!}

--vr-comp (hetType (vr-plus (swapUpToWorks i)) {!!})
--                                  (hetType vr-swap {!!})

swapDownFromWorks : {n : ℕ} → (i : F.Fin n) →
                    vecRep (swapDownFrom i) (permuteRight (F.inject₁ i))
swapDownFromWorks {zero} ()
swapDownFromWorks {suc n} F.zero = vr-id
swapDownFromWorks {suc n} (F.suc i) with permuteRight (F.inject₁ i)
swapDownFromWorks {suc n} (F.suc i) | F.zero ∷ z = {!vr-comp vr-swap ?!}
swapDownFromWorks {suc n} (F.suc i) | F.suc x ∷ z = {!!}

-- Will probably be a key lemma in swapmnWorks
-- XXX: probably should just be composed with ∘̬ after all instead of explicitly
-- including the vector as an argument (whoops), with a helper lemma that says
-- (tabulate f) ∘̬ (tabulate g) ≡ tabulate (g ○ f)
shuffle : {n : ℕ} → (i : F.Fin n) →
           (permLeftID (F.inject₁ i)
          ∘̬ swapInd (F.inject₁ i) (F.suc i)
          ∘̬ permRightID (F.inject₁ i))
        ≡ swapInd F.zero (F.suc i)
shuffle {zero} ()
shuffle {suc n} F.zero = {!!}
shuffle {suc n} (F.suc i) = {!!}


_◎∘̬_ : {n : ℕ} → Compiled n → Compiled n → Compiled n
(c₁ ► v₁ ⟨ p₁ ⟩) ◎∘̬ (c₂ ► v₂ ⟨ p₂ ⟩) = ((c₁ ◎ c₂) ► v₁ ∘̬ v₂ ⟨ vr-comp p₁ p₂ ⟩ )

vecToComb : {n : ℕ} → Vec (F.Fin n) n → (fromℕ n) ⇛ (fromℕ n)
vecToComb {n} vec = 
  foldr (λ i → fromℕ n ⇛ fromℕ n) _◎_ id⇛ (map (λ i → makeSingleComb (vec !! i) i) (upTo n))
{- vecToComb {zero} _ = id⇛
vecToComb {suc n} vec = 
    foldr₁ _◎_ (zipWith makeSingleComb vec (upTo (suc n))) -}

mutual
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
  evalComb (sym⇛ c) v = evalBComb c v 
  evalComb (c₁ ◎ c₂) v = evalComb c₂ (evalComb c₁ v)
  evalComb (c ⊕ c₁) (inj₁ x) = inj₁ (evalComb c x)
  evalComb (c ⊕ c₁) (inj₂ y) = inj₂ (evalComb c₁ y)
  evalComb (c ⊗ c₁) (proj₁ , proj₂) = evalComb c proj₁ , evalComb c₁ proj₂

  evalBComb : {a b : FT} → a ⇛ b → ⟦ b ⟧ → ⟦ a ⟧
  evalBComb unite₊⇛ v = inj₂ v
  evalBComb uniti₊⇛ (inj₁ ())
  evalBComb uniti₊⇛ (inj₂ y) = y
  evalBComb swap₊⇛ (inj₁ x) = inj₂ x
  evalBComb swap₊⇛ (inj₂ y) = inj₁ y
  evalBComb assocl₊⇛ (inj₁ (inj₁ x)) = inj₁ x
  evalBComb assocl₊⇛ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  evalBComb assocl₊⇛ (inj₂ y) = inj₂ (inj₂ y)
  evalBComb assocr₊⇛ (inj₁ x) = inj₁ (inj₁ x)
  evalBComb assocr₊⇛ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  evalBComb assocr₊⇛ (inj₂ (inj₂ y)) = inj₂ y
  evalBComb unite⋆⇛ x = tt , x
  evalBComb uniti⋆⇛ x = proj₂ x
  evalBComb swap⋆⇛ (x , y) = y , x
  evalBComb assocl⋆⇛ ((x , y) , z) = x , y , z
  evalBComb assocr⋆⇛ (x , y , z) = (x , y) , z
  evalBComb distz⇛ ()
  evalBComb factorz⇛ (() , _)
  evalBComb dist⇛ (inj₁ (proj₁ , proj₂)) = inj₁ proj₁ , proj₂
  evalBComb dist⇛ (inj₂ (proj₁ , proj₂)) = inj₂ proj₁ , proj₂
  evalBComb factor⇛ (inj₁ x , proj₂) = inj₁ (x , proj₂)
  evalBComb factor⇛ (inj₂ y , proj₂) = inj₂ (y , proj₂)
  evalBComb id⇛ x = x
  evalBComb (sym⇛ c) x = evalComb c x
  evalBComb (c ◎ c₁) x = evalBComb c (evalBComb c₁ x)
  evalBComb (c ⊕ c₁) (inj₁ x) = inj₁ (evalBComb c x)
  evalBComb (c ⊕ c₁) (inj₂ y) = inj₂ (evalBComb c₁ y)
  evalBComb (c ⊗ c₁) (proj₁ , proj₂) = evalBComb c proj₁ , evalBComb c₁ proj₂

finToVal : {n : ℕ} → F.Fin n → ⟦ fromℕ n ⟧
finToVal F.zero = inj₁ tt
finToVal (F.suc n) = inj₂ (finToVal n)

valToFin : {n : ℕ} → ⟦ fromℕ n ⟧ → F.Fin n
valToFin {zero} ()
valToFin {suc n} (inj₁ tt) = F.zero
valToFin {suc n} (inj₂ v) = F.suc (valToFin v)

finToValToFin : {n : ℕ} → (v : ⟦ fromℕ n ⟧) → finToVal (valToFin v) ≡ v
finToValToFin {zero} ()
finToValToFin {suc n} (inj₁ tt)  = refl (inj₁ tt)
finToValToFin {suc n} (inj₂ v) = ap inj₂ (finToValToFin v)

valToFinToVal : {n : ℕ} → (i : F.Fin n) → valToFin (finToVal i) ≡ i
valToFinToVal F.zero = refl F.zero
valToFinToVal (F.suc i) = ap F.suc (valToFinToVal i)

combToVec : {n : ℕ} → (fromℕ n) ⇛ (fromℕ n) → Vec (F.Fin n) n
combToVec c = tabulate (valToFin ○ (evalComb c) ○ finToVal)

twoF4 : F.Fin four
twoF4 = F.suc (F.suc F.zero)

fourF5 : F.Fin five
fourF5 = F.suc (F.suc F.zero)

swapUpToTest : Vec (F.Fin five) five
swapUpToTest = combToVec (swapUpTo twoF4)

pltest : (n : ℕ) → (i : F.Fin n) → Vec (F.Fin n) n
pltest n i = permuteLeft i (upTo n)

prtest : Vec (F.Fin five) five
prtest = permuteRight fourF5 -- (F.suc (F.suc (F.suc (F.suc F.zero))))
                        
sdftest : Vec (F.Fin five) five
sdftest = combToVec (swapDownFrom twoF4)

sucomptest : {n : ℕ} → (i : F.Fin n) → Vec (F.Fin (suc (suc n))) (suc (suc n))
sucomptest {n} i = (F.zero ∷ vmap F.suc (permuteLeft (F.inject₁ i) (upTo (suc n))))
                   ∘̬ (F.suc F.zero ∷ F.zero ∷ vmap (F.suc ○ F.suc) (upTo n))

sit : Vec (F.Fin five) five
sit = combToVec (swapi (F.suc (F.suc F.zero)))
                        
mntest : Vec (F.Fin five) five
mntest = combToVec (makeSingleComb (F.suc (F.suc (F.suc F.zero))) F.zero)
                        
evalVec : {n : ℕ} → Vec (F.Fin n) n → F.Fin n → ⟦ fromℕ n ⟧
evalVec vec i = finToVal (lookup i vec)

permLeftTest : F.Fin four
permLeftTest = valToFin (evalVec (permLeftID (F.suc (F.suc F.zero))) (F.zero))

lookupToEvalVec : {n : ℕ} → (i : F.Fin n) → (v : Vec (F.Fin n) n) → lookup i v ≡ valToFin (evalVec v i)
lookupToEvalVec i v = ! (valToFinToVal (lookup i v) )

--  Might want to take a ⟦ fromℕ n ⟧ instead of a Fin n as the second
--  argument here?
combToVecWorks : {n : ℕ} → (c : (fromℕ n) ⇛ (fromℕ n)) → 
  (i : F.Fin n) → (evalComb c (finToVal i)) ≡ evalVec (combToVec c) i
combToVecWorks c i = (! (finToValToFin _)) ∘ (ap finToVal (! (lookupTab i)))

-- Lemma for proving things about calls to foldr; possibly not needed.
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

-- evalComb on foldr becomes a foldl of flipped evalComb
evalComb∘foldr : {n j : ℕ} → (i : ⟦ fromℕ n ⟧ ) → (c-vec : Vec (fromℕ n ⇛ fromℕ n) j) →  evalComb (foldr (λ _ → fromℕ n ⇛ fromℕ n) _◎_ id⇛ c-vec) i ≡ foldl (λ _ → ⟦ fromℕ n ⟧) (λ i c → evalComb c i) i c-vec
evalComb∘foldr {zero} () v
evalComb∘foldr {suc _} i [] = refl i
evalComb∘foldr {suc n} i (c ∷ cv) = evalComb∘foldr {suc n} (evalComb c i) cv

-- foldl on a map: move the function in; specialize to this case. 
foldl∘map : {n m : ℕ} {A C : Set} (f : C → A → C) 
    (j : C) (g : F.Fin m → F.Fin m → A) → (v : Vec (F.Fin m) m) → (z : Vec (F.Fin m) n) → 
  foldl (λ _ → C) f j (map (λ i → g (v !! i) i) z) ≡ 
  foldl (λ _ → C) (λ h i → i h) j (map (λ x₂ → λ w → f w (g (v !! x₂) x₂)) z)
foldl∘map {zero} f j g v [] = refl j
foldl∘map {suc n} {zero} f j g [] (() ∷ z)
foldl∘map {suc n} {suc m} f j g v (x ∷ z) = foldl∘map f (f j (g (lookup x v) x)) g v z

-- Maybe we won't end up needing these to plug in to vecToCombWorks,
-- but I'm afraid we will, which means we'll have to fix them eventually.
-- I'm not sure how to do this right now and I've spent too much time on
-- it already when there are other, more tractable problems that need to
-- be solved. If someone else wants to take a shot, be my guest. [Z]

{-    
foldri : {A : Set} → (B : ℕ → Set) → {m : ℕ} → 
       ({n : ℕ} → F.Fin m → A → B n → B (suc n)) →
       B zero →
       Vec A m → B m
foldri {A} b {m} combine base vec =
  foldr
    b
    (uncurry combine)
    base
    (Data.Vec.zip (upTo _) vec)

postulate foldriWorks : {A : Set} → {m : ℕ} →
              (B : ℕ → Set) → (P : (n : ℕ) → Vec A n → B n → Set) →
              (combine : {n : ℕ} → F.Fin m → A → B n → B (suc n)) →
              (base : B zero) →
              ({n : ℕ} → (i : F.Fin m) → (a : A) → (v : Vec A n) → (b : B n)
                → P n v b
                → P (suc n) (a ∷ v) (combine i a b)) →
              P zero [] base →
              (v : Vec A m) →
              P m v (foldri B combine base v)
-}
-- following definition doesn't work, or at least not obviously
-- need a more straightforward definition of foldri, but none comes to mind
-- help? [Z]
{--               
foldriWorks {A} {m} B P combine base pcombine pbase vec =
  foldrWorks {F.Fin m × A}
    B
    (λ n v b → P n (map proj₂ v) b)
    (uncurry combine)
    base
    ? -- (uncurry pcombine)
    pbase
    (Data.Vec.zip (upTo _) vec)
--}              

-- helper lemmas for vecRepWorks

swapElsewhere : {n : ℕ} → (x : ⟦ fromℕ n ⟧) →
                inj₂ (inj₂ x) ≡ (evalComb (swapi F.zero) (inj₂ (inj₂ x)))
swapElsewhere x = refl _

-- This lemma is the hammer that will let us use vecRep to (hopefully) simply
-- prove some lemmas about the helper functions used in vecToComb, then apply
-- vecRepWorks at the end to make sure they all "do the right thing"
vecRepWorks : {n : ℕ} → {c : (fromℕ n) ⇛ (fromℕ n)} → {v : Vec (F.Fin n) n} → 
  vecRep c v → (i : F.Fin n) → (evalVec v i) ≡ (evalComb c (finToVal i))
vecRepWorks vr-id i = ap finToVal (lookupTab i)
vecRepWorks vr-swap F.zero = refl (inj₂ (inj₁ tt))
vecRepWorks vr-swap (F.suc F.zero) = refl (inj₁ tt)
vecRepWorks {suc (suc n)} vr-swap (F.suc (F.suc i)) = ap finToVal (lookupTab i)
vecRepWorks (vr-comp {n} {c₁} {c₂} {v₁} {v₂} vr vr₁) i = 
  finToVal (lookup i (tabulate (λ j → lookup (lookup j v₁) v₂))) 
 ≡⟨ ap finToVal (lookup∘tabulate i (λ j → lookup (lookup j v₁) v₂)) ⟩ 
  finToVal (lookup (lookup i v₁) v₂) 
 ≡⟨ ap (λ x → finToVal (lookup x v₂)) (lookupToEvalVec i v₁) ⟩ 
  finToVal (lookup (valToFin (evalVec v₁ i)) v₂) 
 ≡⟨ ap (λ x → finToVal (lookup (valToFin x) v₂)) (vecRepWorks vr i) ⟩ 
  finToVal (lookup (valToFin (evalComb c₁ (finToVal i))) v₂)
 ≡⟨ ap finToVal (lookupToEvalVec (valToFin (evalComb c₁ (finToVal i))) v₂) ⟩ 
  finToVal (valToFin (evalVec v₂ (valToFin (evalComb c₁ (finToVal i)))))
 ≡⟨ finToValToFin (evalVec v₂ (valToFin (evalComb c₁ (finToVal i)))) ⟩ 
 evalVec v₂ (valToFin (evalComb c₁ (finToVal i)))
 ≡⟨ vecRepWorks vr₁ (valToFin (evalComb c₁ (finToVal i))) ⟩ 
 evalComb c₂ (finToVal (valToFin (evalComb c₁ (finToVal i))))
 ≡⟨ ap (evalComb c₂) (finToValToFin (evalComb c₁ (finToVal i))) ⟩ 
 evalComb (c₁ ◎ c₂) (finToVal i) ∎
vecRepWorks {suc n} (vr-plus vr) F.zero = refl (inj₁ tt)
vecRepWorks (vr-plus {c = c} {v = v} vr) (F.suc i) = 
  evalVec (F.zero ∷ vmap F.suc v) (F.suc i)  ≡⟨ ap finToVal (map!! F.suc v i) ⟩
  inj₂ (finToVal (v !! i))                  ≡⟨ ap inj₂ (vecRepWorks vr i) ⟩
  (evalComb (id⇛ ⊕ c) (finToVal (F.suc i)) ∎)

lemma3 : {n : ℕ} → 
  (v : Vec (F.Fin n) n) → (i : F.Fin n) → 
  (evalComb (vecToComb v) (finToVal i)) ≡  foldl (λ _ → ⟦ fromℕ n ⟧) 
      (λ h i₁ → i₁ h) (finToVal i)
      (replicate (λ x₂ → evalComb (makeSingleComb (lookup x₂ v) x₂)) ⊛
       tabulate (λ x → x))
lemma3 {n} v i = 
  evalComb (vecToComb v) (finToVal i)
 ≡⟨ evalComb∘foldr (finToVal i) (map (λ i → makeSingleComb (v !! i) i) (upTo n)) ⟩
  foldl (λ _ → ⟦ fromℕ n ⟧) (λ j c → evalComb c j) (finToVal i) (map (λ i → makeSingleComb (v !! i) i) (upTo n)) 
 ≡⟨ foldl∘map (λ j c → evalComb c j) (finToVal i) makeSingleComb v (upTo n) ⟩ 
    refl (
      foldl (λ _ → ⟦ fromℕ n ⟧) (λ h i₁ → i₁ h) (finToVal i)
        (replicate (λ x₂ → evalComb (makeSingleComb (lookup x₂ v) x₂)) ⊛
         tabulate id)  )

-- [JC] flip the conclusion around, as 'evalVec v i' is trivial.  Makes
-- equational reasoning easier  
vecToCombWorks : {n : ℕ} → 
  (v : Vec (F.Fin n) n) → (i : F.Fin n) → 
  (evalComb (vecToComb v) (finToVal i)) ≡ (evalVec v i)
vecToCombWorks {n} v i = 
  evalComb (vecToComb v) (finToVal i)
 ≡⟨ evalComb∘foldr (finToVal i) (map (λ i → makeSingleComb (v !! i) i) (upTo n)) ⟩
  foldl (λ _ → ⟦ fromℕ n ⟧) (λ j c → evalComb c j) (finToVal i) (map (λ i → makeSingleComb (v !! i) i) (upTo n)) 
 ≡⟨ foldl∘map (λ j c → evalComb c j) (finToVal i) makeSingleComb v (upTo n) ⟩ 
  {!!} 

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

------------------------------------------------------------------
-- Goal: 

lemma1 : {n : ℕ} (v : Vec (F.Fin n) n) → (i : F.Fin n) → 
    (evalVec v i) ≡ (evalComb (vecToComb v) (finToVal i))
lemma1 v i = ! (vecToCombWorks v i)

lemma2 : {n : ℕ} (c : (fromℕ n) ⇛ (fromℕ n)) → (i : F.Fin n) → 
    (evalComb c (finToVal i)) ≡ evalVec (combToVec c) i
lemma2 c i = combToVecWorks c i
