module Alg where

open import Data.Bool
open import Data.Fin hiding (_+_ ; fold)
open import Data.List hiding (lookup ; [_] ; map)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Vec hiding (_++_)

open import Size

RankedAlphabet : ℕ → Set
RankedAlphabet = Vec ℕ

-- natural numbers = { zero_0, suc_1 }
rNat : RankedAlphabet 2
rNat = zero ∷ suc zero ∷ []

-- words over {t,f} = { eps_0, false_1, true_1 } 
rBin : RankedAlphabet 3
rBin = zero ∷ suc zero ∷ suc zero ∷ []

-- binary trees = { leaf_0, branch_2 }
rBtr : RankedAlphabet 2
rBtr = zero ∷ suc (suc zero) ∷ []

module FailedAttempt where
  -- terms
  data Term {n} (ra : RankedAlphabet n) : Set where
    mk : (sym : Fin n) → (Fin (lookup sym ra) → Term ra) → Term ra

  tNat0 : Term rNat
  tNat0 = mk zero (λ ())

  tNat1 : Term rNat
  tNat1 = mk (suc zero) λ zero → tNat0

  tNat2 : Term rNat
  tNat2 = mk (suc zero) λ zero → tNat1

  -- interpretations
  nary : Set → ℕ → Set
  nary A zero = A
  nary A (suc n) = A → nary A n
  
  Algebra : ∀ {n} → RankedAlphabet n → Set → Set
  Algebra {n} ra A = (sym : Fin n) → nary A (lookup sym ra)
  
  -- I don't see how to implement this as a function
  postulate 
    eval : ∀ {n} {ra : RankedAlphabet n} {A} → Term ra → Algebra ra A → A
-- end FailedAttempt

-- interpretations

nary : Set → ℕ → Set
nary A n = Vec A n → A

Algebra : ∀ {n} → RankedAlphabet n → Set → Set
Algebra {n} ra A = (sym : Fin n) → nary A (lookup sym ra)

-- natural numbers
aNat : Algebra rNat ℕ
aNat zero = λ [] → 0
aNat (suc zero) = λ{ (x ∷ []) → suc x }
aNat (suc (suc ()))

-- bitstrings
aBin : Algebra rBin (List Bool)
aBin zero = λ _ → []
aBin (suc zero) = λ x → false ∷ lookup zero x
aBin (suc (suc zero)) = λ x → true ∷ lookup zero x
aBin (suc (suc (suc ())))

-- compute value of bitstring
aBinVal : Algebra rBin ℕ
aBinVal zero = λ [] → 0
aBinVal (suc zero) = λ{ (x ∷ []) → x + x }
aBinVal (suc (suc zero)) = λ{ (x ∷ []) →  suc (x + x) }
aBinVal (suc (suc (suc ())))

-- the initial btree algebra
data BTree : Set where
  Leaf : BTree
  Branch : BTree → BTree → BTree

aBtrInitial : Algebra rBtr BTree
aBtrInitial zero = λ [] → Leaf
aBtrInitial (suc zero) = λ{ (l ∷ r ∷ []) → Branch l r }
aBtrInitial (suc (suc ()))

-- count leaves
aBtrCount : Algebra rBtr ℕ
aBtrCount zero = λ [] → 1
aBtrCount (suc zero) = λ{ (l ∷ r ∷ []) → l + r }
aBtrCount (suc (suc ()))

-- height
aBtrHeight : Algebra rBtr ℕ
aBtrHeight zero = λ [] → 0
aBtrHeight (suc zero) = λ{ (l ∷ r ∷ []) → suc (l ⊔ r) }
aBtrHeight (suc (suc ()))

-- terms (using sized types)
data Term {n} (ra : RankedAlphabet n) : {i : Size} → Set where
  mk : ∀ {i} → (sym : Fin n) → Vec (Term ra {i}) (lookup sym ra) → Term ra {↑ i}

eval : ∀ {n} {ra : RankedAlphabet n} {A} {i} → Algebra ra A → Term ra {i} → A
eval alg (mk sym subterms) = alg sym (map (eval alg) subterms)

tNat0 : Term rNat
tNat0 = mk zero []

tNat1 : Term rNat
tNat1 = mk (suc zero) [ tNat0 ]

tNat2 : Term rNat
tNat2 = mk (suc zero) [ tNat1 ]

aNatTerm : Algebra rNat (Term rNat)
aNatTerm = mk

----------------------------------------------------------------------
-- many-sorted algebra

open import Data.Unit
open import Data.Nat.GeneralisedArithmetic

Sorts = Fin

Signature : ℕ → ℕ → Set
Signature s = Vec (List (Sorts s) × Sorts s)

sNat : Signature 1 2
sNat = ([] , zero) ∷ (( zero ∷ []) , zero) ∷ []

sMon : Signature 2 6
sMon = ([] , zero) ∷ (zero ∷ [] , zero) ∷
       ([] , suc zero) ∷ (suc zero ∷ [] , suc zero) ∷ (suc zero ∷ [] , suc zero) ∷ 
       (zero ∷ suc zero ∷ [] , suc zero) ∷ []
-- this is:   0. S. eps. 0(). 1(). n*s.

sary : ∀ {s} → (Sorts s → Set) → List (Sorts s) → Set
sary int [] = ⊤
sary int (sort ∷ sort*) = int sort × sary int sort*

data STerm {s} {n} (sig : Signature s n) : Sorts s → Set where
  mk : (sym : Fin n) →
    let (sort* , sort) = lookup sym sig in
    sary (STerm sig) sort* →
    STerm sig sort

sNat0 : STerm sNat zero
sNat0 = mk zero tt

sNat1 : STerm sNat zero
sNat1 = mk (suc zero) (sNat0 , tt)

SAlgebra : ∀ {s n} → Signature s n → (Sorts s → Set) → Set
SAlgebra sig int = (sym : Fin _) →
    let (sort* , sort) = lookup sym sig in
    sary int sort* → int sort

asNat : SAlgebra sNat λ zero → ℕ
asNat zero = λ{ tt → 0 }
asNat (suc zero) = λ{ (x , tt) → suc x }
asNat (suc (suc ()))

asNatTerm : SAlgebra sNat (STerm sNat)
asNatTerm = mk
{- written out:
asNatTerm zero = mk zero
asNatTerm (suc zero) = mk (suc zero) 
asNatTerm (suc (suc ()))
-}

asMon : SAlgebra sMon λ{ zero → ℕ ; (suc zero) → List Bool ; (suc (suc ())) }
asMon zero tt = 0
asMon (suc zero) (n , _) = suc n
asMon (suc (suc zero)) tt = []
asMon (suc (suc (suc zero))) (w , _) = true ∷ w
asMon (suc (suc (suc (suc zero)))) (w , _) = false ∷ w
asMon (suc (suc (suc (suc (suc zero))))) (n , w , _) = fold [] (_++_ w) n
asMon (suc (suc (suc (suc (suc (suc ())))))) x
