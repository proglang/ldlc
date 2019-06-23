module Alg where

open import Data.Bool
open import Data.Fin hiding (_+_)
open import Data.List hiding (lookup ; [_] ; map)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Vec

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

-- terms
data Term {n} (ra : RankedAlphabet n) : Set where
  mk : (sym : Fin n) → Vec (Term ra) (lookup sym ra) → Term ra

-- interpretations

nary : Set → ℕ → Set
nary A n = Vec A n → A

Algebra : ∀ {n} → RankedAlphabet n → Set → Set
Algebra {n} ra A = (sym : Fin n) → nary A (lookup sym ra)

eval : ∀ {n} {ra : RankedAlphabet n} {A} → Algebra ra A → Term ra → A
eval alg (mk sym subterms) =
  alg sym (f subterms)
  where
  f : ∀ {m} → Vec (Term _) m → Vec _ m
  f [] = []
  f (t ∷ ts) = (eval alg t) ∷ f ts
  -- should be able to write
  --   let values = map (eval alg) subterms in alg sym values
  -- but the termination checker won't let me 
  -- possibly fixable using "sized types"

-- natural numbers
aNat : Algebra rNat ℕ
aNat zero = λ [] → 0
aNat (suc zero) = λ{ (x ∷ []) → suc x }
aNat (suc (suc ()))

tNat0 : Term rNat
tNat0 = mk zero []

tNat1 : Term rNat
tNat1 = mk (suc zero) [ tNat0 ]

tNat2 : Term rNat
tNat2 = mk (suc zero) [ tNat1 ]

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
