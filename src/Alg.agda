module Alg where

open import Data.Bool
open import Data.Fin
open import Data.List hiding (lookup ; [_] ; map)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Vec

RankedAlphabet : ℕ → Set
RankedAlphabet = Vec ℕ

-- terms
data Term {n} (ra : RankedAlphabet n) : Set where
  mk : (sym : Fin n) → (Fin (lookup sym ra) → Term ra) → Term ra

data Term' {n} (ra : RankedAlphabet n) : Set where
  mk : (sym : Fin n) → Vec (Term' ra) (lookup sym ra) → Term' ra



-- interpretations
nary : Set → ℕ → Set
nary A zero = A
nary A (suc n) = A → nary A n

Algebra : ∀ {n} → RankedAlphabet n → Set → Set
Algebra {n} ra A = (sym : Fin n) → nary A (lookup sym ra)

-- I don't see how to finish this
eval : ∀ {n} {ra : RankedAlphabet n} {A} → Term ra → Algebra ra A → A
eval (mk sym x) alg = alg {!!}

nary' : Set → ℕ → Set
nary' A n = Vec A n → A

Algebra' : ∀ {n} → RankedAlphabet n → Set → Set
Algebra' {n} ra A = (sym : Fin n) → nary' A (lookup sym ra)

eval' : ∀ {n} {ra : RankedAlphabet n} {A} → Algebra' ra A → Term' ra → A
eval' alg (mk sym subterms) =
  alg sym (f subterms)
  where
  f : ∀ {m} → Vec (Term' _) m → Vec _ m
  f [] = []
  f (t ∷ ts) = (eval' alg t) ∷ f ts
  -- should be able to write
  --   let values = map (eval' alg) subterms in alg sym values
  -- but the termination checker won't let me 
  -- possibly fixable using "sized types"

-- natural numbers = { zero_0, suc_1 }
rNat : RankedAlphabet 2
rNat = zero ∷ suc zero ∷ []

aNat : Algebra rNat ℕ
aNat zero = 0
aNat (suc zero) = suc
aNat (suc (suc ()))

tNat0 : Term rNat
tNat0 = mk zero (λ ())

tNat1 : Term rNat
tNat1 = mk (suc zero) λ zero → tNat0

tNat2 : Term rNat
tNat2 = mk (suc zero) λ zero → tNat1

tNat0' : Term' rNat
tNat0' = mk zero []

tNat1' : Term' rNat
tNat1' = mk (suc zero) [ tNat0' ]

tNat2' : Term' rNat
tNat2' = mk (suc zero) [ tNat1' ]

-- words over {t,f} = { eps_0, false_1, true_1 } 
rBin : RankedAlphabet 3
rBin = zero ∷ suc zero ∷ suc zero ∷ []

aBin : Algebra rBin (List Bool)
aBin zero = []
aBin (suc zero) = _∷_ false
aBin (suc (suc zero)) = _∷_ true
aBin (suc (suc (suc ())))


