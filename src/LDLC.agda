module LDLC where

open import Data.List
open import Data.List.All
open import Data.Unit
open import Data.Nat
open import Data.Fin.Subset

-- the index nl stands for the number of labels
data LTy (nl : ℕ) : Set where
  Tunit : LTy nl
  Tlabel : Subset nl → LTy nl
  Tfun : LTy nl → LTy nl → LTy nl
  
LTEnv : ℕ → Set
LTEnv nl = List (LTy nl)

data LExpr (nl : ℕ) : LTEnv nl → LTy nl → Set where
  -- to be continued
