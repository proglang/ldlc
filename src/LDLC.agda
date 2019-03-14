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

data _∈`_ {nl : ℕ} : LTy nl → LTEnv nl → Set where
  here  : ∀ {lt φ} → lt ∈` (lt ∷ φ)
  there : ∀ {lt lt' φ} → lt ∈` φ → lt ∈` (lt' ∷ φ)

data LExpr {nl : ℕ} : LTEnv nl → LTy nl → Set where
  Var      : ∀ {φ t} → (x : t ∈` φ) → LExpr φ t
  SubType  : ∀ {snl snl' φ} →  LExpr φ (Tlabel snl) → snl ⊆ snl'
                            →  LExpr φ (Tlabel snl')
  Lab-I    : ∀ {l snl φ} → l ∈ snl → LExpr φ (Tlabel ⁅ l ⁆)
  Lab-E    : ∀ {snl φ B} → LExpr φ (Tlabel snl)
                         → ∀ l → l ∈ snl
                         → (Nₗ : B ∈` (Tlabel (⁅ l ⁆) ∷ φ))
                         → LExpr φ B             
  -- to be continued
