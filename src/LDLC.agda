module LDLC where

open import Data.List
open import Data.List.All
open import Data.Unit
open import Data.Nat
open import Data.Fin.Subset

-- Mutual definition
data LTy (nl : ℕ) : Set
record Π {nl : ℕ} : Set

-- the index nl stands for the number of labels
data LTy nl where
  Tunit : LTy nl
  Tlabel : Subset nl → LTy nl
  Tfun : LTy nl → LTy nl → LTy nl
  Tpi  : Π {nl} → LTy nl

record Π {nl} where
  inductive
  constructor Π[_]_
  field
    snl : Subset nl
    B   : ∀ {l} → l ∈ snl → LTy nl
    
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
                         → ∀ l
                         → l ∈ snl
                         → LExpr (Tlabel (⁅ l ⁆) ∷ φ) B 
                         → LExpr φ B
  Pi-I     : ∀ {K B A φ ΠB l} → LExpr φ K
                              → LExpr (A ∷ φ) B
                              → (x : (l ∈ Π.snl ΠB))
                              → LExpr φ (Tpi ΠB)
  Pi-E     : ∀ {ΠB φ l} → LExpr φ (Tpi ΠB)
                        → LExpr φ (Tlabel ⁅ l ⁆)
                        → (t : (l ∈ Π.snl ΠB))
                        → LExpr φ ((Π.B ΠB) t)
  -- to be continued
