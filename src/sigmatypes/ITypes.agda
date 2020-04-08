-- Inductive types
-- See Chapter 15 of "Practical Foundations for Programming Languages" by Robert Harper

module ITypes where

open import Data.Vec
open import Data.Nat
open import Data.List
open import Data.Fin.Base

-- auxiliary
data Bool : Set where
  True False : Bool

_if_else_ : {A : Set} → A → Bool → A → A
A if True  else B = A
A if False else B = B
-- end of auxiliary

{-- required later on
data IType' (n : ℕ) : Set
data IType' n where
   Unit Nat : IType' n
   Pair Sum : IType n → IType n → IType' n

Map'[_,_]_ : ∀ {n} → Fin n → IType' n → IType n → IType' n
Map'[ var , Unit ] type'           = Unit
Map'[ var , Nat ] type'            = Nat
Map'[ var , Pair x x₁ ] type'      = Pair (Map[ var , x ] type') (Map[ var , x₁ ] type')
Map'[ var , Sum x x₁ ] type'       = Sum (Map[ var , x ] type') (Map[ var , x₁ ] type')
--}

data IType (n : ℕ) : Set

data IType n where
  Unit Nat : IType n
  Pair Sum : IType n → IType n → IType n
  Ind : IType (suc n)  → IType n
  Var : Fin n → IType n
  Func : IType n → IType n → IType n

FinEq : ∀ {n} → Fin n → Fin n → Bool
FinEq zero zero         = True
FinEq zero (suc b)      = False
FinEq (suc a) zero      = False
FinEq (suc a) (suc b) = FinEq a b

-- Substitute type' for var in type
Map[_,_]_ : ∀ {n} → Fin (suc n) → IType (suc n) → IType n → IType n
Map[ var , Unit ] type'            = Unit
Map[ var , Nat ] type'             = Nat
Map[ var , Pair type type₁ ] type' = Pair (Map[ var , type ] type') (Map[ var , type₁ ] type')
Map[ var , Sum type type₁ ] type'  = Pair (Map[ var , type ] type') (Map[ var , type₁ ] type')
Map[ var , Ind x ] type'           = {!!} --Ind (Map[ var , x ] type')
Map[ var , Func a b ] type'        = Func (Map[ var , a ] type') (Map[ var , b ] type')
Map[ var , Var x ] type'           = type' if (FinEq var x) else Var {!!}

-- Alternative notation
[_/_]_ : ∀ {n} → IType n → Fin (suc n) → IType (suc n) → IType n
[ type' / var ] type = Map[ var , type ] type'

Env : ℕ → Set
Env n = List (IType n)

-- Environment lookup
data _∈`_ {n} : IType n → Env n → Set where
  here  : ∀ {φ A}    → A ∈` (A ∷ φ)
  there : ∀ {φ A A'} → A ∈` φ → A ∈` (A' ∷ φ)

-- Expressions
data Expr {n} : Env n → IType n → Set where
--  Fold       : ∀ {ϕ t τ} → Expr ϕ ([ Ind τ / t ] τ) → Expr ϕ (Ind τ)
--  Rec        : ∀ {ϕ t τ ρ} → Expr ((Map[ t , τ ] ρ) ∷ ϕ) ρ → Expr ϕ (Ind τ) → {!!}
  FoldNat    : ∀ {ϕ}     → Expr ϕ (Sum Unit Nat) → Expr ϕ Nat
  RecNat     : ∀ {ϕ}   → Expr (Sum Unit Nat ∷ ϕ) Nat → Expr ϕ Nat → Expr ϕ Nat
  Var        : ∀ {φ τ}   → τ ∈` φ → Expr φ τ
  Abs        : ∀ {φ τ τ'} → Expr (τ ∷ φ) τ' → Expr φ (Func τ τ')
  App        : ∀ {φ τ τ'} → Expr φ (Func τ τ') → Expr φ τ → Expr φ τ'

-- Expression substitution
[_//_] : ∀ {n ϕ} {τ τ' : IType n} → Expr (τ' ∷ ϕ) τ → Expr ϕ τ' → Expr ϕ τ
-- TODO

data _↦_ {n ϕ} : {τ : IType n} → Expr ϕ τ → Expr ϕ τ → Set where

  ξ-RecNat : ∀ {e} {e' e''}
             → e' ↦ e''
             → _↦_ {τ = Nat} (RecNat e e') (RecNat e e'')

  β-RecNat : ∀ {e e'}
             → _↦_ {τ = Nat} (RecNat e (FoldNat e')) [ e // e' ]
  

-- IValue
-- data IValue (n : ℕ) : Set where

-- Interpreter
-- int : ∀ {n} → IType n → Set
-- int' : ∀ {n} → IType' n → Set
--- int {n} (Ind it') = IValue n (int' it')
