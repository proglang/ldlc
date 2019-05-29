-- Σ-Terms 
module Terms where

open import Data.Vec hiding (_++_)
open import Agda.Builtin.Equality
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.Fin.Base

-- Types
data Type : Set where
  Σ    : ∀ {n} → Vec ℕ n → Type
  Fun  : Type → Type → Type

-- Type environment
Env : Set
Env = List Type

-- Environment lookup
data _∈`_ : Type → Env → Set where
  here  : ∀ {φ A}    → A ∈` (A ∷ φ)
  there : ∀ {φ A A'} → A ∈` φ → A ∈` (A' ∷ φ)

-- Bind a type n times on top of an environment
bind : Env → (A : Type) → ℕ → Env
bind φ A zero    = φ
bind φ A (suc n) = A ∷ (bind φ A n)

-- Zero & Successor, Variables, prim. recursion on Σ-Nat, Abstraction, Application
data Expr : Env → Type → Set where
  -- All symbols σ with arity α(σ) = 0 are terms
  σ-I    : ∀ {φ n vec} → (i : Fin n) → (Data.Vec.lookup vec i) ≡ 0 → Expr φ (Σ vec)
  -- Given terms σ₁, ..., σₘ and a term σ with arity α(σ) = m, we get a new term σ(σ₁, ..., σₘ)
  σ-E    : ∀ {φ n m vec} → (i : Fin n) → (∀ (l : Fin m) → Expr φ (Σ vec)) → (Data.Vec.lookup vec i) ≡ m → Expr φ (Σ vec)
  -- Recursion on Σ-terms: For every term σ ∈ Σ with arity α(σ) = m, we have an expression of type A in an environment that binds m variables of type A 
  --                       Together with an expression of type Σ, by recursion on the correct expression we get an expression of type A
  Σ-Rec  : ∀ {φ n vec A} → (∀ (l : Fin n) → ∀ {m} → (Data.Vec.lookup vec l) ≡ m → Expr (bind φ A m) A) → Expr φ (Σ vec) → Expr φ A
  Var    : ∀ {φ A}   → A ∈` φ → Expr φ A
  Abs    : ∀ {φ A B} → Expr (A ∷ φ) B → Expr φ (Fun A B)
  App    : ∀ {φ A B} → Expr φ (Fun A B) → Expr φ A → Expr φ B


----- Big step semantics using Agda semantics -----
-- Data type for terms
data Σ' {n} : Vec ℕ n →  Set where
  -- Introduction
  σ∈Σ⁰ : ∀ {vec} → (i : Fin n) → (Data.Vec.lookup vec i) ≡ 0 → (Σ' vec)
  -- Composition
  σ∈Σᵐ : ∀ {vec m} → (i : Fin n) → (∀ (l : Fin m) → (Σ' vec)) → (Data.Vec.lookup vec i) ≡ m → (Σ' vec)

-- From data type to expression
conversion : ∀ {φ n} {vec : Vec ℕ n} → Σ' vec → Expr φ (Σ vec)
conversion (σ∈Σ⁰ i x)    = σ-I i x
conversion (σ∈Σᵐ i x x₁) = σ-E i (λ l → conversion (x l)) x₁

-- Value definition
Value : Type → Set
Value (Σ vec)    = Σ' vec
Value (Fun A B)  = Value A → Value B

-- Lookup in environment of values
access : ∀ {A φ} → A ∈` φ → All Value φ → Value A
access here      (px ∷ p) = px
access (there x) (px ∷ p) = access x p

-- Given a map from Fin (suc m) to anything; we can derive a map from Fin m to anything
-- (make the Urbild smaller)
urbild : ∀ {m} {A : Set} → (Fin (suc m) → A) → (Fin m → A)
urbild l = λ x → l (raise 1 x)

{-# TERMINATING #-}
eval : ∀ {φ A} → Expr φ A → All Value φ → Value A
rec  : ∀ {φ A n m} {vec : Vec ℕ n} → (∀ (l : Fin n) → ∀ {m} → (Data.Vec.lookup vec l) ≡ m → Expr (bind φ A m) A) → All Value φ → (∀ (l : Fin m) → (Σ' vec)) → All Value (bind φ A m)
rec {m = zero} σ-exprs ϱ terms  = ϱ
rec {m = suc m} σ-exprs ϱ terms = eval (Σ-Rec σ-exprs (conversion (terms (fromℕ m)))) ϱ ∷ (rec{m = m} σ-exprs ϱ (urbild terms))

-- Evaluation 
eval (σ-I i x) ϱ             = σ∈Σ⁰ i x
eval (σ-E i terms Σ[i]≡m) ϱ  = σ∈Σᵐ i (λ l → eval (terms l) ϱ) Σ[i]≡m
eval (Σ-Rec σ-exprs eₛ) ϱ with (eval eₛ ϱ)
... | σ∈Σ⁰ i x    = eval (σ-exprs i x) ϱ
... | σ∈Σᵐ i x x₁ = eval (σ-exprs i x₁) (rec σ-exprs ϱ x)
eval (Var x) ϱ               = access x ϱ
eval (Abs e) ϱ               = λ x → eval e (x ∷ ϱ)
eval (App e e₁) ϱ            = (eval e ϱ) (eval e₁ ϱ)
-----

-- Example: ℕ; Σ = {Z⁰, S¹} (where ⁿ defines arity)
Σ-Nat : Type
Σ-Nat = Σ (0 ∷ 1 ∷ [])

--- Natural number to expression
ℕtoE : ℕ → Expr [] Σ-Nat
-- 0     ~ Z
ℕtoE zero    = σ-I zero refl
-- suc n ~ S (ℕtoE n)
ℕtoE (suc n) = σ-E{m = 1} (suc zero) (λ l → ℕtoE n) refl


--- Cases
plus-exprs : ℕ → (∀ (l : Fin 2) → ∀ {m} → (Data.Vec.lookup (0 ∷ 1 ∷ []) l) ≡ m → Expr (bind [] (Σ-Nat) m) Σ-Nat)
-- base case for n + zero = n
plus-exprs n zero       {zero}        0≡0  = ℕtoE n
-- suc case, n + (suc m) = suc (n + m); (n + m) recursively calculated and put ontop of the environemnt, hence Var here
plus-exprs n (suc zero) {suc zero}    1≡1  = σ-E{m = 1} (suc zero) (λ l → Var here) refl

_plus_ : ℕ → ℕ → Expr [] (Σ-Nat)
n plus m = Σ-Rec (plus-exprs n) (ℕtoE m)

-- Example with explanation
_ : eval (3 plus 2) [] ≡ (σ∈Σᵐ (suc zero)           -- suc zero stands for Σ[1] ~ S                                                S
                         (λ l → σ∈Σᵐ (suc zero)    -- λ comes from ℕtoE, necessary for telling σ-E the expression e in (S e)     S
                         (λ l₁ → σ∈Σᵐ (suc zero)   --                                                                             S
                         (λ l₂ → σ∈Σᵐ (suc zero)   --                                                                             S
                         (λ l₃ → σ∈Σᵐ (suc zero)   --                                                                             S
                         (λ l₄ → σ∈Σ⁰ zero refl) refl) refl) refl) refl) refl) -- refls are the proofs required                   Z
                                                                                -- for arity, e.g. Z ~ Σ[0] ≡ 0                    S (S (S (S (S Z)))) ~ 5
_ = refl





