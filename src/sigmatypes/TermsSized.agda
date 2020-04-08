-- Terms using Agdas Sized Types --
module TermsSized where

open import Data.Vec hiding (_++_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.Fin.Base

open import Size

-- Ranked alphabet: Vector of natural numbers, where vec[i] denotes the arity of symbol i
RankedAlphabet : ℕ → Set
RankedAlphabet n = Vec ℕ n

-- Types
data Type : Set where
  TTerm : ∀ {n} → RankedAlphabet n → Type
  TFun  : Type → Type → Type

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

-- Zero & Successor, Variables, prim. recursion, Abstraction, Application
data Expr : {j : Size} → Env → Type → Set where
  ETerm      : ∀ {j : Size} {φ n} {vec : RankedAlphabet n} {sym : Fin n} → Vec (Expr {j} φ (TTerm vec)) (Data.Vec.lookup vec sym) → Expr {↑ j} φ (TTerm vec)
  ETerm-Rec  : ∀ {j : Size} {φ n} {vec : RankedAlphabet n} {A} → (∀ {sym : Fin n} → Expr {j} (bind φ A (Data.Vec.lookup vec sym)) A) → Expr {j} φ (TTerm vec) → Expr {↑ j} φ A
  Var        : ∀ {φ A}   → A ∈` φ → Expr {∞} φ A
  Abs        : ∀ {φ A B} → Expr (A ∷ φ) B → Expr φ (TFun A B)
  App        : ∀ {φ A B} → Expr φ (TFun A B) → Expr φ A → Expr φ B

-- Terms
data Term {n} (ra : RankedAlphabet n) : {i : Size} → Set where
  mk : ∀ {i} → (sym : Fin n) → Vec (Term ra {i}) (Data.Vec.lookup ra sym) → Term ra {↑ i}

-- Values
Value : Type → Set
Value (TTerm ra) = Term ra
Value (TFun A B) = Value A → Value B

-- Lookup in environment of all Values
access : ∀ {A φ} → A ∈` φ → All Value φ → Value A
access here      (px ∷ p) = px
access (there x) (px ∷ p) = access x p

extend : ∀ {ϕ A} →
  (m : ℕ) →
  (ϱ₁    : Vec (Value A) m) →
  (ϱ     : All Value ϕ) →
  All Value (bind ϕ A m)
extend 0F [] ϱ = ϱ
extend (suc m) (x ∷ ϱ₁) ϱ = x ∷ extend m ϱ₁ ϱ

trec : ∀ {j : Size} {a} {n} {VA : Set a} (ra : RankedAlphabet n) → ((sym : Fin n) → Vec VA (Data.Vec.lookup ra sym) → VA) → Term ra {j} → VA
trec ra g (mk sym₁ subterms) = g sym₁ (Data.Vec.map (trec ra g) subterms)

-- Evaluation
eval : ∀ {j : Size} {ϕ A} → Expr{j} ϕ A → All Value ϕ → Value A
eval (ETerm{sym = sym} x) ϱ   = mk sym (Data.Vec.map (λ exp → eval exp ϱ) x)
eval {j} {ϕ} {A} (ETerm-Rec{n = n}{vec = ra} exprs body) ϱ with eval body ϱ
...          | term = trec {VA = Value A} ra (λ sym₁ ϱ₁ → eval {A = A} (exprs {sym₁}) (extend (Data.Vec.lookup ra sym₁) ϱ₁ ϱ)) term
eval (Var x) ϱ            = access x ϱ
eval (Abs expr) ϱ         = λ x → eval expr (x ∷ ϱ)
eval (App expr expr₁) ϱ   = (eval expr ϱ) (eval expr₁ ϱ)

-- Example: Very tiny subset of propositional logic
-- Σ = {¬, ⊤, ⊥}, α(¬) = 1, α(⊤) = 0, α(⊥) = 0
Σ : Vec ℕ 3
Σ = (1 ∷ 0 ∷ 0 ∷ [])

PropLog : Type
PropLog = TTerm Σ

1≤3 : 1 Data.Nat.< 3
1≤3 = s≤s (s≤s z≤n)

2≤3 : 2 Data.Nat.< 3
2≤3 = s≤s (s≤s (s≤s z≤n))

⊤ : Expr [] PropLog
⊤ = ETerm{n = 3} {sym = fromℕ< {1} {3} 1≤3} []

⊥ : Expr [] PropLog
⊥ = ETerm{n = 3} {sym = fromℕ< {2} {3} 2≤3} []

NegFunc : ∀ {sym : Fin 3} → Expr (bind [] PropLog (Data.Vec.lookup Σ sym)) PropLog
NegFunc {zero}       = Var here
NegFunc {suc zero}       = ⊥
NegFunc {suc (suc zero)} = ⊤

¬⊥ : Expr [] PropLog
¬⊥ = ETerm-Rec{vec = Σ} (λ {sym} → NegFunc {sym}) (ETerm{n = 3} {sym = fromℕ< {0} {3} (s≤s z≤n)} (⊥ ∷ []) )

_ : (eval ¬⊥ []) ≡ (eval ⊤ [])
_ = refl





