-- Implementation of Gödel's System T as an example for
-- Σ-terms (Σ = {Z, S}; α(Z) = 0; α(S) = 1) with primitive recursion
module SystemT where

open import Data.Vec hiding (_++_)
open import Data.Nat
open import Data.List
open import Data.List.All

-- Not in use yet:
-- Σ is a vector of given length n of natural numbers denoting the arity of symbols
data Σ {n : ℕ} : Set where
  intr : Vec ℕ n → Σ
  
-- Successor has arity one, Zero has arity 0
Σ-Nat = intr (1 ∷ 0 ∷ [])

-- Types
data Type : Set where
  Nat  : Type
  Fun  : Type → Type → Type

-- Type environment
Env : Set
Env = List Type

-- Environment lookup
data _∈`_ : Type → Env → Set where
  here  : ∀ {φ A}    → A ∈` (A ∷ φ)
  there : ∀ {φ A A'} → A ∈` φ → A ∈` (A' ∷ φ)

-- Zero & Successor, Variables, prim. recursion on Σ-Nat, Abstraction, Application
data Expr : Env → Type → Set where
  Z      : ∀ {φ}     → Expr φ Nat
  S      : ∀ {φ}     → Expr φ Nat → Expr φ Nat
  Var    : ∀ {φ A}   → A ∈` φ → Expr φ A
  NatRec : ∀ {φ A}   → Expr φ A → Expr (A ∷ φ) A → Expr φ Nat → Expr φ A
  Abs    : ∀ {φ A B} → Expr (A ∷ φ) B → Expr φ (Fun A B)
  App    : ∀ {φ A B} → Expr φ (Fun A B) → Expr φ A → Expr φ B


----- Big step semantics using Agda semantics -----
Value : Type → Set
Value Nat        = ℕ
Value (Fun A B)  = Value A → Value B

-- Lookup in environment of values
access : ∀ {A φ} → A ∈` φ → All Value φ → Value A
access here      (px ∷ p) = px
access (there x) (px ∷ p) = access x p

-- Conversion of a natural number to an expression
natconv : ∀ {φ} → ℕ → Expr φ Nat
natconv zero    = Z
natconv (suc n) = S (natconv n)

natrec : ∀ {A : Set} → A → (A → A) → ℕ → A
natrec vz vs zero    = vz
natrec vz vs (suc n) = vs (natrec vz vs n)

-- Evaluation
eval : ∀ {φ A} → Expr φ A → All Value φ → Value A
eval Z ϱ                   = zero
eval (S x) ϱ               = suc (eval x ϱ)
eval (Var x) ϱ             = access x ϱ
eval (NatRec ez es enat) ϱ = natrec (eval ez ϱ) (λ v → eval es (v ∷ ϱ)) (eval enat ϱ)
eval (Abs e) ϱ             = λ x → eval e (x ∷ ϱ)
eval (App e e₁) ϱ          = (eval e ϱ) (eval e₁ ϱ)

----- Small step semantics -----
----- Substitution: Two methods.
-- a) Define simultaneous substitution with a map from variables to expression; see LDLC.agda and
--    the book "Programming Language Foundations in Agda"
-- b) Define singular substitution but "within" environments, i.e. for terms of the form (φ' ++ A ∷ φ)
--    This makes the Var case a tiny bit more tricky. See also type substitution in LDLC.agda
----- Method b is chosen since it is a bit shorter and (subjectively) easier to understand

-- Lemmas required for substitution, esp. Var case
-- 0) Insertion: Insert a variable and adjust DeBruijn indices
--  0.1) De Bruijn adjustement
insdebr : ∀ {φ φ'} {A B} → B ∈` (φ' ++ φ) → B ∈` (φ' ++ (A ∷ φ))
insdebr {φ' = []} here           = there here
insdebr {φ' = []} (there x)      = there (there x)
insdebr {φ' = y ∷ ys} here      = here
insdebr {φ' = y ∷ ys} (there x) = there (insdebr x)
--  0.2) Insertion
ins : ∀ {φ φ'} {A B} → Expr (φ' ++ φ) B → Expr (φ' ++ A ∷ φ) B
ins Z                                   = Z
ins (S x)                               = S (ins x)
ins (Var x)                             = Var (insdebr x)
ins {φ' = φ'} (NatRec{A = A'} ez es en) = NatRec (ins ez) (ins{φ' = A' ∷ φ'} es) (ins en)
ins {φ' = φ'} (Abs{A = A'} x)           = Abs (ins{φ' = A' ∷ φ'}  x)
ins (App x y)                           = App (ins x) (ins y)
-- 1) Variable substitution
varsub : ∀ {φ φ'} {A B} → A ∈` (φ' ++ B ∷ φ) → Expr φ B → Expr (φ' ++ φ) A
varsub {φ' = []} here M           = M
varsub {φ' = []} (there x) M      = Var x
varsub {φ' = z ∷ zs} here M      = Var here
varsub {φ' = z ∷ zs} (there x) M = ins{φ' = []} (varsub x M)

-- Substitution: Given an expression that binds topmost variable to B and has type A & 
--               an expression of type B => we get an expression of type A by binding the topmost
--               variable to that expression
_[[_]] : ∀ {φ φ'} {A B : Type} → Expr (φ' ++ B ∷ φ) A → Expr φ B → Expr (φ' ++ φ) A
Z [[ M ]]               = Z
S N [[ M ]]             = S (N [[ M ]])
Var x [[ M ]]           = varsub x M
NatRec N N' N'' [[ M ]] = NatRec (N [[ M ]]) (N' [[ M ]]) (N'' [[ M ]])
Abs N [[ M ]]           = Abs (N [[ M ]])
App N N' [[ M ]]        = App (N [[ M ]]) (N' [[ M ]])

-- Values
data Value' {φ} : (t : Type) → Expr φ t → Set where
  VZero : Value' Nat Z
  VSuc  : ∀ {x} →  Value' Nat x → Value' Nat (S x)
  VFun  : ∀ {A B exp} → Value' (Fun A B) (Abs exp)

-- Semantics
data _↠_ {φ} : {A : Type} → Expr φ A → Expr φ A → Set where
  -- Basic call-by-value λ-calc. stuff
  -- Application: Elimination & Reduction
  ξ-App1 : ∀ {A B} {L L' : Expr φ (Fun B A)} {M}
           → L ↠ L'
           → App L M ↠ App L' M

  ξ-App2 : ∀ {A B} {M M' : Expr φ A} {L : Expr φ (Fun A B)}
           → Value' (Fun A B) L
           → M ↠ M'
           → App L M ↠ App L M'

  β-App : ∀ {A B M exp}
          → Value' B M
          → App{B = A} (Abs exp) M ↠ (exp [[ M ]])

  -- Elimination for successor
  ξ-Nat : ∀ {L L'}
          → L ↠ L'
          → S L ↠ S L'
  
  -- Interesting cases
  ξ-NatRec : ∀ {A} {Ez : Expr φ A} {Es En En'}
             → En ↠ En'
             → NatRec Ez Es En ↠ NatRec Ez Es En'

  β-NatRec-Z : ∀ {A} {Ez : Expr φ A} {Es} 
               → NatRec Ez Es Z ↠ Ez

  β-NatRec-S : ∀ {A} {Ez : Expr φ A} {Es} {n}
               → Value' Nat n
               → NatRec Ez Es (S n) ↠ (Es [[ NatRec Ez Es n ]])

----- Reflexive & Transitive closure of ↠; defined for chain reasoning
infix 1 begin_
infix 2 _⇨_
infix 2 _⇨⟨_⟩_
infix 3 _∎

data _⇨_ : ∀ {φ} {A} → Expr φ A → Expr φ A → Set where
  -- Reflexivity / end of Reasoning
  _∎ : ∀ {φ} {A} (L : Expr φ A)
       → (L ⇨ L)

  -- Transitivity / chain Reasoning
  _⇨⟨_⟩_ : ∀ {φ A} {L' M : Expr φ A}
           → (L : Expr φ A)
           → L ↠ L'
           → L' ⇨ M
           → L ⇨ M

-- Highlight the start of a chain of reasoning
begin_ : ∀ {φ} {A} {M N : Expr φ A} → M ⇨ N → M ⇨ N
begin x = x

----- Progress Theorem; also used to generate evaluation sequence (since it defines how to evaluate)
-- Definition: ∀ M : (Value'(M) ∨ (∃ N : M ↠ N))
data Progress {A} (M : Expr [] A) : Set where
  step : ∀ {N : Expr [] A} → M ↠ N → Progress M
  done : Value' A M → Progress M

-- Proof
progress : ∀ {A} → (M : Expr [] A) → Progress M
progress Z                 = done VZero
progress (S L) with progress L
... | step L↠N            = step (ξ-Nat L↠N)
... | done y               = done (VSuc y)
progress (NatRec ez es en) with progress en
... | step en↠en'         = step (ξ-NatRec en↠en')
... | done (VZero)         = step (β-NatRec-Z)
... | done (VSuc x)        = step (β-NatRec-S x)
progress (Abs L)           = done VFun
progress (App L N) with progress L
... | step L↠L'           = step (ξ-App1 L↠L')
... | done VFun with progress N
...   | step N↠N'         = step (ξ-App2 VFun N↠N')
...   | done val           = step (β-App val)

----- Generation of evaluation sequence (idea & implementation from PLFA)
-- Used to limit number of steps taken
data Gas : Set where
  gas : ℕ → Gas

-- Either enough steps taken or Value' reached
data Finished {φ A} (N : Expr φ A) : Set where
  done : Value' A N → Finished N
  out-of-gas : Finished N

-- Encapsulates the steps taken
data Steps : ∀ {A} → Expr [] A → Set where
  steps : ∀ {A} {L N : Expr [] A}
          → L ⇨ N
          → Finished N
          → Steps L

-- Generation of evaluation
eval' : ∀ {A} → Gas → (L : Expr [] A) → Steps L
eval' (gas zero) L                    = steps (L ∎) out-of-gas
eval' (gas (suc m)) L with progress L
... | done VL                         = steps (L ∎) (done VL)
... | step {M} L↠M with eval' (gas m) M
...    | steps M⇨N fin               = steps (L ⇨⟨ L↠M ⟩ M⇨N) fin
  

----- Examples
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

emptyenv : All Value []
emptyenv = []

-- Addition of two numbers defined as primitive recursion
_plus_ : ℕ → ℕ → Expr [] Nat
n plus m  = NatRec (natconv n) (S (Var here)) (natconv m)

-- _ : eval (3 plus 5) emptyenv ≡ 8
-- _ = refl

_ : eval' (gas 5) (1 plus 2) ≡ steps
  (NatRec (S Z) (S (Var here)) (S (S Z)) ⇨⟨ β-NatRec-S (VSuc VZero) ⟩
  (S (NatRec (S Z) (S (Var here)) (S Z)) ⇨⟨ ξ-Nat (β-NatRec-S VZero) ⟩
  (S (S (NatRec (S Z) (S (Var here)) Z)) ⇨⟨ ξ-Nat (ξ-Nat β-NatRec-Z) ⟩ S (S (S Z)) ∎)))
  (done (VSuc (VSuc (VSuc VZero)))) -- 3
_ = refl

-- Multiplication of two numbers defined as primitive recursion using addition
_times_ : ℕ → ℕ → Expr [] Nat
n times m = NatRec Z (NatRec (natconv n) (S (Var here)) (Var here)) (natconv m)

-- _ : eval (50 times 5) emptyenv ≡ 250
-- _ = refl

_ : eval' (gas 10) (2 times 2) ≡ steps
 (NatRec Z (NatRec (S (S Z)) (S (Var here)) (Var here)) (S (S Z)) ⇨⟨ β-NatRec-S (VSuc VZero) ⟩
 (NatRec (S (S Z)) (S (Var here))
  (NatRec Z (NatRec (S (S Z)) (S (Var here)) (Var here)) (S Z))  ⇨⟨ ξ-NatRec (β-NatRec-S VZero) ⟩
  (NatRec (S (S Z)) (S (Var here))
   (NatRec (S (S Z)) (S (Var here))
    (NatRec Z (NatRec (S (S Z)) (S (Var here)) (Var here)) Z)) ⇨⟨ ξ-NatRec (ξ-NatRec β-NatRec-Z) ⟩
   (NatRec (S (S Z)) (S (Var here))
    (NatRec (S (S Z)) (S (Var here)) Z) ⇨⟨ ξ-NatRec β-NatRec-Z ⟩
    (NatRec (S (S Z)) (S (Var here)) (S (S Z)) ⇨⟨ β-NatRec-S (VSuc VZero) ⟩
     (S (NatRec (S (S Z)) (S (Var here)) (S Z)) ⇨⟨ ξ-Nat (β-NatRec-S VZero) ⟩
      (S (S (NatRec (S (S Z)) (S (Var here)) Z)) ⇨⟨ ξ-Nat (ξ-Nat β-NatRec-Z) ⟩ S (S (S (S Z))) ∎)))))))
 (done (VSuc (VSuc (VSuc (VSuc VZero))))) -- 4
_ = refl
