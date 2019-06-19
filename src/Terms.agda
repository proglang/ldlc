-- Σ-Terms 
module Terms where

open import Data.Vec hiding (_++_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.Fin.Base

-- Types
data Type : Set where
  -- Term not just ranked alphabet, but index included
  TTerm : ∀ {n} {i : Fin n} → Vec ℕ n → Type
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

-- Zero & Successor, Variables, prim. recursion on Σ-Nat, Abstraction, Application
data Expr : Env → Type → Set where
  -- All symbols σ with arity α(σ) = 0 are terms; special case of Term with m = 0
  -- Given terms σ₁, ..., σₘ and a term σ with arity α(σ) = m, we get a new term σ(σ₁, ..., σₘ)
  Term    : ∀ {φ n vec} {i : Fin n} {m} {eq : Data.Vec.lookup vec i ≡ m} → (∀ (l : Fin m) → Expr φ (TTerm{i = i} vec)) → Expr φ (TTerm{i = i} vec)
  -- Recursion on Terms: For every term σ ∈ Σ with arity α(σ) = m, we have an expression of type A in an environment that binds m variables of type A 
  --                     Together with an expression of type Σ, by recursion on the correct expression we get an expression of type A
  Term-Rec  : ∀ {φ n vec A} {i : Fin n} → (∀ {l : Fin n} {m} {eq : (Data.Vec.lookup vec l) ≡ m} → Expr (bind φ A m) A) → Expr φ (TTerm{i = i} vec) → Expr φ A
  Var    : ∀ {φ A}   → A ∈` φ → Expr φ A
  Abs    : ∀ {φ A B} → Expr (A ∷ φ) B → Expr φ (TFun A B)
  App    : ∀ {φ A B} → Expr φ (TFun A B) → Expr φ A → Expr φ B


----- Big step semantics using Agda semantics -----
-- Data type for terms
data TTerm' {n} : Vec ℕ n →  Set where
  Term' : ∀ {vec m} {i : Fin n} {eq : (Data.Vec.lookup vec i) ≡ m} → (∀ (l : Fin m) → (TTerm' vec)) → (TTerm' vec)

-- From data type to expression
conversion : ∀ {φ n} {vec : Vec ℕ n} → TTerm' vec → Expr φ (TTerm vec)
conversion (Term'{m = zero}{eq = eq} x)   = Term{eq = eq} λ ()
conversion (Term'{m = suc n}{eq = eq} x)  = Term{eq = eq} (λ l → conversion (x l))

-- Value definition
Value : Type → Set
Value (TTerm vec) = TTerm' vec
Value (TFun A B)  = Value A → Value B

-- Lookup in environment of values
access : ∀ {A φ} → A ∈` φ → All Value φ → Value A
access here      (px ∷ p) = px
access (there x) (px ∷ p) = access x p

-- Given a map from Fin (suc m) to anything; we can derive a map from Fin m to anything
-- (make the Urbild smaller)
urbild : ∀ {m} {A : Set} → (Fin (suc m) → A) → (Fin m → A)
urbild l = λ x → l (raise 1 x)

term-rec : ∀ {A : Set} {n : ℕ} {vec : Vec ℕ n} → (∀ {l : Fin n} {m : ℕ} {eq : Data.Vec.lookup vec l ≡ m} → Vec A m → A) → TTerm' vec → A
term-rec v (Term'{m = zero}   x)  = {!!}
term-rec v (Term'{m = suc m}  x)  = {!!}

-- Evaluation 
eval : ∀ {φ A} → Expr φ A → All Value φ → Value A
--
eval (Term{m = zero}{eq = eq} x) ϱ    = Term'{eq = eq} λ ()
eval (Term{m = suc n}{eq = eq} x) ϱ   = Term'{eq = eq} (λ l → eval (x l) ϱ)
eval (Term-Rec σ-exprs eₛ) ϱ          = {!!}
eval (Var x) ϱ                        = access x ϱ
eval (Abs e) ϱ                        = λ x → eval e (x ∷ ϱ)
eval (App e e₁) ϱ                     = (eval e ϱ) (eval e₁ ϱ)
-----


{--
-- eval (Σ-Rec σ-exprs eₛ)  with (eval eₛ ϱ)
-- ... | σ∈Σ⁰ i x    = eval (σ-exprs i x) ϱ
-- ... | σ∈Σᵐ i x x₁ = eval (σ-exprs i x₁) (rec σ-exprs ϱ x)
-- rec  : ∀ {φ A n m} {vec : Vec ℕ n} → (∀ (l : Fin n) → ∀ {m} → (Data.Vec.lookup vec l) ≡ m → Expr (bind φ A m) A) → All Value φ → (∀ (l : Fin m) → (Σ' vec)) → All Value (bind φ A m)
-- rec {m = zero} σ-exprs ϱ terms  = ϱ
-- rec {m = suc m} σ-exprs ϱ terms = eval (Σ-Rec σ-exprs (conversion (terms (fromℕ m)))) ϱ ∷ (rec{m = m} σ-exprs ϱ (urbild terms))


-- Example: ℕ; Σ = {Z⁰, S¹} (where ⁿ defines arity)
Nat : Type
Nat = TTerm (0 ∷ 1 ∷ [])

--- Natural number to expression
ℕtoE : ℕ → Expr [] Nat

--- Cases
plus-exprs : ℕ → (∀ (l : Fin 2) → ∀ {m} → (Data.Vec.lookup (0 ∷ 1 ∷ []) l) ≡ m → Expr (bind [] (Nat) m) Nat)
-- base case for n + zero = n
plus-exprs n zero       {zero}        0≡0  = ℕtoE n
-- suc case, n + (suc m) = suc (n + m); (n + m) recursively calculated and put ontop of the environemnt, hence Var here
-- plus-exprs n (suc zero) {suc zero}    1≡1  = Term{m = 1} (suc zero) (λ l → Var here) refl

_plus_ : ℕ → ℕ → Expr [] (Nat)
n plus m = Term-Rec (plus-exprs n) (ℕtoE m)

-- Example with explanation
--
--}
----- Small step semantics -----
----- Substitution: See SystemT.agda for a more detailed description
insdebr : ∀ {φ φ'} {A B} → B ∈` (φ' ++ φ) → B ∈` (φ' ++ (A ∷ φ))
insdebr {φ' = []} here           = there here
insdebr {φ' = []} (there x)      = there (there x)
insdebr {φ' = y ∷ ys} here      = here
insdebr {φ' = y ∷ ys} (there x) = there (insdebr x)

-- Extract the ℕ m from proof that vector contains it at index l
extr : ∀ {n l m} {vec : Vec ℕ n} → (Data.Vec.lookup vec l ≡ m) → ℕ
extr {m} refl = m

listext : ∀ (A : Type) (L : Env) → Env
listext A L = (A ∷ L)

-- Proof that (A' ∷ ... ∷ A' ∷ (φ' ++ A ∷ φ)) is "equal to itself", Agda cannot see this
-- from the definition of bind
insbind : ∀ (φ' : Env)  (φ : Env)  (A' : Type) (m : ℕ) → bind (φ' ++ φ) A' m ≡  bind φ' A' m ++ φ
insbind [] φ' A' zero          = refl
insbind [] φ' A' (suc m)       = cong (listext A') (insbind [] φ' A' m)
insbind (x ∷ φ) φ' A' zero    = refl
insbind (x ∷ φ) φ' A' (suc m) = cong (listext A') (insbind (x ∷ φ) φ' A' m)

ins : ∀ {φ φ'} {A B} → Expr (φ' ++ φ) B → Expr (φ' ++ A ∷ φ) B
ins (Var x)                             = Var (insdebr x)
ins (Term{m = zero}{eq = eq} x)         = Term{eq = eq} (λ ())
ins (Term{m = suc m}{eq = eq} x)        = Term{eq = eq} λ l → ins (x l)
-- Direct rewriting does not work since arity (m) is not in scope
-- ins {φ} {φ'} {A} {B} (Term-Rec{n = n}{vec = vec}{A = .B} x x₁) rewrite (insbind φ' φ B {!!})
ins {φ} {φ'} {A} {B} (Term-Rec{n = n}{vec = vec}{A = .B} x x₁)
    = Term-Rec (λ {l : Fin n} {m} {eq : Data.Vec.lookup vec l ≡ m} → ϱ{vec = vec} l m eq (x {l} {m} {eq})) (ins x₁)
    where
    ϱ : ∀ {vec} → (l : Fin n) → (m : ℕ) → (Data.Vec.lookup vec l) ≡ m → Expr (bind (φ' ++ φ) B m) B → Expr (bind (φ' ++ (A ∷ φ)) B m) B
    ϱ l m eq ex rewrite (insbind φ' φ B m) | (insbind φ' (A ∷ φ) B m) = ins{φ = φ}{φ' = bind φ' B m}{A = A} ex
ins {φ' = φ'} (Abs{A = A'} x)           = Abs (ins{φ' = A' ∷ φ'}  x)
ins (App x y)                           = App (ins x) (ins y)

varsub : ∀ {φ φ'} {A B} → A ∈` (φ' ++ B ∷ φ) → Expr φ B → Expr (φ' ++ φ) A
varsub {φ' = []} here M           = M
varsub {φ' = []} (there x) M      = Var x
varsub {φ' = z ∷ zs} here M      = Var here
varsub {φ' = z ∷ zs} (there x) M = ins{φ' = []} (varsub x M)

_[[_]] : ∀ {φ φ'} {A B : Type} → Expr (φ' ++ B ∷ φ) A → Expr φ B → Expr (φ' ++ φ) A
Var x [[ M ]]                      = varsub x M
Term{m = zero}{eq = eq} x [[ M ]]  = Term{eq = eq} (λ ())
Term{m = suc m}{eq = eq} x [[ M ]] = Term{eq = eq} λ l → x l [[ M ]]
_[[_]] {φ} {φ'} {A} {B} (Term-Rec{n = n}{vec = vec}{A = A'} trms e) M
--  = Term-Rec {!λ {l} {m} {eq} → _[[_]] {φ = φ} {φ' = bind φ' A' m} (trms {l} {m} {eq}) M!} (e [[ M ]])
  = Term-Rec (λ {l} {m} {eq} → ϱ{vec = vec} l m eq (trms {l} {m} {eq})) (e [[ M ]])
  where
  ϱ : ∀ {vec} → (l : Fin n) → (m : ℕ) → (Data.Vec.lookup vec l) ≡ m → Expr (bind (φ' ++ B ∷ φ) A m) A → Expr (bind (φ' ++ φ) A m) A
  ϱ l m eq expr rewrite (insbind φ' (B ∷ φ) A m) | (insbind φ' φ A m) = _[[_]] {φ} {bind φ' A m} {A} {B} expr M
Abs N [[ M ]]                      = Abs (N [[ M ]])
App N N' [[ M ]]                   = App (N [[ M ]]) (N' [[ M ]])


-- Values
data Value' {φ} : (t : Type) → Expr φ t → Set where
  VTerm : ∀ {n} {vec : Vec ℕ n} {expr} → Value' (TTerm vec) expr
  VFun  : ∀ {A B expr} → Value' (TFun A B) (Abs expr)

-- Select term from Term-Rec
termsel : ∀ {φ A n m vec} → (∀ {l : Fin n} {m = m} {eq : Data.Vec.lookup vec l ≡ m} → Expr (bind φ A m) A) → Expr φ (TTerm vec) → Expr (bind φ A m) A

data _↠_ {φ} : {A : Type} → Expr φ A → Expr φ A → Set where
  -- Basic call-by-value λ-calc. stuff
  -- Application: Elimination & Reduction
  ξ-App1 : ∀ {A B} {L L' : Expr φ (TFun B A)} {M}
           → L ↠ L'
           → App L M ↠ App L' M

  ξ-App2 : ∀ {A B} {M M' : Expr φ A} {L : Expr φ (TFun A B)}
           → Value' (TFun A B) L
           → M ↠ M'
           → App L M ↠ App L M'

  β-App : ∀ {A B M exp}
          → Value' B M
          → App{B = A} (Abs exp) M ↠ (exp [[ M ]])

  -- Term recursion
  ξ-TermRec : ∀ {A} {n i} {vec : Vec ℕ n} {e e'}
               {trms : (∀ {l : Fin n} {m : ℕ} {eq : (Data.Vec.lookup vec i ≡ m)} → Expr (bind φ A m) A)}
              → e ↠ e'
              → Term-Rec{n = n}{vec = vec} trms e ↠ Term-Rec trms e'

  β-TermRec : ∀ {A} {n i} {vec : Vec ℕ n} {e}
               {trms : (∀ {l : Fin n} {m : ℕ} {eq : (Data.Vec.lookup vec i ≡ m)} → Expr (bind φ A m) A)}
             → Value' (TTerm vec) e
             → {!!}

