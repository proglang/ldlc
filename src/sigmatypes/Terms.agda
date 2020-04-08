-- Σ-Terms 
module Terms where

open import Data.Vec hiding (_++_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.Fin.Base

open import Size

-- Ranked alphabet: Vector of natural numbers, where vec[i] denotes the arity of symbol i
RankAlph : ℕ → Set
RankAlph n = Vec ℕ n

-- Types
data Type : Set where
  TTerm : ∀ {n} → RankAlph n → Type
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
  -- Given terms σ₁, ..., σₘ and a term σ with arity α(σ) = m, we get a new term σ(σ₁, ..., σₘ); Special case: m = 0
  Term    : ∀ {φ n vec} {i : Fin n} {m} {eq : Data.Vec.lookup vec i ≡ m} → (∀ (l : Fin m) → Expr φ (TTerm vec)) → Expr φ (TTerm vec)
  -- Recursion on Terms: For every term σ ∈ Σ with arity α(σ) = m, we have an expression of type A in an environment that binds m variables of type A 
  --                     Together with an expression of type Σ, by recursion on the correct expression we get an expression of type A
  Term-Rec  : ∀ {φ n vec A} → (∀ {l : Fin n} {m} {eq : (Data.Vec.lookup vec l) ≡ m} → Expr (bind φ A m) A) → Expr φ (TTerm vec) → Expr φ A
  Var    : ∀ {φ A}   → A ∈` φ → Expr φ A
  Abs    : ∀ {φ A B} → Expr (A ∷ φ) B → Expr φ (TFun A B)
  App    : ∀ {φ A B} → Expr φ (TFun A B) → Expr φ A → Expr φ B


----- Big step semantics using Agda semantics -----
-- Data type for terms
data TTerm' {n} : RankAlph n →  Set where
  Term' : ∀ {vec m} {i : Fin n} {eq : (Data.Vec.lookup vec i) ≡ m} → (∀ (l : Fin m) → (TTerm' vec)) → (TTerm' vec)

data TTerm'' {n} (ra : RankAlph n) : {i : Size} → Set where
  mk : ∀ {i} → (symb : Fin n) → Vec (TTerm'' ra {i}) (Data.Vec.lookup ra symb) → TTerm'' ra {↑ i}

-- From data type to expression
conversion : ∀ {φ n} {vec : RankAlph n} → TTerm' vec → Expr φ (TTerm vec)
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

nary : (A : Set) → ℕ → Set
nary A zero = A
nary A (suc n) = A → nary A n

algebra : ∀ {n} → RankAlph n → (A : Set) → Vec Set n
algebra vec A = Data.Vec.map (nary A) vec

term-rec : ∀ {A : Set} {n : ℕ} {vec : RankAlph n} → (alg : Vec Set n) → TTerm' vec → A
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
extr : ∀ {n l m} {vec : RankAlph n} → (Data.Vec.lookup vec l ≡ m) → ℕ
extr {m} refl = m

-- Proof that (A' ∷ ... ∷ A' ∷ (φ' ++ A ∷ φ)) is "equal to itself", Agda cannot see this
-- from the definition of bind
insbind : ∀ (φ' : Env)  (φ : Env)  (A' : Type) (m : ℕ) → bind (φ' ++ φ) A' m ≡  bind φ' A' m ++ φ
insbind [] φ' A' zero          = refl
insbind [] φ' A' (suc m)       = cong (_∷_ A') (insbind [] φ' A' m)
insbind (x ∷ φ) φ' A' zero    = refl
insbind (x ∷ φ) φ' A' (suc m) = cong (_∷_ A') (insbind (x ∷ φ) φ' A' m)

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
  = Term-Rec (λ {l} {m} {eq} → ϱ{vec = vec} l m eq (trms {l} {m} {eq})) (e [[ M ]])
  where
  ϱ : ∀ {vec} → (l : Fin n) → (m : ℕ) → (Data.Vec.lookup vec l) ≡ m → Expr (bind (φ' ++ B ∷ φ) A m) A → Expr (bind (φ' ++ φ) A m) A
  ϱ l m eq expr rewrite (insbind φ' (B ∷ φ) A m) | (insbind φ' φ A m) = _[[_]] {φ} {bind φ' A m} {A} {B} expr M
Abs N [[ M ]]                      = Abs (N [[ M ]])
App N N' [[ M ]]                   = App (N [[ M ]]) (N' [[ M ]])


-- Values
data Value' {φ} : (t : Type) → Expr φ t → Set where
  VTerm : ∀ {n} {vec : Vec ℕ n} {i : Fin n} {m} {eq : Data.Vec.lookup vec i ≡ m}
    → (subt : Fin m → Expr φ (TTerm vec))
    → (∀ {l : Fin m} → Value' (TTerm vec) (subt l))
    → Value' (TTerm vec) (Term {i = i}{m}{eq} subt)
  VFun  : ∀ {A B expr} → Value' (TFun A B) (Abs expr)

---- Functions required for Term-Rec
-- Select term for recursion
termsel : ∀ {φ A n m vec} → (∀ {l : Fin n} {m'} {eq : Data.Vec.lookup vec l ≡ m'} → Expr (bind φ A m') A) → Expr φ (TTerm vec) → Expr (bind φ A m) A
termsel {m = m} {vec = vec} trms (Term{i = i}{m = m'}{eq = eq} x) = {!!}
termsel trms (Term-Rec x trm) = {!!}
termsel trms (Var x)          = {!!}
termsel trms (App trm trm₁)   = {!!}

-- Proof that (bind (A ∷ φ) A m) ≡ (A ∷ bind φ A m)
bindapp : ∀ {φ A m} → bind (A ∷ φ) A m ≡ (A ∷ bind φ A m)
bindapp {m = zero}  = refl
bindapp {A = A} {m = suc m} = cong (_∷_ A) bindapp

-- Looks more complicated than it is:
-- Given a Term-Rec expression - including a map that for each term t' in our ranked alphabet with arity α(t') = m'
-- defines an expression with m' bound variables - and a specific Term t with arity α(t) = m:
-- Recursively, on m from "right-to-left", bind a Term-Rec expression with the same map using the topmost subterm on top of the environment
-- Term-Rec trms σ(t₁, ..., tₘ) →
-- ( ... ((trms(σ) [y₁ ↦ Term-Rec trms t₁]) [y₂ ↦ Term-Rec trms t₂]) ...) [yₘ ↦ Term-Rec trms tₘ]
bindtosubs : ∀ {m n φ A} {vec : RankAlph n} →
  (trms : (∀ {l : Fin n} {m'} {eq : Data.Vec.lookup vec l ≡ m'} → Expr (bind φ A m') A)) →
  (subtrms : (∀ (l : Fin m) → Expr φ (TTerm vec))) →
  Expr (bind φ A m) A →
  Expr φ A
bindtosubs {zero} trms subtrms e  = e
bindtosubs {suc m} {n = n} {φ} {A} {vec = vec} trms subtrms e rewrite sym (bindapp {φ} {A} {m}) 
                                  = (bindtosubs{m = m}{n = n}{vec = vec} (λ {l} {m'} {eq} → ϱ l m' eq (trms {l} {m'} {eq})) (λ l → ins{φ' = []}{A = A} ((urbild subtrms) l)) e)
                                    [[ Term-Rec (λ {l} {m'} {eq} → trms {l} {m'} {eq}) (subtrms (fromℕ m)) ]]
                                    where -- Adjustement of environment/DeBruijn indices: In the recursion step, we have to adjust the term map (∀ t' with α(t') = m' we get an Expr with m' bound vars)
                                          --                                              by adding another bound variable. If we for example have a "Var here" in σ, this adjustement leads to the correct
                                          --                                              substitution with evaluated σ₁ that has m bound variables.
                                    ϱ : (l : Fin n) → (m' : ℕ) → (Data.Vec.lookup vec l) ≡ m' → Expr (bind φ A m') A → Expr (bind (A ∷ φ) A m') A
                                    ϱ l m' eq ex rewrite (bindapp {φ} {A} {m'}) = ins{φ' = []}{A = A} ex
  
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

  -- Term elimination
  ξ-TermRec : ∀ {A} {n} {vec : RankAlph n} {e e'}
               {trms : (∀ {l : Fin n} {m : ℕ} {eq : (Data.Vec.lookup vec l ≡ m)} → Expr (bind φ A m) A)}
              → e ↠ e'
              → Term-Rec{n = n}{vec = vec} (λ {l} {m'} {eq} → trms {l} {m'} {eq}) e ↠ Term-Rec (λ {l} {m'} {eq} → trms {l} {m'} {eq}) e'

{-
  β-TermRec : ∀ {A} {n i} {vec : Vec ℕ n} {e}
               {trms : (∀ {l : Fin n} {m : ℕ} {eq : (Data.Vec.lookup vec i ≡ m)} → Expr (bind φ A m) A)}
             → Value' (TTerm vec) e
             → {!!}
-}

