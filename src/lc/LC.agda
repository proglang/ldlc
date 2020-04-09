-- simply-typed λ-calculus w/ DeBruijn indices

module LC where

open import Agda.Primitive
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.Relation.Unary.All
open import Agda.Builtin.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

-- definitions

data Exp : Set where
  Var : ℕ → Exp
  Abs : Exp → Exp
  App : Exp → Exp → Exp

data Ty : Set where
  Fun : Ty → Ty → Ty

-- typing

data Env : Set where
  ∅ : Env
  _,_∶_ : Env → ℕ → Ty → Env

data _∶_∈_ : ℕ → Ty → Env → Set where
  here : {n : ℕ} {Γ : Env} {T : Ty} → n ∶ T ∈ (Γ , n ∶ T)
  there : {n m : ℕ} {Γ : Env} {T T' : Ty} → n ≢ m → n ∶ T ∈ Γ → n ∶ T ∈ (Γ , m ∶ T')

data _⊢_∶_ : Env → Exp → Ty → Set where
  TVar : {n : ℕ} {Γ : Env} {T : Ty} → n ∶ T ∈ Γ → Γ ⊢ (Var n) ∶ T
  TAbs : {Γ : Env} {T₁ T₂ : Ty} {e : Exp} → (Γ , 0 ∶ T₁) ⊢ e ∶ T₂ → Γ ⊢ (Abs e) ∶ (Fun T₁ T₂)
  TApp : {Γ : Env} {T₁ T₂ : Ty} {e₁ e₂ : Exp} → Γ ⊢ e₁ ∶ (Fun T₁ T₂) → Γ ⊢ e₂ ∶ T₁ → Γ ⊢ (App e₁ e₂) ∶ T₂

-- denotational semantics

-- extract a list of types
Env2List : Env → List Ty
Env2List ∅ = []
Env2List (Γ , x ∶ T) = T ∷ (Env2List Γ)

Valᵈ : Ty → Set
Valᵈ (Fun Ty₁ Ty₂) = (Valᵈ Ty₁) → (Valᵈ Ty₂)

access : {n : ℕ} {Γ : Env} {T : Ty} → n ∶ T ∈ Γ → All Valᵈ (Env2List Γ) → Valᵈ T
access here (V ∷ Γ) = V
access (there neq J) (V ∷ Γ) = access J Γ

eval : {Γ : Env} {T : Ty} {e : Exp} → Γ ⊢ e ∶ T → All Valᵈ (Env2List Γ) → Valᵈ T
eval (TVar c) Val-Γ = access c Val-Γ 
eval (TAbs TJ) Val-Γ = λ V → eval TJ (V ∷ Val-Γ)
eval (TApp TJ TJ₁) Val-Γ = (eval TJ Val-Γ) (eval TJ₁ Val-Γ)


-- operational semantics (call-by-value)

-- shifting, required to avoid variable-capturing in substitution
-- see Pierce 2002, pg. 78/79
↑_,_[_] : ℕ → ℕ → Exp → Exp
↑ d , c [ Var x ] with (_<ᵇ_ x c)
... | true = Var x
... | false = Var (x + d)
↑ d , c [ Abs t ] = Abs (↑ d , (suc c) [ t ])
↑ d , c [ App t t₁ ] = App (↑ d , c [ t ]) (↑ d , c [ t₁ ])

-- substitution
-- see Pierce 2002, pg. 80
[_↦_]_ : ℕ → Exp → Exp → Exp
[ k ↦ s ] Var x with (_≡ᵇ_ x k)
... | false = Var x
... | true = s
[ k ↦ s ] Abs t = Abs ([ suc k ↦ ↑ 1 , 0 [ s ] ] t)
[ k ↦ s ] App t t₁ = App ([ k ↦ s ] t) ([ k ↦ s ] t₁)


data Val : Exp → Set where
  VFun : {e : Exp} → Val (Abs e)

-- reduction relation
data _⇒_ : Exp → Exp → Set where
  ξ-App1 : {e₁ e₁' e₂ : Exp} → e₁ ⇒ e₁' → App e₁ e₂ ⇒ App e₁' e₂
  ξ-App2 : {e e' v : Exp} → Val v → e ⇒ e' → App v e ⇒ App v e'
  β-App : {e v : Exp} → Val v → (App (Abs e) v) ⇒ ([ 0 ↦ v ] e)


-- progress theorem, i.e. all well-typed closed expressions are either a value
-- or can be reduced further
data Progress (e : Exp) {T : Ty} {j : ∅ ⊢ e ∶ T}  : Set where
  step : {e' : Exp} → e ⇒ e' → Progress e
  value : Val e → Progress e

progress : (e : Exp) {T : Ty} {j : ∅ ⊢ e ∶ T} → Progress e {T} {j}
progress (Var x) {T} {TVar ()}
progress (Abs e) = value VFun
progress (App e e₁) {T} {TApp{T₁ = T₁}{T₂ = .T} j j₁} with progress e {Fun T₁ T} {j}
... | step x = step (ξ-App1 x)
... | value VFun with progress e₁ {T₁} {j₁}
...    | step x₁ = step (ξ-App2 VFun x₁)
...    | value x₁ = step (β-App x₁)

-- a natural number cannot be unequal to itself
¬n≢n : {n : ℕ} → (n ≢ n) → ⊥
¬n≢n {n} x = {!!}

-- weaken, if (n : T ∈ Γ), then (n : T ∈ (Γ , m ∶ S)) for m ≠ n
weaken : {n m : ℕ} {T S : Ty} {Γ : Env} → n ≢ m → n ∶ T ∈ Γ → n ∶ T ∈ (Γ , m ∶ S)
weaken {n} {m} {T} {S} {(Γ , n ∶ T)} neq here = there neq here
weaken {n} {m} {T} {S} {(_ , _ ∶ _)} neq (there neq' j) = there neq (there neq' j)

-- strengthen, the opposite of weaken
strengthen : {n m : ℕ} {T S : Ty} {Γ : Env} → n ≢ m → n ∶ T ∈ (Γ , m ∶ S) → n ∶ T ∈ Γ
strengthen {n} {.n} {T} {.T} n≢n here = {!!}  -- n≢n is impossible
strengthen {n} {m} {T} {S} {Γ} n≢m (there neq j) = j

-- preservation under substitution
preserve-subst : {T S : Ty} {Γ : Env} {e s : Exp} (j : (Γ , 0 ∶ S) ⊢ e ∶ T) (j' : Γ ⊢ s ∶ S) → Γ ⊢ ([ 0 ↦ s ] e) ∶ T
preserve-subst (TVar {zero} here) j' = j'
preserve-subst (TVar {zero} (there 0≢0 j)) j' = {!!}  -- 0≢0 is impossible
preserve-subst (TVar {suc n} x) j' = TVar (strengthen{suc n}{0} 1+n≢0 x)
preserve-subst (TAbs j) j' = {!!}
preserve-subst (TApp j j₁) j' = {!!}

-- preservation theorem, i.e. a well-typed expression reduces to a well-typed expression
preserve : {T : Ty} {Γ : Env} (e e' : Exp) (j : Γ ⊢ e ∶ T) (r : e ⇒ e') → Γ ⊢ e' ∶ T
preserve (App s₁ s₂) .(App _ s₂) (TApp j j') (ξ-App1{e₁' = s₁'} r) = TApp (preserve s₁ s₁' j r) j' -- IH on inner reduction
preserve (App s₁ s₂) .(App s₁ _) (TApp j j') (ξ-App2{e' = s₂'} x r) = TApp j (preserve s₂ s₂' j' r)
preserve (App (Abs e) s') .([ 0 ↦ s' ] e) (TApp (TAbs j) j') (β-App x) = preserve-subst j j'



{- intermingling of substitution and typing?
--
data _∶_∈_ : ℕ → Ty → Env → Set where
  here : {T : Ty} {Γ : Env} → 0 ∶ T ∈ (T ∷ Γ)
  there : {n : ℕ} {T₁ T₂ : Ty} {Γ : Env} → n ∶ T₁ ∈ Γ → (suc n) ∶ T₁ ∈ (T₂ ∷ Γ) 

-- alt. substitution, capturing the idea that DeBruijn indices correspond
-- to positions from top of the environemnt (when typed)
[_↦'_]_ : ℕ → Exp → Exp → Exp
[ k ↦' s ] Abs e = Abs ([ (suc k) ↦' s ] e)
[ k ↦' s ] App e e₁ = App ([ k ↦' s ] e) ([ k ↦' s ] e₁)
[ zero ↦' s ] Var zero = s
[ suc k ↦' s ] Var zero = Var zero
[ zero ↦' s ] Var (suc x) = Var x
[ suc k ↦' s ] Var (suc x) = [ k ↦' s ] (Var x)

--
preserve-subst : {T S : Ty} {Γ : Env} {e s : Exp} (j : (S ∷ Γ) ⊢ e ∶ T) (j' : Γ ⊢ s ∶ S) → Γ ⊢ ([ 0 ↦' s ] e) ∶ T
preserve-subst (TVar {zero} here) j' = j'
preserve-subst {T} {S} {Γ} {Var (suc n)} {s} (TVar {suc n} (there x)) j' = TVar x
-}
