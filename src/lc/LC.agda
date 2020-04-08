-- simply-typed λ-calculus

module LC where

open import Agda.Primitive
open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All
open import Agda.Builtin.Bool

-- definitions

data Exp : Set where
  Var : ℕ → Exp
  Abs : Exp → Exp
  App : Exp → Exp → Exp

data Ty : Set where
  Fun : Ty → Ty → Ty

-- typing

Env = List Ty

data _∶_∈_ : ℕ → Ty → Env → Set where
  here : {T : Ty} {Γ : Env} → 0 ∶ T ∈ (T ∷ Γ)
  there : {n : ℕ} {T₁ T₂ : Ty} {Γ : Env} → n ∶ T₁ ∈ Γ → (suc n) ∶ T₁ ∈ (T₂ ∷ Γ) 

data _⊢_∶_ : Env → Exp → Ty → Set where
  TVar : {n : ℕ} {Γ : Env} {T : Ty} → n ∶ T ∈ Γ → Γ ⊢ (Var n) ∶ T
  TAbs : {Γ : Env} {T₁ T₂ : Ty} {e : Exp} → (T₁ ∷ Γ) ⊢ e ∶ T₂ → Γ ⊢ (Abs e) ∶ (Fun T₁ T₂)
  TApp : {Γ : Env} {T₁ T₂ : Ty} {e₁ e₂ : Exp} → Γ ⊢ e₁ ∶ (Fun T₁ T₂) → Γ ⊢ e₂ ∶ T₁ → Γ ⊢ (App e₁ e₂) ∶ T₂

-- denotational semantics

Valᵈ : Ty → Set
Valᵈ (Fun Ty₁ Ty₂) = (Valᵈ Ty₁) → (Valᵈ Ty₂)

access : {n : ℕ} {Γ : Env} {T : Ty} → n ∶ T ∈ Γ → All Valᵈ Γ → Valᵈ T
access here (V ∷ Γ) = V
access (there X) (V ∷ Γ) = access X Γ

eval : {Γ : Env} {T : Ty} {e : Exp} → Γ ⊢ e ∶ T → All Valᵈ Γ → Valᵈ T
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
data Progress (e : Exp) {T : Ty} {j : [] ⊢ e ∶ T}  : Set where
  step : {e' : Exp} → e ⇒ e' → Progress e
  value : Val e → Progress e

progress : (e : Exp) {T : Ty} {j : [] ⊢ e ∶ T} → Progress e {T} {j}
progress (Var x) {T} {TVar ()}
progress (Abs e) = value VFun
progress (App e e₁) {T} {TApp{T₁ = T₁}{T₂ = .T} j j₁} with progress e {Fun T₁ T} {j}
... | step x = step (ξ-App1 x)
... | value VFun with progress e₁ {T₁} {j₁}
...    | step x₁ = step (ξ-App2 VFun x₁)
...    | value x₁ = step (β-App x₁)


-- next: preservation, preservation under substitution lemma required
preserve : {T : Ty} {Γ : Env} (e e' : Exp) (j : Γ ⊢ e ∶ T) (r : e ⇒ e') → Γ ⊢ e' ∶ T
preserve e e' j r = {!j!}
