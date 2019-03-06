module Lam where

-- simply typed terminating lambda calculus interpreter

open import Data.List
open import Data.List.All
open import Data.Unit
open import Data.Nat

data Ty : Set where
  Tunit : Ty
  Tfun : Ty → Ty → Ty

TEnv = List Ty

data _∈_ : Ty → TEnv → Set where
  here : ∀ {t Φ} → t ∈ (t ∷ Φ)
  there : ∀ {t t' Φ} → t ∈ Φ → t ∈ (t' ∷ Φ)

data Exp : TEnv → Ty → Set where
  Var : ∀ {Φ t} → (x : t ∈ Φ) → Exp Φ t
  Abs : ∀ {Φ t t'} → Exp (t ∷ Φ) t' → Exp Φ (Tfun t t')
  App : ∀ {Φ t t'} → Exp Φ (Tfun t t') → Exp Φ t → Exp Φ t'

Val : Ty → Set
Val Tunit = ⊤
Val (Tfun t t₁) = Val t → Val t₁

access : ∀ {t Φ} → t ∈ Φ → All Val Φ → Val t
access here (px ∷ ρ) = px
access (there x) (px ∷ ρ) = access x ρ

eval : ∀ {Φ t} → Exp Φ t → All Val Φ → Val t
eval (Var x) ρ = access x ρ
eval (Abs e) ρ = λ x → eval e (x ∷ ρ)
eval (App e e₁) ρ = (eval e ρ) (eval e₁ ρ)
