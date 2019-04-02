module LDLC where

open import Data.List
open import Data.List.All
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_≤_)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.Fin hiding (_≤_)
open import Data.Product

data LTy (nl : ℕ) : Set

-- the index nl stands for the number of labels
data LTy nl where
  Tunit : LTy nl
  Tlabel : Subset nl → LTy nl
  Tfun : LTy nl → LTy nl → LTy nl

-- subtype relation
data _≤_ {nl} : LTy nl → LTy nl → Set where
  Sunit  : Tunit ≤ Tunit
  Slabel : ∀ {snl snl'} → snl ⊆ snl' → (Tlabel snl) ≤ (Tlabel snl')
  Sfun   : ∀ {A A' B B'} → A' ≤ A → B ≤ B' → (Tfun A B) ≤ (Tfun A' B')

-- Transitivity of ⊆
⊆-trans : ∀ {nl} {snl snl' snl'' : Subset nl} → snl ⊆ snl' → snl' ⊆ snl'' → snl ⊆ snl''
⊆-trans snl⊆snl' snl'⊆snl'' = λ x → snl'⊆snl'' (snl⊆snl' x)
-- snl⊆snl'   = ∀ {x} → x ∈ snl → x ∈ snl'
-- snl'⊆snl'' = ∀ {x} → x ∈ snl' → x ∈ snl''

-- Transitivity of ≤ 
≤-trans : ∀ {nl} {t t' t'' : LTy nl} → t ≤ t' → t' ≤ t'' → t ≤ t''
≤-trans Sunit Sunit = Sunit 
≤-trans (Slabel snl⊆snl') (Slabel snl'⊆snl'') = Slabel (⊆-trans snl⊆snl' snl'⊆snl'')
≤-trans (Sfun a'≤a b≤b') (Sfun a''≤a' b'≤b'') = Sfun (≤-trans a''≤a' a'≤a) (≤-trans b≤b' b'≤b'')

LTEnv : ℕ → Set
LTEnv nl = List (LTy nl)


data _∈`_ {nl : ℕ} : LTy nl → LTEnv nl → Set where
  here  : ∀ {lt φ} → lt ∈` (lt ∷ φ)
  there : ∀ {lt lt' φ} → lt ∈` φ → lt ∈` (lt' ∷ φ)

data LExpr {nl : ℕ} : LTEnv nl → LTy nl → Set where
  Var      : ∀ {φ t} → (x : t ∈` φ) → LExpr φ t
  SubType  : ∀ {A A' φ} →  LExpr φ A → A ≤ A'
                        →  LExpr φ A'
  Lab-I    : ∀ {l snl φ} → l ∈ snl → LExpr φ (Tlabel ⁅ l ⁆)
  Lab-E    : ∀ {snl φ B} → LExpr φ (Tlabel snl)
                         → (∀ l → l ∈ snl → LExpr (Tlabel (⁅ l ⁆) ∷ φ) B) 
                         → LExpr φ B
  Abs     : ∀ {B A φ} → LExpr (A ∷ φ) B
                      → LExpr φ (Tfun A B)
  App     : ∀ {A B φ} → LExpr φ (Tfun A B)
                      → (ex : LExpr φ A)
                      → LExpr φ B
                 
-- Big step semantics
Val : ∀ {n} → LTy n → Set
Val Tunit = Data.Unit.⊤
Val {n} (Tlabel snl) = Σ (Fin n) (λ l → l ∈ snl)
Val (Tfun ty ty₁) = (Val ty) → (Val ty₁)

coerce : ∀ {nl} {t t' : LTy nl} → t ≤ t' → Val t → Val t'
-- t is Val Unit
coerce Sunit t = tt
-- Since snl⊆snl' = ∀ x → x ∈ snl → x ∈ snl'
coerce (Slabel snl⊆snl') (Finnl , Finnl∈snl) = (Finnl , (snl⊆snl' Finnl∈snl))
-- t, t' functions, induction on t then using inductive hypothesis and application of t'
coerce (Sfun Sunit b≤b') unit→b = λ x → coerce b≤b' (unit→b x)
coerce (Sfun (Slabel snl'⊆snl) b≤b') snl'→b = λ x → (coerce b≤b' (snl'→b (Σ.proj₁ x , snl'⊆snl (Σ.proj₂ x))))
coerce (Sfun (Sfun a'≤a b≤b') b₁≤b'') [a'→b']→b₁ = λ x → (coerce b₁≤b'' ([a'→b']→b₁ (coerce (Sfun a'≤a b≤b') x)))
-- λ (x : (A → B)) coerce b₁≤b'' ([a'→b']→b₁ (coerce (a→b ≤ a'→b') x))

access : ∀ {n} {t : LTy n} {φ} → t ∈` φ → All Val φ → Val t
access here (px ∷ ρ) = px
access (there x) (px ∷ ρ) = access x ρ

eval : ∀ {n φ t} → LExpr {n} φ t → All Val φ → Val t
eval (Var x) ϱ = access x ϱ
eval (SubType e a≤a') ϱ = coerce a≤a' (eval e ϱ)
eval (Lab-I {l} l∈snl) ϱ = l , (x∈⁅x⁆ l)
-- Apply case function to evaluated expression, evaluate result under environment with added
-- Tlabel Value l
-- eval e = Σ (l : Fin n) (λ l → l ∈ snl)
-- eval (case l (l ∈ snl)) (Tlabel l :: ϱ)
eval (Lab-E e case) ϱ = eval (case (Σ.proj₁ (eval e ϱ)) (Σ.proj₂ (eval e ϱ)))
                        ((Σ.proj₁ (eval e ϱ) , x∈⁅x⁆ (Σ.proj₁ (eval e ϱ))) ∷ ϱ)
eval (Abs e) ϱ = λ x → eval e (x ∷ ϱ)
eval (App e e₁) ϱ = (eval e ϱ) (eval e₁ ϱ)

-- Small step semantics

-- To-Do: Reduction rules; eval
--        Substitution needed?

-- We force values to have type SubType, since Lab-I results in expressions with type of only one
-- element of a label set and we want to keep the complete label set
data Val' {n φ} : (t : LTy n) → LExpr {n} φ t → Set where
  Vlab : ∀ {l snl x l∈snl tl≤tout} → Val' (Tlabel x) (SubType (Lab-I{l = l}{snl} l∈snl) tl≤tout)
  Vfun : ∀ {ty ty' A B ty≤A B≤ty' exp}
         → Val' (Tfun ty ty') (SubType (Abs exp) (Sfun {n} {A} {ty} {B} ty≤A B≤ty'))

data _~>_ {n φ t} : LExpr {n} φ t → LExpr {n} φ t → Set where
  -- The following rules roughly correspond to the rules used in the PLFA (Progr. Language Foundations)
  -- book, from the chapter about Lambda Calculus

  ξ-App1 : ∀ {A} {L L' : (LExpr φ (Tfun A t))} {M} → L ~> L' → App L M ~> App L' M
  
  ξ-App2 : ∀ {M M' : LExpr φ t} {L} → M ~> M' → App L M ~> App L M'

-- Requires substitution:
--  β-App  : ∀ {} → Val' V → (App (Abs {A} {Φ} Expr) V) ~> Expr[V]


-- Substitution
_[_:=_] : ∀ {n φ t} → LExpr {n} φ t → (x : t ∈` φ) → LExpr φ t → LExpr φ t
Var x₁ [ x := V ] = {!!}
SubType expr x₁ [ x := V ] = {!!}
Lab-I x₁ [ x := V ] = {!!}
Lab-E expr x₁ [ x := V ] = {!!}
Abs expr [ x := V ] = {!!}
App expr expr₁ [ x := V ] = {!!} 
