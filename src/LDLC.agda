module LDLC where

open import Data.List
open import Data.List.All
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_≤_)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.Fin hiding (_≤_)
open import Data.Product

-- Types: nl ~ (max.) number of labels
data LTy (nl : ℕ) : Set where
  Tunit : LTy nl
  Tlabel : Subset nl → LTy nl
  Tfun : LTy nl → LTy nl → LTy nl

-- Subtyping relation
data _≤_ {nl} : LTy nl → LTy nl → Set where
  Sunit  : Tunit ≤ Tunit
  Slabel : ∀ {snl snl'} → snl ⊆ snl' → (Tlabel snl) ≤ (Tlabel snl')
  Sfun   : ∀ {A A' B B'} → A' ≤ A → B ≤ B' → (Tfun A B) ≤ (Tfun A' B')

----- Properties: Transitiviy of ⊆ (from Data.Fin.Subset) and subtyping relation
⊆-trans : ∀ {nl} {snl snl' snl'' : Subset nl} → snl ⊆ snl' → snl' ⊆ snl'' → snl ⊆ snl''
⊆-trans snl⊆snl' snl'⊆snl'' = λ x → snl'⊆snl'' (snl⊆snl' x)
-- snl⊆snl'   = ∀ {x} → x ∈ snl → x ∈ snl'
-- snl'⊆snl'' = ∀ {x} → x ∈ snl' → x ∈ snl''

≤-trans : ∀ {nl} {t t' t'' : LTy nl} → t ≤ t' → t' ≤ t'' → t ≤ t''
≤-trans Sunit Sunit = Sunit 
≤-trans (Slabel snl⊆snl') (Slabel snl'⊆snl'') = Slabel (⊆-trans snl⊆snl' snl'⊆snl'')
≤-trans (Sfun a'≤a b≤b') (Sfun a''≤a' b'≤b'') = Sfun (≤-trans a''≤a' a'≤a) (≤-trans b≤b' b'≤b'')
-----

-- Environment: List of types, each having a defined number of labels
LTEnv : ℕ → Set
LTEnv nl = List (LTy nl)

-- Lookup in environment
data _∈`_ {nl : ℕ} : LTy nl → LTEnv nl → Set where
  here  : ∀ {lt φ} → lt ∈` (lt ∷ φ)
  there : ∀ {lt lt' φ} → lt ∈` φ → lt ∈` (lt' ∷ φ)

-- Expressions: Variables, Subtypes, Label Introduction & Elimination, Abstraction,
--              Application
data LExpr {nl : ℕ} : LTEnv nl → LTy nl → Set where
  Var      : ∀ {φ t} → (x : t ∈` φ) → LExpr φ t   -- t ∈` φ gives us the position of "x" in env
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

----- BIG STEP SEMANTICS -----
-- Values
Val : ∀ {nl} → LTy nl → Set
Val Tunit = Data.Unit.⊤
Val {nl} (Tlabel snl) = Σ (Fin nl) (λ l → l ∈ snl)
Val (Tfun ty ty₁) = (Val ty) → (Val ty₁)

-- Coerce: Supertype of a Value is also a Value
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

-- Lookup in environment of values;
-- All Val φ ~ All elements in φ satisfy Value predicate (are a value)
access : ∀ {nl} {t : LTy nl} {φ} → t ∈` φ → All Val φ → Val t
access here (px ∷ ρ) = px
access (there x) (px ∷ ρ) = access x ρ

-- Evaluation of Expressions
eval : ∀ {nl φ t} → LExpr {nl} φ t → All Val φ → Val t
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


----- SMALL STEP SEMANTICS -----
----- The following rules roughly correspond to these introduced in -----
----- PLFA (Programming Language Foundations in Agda)               -----

----- Property required for renaming: Given a correspondence between variables from two environments,
-----                                 extending both similiarly is possible without loss of
-----                                 correspondence
ext : ∀ {nl φ ψ} → (∀ {A : LTy nl} → A ∈` φ → A ∈` ψ)
                 → (∀ {A B} → A ∈` (B ∷ φ) → A ∈` (B ∷ ψ))
ext ϱ here      = here
ext ϱ (there x) = there (ϱ x)

---- Renaming: Correspondence between variables from two environments yields in a correspondence
----           between expressions in these environments
---- E.g. λx. x ~ λy. y
rename : ∀ {nl φ ψ} → (∀ {A : LTy nl} → A ∈` φ → A ∈` ψ)
                    → (∀ {A} → LExpr φ A → LExpr ψ A)
rename ϱ (Var x)                 = Var (ϱ x)
rename ϱ (SubType expr:A' A'≤A)  = SubType (rename ϱ expr:A') A'≤A
rename {ψ} ϱ (Lab-I l∈snl)       = Lab-I {ψ} l∈snl
rename ϱ (Lab-E expr:snl case)   = Lab-E (rename ϱ expr:snl)
                                   λ l l∈snl → (rename (ext ϱ) (case l l∈snl))
rename ϱ (Abs expr:B)            = Abs (rename (ext ϱ) expr:B)
rename ϱ (App expr:A->B expr:A)  = App (rename ϱ expr:A->B) (rename ϱ expr:A)

----- Property required for simultaneous substitution: Given a map from variables in one env.
-----                                                  to terms in another, extending both similiarly
-----                                                  is allowed
exts : ∀ {nl φ ψ} → (∀ {A : LTy nl} → A ∈` φ → LExpr ψ A)
                  → (∀ {A B} → A ∈` (B ∷ φ) → LExpr (B ∷ ψ) A)
exts ϱ here      = Var (here)
exts ϱ (there x) = rename there (ϱ x)

----- Simultaneous substitution -----
subst : ∀ {nl φ ψ} → (∀ {A : LTy nl} → A ∈` φ → LExpr ψ A)
                   → (∀ {A : LTy nl} → LExpr φ A → LExpr ψ A)
subst ϱ (Var x)                    = ϱ x
subst ϱ (SubType expr:A' A'≤A)     = SubType (subst ϱ expr:A') A'≤A
subst {ψ} ϱ (Lab-I l∈snl)          = Lab-I {ψ} l∈snl
subst ϱ (Lab-E expr:snl case)      = Lab-E (subst ϱ expr:snl)
                                     λ l l∈snl → (subst (exts ϱ) (case l l∈snl))
subst ϱ (Abs expr:B)               = Abs (subst (exts ϱ) expr:B)
subst ϱ (App expr:A→B expr:A)     = App (subst ϱ expr:A→B) (subst ϱ expr:A)

----- Single substitution, using simultaneous substitution
----- Given an expression in environment (φ.B) with type A, we replace
----- the variable of type B with an expression in environment φ by using
----- the map ϱ which maps last variable in environment to the expr. of type B
----- and every other free variable to itself for substitution
_[[_]] : ∀ {nl φ} {A B : LTy nl} → LExpr (B ∷ φ) A → LExpr φ B → LExpr φ A
_[[_]] {nl} {φ} {A} {B} N M = subst {nl} {B ∷ φ} {φ} ϱ {A} N
  where
  ϱ : ∀ {A} → A ∈` (B ∷ φ) → LExpr φ A
  ϱ here      = M
  ϱ (there x) = Var x 

-- We force values to have type SubType, since Lab-I results in expressions with type {l}
-- and we want to keep the information about which subset l is in
data Val' {n φ} : (t : LTy n) → LExpr {n} φ t → Set where
  -- Vlab : ∀ {l snl x l∈snl tl≤tout} → Val' (Tlabel x) (SubType (Lab-I{l = l}{snl} l∈snl) tl≤tout)
  -- Changed x to snl, required for β-Lab-E ?
  Vlab : ∀ {l snl l∈snl tl≤tout} → Val' (Tlabel snl) (SubType (Lab-I{l = l}{snl} l∈snl) tl≤tout)
  Vfun : ∀ {ty ty' A B ty≤A B≤ty' exp}
         → Val' (Tfun ty ty') (SubType (Abs exp) (Sfun {n} {A} {ty} {B} ty≤A B≤ty'))

data _~>_ {n φ A} : LExpr {n} φ A → LExpr {n} φ A → Set where

  ξ-App1 : ∀ {B} {L L' : (LExpr φ (Tfun B A))} {M} → L ~> L'
                                                   → App L M ~> App L' M
  
  ξ-App2 : ∀ {M M' : LExpr φ A} {L} → M ~> M'
                                    → App L M ~> App L M'

  β-App : ∀ {A' B B' A'≤A B≤B' exp W}
          -- → Val' (Tfun ty ty') (SubType (Abs exp) (Sfun {n} {A} {ty} {B} ty≤A B≤ty'))
          → Val' B W
          → App ((SubType (Abs exp) (Sfun {n} {B'} {B} {A'} {A} B≤B' A'≤A))) W
             ~>
             SubType (exp [[ SubType W B≤B' ]]) A'≤A      
{- non-subtyping version
  β-App  : ∀ {B} {N : LExpr (B ∷ φ) A} {W : LExpr φ B}
           → Val' B W   -- Vfun?
           → App (Abs N) (W) ~> (N [[ W ]])
-}
  ξ-SubType : ∀ {A'≤A} {L L' : LExpr φ A} → L ~> L'
                                          → SubType L A'≤A ~> SubType L' A'≤A

  ξ-Lab-E : ∀ {snl} {L L' : LExpr φ (Tlabel snl)} {cases} → L ~> L'
                                                          → Lab-E L cases ~> Lab-E L' cases

  β-Lab-E : ∀ {l snl l∈snl tl≤tout} {cases}
            → Val' {n} {φ} (Tlabel snl) (SubType (Lab-I{l = l}{snl} l∈snl) tl≤tout)
            → Lab-E (SubType (Lab-I{l = l}{snl} l∈snl) tl≤tout) cases
               ~>
               ((cases l l∈snl) [[ Lab-I{l = l}{snl} l∈snl ]])
               -- Substitute topmost variable for l in expression of case

-- Mutual recursive definition w/ accessing env. instead of substitution?
