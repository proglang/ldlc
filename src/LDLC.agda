module LDLC where

open import Data.List
open import Data.List.All
open import Data.List.Base
open import Data.Vec hiding (_∈_) renaming (_++_ to _+++_)
open import Data.Unit hiding (_≤_ ; poset)
open import Data.Nat hiding (_≤_)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Fin hiding (_≤_)
open import Data.Product
open import Data.Empty
open import Relation.Binary

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

----- Properties
-- Transitivity, reflexivity of ⊆ (the one in Data.Fin.Subset.Properties ?)
⊆-trans : ∀ {nl} {snl snl' snl'' : Subset nl} → snl ⊆ snl' → snl' ⊆ snl'' → snl ⊆ snl''
⊆-trans snl⊆snl' snl'⊆snl'' = λ x → snl'⊆snl'' (snl⊆snl' x)
-- snl⊆snl'   = ∀ {x} → x ∈ snl → x ∈ snl'
-- snl'⊆snl'' = ∀ {x} → x ∈ snl' → x ∈ snl''

⊆-refl : ∀ {nl} → (snl : Subset nl) → snl ⊆ snl
⊆-refl snl = λ x → x

-- Transitivity, reflexivity of ≤
≤-trans : ∀ {nl} {t t' t'' : LTy nl} → t ≤ t' → t' ≤ t'' → t ≤ t''
≤-trans Sunit Sunit = Sunit 
≤-trans (Slabel snl⊆snl') (Slabel snl'⊆snl'') = Slabel (⊆-trans snl⊆snl' snl'⊆snl'')
≤-trans (Sfun a'≤a b≤b') (Sfun a''≤a' b'≤b'') = Sfun (≤-trans a''≤a' a'≤a) (≤-trans b≤b' b'≤b'')

≤-refl : ∀ {nl} → (t : LTy nl) → t ≤ t
≤-refl Tunit = Sunit
≤-refl (Tlabel x) = Slabel (⊆-refl x)
≤-refl (Tfun t t') = Sfun (≤-refl t) (≤-refl t')
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
  Unit     : ∀ {φ} → LExpr φ Tunit
  Var      : ∀ {φ t} → (x : t ∈` φ) → LExpr φ t   -- t ∈` φ gives us the position of "x" in env
  SubType  : ∀ {A A' φ} →  LExpr φ A → A ≤ A'
                        →  LExpr φ A'
  Lab-I    : ∀ {l snl φ} → l ∈ snl → LExpr φ (Tlabel snl)
  Lab-E    : ∀ {snl φ B} → LExpr φ (Tlabel snl)
                         → (∀ l → l ∈ snl → LExpr φ B) 
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
coerce (Sfun A'≤A B≤B') f = λ x → coerce B≤B' (f (coerce A'≤A x))

-- Lookup in environment of values;
-- All Val φ ~ All elements in φ satisfy Value predicate (are a value)
access : ∀ {nl} {t : LTy nl} {φ} → t ∈` φ → All Val φ → Val t
access here (px ∷ ρ) = px
access (there x) (px ∷ ρ) = access x ρ

-- Evaluation of Expressions
eval : ∀ {nl φ t} → LExpr {nl} φ t → All Val φ → Val t
eval Unit ϱ = tt
eval (Var x) ϱ = access x ϱ
eval (SubType e a≤a') ϱ = coerce a≤a' (eval e ϱ)
eval (Lab-I {l} l∈snl) ϱ = l , (l∈snl)
-- Apply case function to evaluated expression
eval (Lab-E e case) ϱ with eval e ϱ
... | lab , lab∈nl = eval (case lab lab∈nl) ϱ
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
rename ϱ Unit                    = Unit
rename ϱ (Var x)                 = Var (ϱ x)
rename ϱ (SubType expr:A' A'≤A)  = SubType (rename ϱ expr:A') A'≤A
rename {ψ} ϱ (Lab-I l∈snl)       = Lab-I {ψ} l∈snl
rename ϱ (Lab-E expr:snl case)   = Lab-E (rename ϱ expr:snl)
                                   λ l l∈snl → (rename ϱ (case l l∈snl))
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
subst ϱ Unit                       = Unit
subst ϱ (Var x)                    = ϱ x
subst ϱ (SubType expr:A' A'≤A)     = SubType (subst ϱ expr:A') A'≤A
subst {ψ} ϱ (Lab-I l∈snl)          = Lab-I {ψ} l∈snl
subst ϱ (Lab-E expr:snl case)      = Lab-E (subst ϱ expr:snl)
                                     λ l l∈snl → (subst ϱ (case l l∈snl))
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

-- Type substitution

-- Lemmas for '++' operator (actually not required, can work with def. of ++)
-- if lt ∈` φ' then also lt ∈` (φ' ++ φ)
expansionlemma : ∀ {nl} {lt : LTy nl} {φ φ'} → lt ∈` φ' → lt ∈` (φ' ++ φ)
expansionlemma here      = here
expansionlemma (there x) = there (expansionlemma x)

-- if lt ∈` φ then also lt ∈` (φ' ++ φ)
extensionlemma : ∀ {nl} {lt : LTy nl} {φ φ'} → lt ∈` φ → lt ∈` (φ' ++ φ)
extensionlemma {φ' = []}        here     = here
extensionlemma {φ' = x ∷ xs}   here     = there (extensionlemma{φ' = xs} here)
extensionlemma {φ' = []}       (there y) = there y
extensionlemma {φ' = x ∷ xs}  (there y) = there (extensionlemma {φ' = xs} (there y))

-- Extension lemma inside a list for De Bruijn indices
inextdebr : ∀ {nl} {B A : LTy nl} {φ' φ} → B ∈` (φ' ++ φ) → B ∈` (φ' ++ (A ∷ φ))
inextdebr {φ' = []} here           = there here
inextdebr {φ' = []} (there x)      = there (there x)
inextdebr {φ' = x ∷ xs} here      = here
inextdebr {φ' = x ∷ xs} (there y) = there (inextdebr{φ' = xs} y)

-- Extension lemma inside a list for expressions
inext : ∀ {nl} {φ φ'} {A B : LTy nl} → LExpr (φ' ++ φ) B → LExpr (φ' ++ (A ∷ φ)) B
inext Unit                                 = Unit
inext {φ' = φ'} (Var x)                    = Var (inextdebr{φ' = φ'} x)
inext {φ = φ}{φ' = φ'} (SubType expr b≤b') = SubType (inext{φ = φ}{φ' = φ'} expr) b≤b'
inext (Lab-I x)                            = Lab-I x
inext {φ = φ} {φ' = φ'} (Lab-E x x₁)       = Lab-E (inext{φ = φ}{φ' = φ'} x) λ l x₂ → inext{φ = φ}{φ' = φ'} (x₁ l x₂)
inext {nl} {φ} {φ'} (Abs{A = A°} x)        = Abs (inext{φ = φ}{φ' = A° ∷ φ'} x)
inext {φ = φ} {φ' = φ'} (App x x₁)         = App (inext{φ = φ}{φ' = φ'} x) (inext{φ = φ}{φ' = φ'} x₁)

{- Direct substitution of _∈`_ not possible:
lolz : ∀ {nl} {B A A' : LTy nl} {φ' φ} → B ∈` (φ' ++ (A ∷ φ)) → A' ≤ A → B ∈` (φ' ++ (A' ∷ φ))
lolz {φ' = []}  here a'≤a          = :(  -- SubTyping required
-}
-- Type substitution for De Bruijn indices
debrsub : ∀ {nl} {B B' A A' : LTy nl} {φ' φ} → B ∈` (φ' ++ (A ∷ φ)) → A' ≤ A → B ≤ B' → LExpr (φ' ++ (A' ∷ φ)) B'
debrsub {φ' = []}  here a'≤a b≤b'          = SubType (Var here) (≤-trans a'≤a b≤b')
debrsub {φ' = []} (there x) a'≤a b≤b'      = SubType (Var (there x)) b≤b'
debrsub {φ' = x ∷ xs} here a'≤a b≤b'      = SubType (Var (here)) b≤b'
debrsub {φ' = x ∷ xs} (there z) a'≤a b≤b' = inext{φ' = []}{A = x} (debrsub{φ' = xs} z a'≤a b≤b')

-- Type substitution required for Abs SubTypes
typesub : ∀ {nl φ φ' A B A' B'} → LExpr{nl} (φ' ++ (A ∷ φ)) B → A' ≤ A → B ≤ B' → LExpr (φ' ++ (A' ∷ φ)) B'
typesub Unit a'≤a Sunit = Unit
typesub {φ = φ} {φ'} {A} {B} {A'} {B'} (Var x) a'≤a b≤b'                        = debrsub{φ' = φ'}{φ = φ} x a'≤a b≤b'
typesub {nl} {φ} {φ'} (SubType expr x) a'≤a b≤b'                                = typesub{nl}{φ}{φ'} expr a'≤a (≤-trans x b≤b')
typesub (Lab-I l∈snl) a'≤a b≤b'                                                 = SubType (Lab-I l∈snl) b≤b'
typesub {nl} {φ} {φ'} (Lab-E{snl = snl} expr cases) a'≤a b≤b'                   = Lab-E (typesub{nl}{φ}{φ'} expr a'≤a (≤-refl (Tlabel snl))) λ l x → typesub{nl}{φ}{φ'} (cases l x) a'≤a b≤b'
typesub {φ' = φ'}{A = A}{B = A°→B°}{A' = A'}{B' = A°°→B°°} (Abs{A = A°} expr) a'≤a (Sfun{A = .A°}{A' = A°°}{B = B°}{B' = B°°} A°°≤A° B°≤B°°)
                                                                                = SubType (Abs (typesub{φ' = A° ∷ φ'} expr a'≤a B°≤B°°)) (Sfun A°°≤A° (≤-refl B°°))
typesub {nl}{φ}{φ'}{A}{B}{A'}{B'} (App{A = A°}{B = .B} expr expr') a'≤a b≤b'    = SubType (App (typesub{nl}{φ}{φ'} expr a'≤a (≤-refl (Tfun A° B))) (typesub{nl}{φ}{φ'} expr' a'≤a (≤-refl A°))) b≤b'


-- We force values to have type SubType, since Lab-I results in expressions with type {l}
-- and we want to keep the information about which subset l is in
data Val' {n φ} : (t : LTy n) → LExpr {n} φ t → Set where
  Vunit :  Val' (Tunit) Unit
  Vlab : ∀ {l snl l∈snl} → Val' (Tlabel snl) (Lab-I{l = l}{snl} l∈snl)
  Vfun : ∀ {A B exp} → Val' (Tfun A B) (Abs exp)

data _~>_ {n φ} : {A : LTy n} → LExpr {n} φ A → LExpr {n} φ A → Set where

  ξ-App1 : ∀ {A B} {L L' : (LExpr φ (Tfun B A))} {M}
           → L ~> L'
           → App L M ~> App L' M
  
  ξ-App2 : ∀ {A B} {M M' : LExpr φ A} {L : LExpr φ (Tfun A B)}
           → Val' (Tfun A B) L
           → M ~> M'
           → App L M ~> App L M'

  β-App : ∀ {A B M exp} 
          → Val' B M
          → App{B = A} (Abs exp) M
             ~>
             (exp [[ M ]])

  ξ-SubType : ∀ {A A' A≤A' } {L L' : LExpr φ A}
              → L ~> L'
              → SubType{A = A}{A'} L A≤A' ~> SubType{A = A} L' A≤A'

  ξ-Lab-E : ∀ {A snl} {L L' : LExpr φ (Tlabel snl)} {cases}
            → L ~> L'
            → Lab-E{B = A} L cases ~> Lab-E L' cases

  β-Lab-E : ∀ {A l snl l∈snl cases}
            → Lab-E{B = A} (Lab-I{l = l}{snl} l∈snl) cases
               ~>
               cases l (l∈snl)

  γ-Lab-I : ∀ {l snl snl'} {l∈snl : l ∈ snl} {snl⊆snl' : snl ⊆ snl'}
            → SubType (Lab-I{l = l}{snl = snl} l∈snl) (Slabel snl⊆snl')
               ~>
               Lab-I (snl⊆snl' l∈snl)

  -- (Abs exp) : A → B <: A' → B' ~> Abs exp : A' → B'
  γ-Abs : ∀ {A B A' B' e} {A'≤A : A' ≤ A} {B≤B' : B ≤ B'}
          → SubType (Abs{B = B}{A = A} e) (Sfun A'≤A B≤B')
             ~>
             Abs{B = B'}{A = A'} (typesub{φ' = []} e A'≤A B≤B')

  γ-SubType : ∀ {A A' A'' A≤A' A'≤A'' expr}
              → SubType{A = A'}{A' = A''} (SubType{A = A} expr A≤A') A'≤A''
                 ~>
                 SubType expr (≤-trans A≤A' A'≤A'')

  -- Either we define Unit values to be SubTypes of Unit≤Unit; or we introducte the following rule
  β-SubType-Unit : SubType Unit Sunit
                   ~>
                   Unit

----- Properties of small-step evaluation -----
----- Reflexive & transitive closure, required for generation of evaluation sequences
infix 2 _~>>_
infix 1 begin_
infixr 2 _~>⟨_⟩_
infix 3 _∎

data _~>>_ : ∀ {n} {φ} {A : LTy n} → LExpr φ A → LExpr φ A → Set where
  _∎ : ∀ {n φ} {A : LTy n} (L : LExpr φ A)
       → L ~>> L

  _~>⟨_⟩_ : ∀ {n φ} {A : LTy n} (L : LExpr φ A) {M N : LExpr φ A}
           → L ~> M
           → M ~>> N
           → L ~>> N

begin_ : ∀ {n φ} {A : LTy n} {M N : LExpr φ A} → M ~>> N → M ~>> N
begin M~>>N = M~>>N


----- Progress Theorem
----- Definiton: ∀ M ∈ (LExpr [] A) : (∃N : M ~> N) ∨ (Val'(M))
data Progress {n A} (M : LExpr{n} [] A) : Set where
  step : ∀ {N : LExpr [] A} → M ~> N → Progress M
  done : Val' A M → Progress M

-- Proof
progress : ∀ {n A} → (M : LExpr{n} [] A) → Progress M
progress Unit                                                                             = done Vunit
progress (Var ())                                                         -- Var requires a proof for A ∈ [] which cannot exist
progress (SubType Unit Sunit)                                                             = step β-SubType-Unit
progress (SubType (Var ()) A'≤A)
progress (SubType (SubType expr:A' x) A'≤A)                                               = step γ-SubType
progress (SubType (Lab-I{l}{snl} l∈snl) (Slabel{snl' = snl'} snl⊆snl'))                  = step γ-Lab-I
progress (SubType (Lab-E expr:A' x) A'≤A) with progress (Lab-E expr:A' x)
...                                           | step a                                    = step (ξ-SubType a)
...                                           | done ()                   -- Lab-E without SubType can't be a value
progress (SubType (Abs expr:A') (Sfun A'≤A B≤B')) with progress (Abs expr:A')
...                                           | step a                                    = step (ξ-SubType a)
...                                           | done Vfun                                 = step γ-Abs
progress (SubType (App expr:A' expr:A'') A'≤A) with progress (expr:A')
...                                           | step a                                    = step (ξ-SubType (ξ-App1 a))
...                                           | done Vfun with progress (expr:A'')
...                                              | step b                                 = step (ξ-SubType (ξ-App2 Vfun b))
...                                              | done val                               = step (ξ-SubType (β-App val))
progress (Lab-I l∈snl)                                                                    = done Vlab 
progress (Lab-E expr cases) with progress expr
...                                           | step expr~>expr'                          = step (ξ-Lab-E expr~>expr')
...                                           | done Vlab                                 = step (β-Lab-E)
progress (Abs expr)                                                                       = done Vfun
progress (App L M) with progress L
...                                           | step L~>L'                                = step (ξ-App1 L~>L')
...                                           | done Vfun with progress M
...                                              | step M~>M'                             = step (ξ-App2 Vfun M~>M')
...                                              | done x                                 = step (β-App x)

----- GENERATION OF EVALUATION SEQUENCES -----
----- Idea and implementation from PLFA

data Gas : Set where
  gas : ℕ → Gas

data Finished {n φ A} (N : LExpr{n} φ A) : Set where
  done : Val' A N → Finished N
  out-of-gas : Finished N

data Steps : ∀ {n A} → LExpr{n} [] A → Set where
  steps : ∀ {n A} {L N : LExpr{n} [] A}
          → L ~>> N
          → Finished N
          → Steps L

eval' : ∀ {n A} → Gas → (L : LExpr{n} [] A) → Steps L
eval' (gas zero) L              = steps (L ∎) out-of-gas
eval' (gas (suc m)) L with progress L
...      | done VL              = steps (L ∎) (done VL)
...      | step {M} L~>M with eval' (gas m) M
...         | steps M~>>N fin   = steps (L ~>⟨ L~>M ⟩ M~>>N) fin 


-- Examples
-- (λ (x : Unit) → x) (Unit)
ex0 : LExpr{suc zero} [] Tunit
ex0 = App (Abs (Unit{φ = (Tunit ∷ [])})) (Unit)

_ : ex0 ~>> Unit
_ =
  begin
    App (Abs (Unit)) (Unit)
  ~>⟨ β-App (Vunit) ⟩
    Unit
  ∎


ex1 : LExpr{suc zero} [] Tunit
ex1 = Lab-E (Lab-I (x∈⁅x⁆ zero)) λ l x → Unit

_ : ex1 ~>> Unit
_ =
  begin
    Lab-E (Lab-I (x∈⁅x⁆ zero)) (λ l x → Unit)
  ~>⟨ β-Lab-E ⟩
    Unit
  ∎

ex2 : LExpr{suc zero} [] Tunit
ex2 = App (SubType (Abs Unit) (Sfun Sunit Sunit)) Unit

-- proof that {inside, outside} ⊆ {inside, inside}
-- i.e.                     {0} ⊆ {0, 1}
x⊆y : (inside ∷ outside ∷ []) ⊆ (inside ∷ inside ∷ [])
x⊆y {.zero}    here      = here
x⊆y {.(suc (suc _))} (there (there ()))

-- proof that zero is in (inside ∷ outside ∷ [])
-- i.e.                    0 ∈ {0}
l∈snl : (zero) ∈ (inside ∷ outside ∷ [])
l∈snl = here

-- [({0, 1}→{0, 1} <: {0}→{0, 1}) (λ x : {0, 1} . x)] 0
ex3 : LExpr{suc (suc zero)} [] (Tlabel (inside ∷ inside ∷ []))
ex3 = App (SubType (Abs{A = Tlabel (inside ∷ inside ∷ [])}  (Var here)) (Sfun (Slabel{snl = (inside ∷ outside ∷ [])} x⊆y) (≤-refl (Tlabel (inside ∷ inside ∷ [])))))
          (Lab-I l∈snl)


