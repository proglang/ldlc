-- labeled λ-calculus

module LLC where

open import Data.List
open import Data.List.All
open import Data.List.Base
open import Data.Vec hiding (_++_)
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_≤_)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Fin hiding (_≤_)
open import Data.Product
open import Data.Empty
open import Relation.Binary

-- definitions

data Ty (nl : ℕ) : Set where   -- nl ~ (max.) number of labels
  Tunit : Ty nl
  Tlabel : Subset nl → Ty nl
  Tfun : Ty nl → Ty nl → Ty nl

TEnv : ℕ → Set
TEnv nl = List (Ty nl)

data _≤_ {nl} : Ty nl → Ty nl → Set where
  Sunit  : Tunit ≤ Tunit
  Slabel : ∀ {snl snl'} → snl ⊆ snl' → (Tlabel snl) ≤ (Tlabel snl')
  Sfun   : ∀ {A A' B B'} → A' ≤ A → B ≤ B' → (Tfun A B) ≤ (Tfun A' B')

data _∈`_ {nl : ℕ} : Ty nl → TEnv nl → Set where
  here  : ∀ {lt φ} → lt ∈` (lt ∷ φ)
  there : ∀ {lt lt' φ} → lt ∈` φ → lt ∈` (lt' ∷ φ)

data Exp {nl : ℕ} : TEnv nl → Ty nl → Set where
  Unit     : ∀ {φ} → Exp φ Tunit
  Var      : ∀ {φ t} → (x : t ∈` φ) → Exp φ t   -- t ∈` φ gives us the position of "x" in env
  SubType  : ∀ {A A' φ} →  Exp φ A → A ≤ A'
                        →  Exp φ A'
  Lab-I    : ∀ {l snl φ} → l ∈ snl → Exp φ (Tlabel snl)
  Lab-E    : ∀ {snl φ B} → Exp φ (Tlabel snl)
                         → (∀ l → l ∈ snl → Exp φ B) 
                         → Exp φ B
  Abs     : ∀ {B A φ} → Exp (A ∷ φ) B
                      → Exp φ (Tfun A B)
  App     : ∀ {A B φ} → Exp φ (Tfun A B)
                      → (ex : Exp φ A)
                      → Exp φ B

-- subtyping properties

≤-trans : ∀ {nl} {t t' t'' : Ty nl} → t ≤ t' → t' ≤ t'' → t ≤ t''
≤-trans Sunit Sunit = Sunit 
≤-trans (Slabel snl⊆snl') (Slabel snl'⊆snl'') = Slabel (⊆-trans snl⊆snl' snl'⊆snl'')
≤-trans (Sfun a'≤a b≤b') (Sfun a''≤a' b'≤b'') = Sfun (≤-trans a''≤a' a'≤a) (≤-trans b≤b' b'≤b'')

≤-refl : ∀ {nl} → (t : Ty nl) → t ≤ t
≤-refl Tunit = Sunit
≤-refl (Tlabel x) = Slabel (⊆-refl)
≤-refl (Tfun t t') = Sfun (≤-refl t) (≤-refl t')
  
-- big-step semantics

Val : ∀ {nl} → Ty nl → Set
Val Tunit = Data.Unit.⊤
Val {nl} (Tlabel snl) = Σ (Fin nl) (λ l → l ∈ snl)
Val (Tfun ty ty₁) = (Val ty) → (Val ty₁)

coerce : ∀ {nl} {t t' : Ty nl} → t ≤ t' → Val t → Val t' -- supertype of a Value is also a Value
coerce Sunit t = tt
coerce (Slabel snl⊆snl') (Finnl , Finnl∈snl) = (Finnl , (snl⊆snl' Finnl∈snl))
coerce (Sfun A'≤A B≤B') f = λ x → coerce B≤B' (f (coerce A'≤A x))

access : ∀ {nl} {t : Ty nl} {φ} → t ∈` φ → All Val φ → Val t
access here (px ∷ ρ) = px
access (there x) (px ∷ ρ) = access x ρ

eval : ∀ {nl φ t} → Exp {nl} φ t → All Val φ → Val t
eval Unit ϱ = tt
eval (Var x) ϱ = access x ϱ
eval (SubType e a≤a') ϱ = coerce a≤a' (eval e ϱ)
eval (Lab-I {l} l∈snl) ϱ = l , (l∈snl)
eval (Lab-E e case) ϱ with eval e ϱ
... | lab , lab∈nl = eval (case lab lab∈nl) ϱ
eval (Abs e) ϱ = λ x → eval e (x ∷ ϱ)
eval (App e e₁) ϱ = (eval e ϱ) (eval e₁ ϱ)


-- small-step semantics
-- substitution taken from PLFA

ext : ∀ {nl φ ψ} → (∀ {A : Ty nl} → A ∈` φ → A ∈` ψ)
                 → (∀ {A B} → A ∈` (B ∷ φ) → A ∈` (B ∷ ψ))
ext ϱ here      = here
ext ϱ (there x) = there (ϱ x)

rename : ∀ {nl φ ψ} → (∀ {A : Ty nl} → A ∈` φ → A ∈` ψ)
                    → (∀ {A} → Exp φ A → Exp ψ A)
rename ϱ Unit                    = Unit
rename ϱ (Var x)                 = Var (ϱ x)
rename ϱ (SubType expr:A' A'≤A)  = SubType (rename ϱ expr:A') A'≤A
rename {ψ} ϱ (Lab-I l∈snl)       = Lab-I {ψ} l∈snl
rename ϱ (Lab-E expr:snl case)   = Lab-E (rename ϱ expr:snl)
                                   λ l l∈snl → (rename ϱ (case l l∈snl))
rename ϱ (Abs expr:B)            = Abs (rename (ext ϱ) expr:B)
rename ϱ (App expr:A->B expr:A)  = App (rename ϱ expr:A->B) (rename ϱ expr:A)

exts : ∀ {nl φ ψ} → (∀ {A : Ty nl} → A ∈` φ → Exp ψ A)
                  → (∀ {A B} → A ∈` (B ∷ φ) → Exp (B ∷ ψ) A)
exts ϱ here      = Var (here)
exts ϱ (there x) = rename there (ϱ x)

subst : ∀ {nl φ ψ} → (∀ {A : Ty nl} → A ∈` φ → Exp ψ A) -- simult. substitution
                   → (∀ {A : Ty nl} → Exp φ A → Exp ψ A)
subst ϱ Unit                       = Unit
subst ϱ (Var x)                    = ϱ x
subst ϱ (SubType expr:A' A'≤A)     = SubType (subst ϱ expr:A') A'≤A
subst {ψ} ϱ (Lab-I l∈snl)          = Lab-I {ψ} l∈snl
subst ϱ (Lab-E expr:snl case)      = Lab-E (subst ϱ expr:snl)
                                     λ l l∈snl → (subst ϱ (case l l∈snl))
subst ϱ (Abs expr:B)               = Abs (subst (exts ϱ) expr:B)
subst ϱ (App expr:A→B expr:A)     = App (subst ϱ expr:A→B) (subst ϱ expr:A)

_[[_]] : ∀ {nl φ} {A B : Ty nl} → Exp (B ∷ φ) A → Exp φ B → Exp φ A -- single substitution
_[[_]] {nl} {φ} {A} {B} N M = subst {nl} {B ∷ φ} {φ} ϱ {A} N
  where
  ϱ : ∀ {A} → A ∈` (B ∷ φ) → Exp φ A
  ϱ here      = M
  ϱ (there x) = Var x 

expansionlemma : ∀ {nl} {lt : Ty nl} {φ φ'} → lt ∈` φ' → lt ∈` (φ' ++ φ)
expansionlemma here      = here
expansionlemma (there x) = there (expansionlemma x)

extensionlemma : ∀ {nl} {lt : Ty nl} {φ φ'} → lt ∈` φ → lt ∈` (φ' ++ φ)
extensionlemma {φ' = []}        here     = here
extensionlemma {φ' = x ∷ xs}   here     = there (extensionlemma{φ' = xs} here)
extensionlemma {φ' = []}       (there y) = there y
extensionlemma {φ' = x ∷ xs}  (there y) = there (extensionlemma {φ' = xs} (there y))

inextdebr : ∀ {nl} {B A : Ty nl} {φ' φ} → B ∈` (φ' ++ φ) → B ∈` (φ' ++ (A ∷ φ))
inextdebr {φ' = []} here           = there here
inextdebr {φ' = []} (there x)      = there (there x)
inextdebr {φ' = x ∷ xs} here      = here
inextdebr {φ' = x ∷ xs} (there y) = there (inextdebr{φ' = xs} y)

inext : ∀ {nl} {φ φ'} {A B : Ty nl} → Exp (φ' ++ φ) B → Exp (φ' ++ (A ∷ φ)) B
inext Unit                                 = Unit
inext {φ' = φ'} (Var x)                    = Var (inextdebr{φ' = φ'} x)
inext {φ = φ}{φ' = φ'} (SubType expr b≤b') = SubType (inext{φ = φ}{φ' = φ'} expr) b≤b'
inext (Lab-I x)                            = Lab-I x
inext {φ = φ} {φ' = φ'} (Lab-E x x₁)       = Lab-E (inext{φ = φ}{φ' = φ'} x) λ l x₂ → inext{φ = φ}{φ' = φ'} (x₁ l x₂)
inext {nl} {φ} {φ'} (Abs{A = A°} x)        = Abs (inext{φ = φ}{φ' = A° ∷ φ'} x)
inext {φ = φ} {φ' = φ'} (App x x₁)         = App (inext{φ = φ}{φ' = φ'} x) (inext{φ = φ}{φ' = φ'} x₁)

debrsub : ∀ {nl} {B B' A A' : Ty nl} {φ' φ} → B ∈` (φ' ++ (A ∷ φ)) → A' ≤ A → B ≤ B' → Exp (φ' ++ (A' ∷ φ)) B'
debrsub {φ' = []}  here a'≤a b≤b'          = SubType (Var here) (≤-trans a'≤a b≤b')
debrsub {φ' = []} (there x) a'≤a b≤b'      = SubType (Var (there x)) b≤b'
debrsub {φ' = x ∷ xs} here a'≤a b≤b'      = SubType (Var (here)) b≤b'
debrsub {φ' = x ∷ xs} (there z) a'≤a b≤b' = inext{φ' = []}{A = x} (debrsub{φ' = xs} z a'≤a b≤b')

typesub : ∀ {nl φ φ' A B A' B'} → Exp{nl} (φ' ++ (A ∷ φ)) B → A' ≤ A → B ≤ B' → Exp (φ' ++ (A' ∷ φ)) B'  -- subtyping "substitution"
typesub Unit a'≤a Sunit = Unit
typesub {φ = φ} {φ'} {A} {B} {A'} {B'} (Var x) a'≤a b≤b'                        = debrsub{φ' = φ'}{φ = φ} x a'≤a b≤b'
typesub {nl} {φ} {φ'} (SubType expr x) a'≤a b≤b'                                = typesub{nl}{φ}{φ'} expr a'≤a (≤-trans x b≤b')
typesub (Lab-I l∈snl) a'≤a b≤b'                                                 = SubType (Lab-I l∈snl) b≤b'
typesub {nl} {φ} {φ'} (Lab-E{snl = snl} expr cases) a'≤a b≤b'                   = Lab-E (typesub{nl}{φ}{φ'} expr a'≤a (≤-refl (Tlabel snl))) λ l x → typesub{nl}{φ}{φ'} (cases l x) a'≤a b≤b'
typesub {φ' = φ'}{A = A}{B = A°→B°}{A' = A'}{B' = A°°→B°°} (Abs{A = A°} expr) a'≤a (Sfun{A = .A°}{A' = A°°}{B = B°}{B' = B°°} A°°≤A° B°≤B°°)
                                                                                = SubType (Abs (typesub{φ' = A° ∷ φ'} expr a'≤a B°≤B°°)) (Sfun A°°≤A° (≤-refl B°°))
typesub {nl}{φ}{φ'}{A}{B}{A'}{B'} (App{A = A°}{B = .B} expr expr') a'≤a b≤b'    = SubType (App (typesub{nl}{φ}{φ'} expr a'≤a (≤-refl (Tfun A° B))) (typesub{nl}{φ}{φ'} expr' a'≤a (≤-refl A°))) b≤b'

-- we force values to have type SubType, since Lab-I results in expressions with type {l}
-- and we want to keep the information about which subset l is in
data Val' {n φ} : (t : Ty n) → Exp {n} φ t → Set where
  Vunit :  Val' (Tunit) Unit
  Vlab : ∀ {l snl l∈snl} → Val' (Tlabel snl) (Lab-I{l = l}{snl} l∈snl)
  Vfun : ∀ {A B exp} → Val' (Tfun A B) (Abs exp)

data _~>_ {n φ} : {A : Ty n} → Exp {n} φ A → Exp {n} φ A → Set where  -- small-steps semantics relation

  ξ-App1 : ∀ {A B} {L L' : (Exp φ (Tfun B A))} {M}
           → L ~> L'
           → App L M ~> App L' M
  
  ξ-App2 : ∀ {A B} {M M' : Exp φ A} {L : Exp φ (Tfun A B)}
           → Val' (Tfun A B) L
           → M ~> M'
           → App L M ~> App L M'

  β-App : ∀ {A B M exp} 
          → Val' B M
          → App{B = A} (Abs exp) M
             ~>
             (exp [[ M ]])

  ξ-SubType : ∀ {A A' A≤A' } {L L' : Exp φ A}
              → L ~> L'
              → SubType{A = A}{A'} L A≤A' ~> SubType{A = A} L' A≤A'

  ξ-Lab-E : ∀ {A snl} {L L' : Exp φ (Tlabel snl)} {cases}
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

  γ-Abs : ∀ {A B A' B' e} {A'≤A : A' ≤ A} {B≤B' : B ≤ B'}
          → SubType (Abs{B = B}{A = A} e) (Sfun A'≤A B≤B')
             ~>
             Abs{B = B'}{A = A'} (typesub{φ' = []} e A'≤A B≤B')

  γ-SubType : ∀ {A A' A'' A≤A' A'≤A'' expr}
              → SubType{A = A'}{A' = A''} (SubType{A = A} expr A≤A') A'≤A''
                 ~>
                 SubType expr (≤-trans A≤A' A'≤A'')

  -- either we define Unit values to be SubTypes of Unit≤Unit; or we introducte the following rule
  β-SubType-Unit : SubType Unit Sunit
                   ~>
                   Unit

-- properties of small-step evaluation
infix 2 _~>>_ -- refl. transitive closure
infix 1 begin_
infixr 2 _~>⟨_⟩_
infix 3 _∎

data _~>>_ : ∀ {n} {φ} {A : Ty n} → Exp φ A → Exp φ A → Set where
  _∎ : ∀ {n φ} {A : Ty n} (L : Exp φ A)
       → L ~>> L

  _~>⟨_⟩_ : ∀ {n φ} {A : Ty n} (L : Exp φ A) {M N : Exp φ A}
           → L ~> M
           → M ~>> N
           → L ~>> N

begin_ : ∀ {n φ} {A : Ty n} {M N : Exp φ A} → M ~>> N → M ~>> N
begin M~>>N = M~>>N


-- progress theorem
data Progress {n A} (M : Exp{n} [] A) : Set where
  step : ∀ {N : Exp [] A} → M ~> N → Progress M
  done : Val' A M → Progress M

-- proof
progress : ∀ {n A} → (M : Exp{n} [] A) → Progress M
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

-- generation of evaluation sequences
-- taken from plfa

data Gas : Set where
  gas : ℕ → Gas

data Finished {n φ A} (N : Exp{n} φ A) : Set where
  done : Val' A N → Finished N
  out-of-gas : Finished N

data Steps : ∀ {n A} → Exp{n} [] A → Set where
  steps : ∀ {n A} {L N : Exp{n} [] A}
          → L ~>> N
          → Finished N
          → Steps L

eval' : ∀ {n A} → Gas → (L : Exp{n} [] A) → Steps L
eval' (gas zero) L              = steps (L ∎) out-of-gas
eval' (gas (suc m)) L with progress L
...      | done VL              = steps (L ∎) (done VL)
...      | step {M} L~>M with eval' (gas m) M
...         | steps M~>>N fin   = steps (L ~>⟨ L~>M ⟩ M~>>N) fin 


-- examples
-- (λ (x : Unit) → x) (Unit)
ex0 : Exp{suc zero} [] Tunit
ex0 = App (Abs (Unit{φ = (Tunit ∷ [])})) (Unit)

_ : ex0 ~>> Unit
_ =
  begin
    App (Abs (Unit)) (Unit)
  ~>⟨ β-App (Vunit) ⟩
    Unit
  ∎


ex1 : Exp{suc zero} [] Tunit
ex1 = Lab-E (Lab-I (x∈⁅x⁆ zero)) λ l x → Unit

_ : ex1 ~>> Unit
_ =
  begin
    Lab-E (Lab-I (x∈⁅x⁆ zero)) (λ l x → Unit)
  ~>⟨ β-Lab-E ⟩
    Unit
  ∎

ex2 : Exp{suc zero} [] Tunit
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
ex3 : Exp{suc (suc zero)} [] (Tlabel (inside ∷ inside ∷ []))
ex3 = App (SubType (Abs{A = Tlabel (inside ∷ inside ∷ [])}  (Var here)) (Sfun (Slabel{snl = (inside ∷ outside ∷ [])} x⊆y) (≤-refl (Tlabel (inside ∷ inside ∷ [])))))
          (Lab-I l∈snl)


