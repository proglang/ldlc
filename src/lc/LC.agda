-- simply-typed λ-calculus w/ DeBruijn indices

module LC where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Integer
open import Data.List
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

open import Auxiliary

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
  there : {n : ℕ} {T₁ T₂ : Ty} {Γ : Env} → n ∶ T₁ ∈ Γ → (ℕ.suc n) ∶ T₁ ∈ (T₂ ∷ Γ)

data _⊢_∶_ : Env → Exp → Ty → Set where
  TVar : {n : ℕ} {Γ : Env} {T : Ty} → n ∶ T ∈ Γ → Γ ⊢ (Var n) ∶ T
  TAbs : {Γ : Env} {T₁ T₂ : Ty} {e : Exp} → (T₁ ∷ Γ) ⊢ e ∶ T₂ → Γ ⊢ (Abs e) ∶ (Fun T₁ T₂)
  TApp : {Γ : Env} {T₁ T₂ : Ty} {e₁ e₂ : Exp} → Γ ⊢ e₁ ∶ (Fun T₁ T₂) → Γ ⊢ e₂ ∶ T₁ → Γ ⊢ (App e₁ e₂) ∶ T₂

-- denotational semantics

Valᵈ : Ty → Set
Valᵈ (Fun Ty₁ Ty₂) = (Valᵈ Ty₁) → (Valᵈ Ty₂)

access : {n : ℕ} {Γ : Env} {T : Ty} → n ∶ T ∈ Γ → All Valᵈ Γ → Valᵈ T
access here (V ∷ Γ) = V
access (there J) (V ∷ Γ) = access J Γ

eval : {Γ : Env} {T : Ty} {e : Exp} → Γ ⊢ e ∶ T → All Valᵈ Γ → Valᵈ T
eval (TVar c) Val-Γ = access c Val-Γ 
eval (TAbs TJ) Val-Γ = λ V → eval TJ (V ∷ Val-Γ)
eval (TApp TJ TJ₁) Val-Γ = (eval TJ Val-Γ) (eval TJ₁ Val-Γ)


-- operational semantics (call-by-value)

-- shifting, required to avoid variable-capturing in substitution
-- see Pierce 2002, pg. 78/79
↑_,_[_] : ℤ → ℕ → Exp → Exp
↑ d , c [ Var x ] with (x Data.Nat.<? c)
... | yes p = Var x
... | no ¬p = Var (∣ (ℤ.pos x) Data.Integer.+ d ∣)  -- should always be positive anyway
↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
↑ d , c [ App t t₁ ] = App (↑ d , c [ t ]) (↑ d , c [ t₁ ])

-- shifting below threshold, required for swapping lemma
↑<_,_[_] : ℤ → ℕ → Exp → Exp
↑< d , c [ Var x ] with (x Data.Nat.<? c)
... | yes p = Var (∣ (ℤ.pos x) Data.Integer.+ d ∣)
... | no ¬p = Var x
↑< d , c [ Abs e ] = Abs (↑< d , (c ∸ 1) [ e ]) -- ↑< -1 , 1 (Abs (Var 0)) → Abs (↑< -1 , 0 (Var 0)) → Abs (Var 0)
↑< d , c [ App e e₁ ] = App (↑< d , c [ e ]) (↑< d , c [ e₁ ])

-- shorthands
↑¹[_] : Exp → Exp
↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

↑⁻¹[_] : Exp → Exp
↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

-- properties of shifting
↑-var-refl : {d : ℤ} {c : ℕ} {x : ℕ} {le : ℕ.suc x Data.Nat.≤ c} → ↑ d , c [ Var x ] ≡ Var x
↑-var-refl {d} {c} {x} {le}
  with (x Data.Nat.<? c)
... | no ¬p = contradiction le ¬p
... | yes p = refl

↑⁻¹ₖ[↑¹ₖ[s]]≡s : {e : Exp} {k : ℕ} → ↑ -[1+ 0 ] , k [ ↑ + 1 , k [ e ] ] ≡ e
↑⁻¹ₖ[↑¹ₖ[s]]≡s {Var x} {k}
  with (x Data.Nat.<? k)
-- x < k
--  => ↑⁻¹ₖ(↑¹ₖ(Var n)) = ↑⁻¹ₖ(Var n) = Var n
... | yes p = ↑-var-refl{ -[1+ 0 ]}{k}{x}{p}
-- x ≥ k
--  => ↑⁻¹ₖ(↑¹ₖ(Var n)) = ↑⁻¹ₖ(Var |n + 1|) = Var (||n + 1| - 1|) = Var n
... | no ¬p with (¬[x≤k]⇒¬[sucx≤k] ¬p)
...   | ¬p' with (x Data.Nat.+ 1) Data.Nat.<? k
...     | yes pp = contradiction pp ¬p'
...     | no ¬pp rewrite (∣nℕ+1⊖1∣≡n{x}) = refl
↑⁻¹ₖ[↑¹ₖ[s]]≡s {Abs e} {k} = cong Abs ↑⁻¹ₖ[↑¹ₖ[s]]≡s
↑⁻¹ₖ[↑¹ₖ[s]]≡s {App e e₁} = cong₂ App ↑⁻¹ₖ[↑¹ₖ[s]]≡s ↑⁻¹ₖ[↑¹ₖ[s]]≡s

-- ↑ᵏ[↑ᵈ]≡↑ᵏ⁺ᵈ : {k d : ℤ} {c : ℕ} {e : Exp} → ↑ k , c [ ↑ d , c [ e ] ] ≡ ↑ k Data.Integer.+ d , c [ e ]

-- substitution
-- see Pierce 2002, pg. 80
[_↦_]_ : ℕ → Exp → Exp → Exp
[ k ↦ s ] Var x with (_≡ᵇ_ x k)
... | false = Var x
... | true = s
[ k ↦ s ] Abs t = Abs ([ ℕ.suc k ↦ ↑¹[ s ] ] t)
[ k ↦ s ] App t t₁ = App ([ k ↦ s ] t) ([ k ↦ s ] t₁)


data Val : Exp → Set where
  VFun : {e : Exp} → Val (Abs e)

-- reduction relation
data _⇒_ : Exp → Exp → Set where
  ξ-App1 : {e₁ e₁' e₂ : Exp} → e₁ ⇒ e₁' → App e₁ e₂ ⇒ App e₁' e₂
  ξ-App2 : {e e' v : Exp} → Val v → e ⇒ e' → App v e ⇒ App v e'
  β-App : {e v : Exp} → Val v → (App (Abs e) v) ⇒ (↑⁻¹[ ([ 0 ↦ ↑¹[ v ] ] e) ])


-- progress theorem, i.e. a well-typed closed expression is either a value
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


swap-subst : {T S : Ty} {Γ Δ : Env} {e : Exp} (j : ((S ∷ Δ) ++ Γ) ⊢ e ∶ T) → (Δ ++ (S ∷ Γ)) ⊢ ↑< -[1+ 0 ] , length Δ [ [ 0 ↦ Var (length Δ) ] e ] ∶ T

-- have to "remember" where S was
-- cannot substitute its position for zero, since ↑< would increase that
-- cannot do ↑< and then subtitute its position for zero, since its (position - 1) would be affected aswell
-- ugly fix: cache in unreachable variable l(Δ) + l(Γ) + 1
swap-subst-inv : {T S : Ty} {Γ Δ : Env} {e : Exp} (j : (Δ ++ (S ∷ Γ)) ⊢ e ∶ T) → (S ∷ (Δ ++ Γ)) ⊢ [ (length Δ Data.Nat.+ length Γ Data.Nat.+ 1) ↦ Var 0 ] (↑< +[1+ 0 ] , (length Δ) [ [ (length Δ) ↦ (Var (length Δ Data.Nat.+ length Γ Data.Nat.+ 1)) ] e ] ) ∶ T

ext-var : {n : ℕ} {Γ Δ : Env} {S : Ty} → n ∶ S ∈ Γ → (n Data.Nat.+ (length Δ)) ∶ S ∈ (Δ ++ Γ)
ext-var {n} {Γ} {[]} {S} j rewrite (n+length[]≡n{A = Ty}{n = n}) = j
ext-var {n} {Γ} {T ∷ Δ} {S} j rewrite (+-suc n (foldr (λ _ → ℕ.suc) 0 Δ)) = there (ext-var j)

ext : {Γ Δ : Env} {S : Ty} {s : Exp} → Γ ⊢ s ∶ S → (Δ ++ Γ) ⊢ ↑ (ℤ.pos (length Δ)) , 0 [ s ] ∶ S
ext (TVar {n} x) = TVar (ext-var x)
ext {Γ} {Δ} {Fun T₁ T₂} {Abs e} (TAbs j) = {!!} --  TAbs (swap-subst-inv{T₂}{T₁}{Γ}{Δ} (ext{T₁ ∷ Γ}{Δ}{s = e} {!!}))
ext (TApp j j₁) = {!!}

-- preservation under substitution
preserve-subst : {T S : Ty} {Γ Δ : Env} {e s : Exp} (j : (Δ ++ (S ∷ Γ)) ⊢ e ∶ T) (j' : Γ ⊢ s ∶ S) → Γ ⊢ ↑ -[1+ 0 ] ,  length Δ [ [ length Δ ↦ ↑ (ℤ.pos (ℕ.suc (length Δ))) , 0 [ s ] ] e ] ∶ T
preserve-subst {Γ = Γ} {Δ = []} {s = s} (TVar here) j' rewrite (↑⁻¹ₖ[↑¹ₖ[s]]≡s{s}{0}) = j'
preserve-subst {Γ = Γ} {Δ = []} (TVar (there x)) j' = TVar x
preserve-subst {Γ = Γ} {Δ = x₁ ∷ Δ} (TVar x) j' = {!!}
preserve-subst {T} {S} {Γ} {Δ} {Abs e'} {s} (TAbs{T₁ = T₁}{T₂} j) j'  = TAbs {!!}
preserve-subst (TApp j j₁) j' = {!!}

-- preservation theorem, i.e. a well-typed expression reduces to a well-typed expression
preserve : {T : Ty} {Γ : Env} (e e' : Exp) (j : Γ ⊢ e ∶ T) (r : e ⇒ e') → Γ ⊢ e' ∶ T
preserve (App s₁ s₂) .(App _ s₂) (TApp j j') (ξ-App1{e₁' = s₁'} r) = TApp (preserve s₁ s₁' j r) j' -- IH on inner reduction
preserve (App s₁ s₂) .(App s₁ _) (TApp j j') (ξ-App2{e' = s₂'} x r) = TApp j (preserve s₂ s₂' j' r)
preserve (App (Abs e) s')  .(↑⁻¹[ [ 0 ↦ ↑¹[ s' ] ] e ]) (TApp (TAbs j) j') (β-App x) = preserve-subst{Δ = []} j j'



{- intermingling of substitution and typing?
--
data _∶_∈_ : ℕ → Ty → Env → Set where
  here : {T : Ty} {Γ : Env} → 0 ∶ T ∈ (T ∷ Γ)
  there : {n : ℕ} {T₁ T₂ : Ty} {Γ : Env} → n ∶ T₁ ∈ Γ → (suc n) ∶ T₁ ∈ (T₂ ∷ Γ) 

-- alt. substitution, capturing the idea that DeBruijn indices correspond
-- to positions from top of the environemnt (when typed)
[_↦'_]_ : ℕ → Exp → Exp → Exp
[ k ↦' s ] Abs e = Abs ([ (suc k) ↦' s ] e) -- ↯ does not avoid capture in s
[ k ↦' s ] App e e₁ = App ([ k ↦' s ] e) ([ k ↦' s ] e₁)
[ zero ↦' s ] Var zero = s
[ suc k ↦' s ] Var zero = Var zero
[ zero ↦' s ] Var (suc x) = Var x
[ suc k ↦' s ] Var (suc x) = [ k ↦' s ] (Var x)

--
preserve-subst : {T S : Ty} {Γ : Env} {e s : Exp} (j : (S ∷ Γ) ⊢ e ∶ T) (j' : Γ ⊢ s ∶ S) → Γ ⊢ ([ 0 ↦' s ] e) ∶ T
preserve-subst (TVar {zero} here) j' = j'
preserve-subst {T} {S} {Γ} {Var (suc n)} {s} (TVar {suc n} (there x)) j' = TVar x


==> had wrong β-App definition
-}
