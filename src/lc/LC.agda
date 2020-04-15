-- simply-typed λ-calculus w/ DeBruijn indices

module LC where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Bool.Properties hiding (≤-trans ; <-trans ; ≤-refl)
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

-- shifting in range [n, m]; by def. m < n implies no shift
↑[_,_]_[_] : ℕ → ℕ → ℤ → Exp → Exp
↑[ n , m ] d [ Var x ]
  with (x Data.Nat.<? n)
... | yes p = Var x
... | no ¬p with (m Data.Nat.<? x)
...   | yes p' = Var x
...   | no ¬p' = Var (∣ (ℤ.pos x) Data.Integer.+ d ∣)
↑[ n , m ] d [ Abs e ] = Abs (↑[ ℕ.suc n , ℕ.suc m ] d [ e ]) 
↑[ n , m ] d [ App e e₁ ] = App (↑[ n , m ] d [ e ]) (↑[ n , m ] d [ e₁ ])

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

↑[]-var-refl-< : {n m x : ℕ} {d : ℤ} {le : x Data.Nat.< n} → ↑[ n , m ] d [ Var x ] ≡ Var x
↑[]-var-refl-< {n} {m} {x} {d} {le}
  with (x Data.Nat.<? n)
... | yes p = refl
... | no ¬p = contradiction le ¬p

↑[]-var-refl-> : {n m x : ℕ} {d : ℤ} {le : m Data.Nat.< x} → ↑[ n , m ] d [ Var x ] ≡ Var x
↑[]-var-refl-> {n} {m} {x} {d} {le}
  with (x Data.Nat.<? n)
... | yes p = refl
... | no p with (m Data.Nat.<? x)
...   | no ¬q = contradiction le ¬q
...   | yes q = refl

↑¹-var : {x : ℕ} → ↑¹[ Var x ] ≡ Var (ℕ.suc x)
↑¹-var {zero} = refl
↑¹-var {ℕ.suc x} rewrite (sym (n+1≡sucn{x Data.Nat.+ 1})) | (sym (n+1≡sucn{x})) = cong ↑¹[_] (↑¹-var{x})

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
[ k ↦ s ] Var x with (Data.Nat._≟_ x k)
... | yes p = s
... | no ¬p = Var x
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

--

data extract-env-or {Δ Γ : Env} {T : Ty} {x : ℕ} : Set where
  in-Δ : x ∶ T ∈ Δ → extract-env-or
  -- x ≥ length Δ is required to make sure x is really in Γ and not also in Δ, e.g.
  -- x = 1, Δ = (S ∷ T), Γ = (T ∷ Γ'); here 1 ∶ T ∈ Δ as well as (1 ∸ 2) ≡ 0 ∶ T ∈ Γ
  in-Γ : (x Data.Nat.≥ length Δ) → (x ∸ length Δ) ∶ T ∈ Γ → extract-env-or

extract : {Δ Γ : Env} {T : Ty} {x : ℕ} (j : x ∶ T ∈ (Δ ++ Γ)) → extract-env-or{Δ}{Γ}{T}{x}
extract {[]} {Γ} {T} {x} j = in-Γ z≤n j
extract {x₁ ∷ Δ} {Γ} {.x₁} {.0} here = in-Δ here
extract {x₁ ∷ Δ} {Γ} {T} {ℕ.suc x} (there j)
  with extract {Δ} {Γ} {T} {x} j
... | in-Δ j'  = in-Δ (there j')
... | in-Γ ge j'' = in-Γ (s≤s ge) j''

-- alt.: include x < length Δ in def. of in-Δ
var-env-< : {Γ : Env} {T : Ty} {n : ℕ} (j : n ∶ T ∈ Γ) → n Data.Nat.< (length Γ)
var-env-< {.(T ∷ _)} {T} {.0} here = s≤s z≤n
var-env-< {.(_ ∷ _)} {T} {.(ℕ.suc _)} (there j) = s≤s (var-env-< j)

var-subst-refl : {n m : ℕ} {neq : n ≢ m} {e : Exp} → [ n ↦ e ] (Var m) ≡ (Var m)
var-subst-refl {n} {m} {neq} {e}
  with Data.Nat._≟_ n m | map′ (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n) (Data.Bool.Properties.T? (m ≡ᵇ n))
... | yes p | _ = contradiction p neq
... | no ¬p | yes q = contradiction q (≢-sym ¬p)
... | no ¬p | no ¬q = refl

ext-behind : {Δ Γ : Env} {T : Ty} {x : ℕ} → x ∶ T ∈ Δ → x ∶ T ∈ (Δ ++ Γ)
ext-behind here = here
ext-behind (there j) = there (ext-behind j)

ext-front : {n : ℕ} {Γ Δ : Env} {S : Ty} → n ∶ S ∈ Γ → (n Data.Nat.+ (length Δ)) ∶ S ∈ (Δ ++ Γ)
ext-front {n} {Γ} {[]} {S} j rewrite (n+length[]≡n{A = Ty}{n = n}) = j
ext-front {n} {Γ} {T ∷ Δ} {S} j rewrite (+-suc n (foldr (λ _ → ℕ.suc) 0 Δ)) = there (ext-front j)

-- some very specific required calculations for swap-subst var case
length-≡ : {Δ ∇ Γ : Env} {S : Ty} → ℕ.suc (length Δ Data.Nat.+ (length Γ Data.Nat.+ length ∇)) ≡ length (Δ ++ S ∷ ∇ ++ Γ)
length-≡ {Δ} {∇} {Γ} {S} rewrite (length[A++B]≡length[A]+length[B]{lzero}{Ty}{Δ}{S ∷ ∇ ++ Γ})
                               | (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{Γ})
                               | (+-suc (length Δ) (length ∇ Data.Nat.+ length Γ))
                               | (+-comm (length ∇) (length Γ)) = refl



length-≡' : {Δ ∇ : Env} {S : Ty} → length (Δ ++ ∇ ++ S ∷ []) ≡ length Δ Data.Nat.+ ℕ.suc (length ∇)
length-≡' {Δ} {∇} {S} rewrite (length[A++B]≡length[A]+length[B]{lzero}{Ty}{Δ}{∇ ++ S ∷ []})
                            | (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{S ∷ []})
                            | (+-suc (length ∇) (0))
                            | (+-identityʳ (length ∇)) = refl


length-≡'' : {Δ ∇ : Env} {S : Ty} → length (Δ ++ ∇ ++ S ∷ []) ≡ ℕ.suc (length ∇ Data.Nat.+ length Δ)
length-≡'' {Δ} {∇} {S} rewrite (cong (ℕ.suc) (+-comm (length ∇) (length Δ)))
                             | (sym (+-suc (length Δ) (length ∇))) = length-≡'{Δ}{∇}{S}  


-- length-≡'{Δ}{∇}{S}

-- y-in-env-rewr : {y : ℕ} {Δ : Env} {T : Ty} (y ∶ T ∈ Δ)

-- we have to "remember" where S was
-- cannot substitute its position for zero, since ↑ would increase that
-- cannot do ↑ and then subtitute its position for zero, since (position - 1) would be affected aswell
-- ugly fix: cache in unreachable variable r
swap-subst : {T S : Ty} {Γ Δ ∇ : Env} {e : Exp} {r : ℕ} {gt : r Data.Nat.> ℕ.suc (length Δ Data.Nat.+ (length Γ Data.Nat.+ length ∇))}
             → (Δ ++ (S ∷ ∇) ++ Γ) ⊢ e ∶ T
             → (Δ ++ ∇ ++ (S ∷ Γ)) ⊢ [ r ↦ Var (length Δ Data.Nat.+ length ∇) ] ↑[ ℕ.suc (length Δ) , length Δ Data.Nat.+ length ∇ ] -[1+ 0 ] [ [ length Δ ↦ Var r ] e ] ∶ T
             -- off by one in the indices in upper limit of shifting: ℕ.suc (length Δ Data.Nat.+ length ∇) was one too far
swap-subst {(Fun T₁ T₂)} {S} {Γ} {Δ} {∇} {(Abs e)} {r} {gt} (TAbs j) rewrite (↑¹-var{length Δ Data.Nat.+ length ∇}) | (n+1≡sucn{r}) = TAbs (swap-subst{T₂}{S}{Γ}{T₁ ∷ Δ}{∇}{e}{ℕ.suc r}{s≤s gt} j)
swap-subst {T} {S} {Γ} {Δ} {∇} {(App e e₁)} {r} {gt} (TApp{T₁ = T₁}{T₂} j j₁) = TApp (swap-subst{Fun T₁ T₂}{S}{Γ}{Δ}{∇}{e}{r}{gt} j) (swap-subst{T₁}{S}{Γ}{Δ}{∇}{e₁}{r}{gt} j₁)
swap-subst {T} {S} {Γ} {Δ} {∇} {Var y} {r} {gt} (TVar j)
  with extract{Δ} {(S ∷ ∇) ++ Γ} {T} {y} j | y Data.Nat.<? (foldr (λ _ → ℕ.suc) 0 Δ) | Data.Nat._≟_ y (length Δ)  
-- y ∈ Δ
... | in-Δ x | yes p | yes q = contradiction q (<⇒≢ p)
... | in-Δ x | yes p | no ¬q  rewrite (↑[]-var-refl-<{ℕ.suc (length Δ)}{length Δ Data.Nat.+ length ∇}{y}{ -[1+ 0 ] }{[k<x]⇒[k<sucx] p})
                                    | (var-subst-refl{r}{y}{≢-sym (<⇒≢ (a<b≤c⇒a<c p (≤-trans (n≤m⇒n≤sucm (m≤m+n (length Δ) (length Γ Data.Nat.+ length ∇))) (<-trans (s≤s ≤-refl) gt))) )}
                                      {Var (foldr (λ _ → ℕ.suc) 0 Δ Data.Nat.+ foldr (λ _ → ℕ.suc) 0 ∇)})
                                      = TVar (ext-behind x)
... | in-Δ x | no ¬p | _ = contradiction (var-env-< x) ¬p
-- y' ∈ ((S ∷ ∇) ++ Γ)
-- here (y @ S), y ≡ length Δ
... | in-Γ ge x | yes p | yes q = contradiction q (<⇒≢ p)
... | in-Γ ge x | no ¬p | yes q = {!!}
-- there (y ∈ ∇ ++ Γ) y > length Δ
... | in-Γ ge x | yes p | no q = contradiction p (≤⇒≯ ge)
... | in-Γ ge x | no p | no q
  with extract{S ∷ ∇} {Γ} {T} {y ∸ length Δ} x
-- y' ∈ ∇
... | in-Δ z = {!!}
-- y ∸ length (Δ) ≥ length (S ∷ ∇) implies  y ∸ length (Δ) + length (Δ) ≥ length (S ∷ ∇) + length (Δ)
-- y ≥ length Δ                    implies  y ∸ length (Δ) + length (Δ) ≡ y
--                                          y ≥ length (S ∷ ∇) + length (Δ) > length S + length Δ
-- hence no shifting takes place
... | in-Γ ge' z
    rewrite (↑[]-var-refl->{ℕ.suc (length Δ)}{length Δ Data.Nat.+ length ∇}{y}{ -[1+ 0 ]}{a<b≤c⇒a<c (s≤s (≤-refl-+-comm{length Δ}{length ∇})) (m≤n∧n≡q⇒m≤q (m≤n⇒m+o≤n+o{o = length Δ} ge') (m∸n+n≡m ge))})
                        | (var-subst-refl{r}{y}{≢-sym (<⇒≢ (<-trans (var-env-< j) (m≤n∧m≡q⇒q≤n gt (cong ℕ.suc (length-≡{Δ}{∇}{Γ}{S})))))}{ Var (foldr (λ _ → ℕ.suc) 0 Δ Data.Nat.+ foldr (λ _ → ℕ.suc) 0 ∇)})
    with ext-front{((y ∸ (length Δ)) ∸ ℕ.suc (length ∇))}{Γ}{Δ ++ ∇ ++ (S ∷ [])}{T}
...   | w rewrite (∸-+-assoc y (length Δ) (ℕ.suc (length ∇)))
                           | (sym (length-≡'{Δ}{∇}{S}))
                           | (m∸n+n≡m{y}{length (Δ ++ ∇ ++ S ∷ [])}  (m≤n∧m≡q⇒q≤n (m≤n∧n≡q⇒m≤q (m≤n⇒m+o≤n+o{o = length Δ} ge') (m∸n+n≡m ge)) (sym (length-≡''{Δ}{∇}{S}))))
                           | (A++B++D∷[]++C≡A++B++D∷C{lzero}{Ty}{Δ}{∇}{Γ}{S}) = TVar (w z)


ext : {Γ Δ : Env} {S : Ty} {s : Exp} → Γ ⊢ s ∶ S → (Δ ++ Γ) ⊢ ↑ (ℤ.pos (length Δ)) , 0 [ s ] ∶ S
ext (TVar {n} x) = TVar (ext-front x)
ext {Γ} {Δ} {Fun T₁ T₂} {Abs e} (TAbs j) = {!!}
ext (TApp j j₁) = TApp (ext j) (ext j₁)


-- preservation under substitution
preserve-subst : {T S : Ty} {Γ Δ : Env} {e s : Exp} (j : (Δ ++ (S ∷ Γ)) ⊢ e ∶ T) (j' : Γ ⊢ s ∶ S) → Γ ⊢ ↑ -[1+ 0 ] ,  length Δ [ [ length Δ ↦ ↑ (ℤ.pos (ℕ.suc (length Δ))) , 0 [ s ] ] e ] ∶ T
preserve-subst {Γ = Γ} {Δ = []} {s = s} (TVar here) j' rewrite (↑⁻¹ₖ[↑¹ₖ[s]]≡s{s}{0}) = j'
preserve-subst {Γ = Γ} {Δ = []} (TVar (there x)) j' = TVar x
preserve-subst {Γ = Γ} {Δ = x₁ ∷ Δ} (TVar x) j' = {!!}
preserve-subst {T} {S} {Γ} {Δ} {Abs e'} {s} (TAbs{T₁ = T₁}{T₂} j) j' = TAbs (preserve-subst{Δ = Δ} ({! swap-subst{T₂}{T₁}{Γ}{[]}{Δ ++ (S ∷ [])} {?} !}) (ext{Δ = T₁ ∷ []} j'))
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


-- shifting below threshold
↑<_,_[_] : ℤ → ℕ → Exp → Exp
↑< d , c [ Var x ] with (x Data.Nat.<? c)
... | yes p = Var (∣ (ℤ.pos x) Data.Integer.+ d ∣)
... | no ¬p = Var x
↑< d , c [ Abs e ] = Abs (↑< d , (c ∸ 1) [ e ]) -- ↑< -1 , 1 (Abs (Var 0)) → Abs (↑< -1 , 0 (Var 0)) → Abs (Var 0)

↯, one level of abstraction deeper the range [1, c + 1] should be shifted.
becomes clear if you imagine an environment next to the expression
Γ ⊢ ↑< d [ Abs e ] : T
S ∷ Γ ⊢ Abs (↑< d [ e ]) : T => "S" should not be shifted


swap-subst : {T S : Ty} {Γ Δ : Env} {e : Exp} {r : ℕ} {gt : r Data.Nat.> length Δ Data.Nat.+ length Γ} (j : ((S ∷ Δ) ++ Γ) ⊢ e ∶ T) → (Δ ++ (S ∷ Γ)) ⊢ [ r ↦ Var (length Δ) ] ↑< -[1+ 0 ] , length Δ Data.Nat.+ 1 [ [ 0 ↦ Var r ] e ] ∶ T
swap-subst {T} {S} {Γ} {Δ} {(Var y)} {r} {gt} (TVar x) = {!!}
swap-subst {(Fun T₁ T₂)} {S} {Γ} {Δ} {(Abs e)} {r} {gt} (TAbs j) = TAbs {!!}  -- not general enough? need to swap arbitrary positions
swap-subst {T} {S} {Γ} {Δ} {(App e e')} {r} {gt} (TApp j j₁) = TApp (swap-subst j) (swap-subst j₁)
swap-subst-inv : {T S : Ty} {Γ Δ : Env} {e : Exp} {r : ℕ} {gt : r Data.Nat.> length Δ Data.Nat.+ length Γ} (j : (Δ ++ (S ∷ Γ)) ⊢ e ∶ T) → (S ∷ (Δ ++ Γ)) ⊢ [ r ↦ Var 0 ] (↑< +[1+ 0 ] , (length Δ) [ [ (length Δ) ↦ Var r ] e ] ) ∶ T

-}
