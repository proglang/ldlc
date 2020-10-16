-- simply-typed λ-calculus w/ DeBruijn indices

module LC where


open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Bool.Properties hiding (≤-trans ; <-trans ; ≤-refl ; <-irrefl)
open import Data.Empty
open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_)
open import Data.Integer.Properties using (⊖-≥ ; 0≤n⇒+∣n∣≡n ; +-monoˡ-≤)
open import Data.List
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

open import Auxiliary

module defs where
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
module denotational where
  open defs

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
module operational where
  open defs

  -- shifting, required to avoid variable-capturing in substitution
  -- see Pierce 2002, pg. 78/79
  ↑_,_[_] : ℤ → ℕ → Exp → Exp
  ↑ d , c [ Var x ]
    with (x <ᴺ? c)
  ...  | yes p = Var x
  ...  | no ¬p = Var (∣ (ℤ.pos x) +ᶻ d ∣)  -- should always be positive anyway
  ↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
  ↑ d , c [ App t t₁ ] = App (↑ d , c [ t ]) (↑ d , c [ t₁ ])

  -- shifting in range [n, m]; by def. m < n implies no shift
  ↑[_,_]_[_] : ℕ → ℕ → ℤ → Exp → Exp
  ↑[ n , m ] d [ Var x ]
    with (x <ᴺ? n)
  ...  | yes p = Var x
  ...  | no ¬p
       with (m <ᴺ? x)
  ...     | yes p' = Var x
  ...     | no ¬p' = Var (∣ (ℤ.pos x) +ᶻ d ∣)
  ↑[ n , m ] d [ Abs e ] = Abs (↑[ ℕ.suc n , ℕ.suc m ] d [ e ]) 
  ↑[ n , m ] d [ App e e₁ ] = App (↑[ n , m ] d [ e ]) (↑[ n , m ] d [ e₁ ])

  -- shorthands
  ↑¹[_] : Exp → Exp
  ↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

  ↑⁻¹[_] : Exp → Exp
  ↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

  -- substitution
  -- see Pierce 2002, pg. 80
  [_↦_]_ : ℕ → Exp → Exp → Exp
  [ k ↦ s ] Var x
    with (Data.Nat._≟_ x k)
  ...  | yes p = s
  ...  | no ¬p = Var x
  [ k ↦ s ] Abs t = Abs ([ ℕ.suc k ↦ ↑¹[ s ] ] t)
  [ k ↦ s ] App t t₁ = App ([ k ↦ s ] t) ([ k ↦ s ] t₁)

  data Val : Exp → Set where
    VFun : {e : Exp} → Val (Abs e)

  -- reduction relation
  data _⇒_ : Exp → Exp → Set where
    ξ-App1 : {e₁ e₁' e₂ : Exp} → e₁ ⇒ e₁' → App e₁ e₂ ⇒ App e₁' e₂
    ξ-App2 : {e e' v : Exp} → Val v → e ⇒ e' → App v e ⇒ App v e'
    β-App : {e v : Exp} → Val v → (App (Abs e) v) ⇒ (↑⁻¹[ ([ 0 ↦ ↑¹[ v ] ] e) ])

  ---- properties & lemmas
  
  --- properties of shifting

  ↑-var-refl : {d : ℤ} {c : ℕ} {x : ℕ} {le : ℕ.suc x ≤ᴺ c} → ↑ d , c [ Var x ] ≡ Var x
  ↑-var-refl {d} {c} {x} {le}
    with (x <ᴺ? c)
  ...  | no ¬p = contradiction le ¬p
  ...  | yes p = refl

  ↑[]-var-refl-< : {n m x : ℕ} {d : ℤ} {le : x <ᴺ n} → ↑[ n , m ] d [ Var x ] ≡ Var x
  ↑[]-var-refl-< {n} {m} {x} {d} {le}
    with (x <ᴺ? n)
  ...  | yes p = refl
  ...  | no ¬p = contradiction le ¬p

  ↑[]-var-refl-> : {n m x : ℕ} {d : ℤ} {le : m <ᴺ x} → ↑[ n , m ] d [ Var x ] ≡ Var x
  ↑[]-var-refl-> {n} {m} {x} {d} {le}
    with (x <ᴺ? n)
  ...  | yes p = refl
  ...  | no p
      with (m <ᴺ? x)
  ...    | no ¬q = contradiction le ¬q
  ...    | yes q = refl

  ↑[]-var-shift : {n m x : ℕ} {d : ℤ} (le1 : n ≤ᴺ x) (le2 : x ≤ᴺ m) → ↑[ n , m ] d [ Var x ] ≡  Var (∣ (ℤ.pos x) +ᶻ d ∣)
  ↑[]-var-shift {n} {m} {x} {d} le1 le2
    with x <ᴺ? n
  ...  | yes p = contradiction p (<⇒≱ (s≤s le1)) 
  ...  | no ¬p
      with m <ᴺ? x
  ...    | yes p' = contradiction p' (<⇒≱ (s≤s le2))
  ...    | no ¬p' = refl

  ↑¹-var : {x : ℕ} → ↑¹[ Var x ] ≡ Var (ℕ.suc x)
  ↑¹-var {zero} = refl
  ↑¹-var {ℕ.suc x}
    rewrite (sym (n+1≡sucn{x +ᴺ 1}))
          | (sym (n+1≡sucn{x}))
          = cong ↑¹[_] (↑¹-var{x})

  ↑⁻¹ₖ[↑¹ₖ[s]]≡s : {e : Exp} {k : ℕ} → ↑ -[1+ 0 ] , k [ ↑ + 1 , k [ e ] ] ≡ e
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {Var x} {k}
    with (x <ᴺ? k)
  -- x < k
  --  => ↑⁻¹ₖ(↑¹ₖ(Var n)) = ↑⁻¹ₖ(Var n) = Var n
  ...  | yes p = ↑-var-refl{ -[1+ 0 ]}{k}{x}{p}
  -- x ≥ k
  --  => ↑⁻¹ₖ(↑¹ₖ(Var n)) = ↑⁻¹ₖ(Var |n + 1|) = Var (||n + 1| - 1|) = Var n
  ...  | no ¬p
       with (¬[x≤k]⇒¬[sucx≤k] ¬p)
  ...     | ¬p'
          with (x +ᴺ 1) <ᴺ? k
  ...        | yes pp = contradiction pp ¬p'
  ...        | no ¬pp
             rewrite (∣nℕ+1⊖1∣≡n{x})
                   = refl
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {Abs e} {k} = cong Abs ↑⁻¹ₖ[↑¹ₖ[s]]≡s
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {App e e₁} = cong₂ App ↑⁻¹ₖ[↑¹ₖ[s]]≡s ↑⁻¹ₖ[↑¹ₖ[s]]≡s

  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] : {k l : ℤ} {c : ℕ} {s : Exp} → l ≥ᶻ +0 → ↑ k , c [ ↑ l , c [ s ] ] ≡ ↑ (l +ᶻ k) , c [ s ]
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {k} {l} {c} {Var x} ge
    with x <ᴺ? c 
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {k} {l} {c} {Var x} ge | no ¬p
      with ∣ + x +ᶻ l ∣ <ᴺ? c
  ...    | yes q = contradiction q (<⇒≱ (n≤m⇒n<sucm (≤-trans (≮⇒≥ ¬p) (m≥0⇒∣n+m∣≥n ge))))
  ...    | no ¬q
         rewrite (0≤n⇒+∣n∣≡n{+ x +ᶻ l} (m≥0⇒n+m≥0 ge))
               | (Data.Integer.Properties.+-assoc (+_ x) l k)
               = refl            
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {k} {l} {c} {Var x} ge | yes p
      with x <ᴺ? c
  ...    | yes p' = refl
  ...    | no ¬p' = contradiction p ¬p'
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {k} {l} {c} {Abs s} le = cong Abs (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s]{k}{l}{ℕ.suc c}{s} le)
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {k} {l} {c} {App s s₁} le = cong₂ App  (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s]{k}{l}{c}{s} le)  (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s]{k}{l}{c}{s₁} le)

  ↑k,q[↑l,c[s]]≡↑l+k,c[s] : {k l : ℤ} {q c : ℕ} {s : Exp} →  + q ≤ᶻ + c +ᶻ l → c ≤ᴺ q → ↑ k , q [ ↑ l , c [ s ] ] ≡ ↑ (l +ᶻ k) , c [ s ]
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {k} {l} {q} {c} {Var x} ge₁ ge₂
    with x <ᴺ? c
  ... | yes p
      with x <ᴺ? q
  ...    | yes p' = refl
  ...    | no ¬p' = contradiction (≤-trans p ge₂) ¬p'
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {k} {l} {q} {c} {Var x} ge₁ ge₂
      | no ¬p
      with ∣ + x +ᶻ l ∣ <ᴺ? q
  ...    | yes p' = contradiction p' (≤⇒≯ (+a≤b⇒a≤∣b∣{q}{+ x +ᶻ l} (Data.Integer.Properties.≤-trans ge₁ ((Data.Integer.Properties.+-monoˡ-≤ l (+≤+ (≮⇒≥ ¬p)))))))
  ...    | no ¬p'
         rewrite (0≤n⇒+∣n∣≡n{+ x +ᶻ l} (Data.Integer.Properties.≤-trans (+≤+ z≤n) ((Data.Integer.Properties.≤-trans ge₁ ((Data.Integer.Properties.+-monoˡ-≤ l (+≤+ (≮⇒≥ ¬p))))))))
               | (Data.Integer.Properties.+-assoc (+_ x) l k)
               = refl
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {k} {l} {q} {c} {Abs s} ge₁ ge₂ = cong Abs (↑k,q[↑l,c[s]]≡↑l+k,c[s] {k} {l} {ℕ.suc q} {ℕ.suc c} {s} (+q≤+c+l⇒+1q≤+1c+l{q}{c}{l} ge₁) (s≤s ge₂)) 
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {k} {l} {q} {c} {App s s₁} ge₁ ge₂ = cong₂ App (↑k,q[↑l,c[s]]≡↑l+k,c[s] {k} {l} {q} {c} {s} ge₁ ge₂) (↑k,q[↑l,c[s]]≡↑l+k,c[s] {k} {l} {q} {c} {s₁} ge₁ ge₂)
  
  --- properties of substitution

  subst-trivial : {x : ℕ} {s : Exp} → [ x ↦ s ] Var x ≡ s
  subst-trivial {x} {s}
    with x Data.Nat.≟ x
  ...  | no ¬p = contradiction refl ¬p
  ...  | yes p = refl

  var-subst-refl : {n m : ℕ} {neq : n ≢ m} {e : Exp} → [ n ↦ e ] (Var m) ≡ (Var m)
  var-subst-refl {n} {m} {neq} {e}
    with Data.Nat._≟_ n m
       | map′ (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n) (Data.Bool.Properties.T? (m ≡ᵇ n))
  ...  | yes p | _ = contradiction p neq
  ...  | no ¬p | yes q = contradiction q (≢-sym ¬p)
  ...  | no ¬p | no ¬q = refl

  --- properties and manipulation of environments
  
  var-env-< : {Γ : Env} {T : Ty} {n : ℕ} (j : n ∶ T ∈ Γ) → n <ᴺ (length Γ)
  var-env-< {.(T ∷ _)} {T} {.0} here = s≤s z≤n
  var-env-< {.(_ ∷ _)} {T} {.(ℕ.suc _)} (there j) = s≤s (var-env-< j)

  -- type to determine whether var type judgement in env. (Δ ++ Γ) is in Δ or Γ
  data extract-env-or {Δ Γ : Env} {T : Ty} {x : ℕ} : Set where
    in-Δ : x ∶ T ∈ Δ → extract-env-or
    -- x ≥ length Δ makes sure that x really is in Γ; e.g.
    -- x = 1, Δ = (S ∷ T), Γ = (T ∷ Γ'); here 1 ∶ T ∈ Δ as well as (1 ∸ 2) ≡ 0 ∶ T ∈ Γ
    in-Γ : (x ≥ᴺ length Δ) → (x ∸ length Δ) ∶ T ∈ Γ → extract-env-or

  extract : {Δ Γ : Env} {T : Ty} {x : ℕ} (j : x ∶ T ∈ (Δ ++ Γ)) → extract-env-or{Δ}{Γ}{T}{x}
  extract {[]} {Γ} {T} {x} j = in-Γ z≤n j
  extract {x₁ ∷ Δ} {Γ} {.x₁} {.0} here = in-Δ here
  extract {x₁ ∷ Δ} {Γ} {T} {ℕ.suc x} (there j)
    with extract {Δ} {Γ} {T} {x} j
  ...  | in-Δ j'  = in-Δ (there j')
  ...  | in-Γ ge j'' = in-Γ (s≤s ge) j''

  ext-behind : {Δ Γ : Env} {T : Ty} {x : ℕ} → x ∶ T ∈ Δ → x ∶ T ∈ (Δ ++ Γ)
  ext-behind here = here
  ext-behind (there j) = there (ext-behind j)

  ext-front : {n : ℕ} {Γ Δ : Env} {S : Ty} → n ∶ S ∈ Γ → (n +ᴺ (length Δ)) ∶ S ∈ (Δ ++ Γ)
  ext-front {n} {Γ} {[]} {S} j
    rewrite (n+length[]≡n{A = Ty}{n = n})
          = j
  ext-front {n} {Γ} {T ∷ Δ} {S} j
    rewrite (+-suc n (foldr (λ _ → ℕ.suc) 0 Δ))
          = there (ext-front j)

  swap-env-behind : {Γ Δ : Env} {T : Ty} → 0 ∶ T ∈ (T ∷ Γ) → 0 ∶ T ∈ (T ∷ Δ)
  swap-env-behind {Γ} {Δ} {T} j = here

  swap-type : {Δ ∇ Γ : Env} {T : Ty} → (length Δ) ∶ T ∈ (Δ ++ T ∷ ∇ ++ Γ) → (length Δ +ᴺ length ∇) ∶ T ∈ (Δ ++ ∇ ++ T ∷ Γ)
  swap-type {Δ} {∇} {Γ} {T} j
    with extract{Δ}{T ∷ ∇ ++ Γ} j
  ...  | in-Δ x = contradiction (var-env-< {Δ} {T} x) (<-irrefl refl)
  ...  | in-Γ le j'
       with extract{T ∷ ∇}{Γ} j'
  ...     | in-Δ j''
          rewrite (n∸n≡0 (length Δ))
                | (sym (length[A++B]≡length[A]+length[B]{lzero}{Ty}{Δ}{∇}))
                | (sym (++-assoc{lzero}{Ty}{Δ}{∇}{T ∷ Γ}))
                = ext-front{0}{T ∷ Γ}{Δ ++ ∇}{T} (swap-env-behind{∇}{Γ}{T} j'')
  ...     | in-Γ le' j''
          rewrite (length[A∷B]≡suc[length[B]]{lzero}{Ty}{T}{∇})
                | (n∸n≡0 (length Δ))
                = contradiction le' (<⇒≱ (s≤s z≤n))

  env-pred : {Γ : Env} {S T : Ty} {y : ℕ} {gt : y ≢ 0} → y ∶ T ∈ (S ∷ Γ) → ∣ y ⊖ 1 ∣ ∶ T ∈ Γ
  env-pred {Γ} {S} {.S} {.0} {gt} here = contradiction refl gt
  env-pred {Γ} {S} {T} {.(ℕ.suc _)} {gt} (there j) = j

  env-type-equiv-here : {Γ : Env} {S T : Ty} → 0 ∶ T ∈ (S ∷ Γ) → T ≡ S
  env-type-equiv-here {Γ} {S} {.S} here = refl

  env-type-equiv : {Δ ∇ : Env} {S T : Ty} → length Δ ∶ T ∈ (Δ ++ S ∷ ∇) → T ≡ S
  env-type-equiv {Δ} {∇} {S} {T} j
    with extract{Δ}{S ∷ ∇} j
  ...  | in-Δ x = contradiction (var-env-< x) (≤⇒≯ ≤-refl) 
  ...  | in-Γ x j'
       rewrite (n∸n≡0 (length Δ))
             = env-type-equiv-here {∇} {S} {T} j'

  env-type-equiv-j : {Γ : Env} {S T : Ty} {n : ℕ} → T ≡ S → n ∶ T ∈ Γ → n ∶ S ∈ Γ
  env-type-equiv-j {Γ} {S} {T} {n} eq j
    rewrite eq
          = j

  -- extension of environment

  ext : {Γ Δ ∇ : Env} {S : Ty} {s : Exp} → (∇ ++ Γ) ⊢ s ∶ S → (∇ ++ Δ ++ Γ) ⊢ ↑ (ℤ.pos (length Δ)) , length ∇ [ s ] ∶ S
  ext {Γ} {Δ} {∇} (TVar {n} x)
    with extract{∇}{Γ} x
  ... | in-Δ x₁
      with n <ᴺ? length ∇
  ...    | yes p = TVar (ext-behind x₁)
  ...    | no ¬p = contradiction (var-env-< x₁) ¬p
  ext {Γ} {Δ} {∇} (TVar {n} x)
      | in-Γ x₁ x₂
      with n <ᴺ? length ∇
  ...    | yes p = contradiction x₁ (<⇒≱ p)
  ...    | no ¬p
         with (ext-front{n ∸ length ∇}{Γ}{∇ ++ Δ} x₂)
  ...       | w
            rewrite (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{Δ})
                  | (sym (+-assoc (n ∸ length ∇) (length ∇) (length Δ)))
                  | (m∸n+n≡m{n}{length ∇} (≮⇒≥ ¬p))
                  | (++-assoc{lzero}{Ty}{∇}{Δ}{Γ})
                  = TVar w 
  ext {Γ} {Δ} {∇} {Fun T₁ T₂} {Abs e} (TAbs j) = TAbs (ext{Γ}{Δ}{T₁ ∷ ∇} j)
  ext {Γ} {Δ} {∇} {S} {App s₁ s₂} (TApp{T₁ = T₁} j₁ j₂) = TApp (ext{Γ}{Δ}{∇}{Fun T₁ S} j₁) (ext{Γ}{Δ}{∇}{T₁} j₂)

  ---- progress and preservation

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

  ---

  -- preservation under substitution
  preserve-subst : {T S : Ty} {Γ Δ : Env} {e s : Exp} (j : (Δ ++ (S ∷ Γ)) ⊢ e ∶ T) (j' : Γ ⊢ s ∶ S) → (Δ ++ Γ) ⊢  ↑ -[1+ 0 ] , length Δ [ [ length Δ ↦ ↑ (ℤ.pos (ℕ.suc (length Δ))) , 0 [ s ] ] e ] ∶ T
  preserve-subst {T} {S} {Γ} {Δ} {e} {s} (TVar{n} x) j'
    with extract{Δ}{S ∷ Γ}{T}{n} x
  ...  | in-Δ x₁
       with n Data.Nat.≟ length Δ
  ...     | yes p = contradiction p (<⇒≢ (var-env-< x₁))
  ...     | no ¬p
          with n <ᴺ? length Δ
  ...        | yes q = TVar (ext-behind{Δ}{Γ} x₁)
  ...        | no ¬q = contradiction (var-env-< x₁) ¬q
  preserve-subst {T} {S} {Γ} {Δ} {e} {s} (TVar{n} x) j'
       | in-Γ x₁ x₂
       with n Data.Nat.≟ length Δ
  ...     | yes p
          rewrite (↑k,q[↑l,c[s]]≡↑l+k,c[s]{ -[1+ 0 ]}{+[1+ length Δ ]}{length Δ}{0}{s} (+≤+ n≤sucn) z≤n)
                | p
                | (env-type-equiv x)
                = ext{Γ}{Δ}{[]} j'
  ...     | no ¬p
          with n <ᴺ? length Δ
  ...        | yes q = contradiction x₁ (<⇒≱ q)
  ...        | no ¬q rewrite (sym (minus-1{n}{length Δ}{≤∧≢⇒< x₁ (≢-sym ¬p)}))
                           = TVar (ext-front{Δ = Δ} (env-pred{Γ}{S}{T}{gt = ≢-sym (<⇒≢ (m>n⇒m∸n≥1 (≤∧≢⇒< x₁ (≢-sym ¬p))))} x₂))
  preserve-subst {T} {S} {Γ} {Δ} {Abs e'} {s} (TAbs{T₁ = T₁}{T₂} j) j'
    with preserve-subst{T₂}{S}{Γ}{T₁ ∷ Δ}{e'}{s} j j'
  ...  | w
       rewrite (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s]{+ 1}{+[1+ length Δ ]}{0}{s} (+≤+ z≤n))
             | (length[A∷B]≡suc[length[B]]{lzero}{Ty}{T₁}{Δ})
             | (n+1≡sucn{length Δ})
             = TAbs w
  preserve-subst (TApp j j₁) j' = TApp (preserve-subst j j') (preserve-subst j₁ j')

  -- preservation theorem, i.e. a well-typed expression reduces to a well-typed expression
  preserve : {T : Ty} {Γ : Env} (e e' : Exp) (j : Γ ⊢ e ∶ T) (r : e ⇒ e') → Γ ⊢ e' ∶ T
  preserve (App s₁ s₂) .(App _ s₂) (TApp j j') (ξ-App1{e₁' = s₁'} r) = TApp (preserve s₁ s₁' j r) j' -- IH on inner reduction
  preserve (App s₁ s₂) .(App s₁ _) (TApp j j') (ξ-App2{e' = s₂'} x r) = TApp j (preserve s₂ s₂' j' r)
  preserve (App (Abs e) s')  .(↑⁻¹[ [ 0 ↦ ↑¹[ s' ] ] e ]) (TApp (TAbs j) j') (β-App x) = preserve-subst{Δ = []} j j'





  -----------------------------------------------------------------------------------------------------------

  -- swap-subst lemma: swap the position of a type in an environment (did not need this after all)

  -- aux. calculations
  length-≡ : {Δ ∇ Γ : Env} {S : Ty} → ℕ.suc (length Δ +ᴺ (length Γ +ᴺ length ∇)) ≡ length (Δ ++ S ∷ ∇ ++ Γ)
  length-≡ {Δ} {∇} {Γ} {S}
    rewrite (length[A++B]≡length[A]+length[B]{lzero}{Ty}{Δ}{S ∷ ∇ ++ Γ})
          | (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{Γ})
          | (+-suc (length Δ) (length ∇ +ᴺ length Γ))
          | (+-comm (length ∇) (length Γ))
          = refl

  length-≡' : {Δ ∇ : Env} {S : Ty} → length (Δ ++ ∇ ++ S ∷ []) ≡ length Δ +ᴺ ℕ.suc (length ∇)
  length-≡' {Δ} {∇} {S}
    rewrite (length[A++B]≡length[A]+length[B]{lzero}{Ty}{Δ}{∇ ++ S ∷ []})
          | (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{S ∷ []})
          | (+-suc (length ∇) (0))
          | (+-identityʳ (length ∇))
          = refl

  length-≡'' : {Δ ∇ : Env} {S : Ty} → length (Δ ++ ∇ ++ S ∷ []) ≡ ℕ.suc (length ∇ +ᴺ length Δ)
  length-≡'' {Δ} {∇} {S}
    rewrite (cong (ℕ.suc) (+-comm (length ∇) (length Δ)))
          | (sym (+-suc (length Δ) (length ∇)))
          = length-≡'{Δ}{∇}{S}

  --- why the "r"? we have to "remember" where S was
  --- cannot substitute its position for zero, since ↑ would increase that
  --- cannot do ↑ and then subtitute its position for zero, since (position - 1) would be affected aswell
  --- fix: cache in unreachable variable r
  swap-subst : {T S : Ty} {Γ Δ ∇ : Env} {e : Exp} {r : ℕ} {gt : r >ᴺ ℕ.suc (length Δ +ᴺ (length Γ +ᴺ length ∇))}
               → (Δ ++ (S ∷ ∇) ++ Γ) ⊢ e ∶ T
               → (Δ ++ ∇ ++ (S ∷ Γ)) ⊢ [ r ↦ Var (length Δ +ᴺ length ∇) ] ↑[ ℕ.suc (length Δ) , length Δ +ᴺ length ∇ ] -[1+ 0 ] [ [ length Δ ↦ Var r ] e ] ∶ T
  swap-subst {(Fun T₁ T₂)} {S} {Γ} {Δ} {∇} {(Abs e)} {r} {gt} (TAbs j)
    rewrite (↑¹-var{length Δ +ᴺ length ∇})
          | (n+1≡sucn{r})
          = TAbs (swap-subst{T₂}{S}{Γ}{T₁ ∷ Δ}{∇}{e}{ℕ.suc r}{s≤s gt} j)
  swap-subst {T} {S} {Γ} {Δ} {∇} {(App e e₁)} {r} {gt} (TApp{T₁ = T₁}{T₂} j j₁) = TApp (swap-subst{Fun T₁ T₂}{S}{Γ}{Δ}{∇}{e}{r}{gt} j) (swap-subst{T₁}{S}{Γ}{Δ}{∇}{e₁}{r}{gt} j₁)
  swap-subst {T} {S} {Γ} {Δ} {∇} {Var y} {r} {gt} (TVar j)
    with extract{Δ} {(S ∷ ∇) ++ Γ} {T} {y} j
       | y <ᴺ? (foldr (λ _ → ℕ.suc) 0 Δ)
       | Data.Nat._≟_ y (length Δ)  
  -- y ∈ Δ
  ... | in-Δ x | yes p | yes q = contradiction q (<⇒≢ p)
  ... | in-Δ x | yes p | no ¬q
    rewrite (↑[]-var-refl-<{ℕ.suc (length Δ)}{length Δ +ᴺ length ∇}{y}{ -[1+ 0 ] }{[k<x]⇒[k<sucx] p})
          | (var-subst-refl{r}{y}{≢-sym (<⇒≢ (a<b≤c⇒a<c p (≤-trans (n≤m⇒n≤sucm (m≤m+n (length Δ) (length Γ +ᴺ length ∇))) (<-trans (s≤s ≤-refl) gt))) )}
            {Var (foldr (λ _ → ℕ.suc) 0 Δ +ᴺ foldr (λ _ → ℕ.suc) 0 ∇)})
          = TVar (ext-behind x)
  ... | in-Δ x | no ¬p | _ = contradiction (var-env-< x) ¬p
  -- y ∈ (S ∷ ∇ ++ Γ)
  ... | in-Γ ge x | p | q
    with extract{S ∷ ∇} {Γ} {T} {y ∸ length Δ} x
  --- y ∈ (S ∷ ∇)
  ---- y @ S
  swap-subst {T} {S} {Γ} {Δ} {∇} {Var y} {r} {gt} (TVar j) | in-Γ ge x | p | yes q' | in-Δ x'
    rewrite (↑[]-var-refl->{ℕ.suc (length Δ)}{length Δ +ᴺ length ∇}{r}{ -[1+ 0 ] }{<-trans (s≤s (n+m≤n+q+m {length Δ} {length ∇} {length Γ})) gt})
          | (subst-trivial{r} {Var (length Δ +ᴺ length ∇)})
          | q'
          | (env-type-equiv j)
          = TVar (swap-type{Δ}{∇}{Γ}{S} (env-type-equiv-j (env-type-equiv j) j))
  ---- y ∈ ∇
  swap-subst {T} {S} {Γ} {Δ} {∇} {Var y} {r} {gt} (TVar j) | in-Γ ge x | p | no ¬q' | in-Δ x'
    rewrite (↑[]-var-shift{ℕ.suc (length Δ)}{length Δ +ᴺ length ∇}{y}{ -[1+ 0 ]} (≤∧≢⇒< ge (≢-sym ¬q')) (≤-trans (≤-pred (m≤n∧m≡q⇒q≤n (m≤n⇒m+o≤n+o{o = length Δ} (var-env-< x'))
            (cong ℕ.suc (m∸n+n≡m ge)))) (≤-refl-+-comm{length ∇}{length Δ})))
          | length-≡ {Δ} {∇} {Γ} {S}
          | (var-subst-refl {r} {∣ y ⊖ 1 ∣} {≢-sym (<⇒≢ (<-trans (n>0⇒n>∣n⊖1∣ (≤-trans (s≤s z≤n) ((≤∧≢⇒< ge (≢-sym ¬q'))))) (<-trans (var-env-< j) gt)))} {Var (length Δ +ᴺ length ∇)})
          | sym (minus-1{y}{length Δ}{≤∧≢⇒< ge (≢-sym ¬q')} )
          = TVar (ext-front{Δ = Δ}(ext-behind{∇}{S ∷ Γ}{T} (env-pred{gt = ≢-sym (<⇒≢ (m>n⇒m∸n≥1{y}{length Δ} ((≤∧≢⇒< ge (≢-sym ¬q')))))} x')))
  --- y ∈ Γ
  swap-subst {T} {S} {Γ} {Δ} {∇} {Var y} {r} {gt} (TVar j) | in-Γ ge x | no ¬p | yes q | in-Γ ge' x'
          = contradiction q (≢-sym (<⇒≢ (m∸n≢0⇒n<m{y}{length Δ} (≢-sym (<⇒≢ (a<b≤c⇒a<c (s≤s z≤n) (≤-trans (length[A∷B]≥1{lzero}{Ty}{S}{∇}) ge')))))))
  swap-subst {T} {S} {Γ} {Δ} {∇} {Var y} {r} {gt} (TVar j) | in-Γ ge x | yes p | yes q | in-Γ ge' x' = contradiction q (<⇒≢ p)
  swap-subst {T} {S} {Γ} {Δ} {∇} {Var y} {r} {gt} (TVar j) | in-Γ ge x | p | no ¬q' | in-Γ ge' x'
    rewrite (↑[]-var-refl->{ℕ.suc (length Δ)}{length Δ +ᴺ length ∇}{y}{ -[1+ 0 ]}{a<b≤c⇒a<c (s≤s (≤-refl-+-comm{length Δ}{length ∇})) (m≤n∧n≡q⇒m≤q (m≤n⇒m+o≤n+o{o = length Δ} ge') (m∸n+n≡m ge))})
          | (var-subst-refl{r}{y}{≢-sym (<⇒≢ (<-trans (var-env-< j) (m≤n∧m≡q⇒q≤n gt (cong ℕ.suc (length-≡{Δ}{∇}{Γ}{S})))))}{ Var (foldr (λ _ → ℕ.suc) 0 Δ +ᴺ foldr (λ _ → ℕ.suc) 0 ∇)})
      with ext-front{((y ∸ (length Δ)) ∸ ℕ.suc (length ∇))}{Γ}{Δ ++ ∇ ++ (S ∷ [])}{T}
  ...     | w rewrite (∸-+-assoc y (length Δ) (ℕ.suc (length ∇)))
                    | (sym (length-≡'{Δ}{∇}{S}))
                    | (m∸n+n≡m{y}{length (Δ ++ ∇ ++ S ∷ [])}  (m≤n∧m≡q⇒q≤n (m≤n∧n≡q⇒m≤q (m≤n⇒m+o≤n+o{o = length Δ} ge') (m∸n+n≡m ge)) (sym (length-≡''{Δ}{∇}{S}))))
                    | (A++B++D∷[]++C≡A++B++D∷C{lzero}{Ty}{Δ}{∇}{Γ}{S})
                    = TVar (w x')
