-- simply-typed labelled λ-calculus w/ DeBruijn indices

-- {-# OPTIONS --show-implicit #-}

module LLC where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Bool.Properties hiding (≤-trans ; <-trans ; ≤-refl ; <-irrefl)
open import Data.Empty
open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_)
open import Data.Integer.Properties using (⊖-≥ ; 0≤n⇒+∣n∣≡n ; +-monoˡ-≤)
open import Data.List
open import Data.List.Relation.Unary.All
-- open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Data.Fin
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ)
open import Data.Product
open import Function
open import Extensionality

open import Auxiliary

module defs where
  data Exp {n : ℕ} : Set where
    Var : ℕ → Exp {n}
    Abs : Exp {n} → Exp {n}
    App : Exp {n} → Exp {n} → Exp {n}
    LabI : {x : Fin n} {s : Subset n} → x ∈ s → Exp {n}
    LabE : {s : Subset n} → (∀ l → l ∈ s → Exp {n}) → Exp {n} → Exp {n}
  
  data Ty {n : ℕ} : Set where
    Fun : Ty {n} → Ty {n} → Ty
    Label : Subset n → Ty
  
  -- shifting and substitution

  -- shifting, required to avoid variable-capturing in substitution
  -- see Pierce 2002, pg. 78/79
  ↑ᴺ_,_[_] : ℤ → ℕ → ℕ → ℕ
  ↑ᴺ d , c [ x ]
    with (x <ᴺ? c)
  ...  | yes p = x
  ...  | no ¬p = ∣ ℤ.pos x +ᶻ d ∣
  
  ↑_,_[_] : ∀ {n} → ℤ → ℕ → Exp {n} → Exp
  ↑ d , c [ Var x ] = Var (↑ᴺ d , c [ x ])
  ↑ d , c [ Abs t ] = Abs (↑ d , (ℕ.suc c) [ t ])
  ↑ d , c [ App t t₁ ] = App (↑ d , c [ t ]) (↑ d , c [ t₁ ])
  ↑ d , c [ LabI ins ] = LabI ins
  ↑ d , c [ LabE f e ] = LabE (λ l x → ↑ d , c [ (f l x) ]) (↑ d , c [ e ])


  -- shifting in range [n, m]; by def. m < n implies no shift
  ↑[_,_]_[_] : ∀ {n} → ℕ → ℕ → ℤ → Exp {n} → Exp
  ↑[ n , m ] d [ Var x ]
    with (x <ᴺ? n)
  ...  | yes p = Var x
  ...  | no ¬p
       with (m <ᴺ? x)
  ...     | yes p' = Var x
  ...     | no ¬p' = Var (∣ (ℤ.pos x) +ᶻ d ∣)
  ↑[ n , m ] d [ Abs e ] = Abs (↑[ ℕ.suc n , ℕ.suc m ] d [ e ]) 
  ↑[ n , m ] d [ App e e₁ ] = App (↑[ n , m ] d [ e ]) (↑[ n , m ] d [ e₁ ])
  ↑[ n , m ] d [ LabI ins ] = LabI ins
  ↑[ n , m ] d [ LabE f e ] = LabE (λ l x → ↑[ n , m ] d [ (f l x) ]) (↑[ n , m ] d [ e ])

  -- shorthands
  ↑¹[_] : ∀ {n} → Exp {n} → Exp
  ↑¹[ e ] = ↑ (ℤ.pos 1) , 0 [ e ]

  ↑⁻¹[_] : ∀ {n} → Exp {n} → Exp
  ↑⁻¹[ e ] = ↑ (ℤ.negsuc 0) , 0 [ e ]

  -- substitution
  -- see Pierce 2002, pg. 80
  [_↦_]_ : ∀ {n} → ℕ → Exp {n} → Exp → Exp
  [ k ↦ s ] Var x
    with (_≟ᴺ_ x k)
  ...  | yes p = s
  ...  | no ¬p = Var x
  [ k ↦ s ] Abs t = Abs ([ ℕ.suc k ↦ ↑¹[ s ] ] t)
  [ k ↦ s ] App t t₁ = App ([ k ↦ s ] t) ([ k ↦ s ] t₁)
  [ k ↦ s ] LabI ins = LabI ins
  [ k ↦ s ] LabE f e = LabE (λ l x → [ k ↦ s ] (f l x)) ([ k ↦ s ] e)

  -- typing

  Env : {ℕ} → Set
  Env {n} = List (Ty {n})

  data _∶_∈_ {n : ℕ} : ℕ → Ty {n} → Env {n} → Set where
    here : {T : Ty} {Γ : Env} → 0 ∶ T ∈ (T ∷ Γ)
    there : {n : ℕ} {T₁ T₂ : Ty} {Γ : Env} → n ∶ T₁ ∈ Γ → (ℕ.suc n) ∶ T₁ ∈ (T₂ ∷ Γ)

  --     LabI : {n : ℕ} {x : Fin n} {s : Subset n} → x ∈ s → Exp
  data _⊢_∶_ {n : ℕ} : Env {n} → Exp {n} → Ty {n} → Set where
    TVar : {m : ℕ} {Γ : Env} {T : Ty} → m ∶ T ∈ Γ → Γ ⊢ (Var m) ∶ T
    TAbs : {Γ : Env} {T₁ T₂ : Ty} {e : Exp} → (T₁ ∷ Γ) ⊢ e ∶ T₂ → Γ ⊢ (Abs e) ∶ (Fun T₁ T₂)
    TApp : {Γ : Env} {T₁ T₂ : Ty} {e₁ e₂ : Exp} → Γ ⊢ e₁ ∶ (Fun T₁ T₂) → Γ ⊢ e₂ ∶ T₁ → Γ ⊢ (App e₁ e₂) ∶ T₂
    TLabI : {Γ : Env} {x : Fin n} {s : Subset n} → (ins : x ∈ s) → Γ ⊢ LabI ins ∶ Label {n} s
    TLabEl : {Γ : Env} {T : Ty} {s : Subset n} {x : Fin n} {ins : x ∈ s} {f : ∀ l → l ∈ s → Exp} → (∀ l i → (Γ ⊢ (f l i) ∶ T))
                                                                                                 → Γ ⊢ LabI {n} {x} {s} ins ∶ Label {n} s
                                                                                                 → Γ ⊢ LabE {n} {s} f (LabI {n} {x} {s} ins) ∶ T
    TLabEx : {Γ : Env} {T : Ty} {m : ℕ} {s : Subset n} {f : ∀ l → l ∈ s → Exp} → (∀ l i → (Γ ⊢ [ m ↦ (LabI i) ] (f l i) ∶ T))
                                                                               → Γ ⊢ Var m ∶ Label {n} s
                                                                               → Γ ⊢ LabE {n} {s} f (Var m) ∶ T
                                                                               

-- denotational semantics
module denotational where
  open defs

  Val : {n : ℕ} → Ty {n} → Set
  Val (Fun Ty₁ Ty₂) = (Val Ty₁) → (Val Ty₂)
  Val {n} (Label s) = Σ (Fin n) (λ x → x ∈ s)

  access : {n m : ℕ} {Γ : Env {n}} {T : Ty {n}} → m ∶ T ∈ Γ → All Val Γ → Val T
  access here (V ∷ Γ) = V
  access (there J) (V ∷ Γ) = access J Γ

  eval : {n : ℕ} {Γ : Env {n}} {T : Ty {n}} {e : Exp {n}} → Γ ⊢ e ∶ T → All Val Γ → Val T
  eval (TVar c) Val-Γ = access c Val-Γ 
  eval (TAbs TJ) Val-Γ = λ V → eval TJ (V ∷ Val-Γ)
  eval (TApp TJ TJ₁) Val-Γ = (eval TJ Val-Γ) (eval TJ₁ Val-Γ)
  eval (TLabI {x = x} ins) Val-Γ = x , ins
  eval (TLabEl {x = x}{ins = ins}{f = f} f' j) Val-Γ = eval (f' x ins) Val-Γ
  eval (TLabEx {m = m}{s}{f} f' j) Val-Γ
    with eval j Val-Γ    -- evaluate variable
  ... | x , ins = eval (f' x ins) Val-Γ


-- operational semantics (call-by-value)
module operational where
  open defs

  data Val {n : ℕ} : Exp {n} → Set where
    VFun : {e : Exp} → Val (Abs e)
    VLab : {x : Fin n} {s : Subset n} {ins : x ∈ s} → Val (LabI ins)

  -- reduction relation
  data _⇒_ {n : ℕ} : Exp {n} → Exp {n} → Set where
    ξ-App1 : {e₁ e₁' e₂ : Exp} → e₁ ⇒ e₁' → App e₁ e₂ ⇒ App e₁' e₂
    ξ-App2 : {e e' v : Exp} → Val v → e ⇒ e' → App v e ⇒ App v e'
    β-App : {e v : Exp} → Val v → (App (Abs e) v) ⇒ (↑⁻¹[ ([ 0 ↦ ↑¹[ v ] ] e) ])
    β-LabE : {s : Subset n} {f : ∀ l → l ∈ s → Exp} {x : Fin n} → (ins : x ∈ s) → LabE f (LabI ins) ⇒ f x ins

  ---- properties & lemmas
  
  --- properties of shifting

  --  ∣ + x +ᶻ k ∣ +ᴺ m ≡ ∣ + (x +ᴺ m) +ᶻ k ∣
  aux-calc-1 : {x m : ℕ} {k : ℤ} → k >ᶻ + 0 → ∣ + x +ᶻ k ∣ +ᴺ m ≡ ∣ + (x +ᴺ m) +ᶻ k ∣
  aux-calc-1 {x} {m} {+_ n} ge
    rewrite (+-assoc x n m)
          | (+-comm n m)
          | (sym (+-assoc x m n))
          = refl
  
  ↑ᴺk,l[x]+m≡↑ᴺk,l+m[x+m] : {k : ℤ} {l x m : ℕ} → k >ᶻ + 0 → ↑ᴺ k , l [ x ] +ᴺ m ≡ ↑ᴺ k , l +ᴺ m [ x +ᴺ m ] 
  ↑ᴺk,l[x]+m≡↑ᴺk,l+m[x+m] {k} {l} {x} {m} ge 
    with x <ᴺ? l
  ...  | yes p
       with x +ᴺ m <ᴺ? l +ᴺ m
  ...     | yes q = refl
  ...     | no ¬q = contradiction (+-monoˡ-< m p) ¬q
  ↑ᴺk,l[x]+m≡↑ᴺk,l+m[x+m] {k} {l} {x} {m} ge
       | no ¬p
       with x +ᴺ m <ᴺ? l +ᴺ m
  ...     | yes q = contradiction q (<⇒≱ (+-monoˡ-< m (≰⇒> ¬p)))
  ...     | no ¬q = aux-calc-1 ge

  -- corollary for suc
  suc[↑ᴺk,l[x]]≡↑ᴺk,sucl[sucx] : {k : ℤ} {l x : ℕ} → k >ᶻ + 0 → ℕ.suc (↑ᴺ k , l [ x ]) ≡ ↑ᴺ k , ℕ.suc l [ ℕ.suc x ]
  suc[↑ᴺk,l[x]]≡↑ᴺk,sucl[sucx] {k} {l} {x} ge
    with  (↑ᴺk,l[x]+m≡↑ᴺk,l+m[x+m] {k} {l} {x} {1} ge)
  ...  | w
       rewrite (n+1≡sucn{↑ᴺ k , l [ x ]})
             | (n+1≡sucn{x})
             | (n+1≡sucn{l})
             = w

  ↑-var-refl : {n : ℕ} {d : ℤ} {c : ℕ} {x : ℕ} {le : ℕ.suc x ≤ᴺ c} → ↑ d , c [ Var {n} x ] ≡ Var x
  ↑-var-refl {n} {d} {c} {x} {le}
    with (x <ᴺ? c)
  ...  | no ¬p = contradiction le ¬p
  ...  | yes p = refl

  ↑[]-var-refl-< : {N n m x : ℕ} {d : ℤ} {le : x <ᴺ n} → ↑[ n , m ] d [ Var {N} x ] ≡ Var x
  ↑[]-var-refl-< {N} {n} {m} {x} {d} {le}
    with (x <ᴺ? n)
  ...  | yes p = refl
  ...  | no ¬p = contradiction le ¬p

  ↑[]-var-refl-> : {N n m x : ℕ} {d : ℤ} {le : m <ᴺ x} → ↑[ n , m ] d [ Var {N} x ] ≡ Var x
  ↑[]-var-refl-> {N} {n} {m} {x} {d} {le}
    with (x <ᴺ? n)
  ...  | yes p = refl
  ...  | no p
      with (m <ᴺ? x)
  ...    | no ¬q = contradiction le ¬q
  ...    | yes q = refl

  ↑[]-var-shift : {N n m x : ℕ} {d : ℤ} (le1 : n ≤ᴺ x) (le2 : x ≤ᴺ m) → ↑[ n , m ] d [ Var {N} x ] ≡  Var (∣ (ℤ.pos x) +ᶻ d ∣)
  ↑[]-var-shift {N} {n} {m} {x} {d} le1 le2
    with x <ᴺ? n
  ...  | yes p = contradiction p (<⇒≱ (s≤s le1)) 
  ...  | no ¬p
      with m <ᴺ? x
  ...    | yes p' = contradiction p' (<⇒≱ (s≤s le2))
  ...    | no ¬p' = refl

  ↑¹-var : {n x : ℕ} → ↑¹[ Var {n} x ] ≡ Var (ℕ.suc x)
  ↑¹-var {n} {zero} = refl
  ↑¹-var {n} {ℕ.suc x}
    rewrite (sym (n+1≡sucn{x +ᴺ 1}))
          | (sym (n+1≡sucn{x}))
          = cong ↑¹[_] (↑¹-var{n}{x})

  ↑⁻¹ₖ[↑¹ₖ[s]]≡s : {n : ℕ} {e : Exp {n} } {k : ℕ} → ↑ -[1+ 0 ] , k [ ↑ + 1 , k [ e ] ] ≡ e
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {n} {Var x} {k}
    with (x <ᴺ? k)
  -- x < k
  --  => ↑⁻¹ₖ(↑¹ₖ(Var n)) = ↑⁻¹ₖ(Var n) = Var n
  ...  | yes p = ↑-var-refl{n}{ -[1+ 0 ]}{k}{x}{p}
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
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {n} {Abs e} {k} = cong Abs ↑⁻¹ₖ[↑¹ₖ[s]]≡s
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {n} {App e e₁} = cong₂ App ↑⁻¹ₖ[↑¹ₖ[s]]≡s ↑⁻¹ₖ[↑¹ₖ[s]]≡s
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {n} {LabI ins} = refl
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {n} {LabE f e} = cong₂ LabE (f-ext (λ x → f-ext (λ ins →  ↑⁻¹ₖ[↑¹ₖ[s]]≡s)))  ↑⁻¹ₖ[↑¹ₖ[s]]≡s

  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] : {n : ℕ} {k l : ℤ} {c : ℕ} {s : Exp {n}} → l ≥ᶻ +0 → ↑ k , c [ ↑ l , c [ s ] ] ≡ ↑ (l +ᶻ k) , c [ s ]
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {Var x} ge
    with x <ᴺ? c 
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {Var x} ge | no ¬p
      with ∣ + x +ᶻ l ∣ <ᴺ? c
  ...    | yes q = contradiction q (<⇒≱ (n≤m⇒n<sucm (≤-trans (≮⇒≥ ¬p) (m≥0⇒∣n+m∣≥n ge))))
  ...    | no ¬q
         rewrite (0≤n⇒+∣n∣≡n{+ x +ᶻ l} (m≥0⇒n+m≥0 ge))
               | (Data.Integer.Properties.+-assoc (+_ x) l k)
               = refl            
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {Var x} ge | yes p
      with x <ᴺ? c
  ...    | yes p' = refl
  ...    | no ¬p' = contradiction p ¬p'
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {Abs s} le = cong Abs (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s]{n}{k}{l}{ℕ.suc c}{s} le)
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {App s s₁} le = cong₂ App  (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s]{n}{k}{l}{c}{s} le)  (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s]{n}{k}{l}{c}{s₁} le)
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {LabI ins} le = refl
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {LabE f e} le = cong₂ LabE (f-ext (λ x → f-ext (λ ins → ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {f x ins} le))) ( ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {e} le)

  ↑k,q[↑l,c[s]]≡↑l+k,c[s] : {n : ℕ} {k l : ℤ} {q c : ℕ} {s : Exp {n}} →  + q ≤ᶻ + c +ᶻ l → c ≤ᴺ q → ↑ k , q [ ↑ l , c [ s ] ] ≡ ↑ (l +ᶻ k) , c [ s ]
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {Var x} ge₁ ge₂
    with x <ᴺ? c
  ... | yes p
      with x <ᴺ? q
  ...    | yes p' = refl
  ...    | no ¬p' = contradiction (≤-trans p ge₂) ¬p'
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {Var x} ge₁ ge₂
      | no ¬p
      with ∣ + x +ᶻ l ∣ <ᴺ? q
  ...    | yes p' = contradiction p' (≤⇒≯ (+a≤b⇒a≤∣b∣{q}{+ x +ᶻ l} (Data.Integer.Properties.≤-trans ge₁ ((Data.Integer.Properties.+-monoˡ-≤ l (+≤+ (≮⇒≥ ¬p)))))))
  ...    | no ¬p'
         rewrite (0≤n⇒+∣n∣≡n{+ x +ᶻ l} (Data.Integer.Properties.≤-trans (+≤+ z≤n) ((Data.Integer.Properties.≤-trans ge₁ ((Data.Integer.Properties.+-monoˡ-≤ l (+≤+ (≮⇒≥ ¬p))))))))
               | (Data.Integer.Properties.+-assoc (+_ x) l k)
               = refl
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {Abs s} ge₁ ge₂ = cong Abs (↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {ℕ.suc q} {ℕ.suc c} {s} (+q≤+c+l⇒+1q≤+1c+l{q}{c}{l} ge₁) (s≤s ge₂)) 
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {App s s₁} ge₁ ge₂ = cong₂ App (↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {s} ge₁ ge₂) (↑k,q[↑l,c[s]]≡↑l+k,c[s]{n} {k} {l} {q} {c} {s₁} ge₁ ge₂)
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {LabI e} ge₁ ge₂ = refl
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {LabE f e} ge₁ ge₂ = cong₂ LabE (f-ext (λ x → f-ext (λ ins → ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {f x ins} ge₁ ge₂))) (↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {e} ge₁ ge₂)

  aux-calc-2 : {x l : ℕ} {k : ℤ} → k >ᶻ + 0 → ∣ + (x +ᴺ l) +ᶻ k ∣ ≡ ∣ + x +ᶻ k ∣ +ᴺ l
  aux-calc-2 {x} {l} {+_ n} ge
    rewrite (+-assoc x l n)
          | (+-comm l n)
          | (+-assoc x n l)
          = refl

  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] : {n : ℕ} {k : ℤ} {q c l : ℕ} {s : Exp {n}} → c ≤ᴺ q → + 0 <ᶻ k →  ↑ k , q +ᴺ l [ ↑ + l , c [ s ] ] ≡ ↑ + l , c [ ↑ k , q [ s ] ]
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {Var x} le le'
    with x <ᴺ? q
  ...  | yes p
       with x <ᴺ? c
  ...     | yes p'
          with x <ᴺ? q +ᴺ l
  ...        | yes p'' = refl
  ...        | no ¬p'' = contradiction (≤-stepsʳ l p) ¬p''
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {Var x} le le'
       | yes p
          | no ¬p'
          with x +ᴺ l <ᴺ? q +ᴺ l
  ...        | yes p'' = refl
  ...        | no ¬p'' = contradiction (Data.Nat.Properties.+-monoˡ-≤ l p) ¬p''
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {Var x} le le'
       | no ¬p
       with x <ᴺ? c
  ...     | yes p' = contradiction p' (<⇒≱ (a≤b<c⇒a<c le (≰⇒> ¬p)))
  ...     | no ¬p'
          with x +ᴺ l <ᴺ? q +ᴺ l
             | ∣ + x +ᶻ k ∣ <ᴺ? c
  ...        | _ | yes p''' = contradiction p''' (<⇒≱ (a≤b<c⇒a<c (≰⇒≥ ¬p') (s≤s (m>0⇒∣n+m∣>n {x} {k} le'))))
  ...        | yes p'' | _ = contradiction p'' (<⇒≱ (+-monoˡ-< l (≰⇒> ¬p)))
  ...        | no ¬p'' | no ¬p''' = cong Var (aux-calc-2 {x} {l} {k} le')
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {Abs s} le le' = cong Abs (↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {ℕ.suc q} {ℕ.suc c} {l} {s} (s≤s le) le')
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {App s s₁} le le' = cong₂ App (↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {s} le le') (↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {s₁} le le')
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {LabI x} le le' = refl
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {LabE f s} le le' = cong₂ LabE (f-ext (λ x → f-ext (λ ins → ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {f x ins} le le'))) (↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {s} le le')

  -- corollary
  ↑k,sucq[↑1,c[s]]≡↑1,c[↑k,q[s]] : {n : ℕ} {k : ℤ} {q c : ℕ} {s : Exp {n}} → c ≤ᴺ q → + 0 <ᶻ k →  ↑ k , ℕ.suc q [ ↑ + 1 , c [ s ] ] ≡ ↑ + 1 , c [ ↑ k , q [ s ] ]
  ↑k,sucq[↑1,c[s]]≡↑1,c[↑k,q[s]] {n} {k} {q} {c} {s} le le'
    rewrite (sym (n+1≡sucn{q}))
          = ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]]{n}{k}{q}{c}{1}{s} le le'

  ↑Lab-triv : {n : ℕ} {s : Subset n} {l : Fin n} (i : l ∈ s) (k : ℤ) (q : ℕ) → LabI i ≡ ↑ k , q [ LabI i ] 
  ↑Lab-triv {n} {s} {l} i k q = refl

  ↑ᴺ-triv : {m : ℤ} {n x : ℕ} → x ≥ᴺ n → ↑ᴺ m , n [ x ] ≡ ∣ + x +ᶻ m ∣ 
  ↑ᴺ-triv {m} {n} {x} ge
    with x <ᴺ? n
  ... | yes p = contradiction p (≤⇒≯ ge)
  ... | no ¬p = refl

  ↑ᴺ⁰-refl : {n : ℕ} {c : ℕ} {x : ℕ} → ↑ᴺ + 0 , c [ x ] ≡ x
  ↑ᴺ⁰-refl {n} {c} {x}
    with x <ᴺ? c
  ...  | yes p = refl
  ...  | no ¬p = +-identityʳ x

  ↑⁰-refl : {n : ℕ} {c : ℕ} {e : Exp {n}} → ↑ + 0 , c [ e ] ≡ e
  ↑⁰-refl {n} {c} {Var x} = cong Var (↑ᴺ⁰-refl{n}{c}{x})
  ↑⁰-refl {n} {c} {Abs e} = cong Abs (↑⁰-refl{n}{ℕ.suc c}{e})
  ↑⁰-refl {n} {c} {App e e₁} = cong₂ App (↑⁰-refl{n}{c}{e}) (↑⁰-refl{n}{c}{e₁})
  ↑⁰-refl {n} {c} {LabI x} = refl
  ↑⁰-refl {n} {c} {LabE x e} = cong₂ LabE (f-ext (λ l → f-ext λ i → ↑⁰-refl{n}{c}{x l i})) (↑⁰-refl{n}{c}{e})

  --- properties of substitution

  subst-trivial : {n : ℕ} {x : ℕ} {s : Exp {n}} → [ x ↦ s ] Var x ≡ s
  subst-trivial {n} {x} {s}
    with x Data.Nat.≟ x
  ...  | no ¬p = contradiction refl ¬p
  ...  | yes p = refl

  var-subst-refl : {N n m : ℕ} {neq : n ≢ m} {e : Exp {N}} → [ n ↦ e ] (Var m) ≡ (Var m)
  var-subst-refl {N} {n} {m} {neq} {e}
    with _≟ᴺ_ n m
       | map′ (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n) (Data.Bool.Properties.T? (m ≡ᵇ n))
  ...  | yes p | _ = contradiction p neq
  ...  | no ¬p | yes q = contradiction q (≢-sym ¬p)
  ...  | no ¬p | no ¬q = refl

  -- this should be true for all k, but limiting to positive k makes the proof simpler
  aux-calc-3 : {m x : ℕ} {k : ℤ} → k >ᶻ + 0 → ∣ + m +ᶻ k ∣ ≡ ∣ + x +ᶻ k ∣ → m ≡ x
  aux-calc-3 {m} {x} {+_ n} gt eqv = +-cancelʳ-≡ m x eqv

  aux-calc-4 : {m x : ℕ} {k : ℤ} → k >ᶻ + 0 → m ≤ᴺ x → m <ᴺ ∣ + x +ᶻ k ∣
  aux-calc-4 {m} {x} {+_ zero} (+<+ ())
  aux-calc-4 {m} {x} {+[1+ n ]} (+<+ (s≤s z≤n)) leq = a≤b<c⇒a<c leq (m<m+n x {ℕ.suc n} (s≤s z≤n))

  subst-shift-swap : {n : ℕ} {k : ℤ} {x q : ℕ} {s e : Exp {n}} → k >ᶻ + 0 → ↑ k , q [ [ x ↦ e ] s ] ≡ [ ↑ᴺ k , q [ x ] ↦ ↑ k , q [ e ] ] ↑ k , q [ s ]
  subst-shift-swap {n} {k} {x} {q} {Var m} {e} gt
    with m ≟ᴺ x
  ...  | yes p
       with m <ᴺ? q | x <ᴺ? q
  ...     | yes p' | yes p''
          with m ≟ᴺ x
  ...        | yes p''' = refl
  ...        | no ¬p''' = contradiction p ¬p'''
  subst-shift-swap {n} {k} {x} {q} {Var m} {e} gt
       | yes p | yes p' | no ¬p'' rewrite (cong ℕ.suc p) = contradiction p' ¬p''
  subst-shift-swap {n} {k} {x} {q} {Var m} {e} gt
       | yes p | no ¬p' | yes p'' rewrite (cong ℕ.suc p) = contradiction p'' ¬p'
  subst-shift-swap {n} {k} {x} {q} {Var m} {e} gt
       | yes p | no ¬p' | no ¬p''
       with ∣ + m +ᶻ k ∣ ≟ᴺ ∣ + x +ᶻ k ∣
  ...     | yes p''' = refl
  ...     | no ¬p''' rewrite p = contradiction refl ¬p'''
  subst-shift-swap {n} {k} {x} {q} {Var m} {e} gt
       | no ¬p
       with m <ᴺ? q | x <ᴺ? q
  ...     | yes p' | yes p''
          with m ≟ᴺ x
  ...        | yes p''' = contradiction p''' ¬p
  ...        | no ¬p''' = refl
  subst-shift-swap {n} {k} {x} {q} {Var m} {e} gt
      | no ¬p | yes p' | no ¬p''
      with m ≟ᴺ ∣ + x +ᶻ k ∣
  ...    | yes p''' = contradiction p''' (<⇒≢ (aux-calc-4 gt (≤-pred (≤-trans p' (≰⇒≥ ¬p'')))))
  ...    | no ¬p''' = refl
  subst-shift-swap {n} {k} {x} {q} {Var m} {e} gt
      | no ¬p | no ¬p' | yes p''
      with ∣ + m +ᶻ k ∣ ≟ᴺ x
  ...    | yes p''' = contradiction p''' (≢-sym (<⇒≢ (aux-calc-4{x}{m}{k} gt (≤-pred (≤-trans p'' (≰⇒≥ ¬p'))))))
  ...    | no ¬p''' = refl
  subst-shift-swap {n} {k} {x} {q} {Var m} {e} gt
      | no ¬p | no ¬p' | no ¬p''
      with ∣ + m +ᶻ k ∣ ≟ᴺ ∣ + x +ᶻ k ∣
  ...    | yes p''' = contradiction p''' (contraposition (aux-calc-3 gt) ¬p)
  ...    | no ¬p''' = refl
  subst-shift-swap {n} {k} {x} {q} {Abs s} {e} gt
    with (subst-shift-swap{n}{k}{ℕ.suc x}{ℕ.suc q}{s}{↑¹[ e ]} gt)
  ...  | w
       rewrite (↑k,sucq[↑1,c[s]]≡↑1,c[↑k,q[s]] {n} {k} {q} {0} {e} z≤n gt)
             | (suc[↑ᴺk,l[x]]≡↑ᴺk,sucl[sucx] {k} {q} {x} gt)
             = cong Abs w
  subst-shift-swap {n} {k} {x} {q} {App s₁ s₂} {e} gt = cong₂ App (subst-shift-swap {n} {k} {x} {q} {s₁} {e} gt) (subst-shift-swap {n} {k} {x} {q} {s₂} {e} gt)
  subst-shift-swap {n} {k} {x} {q} {LabI ins} {e} gt = refl
  subst-shift-swap {n} {k} {x} {q} {LabE f s} {e} gt = cong₂ LabE (f-ext (λ l → f-ext (λ ins → subst-shift-swap {n} {k} {x} {q} {f l ins} {e} gt))) (subst-shift-swap {n} {k} {x} {q} {s} {e} gt)

  --- properties and manipulation of environments
  
  var-env-< : {N : ℕ} {Γ : Env {N}} {T : Ty} {n : ℕ} (j : n ∶ T ∈ Γ) → n <ᴺ (length Γ)
  var-env-< {N} {.(T ∷ _)} {T} {.0} here = s≤s z≤n
  var-env-< {N} {.(_ ∷ _)} {T} {.(ℕ.suc _)} (there j) = s≤s (var-env-< j)

  -- type to determine whether var type judgement in env. (Δ ++ Γ) is in Δ or Γ
  data extract-env-or {n : ℕ} {Δ Γ : Env {n}} {T : Ty} {x : ℕ} : Set where
    in-Δ : x ∶ T ∈ Δ → extract-env-or
    -- x ≥ length Δ makes sure that x really is in Γ; e.g.
    -- x = 1, Δ = (S ∷ T), Γ = (T ∷ Γ'); here 1 ∶ T ∈ Δ as well as (1 ∸ 2) ≡ 0 ∶ T ∈ Γ
    in-Γ : (x ≥ᴺ length Δ) → (x ∸ length Δ) ∶ T ∈ Γ → extract-env-or

  extract : {n : ℕ} {Δ Γ : Env {n}} {T : Ty} {x : ℕ} (j : x ∶ T ∈ (Δ ++ Γ)) → extract-env-or{n}{Δ}{Γ}{T}{x}
  extract {n} {[]} {Γ} {T} {x} j = in-Γ z≤n j
  extract {n} {x₁ ∷ Δ} {Γ} {.x₁} {.0} here = in-Δ here
  extract {n} {x₁ ∷ Δ} {Γ} {T} {ℕ.suc x} (there j)
    with extract {n} {Δ} {Γ} {T} {x} j
  ...  | in-Δ j'  = in-Δ (there j')
  ...  | in-Γ ge j'' = in-Γ (s≤s ge) j''

  ext-behind : {n : ℕ} {Δ Γ : Env {n}} {T : Ty} {x : ℕ} → x ∶ T ∈ Δ → x ∶ T ∈ (Δ ++ Γ)
  ext-behind here = here
  ext-behind (there j) = there (ext-behind j)

  ext-front : {N n : ℕ} {Γ Δ : Env{N}} {S : Ty} → n ∶ S ∈ Γ → (n +ᴺ (length Δ)) ∶ S ∈ (Δ ++ Γ)
  ext-front {N} {n} {Γ} {[]} {S} j
    rewrite (n+length[]≡n{A = Ty {N}}{n = n})
          = j
  ext-front {N} {n} {Γ} {T ∷ Δ} {S} j
    rewrite (+-suc n (foldr (λ _ → ℕ.suc) 0 Δ))
          = there (ext-front j)

  swap-env-behind : {n : ℕ} {Γ Δ : Env {n}} {T : Ty} → 0 ∶ T ∈ (T ∷ Γ) → 0 ∶ T ∈ (T ∷ Δ)
  swap-env-behind {n}{Γ} {Δ} {T} j = here

  swap-type : {n : ℕ} {Δ ∇ Γ : Env {n}} {T : Ty} → (length Δ) ∶ T ∈ (Δ ++ T ∷ ∇ ++ Γ) → (length Δ +ᴺ length ∇) ∶ T ∈ (Δ ++ ∇ ++ T ∷ Γ)
  swap-type {n} {Δ} {∇} {Γ} {T} j
    with extract{n}{Δ}{T ∷ ∇ ++ Γ} j
  ...  | in-Δ x = contradiction (var-env-< {n}{Δ} {T} x) (<-irrefl refl)
  ...  | in-Γ le j'
       with extract{n}{T ∷ ∇}{Γ} j'
  ...     | in-Δ j''
          rewrite (n∸n≡0 (length Δ))
                | (sym (length[A++B]≡length[A]+length[B]{lzero}{Ty}{Δ}{∇}))
                | (sym (++-assoc{lzero}{Ty}{Δ}{∇}{T ∷ Γ}))
                = ext-front{n}{0}{T ∷ Γ}{Δ ++ ∇}{T} (swap-env-behind{n}{∇}{Γ}{T} j'')
  ...     | in-Γ le' j''
          rewrite (length[A∷B]≡suc[length[B]]{lzero}{Ty}{T}{∇})
                | (n∸n≡0 (length Δ))
                = contradiction le' (<⇒≱ (s≤s z≤n))

  env-pred : {n : ℕ} {Γ : Env {n}} {S T : Ty} {y : ℕ} {gt : y ≢ 0} → y ∶ T ∈ (S ∷ Γ) → ∣ y ⊖ 1 ∣ ∶ T ∈ Γ
  env-pred {n} {Γ} {S} {.S} {.0} {gt} here = contradiction refl gt
  env-pred {n} {Γ} {S} {T} {.(ℕ.suc _)} {gt} (there j) = j

  env-type-equiv-here : {n : ℕ} {Γ : Env {n}} {S T : Ty} → 0 ∶ T ∈ (S ∷ Γ) → T ≡ S
  env-type-equiv-here {n} {Γ} {S} {.S} here = refl

  env-type-equiv : {n : ℕ} {Δ ∇ : Env {n}} {S T : Ty} → length Δ ∶ T ∈ (Δ ++ S ∷ ∇) → T ≡ S
  env-type-equiv {n} {Δ} {∇} {S} {T} j
    with extract{n}{Δ}{S ∷ ∇} j
  ...  | in-Δ x = contradiction (var-env-< x) (≤⇒≯ ≤-refl) 
  ...  | in-Γ x j'
       rewrite (n∸n≡0 (length Δ))
             = env-type-equiv-here {n} {∇} {S} {T} j'

  env-type-equiv-j : {N : ℕ} {Γ : Env {N}} {S T : Ty} {n : ℕ} → T ≡ S → n ∶ T ∈ Γ → n ∶ S ∈ Γ
  env-type-equiv-j {N} {Γ} {S} {T} {n} eq j
    rewrite eq
          = j

  -- extension of environment

  ext : {N : ℕ} {Γ Δ ∇ : Env {N}} {S : Ty} {s : Exp} → (∇ ++ Γ) ⊢ s ∶ S → (∇ ++ Δ ++ Γ) ⊢ ↑ (ℤ.pos (length Δ)) , length ∇ [ s ] ∶ S
  ext {N} {Γ} {Δ} {∇} (TVar {m = n} x)
    with extract{N}{∇}{Γ} x
  ... | in-Δ x₁
      with n <ᴺ? length ∇
  ...    | yes p = TVar (ext-behind x₁)
  ...    | no ¬p = contradiction (var-env-< x₁) ¬p
  ext {N} {Γ} {Δ} {∇} (TVar {m = n} x)
      | in-Γ x₁ x₂
      with n <ᴺ? length ∇
  ...    | yes p = contradiction x₁ (<⇒≱ p)
  ...    | no ¬p
         with (ext-front{N}{n ∸ length ∇}{Γ}{∇ ++ Δ} x₂)
  ...       | w
            rewrite (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{Δ})
                  | (sym (+-assoc (n ∸ length ∇) (length ∇) (length Δ)))
                  | (m∸n+n≡m{n}{length ∇} (≮⇒≥ ¬p))
                  | (++-assoc{lzero}{Ty}{∇}{Δ}{Γ})
                  = TVar w 
  ext {N} {Γ} {Δ} {∇} {Fun T₁ T₂} {Abs e} (TAbs j) = TAbs (ext{N}{Γ}{Δ}{T₁ ∷ ∇} j)
  ext {N} {Γ} {Δ} {∇} {S} {App s₁ s₂} (TApp{T₁ = T₁} j₁ j₂) = TApp (ext{N}{Γ}{Δ}{∇}{Fun T₁ S} j₁) (ext{N}{Γ}{Δ}{∇}{T₁} j₂)
  ext {N} {Γ} {Δ} {∇} {S} {LabI ins} (TLabI{x = x}{s} .ins) = TLabI{x = x}{s} ins
  ext {N} {Γ} {Δ} {∇} {S} {LabE f e} (TLabEl{f = .f} f' j) = TLabEl (λ l i → ext{N}{Γ}{Δ}{∇} (f' l i)) (ext{N}{Γ}{Δ}{∇} j)
  ext {N} {Γ} {[]} {∇} {S} {LabE f .(Var m)} (TLabEx {s = s} {f = .f} f' (TVar {m = m} x))
    rewrite (↑ᴺ⁰-refl{N}{length ∇}{m})
          | (f-ext (λ l → f-ext (λ i → ↑⁰-refl{N}{length ∇}{f l i})))
          = TLabEx f' (TVar x)
  -- required lemma needs length Δ > 0, hence the case split
  ext {N} {Γ} {t ∷ Δ} {∇} {S} {LabE f .(Var m)} (TLabEx {s = s} {f = .f} f' (TVar {m = m} x))
    with extract{N}{∇}{Γ} x
  ...  | in-Δ x₁
       with m <ᴺ? length ∇
  ...     | no ¬p = contradiction (var-env-< x₁) ¬p
  ...     | yes p
          with (λ l i → ext{N}{Γ}{t ∷ Δ}{∇} (f' l i))
  ...        | w = TLabEx (rw w) (TVar (ext-behind x₁)) -- if m < k, [ m → ↑ₖ x ] (↑ₖ s) ≡ ↑ₖ ([ m ↦ x ] s)
 
          where rw : ((l : Fin N) → (i : l ∈ s) → (∇ ++ (t ∷ Δ) ++ Γ) ⊢ ↑ + length (t ∷ Δ) , length ∇ [ [ m ↦ LabI i ] (f l i) ] ∶ S)
                   → ((l : Fin N) → (i : l ∈ s) → (∇ ++ (t ∷ Δ) ++ Γ) ⊢ [ m ↦ LabI i ] ↑ + length (t ∷ Δ) , length ∇ [ f l i ] ∶ S)
                rw q l i
                  with q l i              
                ...  | w
                     rewrite (subst-shift-swap{N}{+ length (t ∷ Δ)}{m}{length ∇}{f l i}{LabI i} (+<+ (s≤s z≤n)))
                     with m <ᴺ? length ∇
                ...     | yes p = w 
                ...     | no ¬p = contradiction p ¬p
  ext {N} {Γ} {t ∷ Δ} {∇} {S} {LabE f .(Var _)} (TLabEx {s = s}{f = .f} f' (TVar{m = m} x))
       | in-Γ x₁ x₂
       with m <ᴺ? length ∇
  ...     | yes p = contradiction x₁ (<⇒≱ p)
  ...     | no ¬p
          with (λ l i → (ext{N}{Γ}{t ∷ Δ}{∇} (f' l i))) | (ext-front{N}{m ∸ length ∇}{Γ}{∇ ++ (t ∷ Δ)} x₂)
  ...        | w | w'
             rewrite (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{t ∷ Δ})
                   | (sym (+-assoc (m ∸ length ∇) (length ∇) (length (t ∷ Δ))))
                   | (m∸n+n≡m{m}{length ∇} (≮⇒≥ ¬p))
                   | (++-assoc{lzero}{Ty}{∇}{t ∷ Δ}{Γ})
                  = TLabEx (rw w) (TVar w')
                  
             where rw : ((l : Fin N) → (i : l ∈ s) → ((∇ ++ (t ∷ Δ) ++ Γ) ⊢ ↑ + length (t ∷ Δ) , length ∇ [ [ m ↦ LabI i ] f l i ] ∶ S))
                      → ((l : Fin N) → (i : l ∈ s) → ((∇ ++ (t ∷ Δ) ++ Γ) ⊢ [ m +ᴺ length (t ∷ Δ) ↦ LabI i ] ↑ + length (t ∷ Δ) , length ∇ [ f l i ] ∶ S))
                   rw q l i
                     with q l i
                   ...  | w
                        rewrite (subst-shift-swap {N} {+ length (t ∷ Δ)} {m} {length ∇} {f l i} {LabI i} (+<+ (s≤s z≤n)))
                        with m <ᴺ? length ∇
                   ...     | yes p = contradiction x₁ (<⇒≱ p)
                   ...     | no ¬p =  w 

  --- (trivial) typing properties

  labI-subset-eq : {n : ℕ} {Γ : Env {n}} {s s' : Subset n} {l : Fin n} {x : l ∈ s} → Γ ⊢ LabI{s = s} x ∶ Label s' → s ≡ s'
  labI-subset-eq {n} {Γ} {s} {.s} {l} {x} (TLabI .x) = refl

  subset-eq : {n : ℕ} {s s' : Subset n} → Label s ≡ Label s' → s ≡ s'
  subset-eq {n} {s} {.s} refl = refl

  ---- progress and preservation

  -- progress theorem, i.e. a well-typed closed expression is either a value
  -- or can be reduced further
  data Progress {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ∶ T} : Set where
    step : {e' : Exp{n}} → e ⇒ e' → Progress e
    value : Val e → Progress e

  progress : {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ∶ T} → Progress e {T} {j}
  progress (Var x) {T} {TVar ()}
  progress (Abs e) = value VFun
  progress (App e e₁) {T} {TApp{T₁ = T₁}{T₂ = .T} j j₁}
    with progress e {Fun T₁ T} {j}
  ...  | step x = step (ξ-App1 x)
  ...  | value VFun
       with progress e₁ {T₁} {j₁}
  ...     | step x₁ = step (ξ-App2 VFun x₁)
  ...     | value x₁ = step (β-App x₁)
  progress (LabI ins) {Label s} {TLabI .ins} = value VLab
  progress (LabE f (LabI ins)) {T} {j = TLabEl f' j} = step (β-LabE ins)
  progress {n} (LabE f (Var m)) {T} {TLabEx f' (TVar ())}


  ---

  -- preservation under substitution
  preserve-subst : {n : ℕ} {T S : Ty} {Γ Δ : Env {n}} {e s : Exp} {v : Val s} (j : (Δ ++ (S ∷ Γ)) ⊢ e ∶ T) (j' : Γ ⊢ s ∶ S)
                                                                            → (Δ ++ Γ) ⊢  ↑ -[1+ 0 ] , length Δ [ [ length Δ ↦ ↑ (ℤ.pos (ℕ.suc (length Δ))) , 0 [ s ] ] e ] ∶ T
  preserve-subst {n} {T} {S} {Γ} {Δ} {.(Var _)} {s} {v} (TVar{m} x) j'
    with extract{n}{Δ}{S ∷ Γ}{T}{m} x
  ...  | in-Δ x₁
       with m Data.Nat.≟ length Δ
  ...     | yes p = contradiction p (<⇒≢ (var-env-< x₁))
  ...     | no ¬p
          with m <ᴺ? length Δ
  ...        | yes q = TVar (ext-behind{n}{Δ}{Γ} x₁)
  ...        | no ¬q = contradiction (var-env-< x₁) ¬q
  preserve-subst {n} {T} {S} {Γ} {Δ} {e} {s} {v} (TVar{m} x) j'
       | in-Γ x₁ x₂
       with m Data.Nat.≟ length Δ
  ...     | yes p
          rewrite (↑k,q[↑l,c[s]]≡↑l+k,c[s]{n}{ -[1+ 0 ]}{+[1+ length Δ ]}{length Δ}{0}{s} (+≤+ n≤sucn) z≤n)
                | p
                | (env-type-equiv x)
                = ext{n}{Γ}{Δ}{[]} j'
  ...     | no ¬p
          with m <ᴺ? length Δ
  ...        | yes q = contradiction x₁ (<⇒≱ q)
  ...        | no ¬q rewrite (sym (minus-1{m}{length Δ}{≤∧≢⇒< x₁ (≢-sym ¬p)}))
                           = TVar (ext-front{Δ = Δ} (env-pred{n}{Γ}{S}{T}{gt = ≢-sym (<⇒≢ (m>n⇒m∸n≥1 (≤∧≢⇒< x₁ (≢-sym ¬p))))} x₂))
  preserve-subst {n} {T} {S} {Γ} {Δ} {(Abs e')} {s} {v}(TAbs{T₁ = T₁}{T₂} j) j'
    with preserve-subst{n}{T₂}{S}{Γ}{T₁ ∷ Δ}{e'}{s}{v} j j'
  ...  | w
       rewrite (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s]{n}{+ 1}{+[1+ length Δ ]}{0}{s} (+≤+ z≤n))
             | (length[A∷B]≡suc[length[B]]{lzero}{Ty}{T₁}{Δ})
             | (n+1≡sucn{length Δ})
             = TAbs w
  preserve-subst {n} {T} {S} {Γ} {Δ} {.(App _ _)} {s} {v} (TApp j j₁) j' = TApp (preserve-subst{v = v} j j') (preserve-subst{v = v} j₁ j')
  preserve-subst {n} {.(Label _)} {S} {Γ} {Δ} {.(LabI ins)} {s} {v} (TLabI ins) j' = TLabI ins
  preserve-subst {n} {T} {S} {Γ} {Δ} {.(LabE _ (LabI _))} {s} {v} (TLabEl{ins = ins} f j) j' = TLabEl (λ l i → preserve-subst{v = v} (f l i) j') (TLabI ins)
  preserve-subst {n} {T} {Fun S₁ S₂} {Γ} {Δ} {LabE f .(Var m)} {Abs s} {v} (TLabEx {m = m} f' (TVar{T = Label s'} z)) j'
    with m ≟ᴺ length Δ | preserve-subst (TVar z) j'
  ...  | yes p | w rewrite p = contradiction (env-type-equiv z) (λ ())
  ...  | no ¬p | w = TLabEx {!!} w
       where rw : ((l : Fin n) → (i : l ∈ s') → (Δ ++ Γ) ⊢ ↑ -[1+ 0 ] , length Δ [ [ length Δ ↦ Abs ↑ +[1+ length Δ ] , 1 [ s ] ] ([ m ↦ LabI i ] f l i) ] ∶ T)
                → (l : Fin n) → (i : l ∈ s') → (Δ ++ Γ) ⊢ [ ↑ᴺ -[1+ 0 ] , length Δ [ m ] ↦ LabI i ] (↑ -[1+ 0 ] , length Δ [ [ length Δ ↦ Abs ↑ +[1+ length Δ ] , 1 [ s ] ] f l i ]) ∶ T
             rw q l i
               with q l i
             ...  | w'
                  with m <ᴺ? length Δ
             ...     | yes p' = {!w'!}
             ...     | no ¬p' = {!!}  --- ?
  preserve-subst {n} {T} {(Label s)} {Γ} {Δ} {LabE{s = s'} f .(Var m)} {LabI {s = .s} x} {v} (TLabEx {m = m}{s = .s'} f' (TVar{T = Label .s'} z)) (TLabI{x = l}{s = .s} .x)
    with m ≟ᴺ length Δ | preserve-subst (TVar z) (TLabI x)
  ...  | yes p | w
       rewrite p
             | subset-eq (env-type-equiv z) =  (TLabEl{f = λ l₁ i → ↑ -[1+ 0 ] , length Δ [ [ length Δ ↦ LabI x ] (f l₁ i) ]} (λ l₁ i → {!f' l₁ i!}) (TLabI x))

{- TLabEl (λ l i → {!preserve-subst (f' l i) (TLabI x)!}) w

Goal: (Δ ++ Γ) ⊢
      ↑ -[1+ 0 ] , foldr (λ _ → ℕ.suc) 0 Δ [
      [ foldr (λ _ → ℕ.suc) 0 Δ ↦ LabI x ] f l i ]
      ∶ T
Have: (Δ ++ Γ) ⊢
      ↑ -[1+ 0 ] , length Δ [
      [ length Δ ↦ LabI x ] ([ foldr (λ _ → ℕ.suc) 0 Δ ↦ LabI i ] f l i)
      ]
      ∶ T
-}          
  ...  | no ¬p | w = TLabEx (λ l i → {!!}) w

  -- preservation theorem, i.e. a well-typed expression reduces to a well-typed expression

  preserve : {n : ℕ} {T : Ty {n}} {Γ : Env} (e e' : Exp) (j : Γ ⊢ e ∶ T) (r : e ⇒ e') → Γ ⊢ e' ∶ T
  preserve {n} {T} {Γ} .(App _ _) .(App _ _) (TApp j j') (ξ-App1{e₁ = e₁}{e₁' = e₁'} r) = TApp (preserve e₁ e₁' j r) j'
  preserve {n} {T} {Γ} .(App _ _) .(App _ _) (TApp j j') (ξ-App2{e = e}{e'}{v} x r) = TApp j (preserve e e' j' r)
  preserve {n} {T} {Γ} (App (Abs e) s') .(↑ -[1+ 0 ] , 0 [ [ 0 ↦ ↑ + 1 , 0 [ s' ] ] e ]) (TApp (TAbs j) j') (β-App x) = preserve-subst{Δ = []} j j'
  preserve {n} {T} {Γ} (LabE f (LabI ins)) .(f _ ins) (TLabEl f' j) (β-LabE{x = x} ins) = f' x ins
  
