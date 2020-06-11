-- simply-typed label-dependent λ-calculus w/ DeBruijn indices

-- {-# OPTIONS --show-implicit #-}

module LDLC where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Bool.Properties hiding (≤-trans ; <-trans ; ≤-refl ; <-irrefl)
open import Data.Empty
open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_ ; _≟_ to _≟ᴺ_)
open import Data.Nat.Properties renaming (_<?_ to _<ᴺ?_)
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_)
open import Data.Integer.Properties using (⊖-≥ ; 0≤n⇒+∣n∣≡n ; +-monoˡ-≤)
open import Data.List hiding (length)
open import Data.List.Relation.Unary.All
open import Relation.Unary using (Decidable)
open import Data.Vec.Relation.Unary.Any
open import Data.Vec.Base hiding (length ; _++_ ; foldr)
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-trans)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Data.Fin
open import Data.Fin.Subset renaming (∣_∣ to ∣_∣ˢ)
open import Data.Fin.Subset.Properties using (anySubset?)
open import Data.Fin.Properties using (any?)
open import Data.Product
open import Data.Sum
open import Function

open import Extensionality
open import Auxiliary

module defs where
  data Exp {n : ℕ} : Set where
    Var : ℕ → Exp {n}
    Abs : Exp {n} → Exp {n}
    App : Exp {n} → Exp {n} → Exp {n}
    LabI : Fin n → Exp {n}
    LabE : {s : Subset n} → (f : ∀ l → l ∈ s → Exp {n}) → Exp {n} → Exp {n}
    Prod : Exp {n} → Exp {n} → Exp {n}
    FakeLet : Exp {n} → Exp {n} → Exp {n}

  data Ty {n : ℕ} : Set where
    Label : Subset n → Ty
    Pi : Ty {n} → Ty {n} → Ty
    Sigma : Ty {n} → Ty {n} → Ty
    Case : {s : Subset n} → (f : ∀ l → l ∈ s → Ty {n}) → Exp {n} → Ty 
  
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
  ↑ d , c [ LabI x ] = LabI x
  ↑ d , c [ LabE f e ] = LabE (λ l x → ↑ d , c [ (f l x) ]) (↑ d , c [ e ])
  ↑ d , c [ Prod e e' ] = Prod (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])
  ↑ d , c [ FakeLet e e' ] = FakeLet (↑ d , c [ e ]) (↑ d , (ℕ.suc c) [ e' ])

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
  [ k ↦ s ] Prod e e' = Prod ([ k ↦ s ] e) ([ ℕ.suc k ↦ ↑¹[ s ] ] e')
  [ k ↦ s ] FakeLet e e' = FakeLet ([ k ↦ s ] e) ([ ℕ.suc k ↦ ↑¹[ s ] ] e')

  -- type substitution
  [_↦_]ᵀ_ : ∀ {n} → ℕ → Exp {n} → Ty {n} → Ty {n}
  [ k ↦ s ]ᵀ Label x = Label x
  [ k ↦ s ]ᵀ Pi t t₁ = Pi ([ k ↦ s ]ᵀ t) ([ k ↦ s ]ᵀ t₁)
  [ k ↦ s ]ᵀ Sigma t t₁ = Sigma ([ k ↦ s ]ᵀ t) ([ k ↦ s ]ᵀ t₁)
  [ k ↦ s ]ᵀ Case f e = Case (λ l x → [ k ↦ s ]ᵀ (f l x)) ([ k ↦ s ] e)

  -- variable in expression
  data _∈`_ {N : ℕ} : ℕ → Exp {N} → Set where
    in-Var : {n : ℕ} → n ∈` Var n
    in-Abs : {n : ℕ} {e : Exp} → (ℕ.suc n) ∈` e → n ∈` Abs e
    in-App : {n : ℕ} {e e' : Exp} → n ∈` e ⊎ n ∈` e' → n ∈` App e e'
    in-LabE : {n : ℕ} {s : Subset N} {f : (∀ l → l ∈ s → Exp {N})} {e : Exp {N}} → (∃₂ λ l i → n ∈` (f l i)) ⊎ n ∈` e → n ∈` LabE {N} {s} f e
    
  -- Type environment, formation and typing of expressions
  data TEnv {n : ℕ} : Set
  data _∶_∈_ {n : ℕ} : ℕ → Ty {n} → TEnv {n} → Set
  data _⊢_ {n : ℕ} : TEnv {n} → Ty {n} → Set
  data _⊢_∶_ {n : ℕ} : TEnv {n} → Exp {n} → Ty {n} → Set

  data TEnv {n} where
    [] : TEnv
    ⟨_,_⟩ : (T : Ty) (Γ : TEnv {n}) {ok : Γ ⊢ T} → TEnv

  length : {n : ℕ} → TEnv {n} → ℕ
  length [] = 0
  length ⟨ T , Γ ⟩ = ℕ.suc (length Γ)

  data _∶_∈_ {n} where
    here : {T : Ty} {Γ : TEnv} {ok : Γ ⊢ T} → 0 ∶ T ∈ ⟨ T , Γ ⟩ {ok}
    there : {n : ℕ} {T₁ T₂ : Ty} {Γ : TEnv} {ok : Γ ⊢ T₂} → n ∶ T₁ ∈ Γ → (ℕ.suc n) ∶ T₁ ∈ ⟨ T₂ , Γ ⟩ {ok}

  -- Type formation
  data _⊢_ {n} where
    TLabF : {Γ : TEnv {n}} {s : Subset n} → Γ ⊢ Label s
    TPiF : {Γ : TEnv {n}} {A B : Ty} {x : ℕ} → (ok : Γ ⊢ A) → ⟨ A , Γ ⟩ {ok} ⊢ B → Γ ⊢ Pi A B
    TSigmaF : {Γ : TEnv {n}} {A B : Ty} {x : ℕ} → (ok : Γ ⊢ A) → ⟨ A , Γ ⟩ {ok} ⊢ B → Γ ⊢ Sigma A B
    TCaseF : {Γ : TEnv {n}} {s : Subset n} {e : Exp {n}} {f : ∀ l → l ∈ s → Ty} → (f' : ∀ l i → Γ ⊢ (f l i))
                                                                               → Γ ⊢ e ∶ Label s
                                                                               → Γ ⊢ Case {n} {s} f e

  -- Typing expressions
  data _⊢_∶_ {n} where
    TVarE : {m : ℕ} {Γ : TEnv} {T : Ty} → m ∶ T ∈ Γ → Γ ⊢ (Var m) ∶ T
    TPiI : {Γ : TEnv} {A B : Ty} {e : Exp} {ok : Γ ⊢ A} → ⟨ A , Γ ⟩ {ok} ⊢ e ∶ B → Γ ⊢ (Abs e) ∶ (Pi A B)
    TPiE : {Γ : TEnv} {A B : Ty} {e e' : Exp} → Γ ⊢ e ∶ (Pi A B) → Γ ⊢ e' ∶ A → Γ ⊢ ([ 0 ↦ e' ]ᵀ B) → Γ ⊢ App e e' ∶ ([ 0 ↦ e' ]ᵀ B)
    TSigmaI : {Γ : TEnv} {A B : Ty} {e e' : Exp} {ok : Γ ⊢ A} → Γ ⊢ e ∶ A → ⟨ A , Γ ⟩ {ok} ⊢ e' ∶ B → Γ ⊢ Prod e e' ∶ (Sigma A B)
    TSigmaE : {Γ : TEnv {n}} {A B C : Ty} {e e' : Exp} {ok : Γ ⊢ A} {ok' : ⟨ A , Γ ⟩ {ok} ⊢ B} → Γ ⊢ e ∶ (Sigma A B)
                                                                                               → ⟨ B , ⟨ A , Γ ⟩ {ok} ⟩ {ok'} ⊢ e' ∶ C
                                                                                               →  Γ ⊢ FakeLet e e' ∶ C
    TLabI : {Γ : TEnv} {x : Fin n} {s : Subset n} → (ins : x ∈ s) → Γ ⊢ LabI x ∶ Label {n} s
    TLabEl : {Γ : TEnv {n}} {T : Ty} {s : Subset n} {x : Fin n} {ins : x ∈ s} {f : ∀ l → l ∈ s → Exp} {scopecheck : ∀ l i m → m ∈` (f l i) → m <ᴺ length Γ}
                                                                                                    → Γ ⊢ f x ins ∶ T
                                                                                                    → Γ ⊢ LabI {n} x ∶ Label {n} s
                                                                                                    → Γ ⊢ LabE {n} {s} f (LabI {n} x) ∶ T
    TLabEx : {Γ : TEnv} {T : Ty} {m : ℕ} {s : Subset n} {f : ∀ l → l ∈ s → Exp} → (f' : ∀ l i → (Γ ⊢ [ m ↦ (LabI l) ] (f l i) ∶ T))
                                                                                → Γ ⊢ Var m ∶ Label {n} s
                                                                                → Γ ⊢ LabE {n} {s} f (Var m) ∶ T
                                                                               
{-
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
  eval (TLabEl {x = x}{ins = ins}{f = f} j j') Val-Γ = eval j Val-Γ
  eval (TLabEx {m = m}{s}{f} f' j) Val-Γ
    with eval j Val-Γ    -- evaluate variable
  ... | x , ins = eval (f' x ins) Val-Γ


-- operational semantics (call-by-value)
module operational where
  open defs

  data Val {n : ℕ} : Exp {n} → Set where
    VFun : {e : Exp} → Val (Abs e)
    VLab : {x : Fin n} → Val (LabI x)

  -- reduction relation
  data _⇒_ {n : ℕ} : Exp {n} → Exp {n} → Set where
    ξ-App1 : {e₁ e₁' e₂ : Exp} → e₁ ⇒ e₁' → App e₁ e₂ ⇒ App e₁' e₂
    ξ-App2 : {e e' v : Exp} → Val v → e ⇒ e' → App v e ⇒ App v e'
    β-App : {e v : Exp} → Val v → (App (Abs e) v) ⇒ (↑⁻¹[ ([ 0 ↦ ↑¹[ v ] ] e) ])
    β-LabE : {s : Subset n} {f : ∀ l → l ∈ s → Exp} {x : Fin n} → (ins : x ∈ s) → LabE f (LabI x) ⇒ f x ins

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

  ↑Lab-triv : {n : ℕ} {l : Fin n} (k : ℤ) (q : ℕ) → LabI l ≡ ↑ k , q [ LabI l ] 
  ↑Lab-triv {n} {l} k q = refl

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

  -- inversive lemma for variable in expression relation
  inv-in-var : {N n m : ℕ} → _∈`_ {N} n (Var m) → n ≡ m
  inv-in-var {N} {n} {.n} in-Var = refl
  inv-in-abs : {N n : ℕ} {e : Exp {N}} → _∈`_ {N} n (Abs e) → (ℕ.suc n) ∈` e
  inv-in-abs {N} {n} {e} (in-Abs i) = i
  inv-in-app : {N n : ℕ} {e e' : Exp {N}} → _∈`_ {N} n (App e e') → (_∈`_ n e ⊎ _∈`_ n e')
  inv-in-app {N} {n} {e} {e'} (in-App d) = d
  inv-in-labe : {N n : ℕ} {s : Subset N} {f : (∀ l → l ∈ s → Exp {N})} {e : Exp {N}} → _∈`_ {N} n (LabE {N} {s} f e) → (∃₂ λ l i → n ∈` (f l i)) ⊎ n ∈` e
  inv-in-labe {N} {n} {s} {f} {e} (in-LabE d) = d

  notin-shift : {N n k q : ℕ} {e : Exp {N}} → n ≥ᴺ q → ¬ n ∈` e → ¬ ((n +ᴺ k) ∈` ↑ + k , q [ e ])
  notin-shift {N} {n} {k} {q} {Var x} geq j z
    with x <ᴺ? q
  ...  | no ¬p
       with x ≟ᴺ n
  ...     | yes p' rewrite p' = contradiction in-Var j
  ...     | no ¬p'
          with cong (_∸ k) (inv-in-var z)
  ...        | w
             rewrite (m+n∸n≡m n k)
                   | (m+n∸n≡m x k)
                   = contradiction (sym w) ¬p'
  notin-shift {N} {n} {k} {q} {Var .(n +ᴺ k)} geq j in-Var
       | yes p = contradiction geq (<⇒≱ (≤-trans (s≤s (m≤m+n n k)) p))  -- q ≤ n VS ℕ.suc (n + k) ≤ n
  notin-shift {N} {n} {k} {q} {Abs e} geq j (in-Abs x) = notin-shift (s≤s geq) (λ x₁ → contradiction (in-Abs x₁) j) x
  notin-shift {N} {n} {k} {q} {App e e₁} geq j z
    with dm2 (contraposition in-App j) | (inv-in-app z)
  ...  | fst , snd | inj₁ x = notin-shift geq fst x
  ...  | fst , snd | inj₂ y = notin-shift geq snd y
  notin-shift {N} {n} {k} {q} {LabI x} geq j () 
  notin-shift {N} {n} {k} {q} {LabE f e} geq j z
    with dm2 (contraposition in-LabE j) | (inv-in-labe z)
  ...  | fst , snd | inj₂ y = notin-shift geq snd y
  ...  | fst , snd | inj₁ (fst₁ , fst₂ , snd₁) = notin-shift geq (¬∃⟶∀¬ (¬∃⟶∀¬ fst fst₁) fst₂) snd₁

  -- corollary
  notin-shift-one : {N n : ℕ} {e : Exp{N}} → ¬ n ∈` e → ¬ (ℕ.suc n ∈` ↑¹[ e ])
  notin-shift-one {N} {n} {e} nin rewrite (sym (n+1≡sucn{n})) = notin-shift{N}{n}{1} z≤n nin
  
  -- if n ∉ fv(e), then substitution of n does not do anything
  subst-refl-notin : {N n : ℕ} {e e' : Exp {N}} → ¬ n ∈` e → [ n ↦ e' ] e ≡ e
  subst-refl-notin {N} {n} {Var x} {e'} nin
    with x ≟ᴺ n
  ...  | yes p rewrite p = contradiction in-Var nin
  ...  | no ¬p = refl
  subst-refl-notin {N} {n} {Abs e} {e'} nin = cong Abs (subst-refl-notin (contraposition in-Abs nin))
  subst-refl-notin {N} {n} {App e e₁} {e'} nin
    with dm2 (contraposition in-App nin)
  ...  | fst , snd = cong₂ App (subst-refl-notin fst) (subst-refl-notin snd)
  subst-refl-notin {N} {n} {LabI x} {e'} nin = refl
  subst-refl-notin {N} {n} {LabE x e} {e'} nin
    with dm2 (contraposition in-LabE nin)
  ...  | fst , snd = cong₂ LabE (f-ext (λ l → f-ext (λ x₁ → subst-refl-notin{e' = e'} (¬∃⟶∀¬ (¬∃⟶∀¬ (fst) l) x₁)))) (subst-refl-notin (snd))

  notin-subst : {N n : ℕ} {e e' : Exp {N}} → ¬ n ∈` e' → ¬ (n ∈` ([ n ↦ e' ] e))
  notin-subst {N} {n} {Var x} {e'} nin
    with x ≟ᴺ n
  ...  | yes p = nin
  ...  | no ¬p = λ x₁ → contradiction (inv-in-var x₁) (≢-sym ¬p)
  notin-subst {N} {n} {Abs e} {e'} nin
    with notin-shift{k = 1} z≤n nin
  ...  | w rewrite (n+1≡sucn{n}) = λ x → notin-subst {n = ℕ.suc n} {e = e} {e' = ↑¹[ e' ]} w  (inv-in-abs x)
  notin-subst {N} {n} {App e e₁} {e'} nin (in-App z)
    with z
  ... | inj₁ x = notin-subst{e = e} nin x
  ... | inj₂ y = notin-subst{e = e₁} nin y
  notin-subst {N} {n} {LabI x} {e'} nin = λ ()
  notin-subst {N} {n} {LabE f e} {e'} nin (in-LabE z)
    with z
  ...  | inj₁ (fst , fst₁ , snd) = notin-subst{e = f fst fst₁} nin snd
  ...  | inj₂ y = notin-subst{e = e} nin y

  subst2-refl-notin : {N n : ℕ} {e e' s : Exp {N}} → ¬ n ∈` e' → [ n ↦ e ] ([ n ↦ e' ] s) ≡ [ n ↦ e' ] s
  subst2-refl-notin {N} {n} {e} {e'} {s} nin = subst-refl-notin (notin-subst{e = s} nin)

  -- if n ∈ [ m ↦ s ] e, n ∉ s, then n ≢ m
  subst-in-neq : {N n m : ℕ} {e s : Exp{N}} → ¬ n ∈` s → n ∈` ([ m ↦ s ] e) → n ≢ m
  subst-in-neq {N} {n} {m} {Var x} {s} nin ins
    with x ≟ᴺ m
  ...  | yes p = contradiction ins nin
  subst-in-neq {N} {.x} {m} {Var x} {s} nin in-Var | no ¬p = ¬p
  subst-in-neq {N} {n} {m} {Abs e} {s} nin (in-Abs ins) = sucn≢sucm⇒n≢m (subst-in-neq{e = e} (notin-shift-one nin) ins)
  subst-in-neq {N} {n} {m} {App e e₁} {s} nin (in-App (inj₁ x)) = subst-in-neq{e = e} nin x
  subst-in-neq {N} {n} {m} {App e e₁} {s} nin (in-App (inj₂ y)) = subst-in-neq{e = e₁} nin y
  subst-in-neq {N} {n} {m} {LabE f e} {s} nin (in-LabE (inj₁ (fst , fst₁ , snd))) = subst-in-neq{e = f fst fst₁} nin snd
  subst-in-neq {N} {n} {m} {LabE f e} {s} nin (in-LabE (inj₂ y)) = subst-in-neq{e = e} nin y

  -- if n ≢ m, n ∈` e, then n ∈` [ m ↦ e' ] e
  subst-in : {N n m : ℕ} {e e' : Exp {N}} → n ≢ m → n ∈` e → n ∈` ([ m ↦ e' ] e)
  subst-in {N} {n} {m} {Var x} {e'} neq (in-Var)
    with n ≟ᴺ m
  ...  | yes p = contradiction p neq
  ...  | no ¬p = in-Var
  subst-in {N} {n} {m} {Abs e} {e'} neq (in-Abs j) = in-Abs (subst-in (n≢m⇒sucn≢sucm neq) j)
  subst-in {N} {n} {m} {App e e₁} {e'} neq (in-App z)
    with z
  ...  | inj₁ x = in-App (inj₁ (subst-in neq x))
  ...  | inj₂ y = in-App (inj₂ (subst-in neq y))
  subst-in {N} {n} {m} {LabE f e} {e'} neq (in-LabE z)
    with z
  ...  | inj₁ (fst , fst₁ , snd) = in-LabE (inj₁ (fst , (fst₁ , (subst-in neq snd))))
  ...  | inj₂ y = in-LabE (inj₂ (subst-in neq y))

  -- if n ≢ m, n ∉ e', n ∈ [ m ↦ e' ] e, then n ∈ e
  subst-in-reverse : {N n m : ℕ} {e e' : Exp {N}} → n ≢ m → ¬ (n ∈` e') → n ∈` ([ m ↦ e' ] e) → n ∈` e
  subst-in-reverse {N} {n} {m} {Var x} {e'} neq nin ins
    with x ≟ᴺ m
  ...  | yes p = contradiction ins nin
  ...  | no ¬p = ins
  subst-in-reverse {N} {n} {m} {Abs e} {e'} neq nin (in-Abs ins) = in-Abs (subst-in-reverse (n≢m⇒sucn≢sucm neq) (notin-shift-one{N}{n}{e'} nin) ins)
  subst-in-reverse {N} {n} {m} {App e e₁} {e'} neq nin (in-App (inj₁ x)) = in-App (inj₁ (subst-in-reverse neq nin x))
  subst-in-reverse {N} {n} {m} {App e e₁} {e'} neq nin (in-App (inj₂ y)) = in-App (inj₂ (subst-in-reverse neq nin y))
  subst-in-reverse {N} {n} {m} {LabE f e} {e'} neq nin (in-LabE (inj₁ (fst , fst₁ , snd))) = in-LabE (inj₁ (fst , (fst₁ , subst-in-reverse{e = f fst fst₁} neq nin snd)))
  subst-in-reverse {N} {n} {m} {LabE f e} {e'} neq nin (in-LabE (inj₂ y)) = in-LabE (inj₂ (subst-in-reverse neq nin y))

  var-env-< : {N : ℕ} {Γ : Env {N}} {T : Ty} {n : ℕ} (j : n ∶ T ∈ Γ) → n <ᴺ (length Γ)
  var-env-< {N} {.(T ∷ _)} {T} {.0} here = s≤s z≤n
  var-env-< {N} {.(_ ∷ _)} {T} {.(ℕ.suc _)} (there j) = s≤s (var-env-< j)

  -- variables contained in a term are < length of env.
  free-vars-env-< : {N : ℕ} {e : Exp {N}} {Γ : Env} {T : Ty {N}} → Γ ⊢ e ∶ T → (∀ n → n ∈` e → n <ᴺ length Γ)
  free-vars-env-< {N} {.(Var n)} {Γ} {T} (TVar x) n in-Var = var-env-< x
  free-vars-env-< {N} {.(Abs _)} {Γ} {(Fun T₁ T₂)} (TAbs j) n (in-Abs ins)
    rewrite (length[A∷B]≡suc[length[B]] {lzero} {Ty} {T₁} {Γ})
          = ≤-pred (free-vars-env-< j (ℕ.suc n) ins)
  free-vars-env-< {N} {App e e'} {Γ} {T} (TApp j j') n (in-App z)
    with z
  ...  | inj₁ x = free-vars-env-< j n x
  ...  | inj₂ y = free-vars-env-< j' n y
--   free-vars-env-< {N} {LabE f (LabI l)} {Γ} {T} (TLabEl{scopecheck = s} j j')
  free-vars-env-< {N} {LabE f (LabI l)} {Γ} {T} (TLabEl{scopecheck = s} j j') n (in-LabE z)
    with z
  ...  | inj₁ (fst , fst₁ , snd) = s fst fst₁ n snd
  ...  | inj₂ ()
  free-vars-env-< {N} {LabE f (Var m)} {Γ} {T} (TLabEx f' (TVar j)) n (in-LabE z)
    with n ≟ᴺ m
  ...  | yes p rewrite p = var-env-< j
  ...  | no ¬p
       with z
  ...     | inj₁ (fst , fst₁ , snd) = free-vars-env-< (f' fst fst₁) n (subst-in ¬p snd)
  ...     | inj₂ (in-Var) = var-env-< j

  -- closed expressions have no free variables
  closed-free-vars : {N : ℕ} {e : Exp {N}} {T : Ty {N}} → [] ⊢ e ∶ T → (∀ n → ¬ (n ∈` e))
  closed-free-vars {N} {Var x} {T} (TVar ())
  closed-free-vars {N} {LabI x} {T} j n ()
  closed-free-vars {N} {Abs e} {.(Fun _ _)} (TAbs j) n (in-Abs x) = contradiction (free-vars-env-< j (ℕ.suc n) x) (≤⇒≯ (s≤s z≤n))
  closed-free-vars {N} {e} {T} j n x = contradiction (free-vars-env-< j n x) (≤⇒≯ z≤n)  -- App & LabE have the same proof

  -- shifting with a threshold above number of free variables has no effect
  shift-env-size : {n : ℕ} {k : ℤ} {q : ℕ} {e : Exp {n}} → (∀ n → n ∈` e → n <ᴺ q) → ↑ k , q [ e ] ≡ e
  shift-env-size {n} {k} {q} {Var x} lmap
    with x <ᴺ? q
  ...  | yes p = refl
  ...  | no ¬p = contradiction (lmap x in-Var) ¬p
  shift-env-size {n} {k} {q} {Abs e} lmap = cong Abs (shift-env-size (extr lmap))
    where extr : (∀ n → n ∈` Abs e → n <ᴺ q) → (∀ n → n ∈` e → n <ᴺ ℕ.suc q)
          extr lmap zero ins = s≤s z≤n
          extr lmap (ℕ.suc n) ins = s≤s (lmap n (in-Abs ins))
  shift-env-size {n} {k} {q} {App e e'} lmap = cong₂ App (shift-env-size (extr lmap)) (shift-env-size(extr' lmap))
    where extr : (∀ n → n ∈` App e e' → n <ᴺ q) → (∀ n → n ∈` e → n <ᴺ q)
          extr lmap n ins = lmap n (in-App (inj₁ ins))
          extr' : (∀ n → n ∈` App e e' → n <ᴺ q) → (∀ n → n ∈` e' → n <ᴺ q)
          extr' lmap n ins = lmap n (in-App (inj₂ ins))
  shift-env-size {n} {k} {q} {LabI x} lmap = refl
  shift-env-size {n} {k} {q} {LabE{s = s} f e} lmap = cong₂ LabE (f-ext λ l' → (f-ext λ x → shift-env-size (extr lmap l' x))) (shift-env-size (extr' lmap))
    where extr : (∀ n → n ∈` LabE f e → n <ᴺ q) → (l : Fin n) → (x : l ∈ s) → (∀ n → n ∈` f l x → n <ᴺ q)
          extr lmap l x n ins = lmap n (in-LabE (inj₁ (l , (x , ins))))
          extr' : (∀ n → n ∈` LabE f e → n <ᴺ q) → (∀ n → n ∈` e → n <ᴺ q)
          extr' lmap n ins = lmap n (in-LabE (inj₂ ins))
  
  -- shifting has no effect on closed terms (corollary of shift-env-size)
  closed-no-shift : {n : ℕ} {k : ℤ} {q : ℕ} {e : Exp {n}} {T : Ty {n}} → [] ⊢ e ∶ T → ↑ k , q [ e ] ≡ e
  closed-no-shift {n} {k} {zero} {e} {T} j = shift-env-size (free-vars-env-< j)
  closed-no-shift {n} {k} {ℕ.suc q} {e} {T} j = shift-env-size λ n i → <-trans (free-vars-env-< j n i) (s≤s z≤n)

  -- 
  subst-change-in : {N n m : ℕ} {e s s' : Exp{N}} → ¬ (n ∈` s) × ¬ (n ∈` s') → n ∈` ([ m ↦ s ] e) → n ∈` ([ m ↦ s' ] e)
  subst-change-in {N} {n} {m} {Var x} {s} {s'} (fst , snd) ins
    with x ≟ᴺ m
  ...  | yes eq = contradiction ins fst
  ...  | no ¬eq = ins
  subst-change-in {N} {n} {m} {Abs e} {s} {s'} (fst , snd) (in-Abs ins) = in-Abs (subst-change-in{N}{ℕ.suc n}{ℕ.suc m}{e} (notin-shift-one{N}{n}{s} fst , notin-shift-one{N}{n}{s'} snd) ins)
  subst-change-in {N} {n} {m} {App e e₁} {s} {s'} p (in-App (inj₁ x)) = in-App (inj₁ (subst-change-in{N}{n}{m}{e} p x))
  subst-change-in {N} {n} {m} {App e e₁} {s} {s'} p (in-App (inj₂ y)) = in-App (inj₂ (subst-change-in{N}{n}{m}{e₁} p y))
  subst-change-in {N} {n} {m} {LabE f e} {s} {s'} p (in-LabE (inj₁ (fst , fst₁ , snd))) = in-LabE (inj₁ (fst , (fst₁ , (subst-change-in{N}{n}{m}{f fst fst₁}{s}{s'} p snd))))
  subst-change-in {N} {n} {m} {LabE f e} {s} {s'} p (in-LabE (inj₂ y)) = in-LabE (inj₂ (subst-change-in {N} {n} {m} {e} p y))

  -- swapping of substitutions A & B if variables of A are not free in substitution term of B and vice versa
  subst-subst-swap : {N n m : ℕ} {e e' s : Exp {N}} → n ≢ m → ¬ n ∈` e' → ¬ m ∈` e → [ n ↦ e ] ([ m ↦ e' ] s) ≡ [ m ↦ e' ] ([ n ↦ e ] s)
  subst-subst-swap {N} {n} {m} {e} {e'} {Var x} neq nin nin'
    with x ≟ᴺ m | x ≟ᴺ n
  ...  | yes p | yes p' = contradiction (≡-trans (sym p') p) neq
  ...  | yes p | no ¬p'
       with x ≟ᴺ m
  ...     | yes p'' = subst-refl-notin nin
  ...     | no ¬p'' = contradiction p ¬p''
  subst-subst-swap {N} {n} {m} {e} {e'} {Var x} neq nin nin'
       | no ¬p | yes p'
       with x ≟ᴺ n
  ...     | yes p'' = sym (subst-refl-notin nin') 
  ...     | no ¬p'' = contradiction p' ¬p''
  subst-subst-swap {N} {n} {m} {e} {e'} {Var x} neq nin nin'
       | no ¬p | no ¬p'
       with x ≟ᴺ n | x ≟ᴺ m
  ...     | yes p'' | _ = contradiction p'' ¬p'
  ...     | _       | yes p''' = contradiction p''' ¬p
  ...     | no p''  | no ¬p''' = refl
  subst-subst-swap {N} {n} {m} {e} {e'} {Abs s} neq nin nin'
    with (notin-shift{n = n}{1}{0} z≤n nin) | (notin-shift{n = m}{1}{0} z≤n nin')
  ...  | w | w' rewrite (n+1≡sucn{n}) | (n+1≡sucn{m}) = cong Abs (subst-subst-swap{s = s} (n≢m⇒sucn≢sucm neq) w w')
  subst-subst-swap {N} {n} {m} {e} {e'} {App s s₁} neq nin nin' = cong₂ App (subst-subst-swap{s = s} neq nin nin') (subst-subst-swap{s = s₁} neq nin nin')
  subst-subst-swap {N} {n} {m} {e} {e'} {LabI x} neq nin nin' = refl
  subst-subst-swap {N} {n} {m} {e} {e'} {LabE f s} neq nin nin' = cong₂ LabE (f-ext (λ l → f-ext (λ x → subst-subst-swap{s = f l x} neq nin nin' ))) (subst-subst-swap{s = s} neq nin nin')

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

  env-type-uniq : {N n : ℕ} {Γ : Env {N}} {S T : Ty} → n ∶ T ∈ Γ → n ∶ S ∈ Γ → T ≡ S
  env-type-uniq {N} {.0} {.(S ∷ _)} {S} {.S} here here = refl
  env-type-uniq {N} {(ℕ.suc n)} {(A ∷ Γ)} {S} {T} (there j) (there j') = env-type-uniq {N} {n} {Γ} {S} {T} j j' 

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

  -- lemma required for ∈`
  ext-∈` : {N m k q : ℕ} {e : Exp {N}} → (∀ n → n ∈` e → n <ᴺ m) → (∀ n → n ∈` ↑ + k , q [ e ] → n <ᴺ m +ᴺ k)
  ext-∈` {N} {m} {k} {q} {Var x} f n ins
    with x <ᴺ? q
  ...  | yes p = ≤-trans (f n ins) (≤-stepsʳ{m}{m} k ≤-refl)
  ext-∈` {N} {m} {k} {q} {Var x} f .(x +ᴺ k) in-Var | no ¬p = Data.Nat.Properties.+-monoˡ-≤ k (f x in-Var)
  ext-∈` {N} {m} {k} {q} {Abs e} f n (in-Abs ins) = ≤-pred (ext-∈` {N} {ℕ.suc m} {k} {ℕ.suc q} {e = e} (extr f) (ℕ.suc n) ins)
    where extr : (∀ n → n ∈` Abs e → n <ᴺ m) → (∀ n → n ∈` e → n <ᴺ ℕ.suc m)
          extr f zero ins = s≤s z≤n
          extr f (ℕ.suc n) ins = s≤s (f n (in-Abs ins))
  ext-∈` {N} {m} {k} {q} {App e e₁} f n (in-App (inj₁ x)) = ext-∈`{N}{m}{k}{q}{e} (extr f) n x
    where extr : (∀ n → n ∈` App e e₁ → n <ᴺ m) → (∀ n → n ∈` e → n <ᴺ m)
          extr f n ins = f n (in-App (inj₁ ins))
  ext-∈` {N} {m} {k} {q} {App e e₁} f n (in-App (inj₂ y)) = ext-∈`{N}{m}{k}{q}{e₁} (extr f) n y
    where extr : (∀ n → n ∈` App e e₁ → n <ᴺ m) → (∀ n → n ∈` e₁ → n <ᴺ m)
          extr f n ins = f n (in-App (inj₂ ins))
  ext-∈` {N} {m} {k} {q} {LabE f₁ e} f n (in-LabE (inj₁ (fst , fst₁ , snd))) = ext-∈`{N}{m}{k}{q}{f₁ fst fst₁} (extr f) n snd
    where extr : (∀ n → n ∈` LabE f₁ e → n <ᴺ m) → (∀ n → n ∈` f₁ fst fst₁ → n <ᴺ m)
          extr f n ins = f n (in-LabE (inj₁ (fst , (fst₁ , ins))))
  ext-∈` {N} {m} {k} {q} {LabE f₁ e} f n (in-LabE (inj₂ y)) = ext-∈`{N}{m}{k}{q}{e} (extr f) n y
    where extr : (∀ n → n ∈` LabE f₁ e → n <ᴺ m) → (∀ n → n ∈` e → n <ᴺ m)
          extr f n ins = f n (in-LabE (inj₂ ins))

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
  ext {N} {Γ} {Δ} {∇} {S} {LabI l} (TLabI{x = x}{s} ins) = TLabI{x = x}{s} ins
  ext {N} {Γ} {Δ} {∇} {S} {LabE f e} (TLabEl{ins = ins}{f = .f}{scopecheck = s} j j') = TLabEl{ins = ins}
                                                                                              {scopecheck = λ l i n x₁ → rw n (ext-∈`{N}{length (∇ ++ Γ)}{length Δ}{length ∇}{f l i} (s l i) n x₁)}
                                                                                              (ext{N}{Γ}{Δ}{∇} j) (ext{N}{Γ}{Δ}{∇} j')
    where rw : ∀ n → n <ᴺ length (∇ ++ Γ) +ᴺ length Δ → n <ᴺ length (∇ ++ Δ ++ Γ)
          rw n a rewrite (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{Γ})
                       | (+-assoc (length ∇) (length Γ) (length Δ))
                       | (+-comm (length Γ) (length Δ))
                       | sym (length[A++B]≡length[A]+length[B]{lzero}{Ty}{Δ}{Γ})
                       | sym (length[A++B]≡length[A]+length[B]{lzero}{Ty}{∇}{Δ ++ Γ}) = a
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
 
          where rw : ((l : Fin N) → (i : l ∈ s) → (∇ ++ (t ∷ Δ) ++ Γ) ⊢ ↑ + length (t ∷ Δ) , length ∇ [ [ m ↦ LabI l ] (f l i) ] ∶ S)
                   → ((l : Fin N) → (i : l ∈ s) → (∇ ++ (t ∷ Δ) ++ Γ) ⊢ [ m ↦ LabI l ] ↑ + length (t ∷ Δ) , length ∇ [ f l i ] ∶ S)
                rw q l i
                  with q l i              
                ...  | w
                     rewrite (subst-shift-swap{N}{+ length (t ∷ Δ)}{m}{length ∇}{f l i}{LabI l} (+<+ (s≤s z≤n)))
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
                  
             where rw : ((l : Fin N) → (i : l ∈ s) → ((∇ ++ (t ∷ Δ) ++ Γ) ⊢ ↑ + length (t ∷ Δ) , length ∇ [ [ m ↦ LabI l ] f l i ] ∶ S))
                      → ((l : Fin N) → (i : l ∈ s) → ((∇ ++ (t ∷ Δ) ++ Γ) ⊢ [ m +ᴺ length (t ∷ Δ) ↦ LabI l ] ↑ + length (t ∷ Δ) , length ∇ [ f l i ] ∶ S))
                   rw q l i
                     with q l i
                   ...  | w
                        rewrite (subst-shift-swap {N} {+ length (t ∷ Δ)} {m} {length ∇} {f l i} {LabI l} (+<+ (s≤s z≤n)))
                        with m <ᴺ? length ∇
                   ...     | yes p = contradiction x₁ (<⇒≱ p)
                   ...     | no ¬p =  w 

  
  ext-empty : {N : ℕ} {Γ : Env {N}} {T : Ty} {e : Exp} → [] ⊢ e ∶ T → Γ ⊢ e ∶ T
  ext-empty {N} {Γ} {T} {e} j
    with ext{N}{[]}{Γ}{[]} j
  ...  | w rewrite (closed-no-shift{N}{+ length Γ}{0}{e}{T} j)
                 | (A++[]≡A{lzero}{Ty}{Γ})
                 = w

  -- uniqueness of ∈
  ∈-eq : {N : ℕ} {s : Subset N} {l : Fin N} → (ins : l ∈ s) → (ins' : l ∈ s) → ins ≡ ins'
  ∈-eq {ℕ.suc n} {.(true ∷ _)} {zero} here here = refl
  ∈-eq {ℕ.suc n} {(x ∷ s)} {Fin.suc l} (there j) (there j') = cong there (∈-eq j j')

  --- general typing properties
 
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
  progress (LabI ins) {Label s} {TLabI l} = value VLab
  progress (LabE f (LabI l)) {T} {j = TLabEl{ins = ins} f' j} = step (β-LabE ins)
  progress {n} (LabE f (Var m)) {T} {TLabEx f' (TVar ())}


  ---

  preserve-subst' : {n : ℕ} {T S : Ty {n} } {Δ : Env {n}} {e s : Exp {n}} {v : Val s} (j : (Δ ++ S ∷ []) ⊢ e ∶ T) (j' : [] ⊢ s ∶ S)
                                                                           → Δ ⊢ [ length Δ ↦ s ] e ∶ T
  preserve-subst' {n} {T} {S} {Δ} {(Var m)} {s} {v} (TVar{m} x) j'
    with extract{n}{Δ}{S ∷ []}{T}{m} x
  ...  | in-Δ x₁
       with m ≟ᴺ length Δ
  ...     | yes p = contradiction p (<⇒≢ (var-env-< x₁))
  ...     | no ¬p
          with m <ᴺ? length Δ
  ...        | yes p' = TVar x₁
  ...        | no ¬p' = contradiction (var-env-< x₁) ¬p'
  preserve-subst' {n} {T} {S} {Δ} {(Var m)} {s} {v} (TVar{m} x) j'
       | in-Γ x₁ x₂
       with m ≟ᴺ length Δ
  ...     | yes p
          with ext{n}{[]}{Δ} j'
  ...        | w
               rewrite p
                   | (env-type-equiv x)
                   | (closed-no-shift {n} {+ length Δ} {0} {s} j')
                   | (A++[]≡A{lzero}{Ty}{Δ})
                   = w
  preserve-subst' {n} {T} {S} {Δ} {(Var m)} {s} {v} (TVar{m} x) j'
      | in-Γ x₁ x₂ | no ¬p
          with m <ᴺ? length Δ
  ...        | yes p' = contradiction x₁ (<⇒≱ p')
  ...        | no ¬p'
             with (<⇒≱ (≤∧≢⇒< (≤-step (≤∧≢⇒< (≮⇒≥ ¬p') (≢-sym ¬p))) (≢-sym (n≢m⇒sucn≢sucm ¬p))))
  ...           | w  = contradiction (var-env-< x) (aux w)
             where aux : ¬ (ℕ.suc m ≤ᴺ ℕ.suc (length Δ)) → ¬ (ℕ.suc m ≤ᴺ length (Δ ++ S ∷ []))
                   aux t rewrite (length[A++B]≡length[A]+length[B]{A = Δ}{B = S ∷ []}) | (n+1≡sucn{length Δ})  = t
  preserve-subst' {n} {.(Fun _ _)} {S} {Δ} {(Abs e')} {s} {v} (TAbs{T₁ = T₁}{T₂} j) j'
    with preserve-subst'{n}{T₂}{S}{T₁ ∷ Δ}{e'}{s}{v} j j'
  ...  | w
       rewrite (closed-no-shift {n} {+ 1} {0} {s} j')
             = TAbs w 
  preserve-subst' {n} {T} {S} {Δ} {(App e e')} {s} {v} (TApp j j₁) j' = TApp (preserve-subst'{v = v} j j') (preserve-subst'{v = v} j₁ j')
  preserve-subst' {n} {T} {S} {Δ} {LabI x} {s} {v} (TLabI ins) j' = TLabI ins
  preserve-subst' {n} {T} {S} {Δ} {LabE{s = s'} f (LabI x)} {s} {v} (TLabEl{ins = ins}{scopecheck = sc} j j') j'' = TLabEl{ins = ins}{scopecheck = scopecheck} (preserve-subst'{v = v} j j'') (TLabI ins)
    where scopecheck : (l : Fin n) (i : l ∈ s') (n' : ℕ) → n' ∈` ([ length Δ ↦ s ] f l i) → n' <ᴺ length Δ
          scopecheck l i n' ins
            with subst-in-neq{n}{n'}{length Δ}{f l i}{s} (closed-free-vars j'' n') ins
          ...  | w
               with (sc l i n' (subst-in-reverse{n}{n'}{length Δ}{e' = s} w (closed-free-vars j'' n') ins))
          ...     | w'
                  rewrite (length[A++B∷[]]≡suc[length[A]]{lzero}{Ty}{Δ}{S}) = ≤∧≢⇒< (≤-pred w') w
  preserve-subst' {n} {T} {.(Fun _ _)} {Δ} {LabE f (Var m)} {Abs e} {VFun} (TLabEx f' (TVar{T = Label s} z)) (TAbs j')
    with m ≟ᴺ length Δ | preserve-subst'{v = VFun} (TVar z) (TAbs j')
  ...  | yes p | _ rewrite p = contradiction (env-type-equiv z) λ ()
  ...  | no ¬p | w = TLabEx (rw (λ l i → preserve-subst'{v = VFun} (f' l i) (TAbs j'))) w
       where rw : ((l : Fin n) (i : l ∈ s) → Δ ⊢ [ length Δ ↦ Abs e ] ([ m ↦ LabI l ] f l i) ∶ T) 
                → ((l : Fin n) (i : l ∈ s) → Δ ⊢ [ m ↦ LabI l ] ([ length Δ ↦ Abs e ] f l i) ∶ T)
             rw ρ l i
               with ρ l i
             ...  | w
                  rewrite sym (subst-subst-swap{n}{length Δ}{m}{Abs e}{LabI l}{f l i} (≢-sym ¬p) (λ ()) (closed-free-vars (TAbs j') m)) = w
  preserve-subst' {n} {T} {(Label s')} {Δ} {LabE f (Var m)} {LabI x} {VLab} (TLabEx f' (TVar{T = Label s} z)) (TLabI{s = s'} ins)
    with m ≟ᴺ length Δ | preserve-subst'{v = VLab} (TVar z) (TLabI ins)
  ...  | yes p | w
       rewrite p
             | subset-eq (env-type-equiv z)
             =  TLabEl{f = λ l i → [ length Δ ↦ LabI x ] (f l i)}{scopecheck } (rw{e = f x ins} (preserve-subst'{v = VLab} (f' x ins) (TLabI{s = s'} ins))) w 
       where 
             -- agda didn't let me rewrite this directly
             rw :  {e : Exp} →  (Δ ⊢ [ length Δ ↦ LabI x ] ([ length Δ ↦ LabI x ] e) ∶ T)
                             → ( Δ ⊢ [ length Δ ↦ LabI x ] e ∶ T)
             rw {e} j
               rewrite sym (subst2-refl-notin{n}{length Δ}{LabI x}{LabI x}{e} (λ ())) = j
             -- if n ∈` [length Δ ↦ LabI x] (f l i), then also n ∈` [length Δ ↦ LabI l] (f l i), since both LabI l and LabI x are closed
             -- if n ∈` [length Δ ↦ LabI l] (f l i), then n < length (Δ ++ (S ∷ [])), we get this from f' ((Δ ++ S ∷ []) ⊢ [length Δ ↦ LabI l] (f l i) ∶ T) and free-vars-env-<
             -- if n ∈` [length Δ ↦ LabI l] (f l i), then also n ≢ (length Δ), since LabI closed
             -- hence n < length (Δ ++ (S ∷ [])) = length Δ + 1 ⇒ n ≤ length Δ, n ≤ length Δ and n ≢ length Δ implies n < length Δ
             scopecheck : (l : Fin n) (i : l ∈ s') (n' : ℕ) → n' ∈` ([ length Δ ↦ LabI x ] f l i) → n' <ᴺ length Δ
             scopecheck l i n' ins
               with (free-vars-env-< (f' l i) n' (subst-change-in{n}{n'}{length Δ}{f l i}{LabI x}{LabI l} ((λ ()) , (λ ())) ins))       
             ...  | w
                  rewrite (length[A++B∷[]]≡suc[length[A]]{lzero}{Ty}{Δ}{Label s'})= ≤∧≢⇒< (≤-pred w) (subst-in-neq{n}{n'}{length Δ}{f l i}{LabI x} (λ ()) ins)
  ...  | no ¬p | w = TLabEx (rw λ l i → preserve-subst'{v = VLab} (f' l i) (TLabI ins)) w
       where rw : ((l : Fin n) (i : l ∈ s) → Δ ⊢ [ length Δ ↦ LabI x ] ([ m ↦ LabI l ] f l i) ∶ T) 
                → ((l : Fin n) (i : l ∈ s) → Δ ⊢ [ m ↦ LabI l ] ([ length Δ ↦ LabI x ] f l i) ∶ T)
             rw ρ l i
               with ρ l i
             ...  | w
                  rewrite sym (subst-subst-swap{n}{length Δ}{m}{LabI x}{LabI l}{f l i} (≢-sym ¬p) (λ ()) (closed-free-vars (TLabI ins) m)) = w


  preserve' : {n : ℕ} {T : Ty {n}} (e e' : Exp) (j : [] ⊢ e ∶ T) (r : e ⇒ e') → [] ⊢ e' ∶ T
  preserve' {n} {T} .(App e₁ _) .(App e₁' _) (TApp j j') (ξ-App1 {e₁ = e₁} {e₁' = e₁'} r) = TApp (preserve' e₁ e₁' j r) j'
  preserve' {n} {T} .(App _ _) .(App _ _) (TApp j j') (ξ-App2{e = e}{e' = e'} x r) = TApp j (preserve' e e' j' r)
  preserve' {n} {T} (App (Abs e) s') .(↑ -[1+ 0 ] , 0 [ [ 0 ↦ ↑ + 1 , 0 [ s' ] ] e ]) (TApp (TAbs j) j₁) (β-App x)
    rewrite (closed-no-shift {n} {+ 1} {0} {s'} j₁)
          | (closed-no-shift {n} { -[1+ 0 ]} {0} {[ 0 ↦ s' ] e} (preserve-subst'{Δ = []}{v = x} j j₁))
          = preserve-subst'{Δ = []}{v = x} j j₁
  preserve' {n} {T} (LabE f (LabI l)) .(f x ins) (TLabEl{ins = ins'} j j') (β-LabE {x = x} ins) rewrite (∈-eq ins ins') = j

-}
