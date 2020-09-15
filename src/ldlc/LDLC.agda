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
open import Data.List hiding (length ; _++_)
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

  data Val {n : ℕ} : Exp {n} → Set where
    VVar : {n : ℕ} → Val (Var n)
    VLab : {x : Fin n} → Val (LabI x)
    VFun : {e : Exp} → Val (Abs e)
    VProd : {e e' : Exp} → Val (Prod e e')

  data Ty {n : ℕ} : Set where
    Label : Subset n → Ty
    Pi : Ty {n} → Ty {n} → Ty
    Sigma : Ty {n} → Ty {n} → Ty
    Case : {s : Subset n} → (f : ∀ l → l ∈ s → Ty {n}) → Exp{n} → Ty 
  
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
  ↑ d , c [ FakeLet e e' ] = FakeLet (↑ d , c [ e ]) (↑ d , (ℕ.suc (ℕ.suc c)) [ e' ])

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
  [ k ↦ s ] FakeLet e e' = FakeLet ([ k ↦ s ] e) ([ (ℕ.suc (ℕ.suc k)) ↦ ↑ (ℤ.pos 2) , 0 [ s ] ] e')

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
    in-Prod : {n : ℕ} {e e' : Exp} → n ∈` e ⊎ (ℕ.suc n) ∈` e' → n ∈` Prod e e'
    in-FakeLet : {n : ℕ} {e e' : Exp} → n ∈` e ⊎ (ℕ.suc (ℕ.suc n)) ∈` e' → n ∈` FakeLet e e'
    
  -- Type environment, formation and typing of expressions
  data TEnv {n : ℕ} : Set
  data _∶_∈_ {n : ℕ} : ℕ → Ty {n} → TEnv {n} → Set
  data _⊢_ {n : ℕ} : TEnv {n} → Ty {n} → Set
  data _⊢_∶_ {n : ℕ} : TEnv {n} → Exp {n} → Ty {n} → Set
  data _⊢_≡ᵀ_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set
  data _⊢_≡ᵀ'_ {n : ℕ} : TEnv {n} → Ty {n} → Ty {n} → Set

  data TEnv {n} where
    [] : TEnv
    ⟨_,_⟩ : (T : Ty) (Γ : TEnv {n}) {ok : Γ ⊢ T} → TEnv

  length : {n : ℕ} → TEnv {n} → ℕ
  length [] = 0
  length ⟨ T , Γ ⟩ = ℕ.suc (length Γ)

  -- env-tail ⟨ A , B , C , [] ⟩ 0 = ⟨ B , C , [] ⟩
  env-tail : {n : ℕ} → TEnv {n} → ℕ → TEnv {n}
  env-tail [] n = []
  env-tail ⟨ T , Γ ⟩ zero = Γ
  env-tail ⟨ T , Γ ⟩ (ℕ.suc n) = env-tail Γ n

  data _∶_∈_ {n} where
    here : {T : Ty} {Γ : TEnv} {ok : Γ ⊢ T} → 0 ∶ T ∈ ⟨ T , Γ ⟩ {ok}
    there : {n : ℕ} {T₁ T₂ : Ty} {Γ : TEnv} {ok : Γ ⊢ T₂} → n ∶ T₁ ∈ Γ → (ℕ.suc n) ∶ T₁ ∈ ⟨ T₂ , Γ ⟩ {ok}

  -- Type formation
  data _⊢_ {n} where
    TLabF : {Γ : TEnv {n}} {s : Subset n} → Γ ⊢ Label s
    TPiF : {Γ : TEnv {n}} {A B : Ty}  → (ok : Γ ⊢ A) → ⟨ A , Γ ⟩ {ok} ⊢ B → Γ ⊢ Pi A B
    TSigmaF : {Γ : TEnv {n}} {A B : Ty}  → (ok : Γ ⊢ A) → ⟨ A , Γ ⟩ {ok} ⊢ B → Γ ⊢ Sigma A B
    TCaseF : {Γ : TEnv {n}} {s : Subset n} {e : Exp {n}} {f : ∀ l → l ∈ s → Ty} → (f' : ∀ l i → Γ ⊢ (f l i))
                                                                                → (v : Val e)
                                                                                → Γ ⊢ e ∶ Label s
                                                                                → Γ ⊢ Case {n} {s} f e

  -- Typing expressions
  data _⊢_∶_ {n} where
    TConv : {Γ : TEnv} {T T' : Ty {n}} {e : Exp} → Γ ⊢ e ∶ T → Γ ⊢ T ≡ᵀ T' → Γ ⊢ e ∶ T'
    TVarE : {m : ℕ} {Γ : TEnv} {T T' : Ty} → m ∶ T ∈ Γ → env-tail Γ m ⊢ T' ≡ᵀ T → Γ ⊢ (Var m) ∶ T'
    -- adjustment: env-tail Γ m ⊢ T' ≡ᵀ T
    --
    -- Terms of the form ⟨ A , Γ ⟩ ⊢ Var 0 ∶ B can occur through type conversion (if ≡ᵀ⇒⊢, i.e. Γ ⊢ A ≡ᵀ B ⇒ Γ ⊢ A × Γ ⊢ B, should hold), e.g.:
    --
    --- ∅ ⊢ Label ≡ᵀ (Case (λ ⇒ Label) l)
    --- ⟨ Label , ∅ ⟩ ⊢ (Case (λ ⇒ Label) 0) ≡ᵀ (Case (λ ⇒ Label) 0)
    ---- ∅ ⊢ Pi Label (Case (λ ⇒ Label) 0) ≡ᵀ Pi (Case (λ ⇒ Label) l) (Case (λ ⇒ Label) 0)  
    --
    --- (Γ ⊢ A ≡ᵀ B ⇒ Γ ⊢ A × Γ ⊢ B)
    --- ∅ ⊢ Pi Label (Case (λ ⇒ Label) 0) ≡ᵀ Pi (Case (λ ⇒ Label) l) (Case (λ ⇒ Label) 0)
    ---- ∅ ⊢ Pi (Case (λ ⇒ Label) l) (Case (λ ⇒ Label) 0)
    ----- ⟨ (Case (λ ⇒ Label) l) , ∅ ⟩ ⊢ (Case (λ ⇒ Label) 0)
    ------ ⟨ (Case (λ ⇒ Label) l) , ∅ ⟩ ⊢ 0 : Label
    TPiI : {Γ : TEnv} {A B : Ty} {e : Exp} {ok : Γ ⊢ A} {ok' : ⟨ A , Γ ⟩ {ok} ⊢ B} → ⟨ A , Γ ⟩ {ok} ⊢ e ∶ B → Γ ⊢ (Abs e) ∶ (Pi A B)
    TPiE : {Γ : TEnv} {A B : Ty} {e e' : Exp} → Γ ⊢ e ∶ (Pi A B) → Γ ⊢ e' ∶ A → Γ ⊢ ([ 0 ↦ e' ]ᵀ B) → Γ ⊢ App e e' ∶ ([ 0 ↦ e' ]ᵀ B)
    TSigmaI : {Γ : TEnv} {A B : Ty} {e e' : Exp} {ok : Γ ⊢ A} {ok' : ⟨ A , Γ ⟩ {ok} ⊢ B}  → Γ ⊢ e ∶ A → ⟨ A , Γ ⟩ {ok} ⊢ e' ∶ B → Γ ⊢ Prod e e' ∶ (Sigma A B)
    -- adjustment (also in TPiI): {ok' : ⟨ A , Γ ⟩ ⊢ B}
    --
    -- since I couldn't prove that it holds without the rule (Γ ⊢ e ∶ T does not imply Γ ⊢ T, see TSigmaE: FakeLet e e' ∶ C because of e')
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

  -- Type conversion
  data _⊢_≡ᵀ_ {n} where
    CRefl : {Γ : TEnv {n}} {T : Ty} {ok : Γ ⊢ T}  → Γ ⊢ T ≡ᵀ T
    CSym : {Γ : TEnv {n}} {T T' : Ty} → Γ ⊢ T ≡ᵀ T' → Γ ⊢ T' ≡ᵀ T
    CTrans : {Γ : TEnv {n}} {T T' T'' : Ty} → Γ ⊢ T ≡ᵀ T' → Γ ⊢ T' ≡ᵀ T'' → Γ ⊢ T ≡ᵀ T''
    CLabEta : {Γ : TEnv {n}} {s : Subset n} {x : Fin n} {T : Ty} {ins : x ∈ s} → Γ ⊢ LabI x ∶ Label s → Γ ⊢ T → Γ ⊢ T ≡ᵀ (Case {s = s} (λ l i → T) (LabI x))
    CLabBeta : {Γ : TEnv {n}} {s : Subset n} {x : Fin n} {f : (∀ l → l ∈ s → Ty)} → Γ ⊢ Case f (LabI x) → (ins : x ∈ s) → Γ ⊢ Case f (LabI x) ≡ᵀ (f x ins)
    CPi : {Γ : TEnv {n}} {A B A' B' : Ty} {ok : Γ ⊢ A} → Γ ⊢ A ≡ᵀ B → ⟨ A , Γ ⟩ {ok} ⊢ A' ≡ᵀ B' → Γ ⊢ Pi A A' ≡ᵀ Pi B B'
    CSigma : {Γ : TEnv {n}} {A B A' B' : Ty} {ok : Γ ⊢ A} → Γ ⊢ A ≡ᵀ B → ⟨ A , Γ ⟩ {ok} ⊢ A' ≡ᵀ B' → Γ ⊢ Sigma A A' ≡ᵀ Sigma B B'
    CLab : {Γ : TEnv {n}} {s : Subset n} {f f' : (∀ l → l ∈ s → Ty)} {e : Exp {n}} → (Γ ⊢ Case f e) → (∀ l i → Γ ⊢ (f l i) ≡ᵀ (f' l i)) → Γ ⊢ Case f e ≡ᵀ Case f' e
    -- adjustment: (Val e) -> (Γ ⊢ Case f e) else illegal terms possible and property ≡ᵀ⇒⊢ wouldn't hold (i.e. Γ ⊢ A ≡ᵀ B ⇒ Γ ⊢ A × Γ ⊢ B)


  -- Type conversion without explicit transitivity and symmetry
  data _⊢_≡ᵀ'_ {n} where
    CRefl' : {Γ : TEnv {n}} {T : Ty} {ok : Γ ⊢ T}  → Γ ⊢ T ≡ᵀ' T
    CLabEta' : {Γ : TEnv {n}} {s : Subset n} {x : Fin n} {T : Ty} {ins : x ∈ s} {f : (∀ l → l ∈ s → Ty)} → Γ ⊢ LabI x ∶ Label s → (∀ l → (ins' : l ∈ s) → Γ ⊢ f l ins') → (Γ ⊢ f x ins  ≡ᵀ' T) →  Γ ⊢ T ≡ᵀ' (Case {s = s} f (LabI x))
    CLabBeta' : {Γ : TEnv {n}} {s : Subset n} {x : Fin n} {f : (∀ l → l ∈ s → Ty)} {T : Ty {n}} → Γ ⊢ Case f (LabI x) → (ins : x ∈ s) → (Γ ⊢ f x ins ≡ᵀ' T) → Γ ⊢ Case f (LabI x) ≡ᵀ' T
    CPi' : {Γ : TEnv {n}} {A B A' B' : Ty} {ok : Γ ⊢ A} → Γ ⊢ A ≡ᵀ' B → (⟨ A , Γ ⟩ {ok} ⊢ A' ≡ᵀ' B')→ Γ ⊢ Pi A A' ≡ᵀ' Pi B B'
    CSigma' : {Γ : TEnv {n}} {A B A' B' : Ty} {ok : Γ ⊢ A} → Γ ⊢ A ≡ᵀ' B → ⟨ A , Γ ⟩ {ok} ⊢ A' ≡ᵀ' B' → Γ ⊢ Sigma A A' ≡ᵀ' Sigma B B'
    CLab' : {Γ : TEnv {n}} {s : Subset n} {f f' : (∀ l → l ∈ s → Ty)} {e : Exp {n}}  {ok : ∀ l' → (i : l' ∈ s) → Γ ⊢ f l' i} {ok' : ∀ l' → (i : l' ∈ s) → Γ ⊢ f' l' i}
                                          → (Γ ⊢ Case f e) → (∀ l i → Γ ⊢ (f l i) ≡ᵀ' (f' l i)) → Γ ⊢ Case f e ≡ᵀ' Case f' e
    CLabSub' : {Γ : TEnv {n}} {s : Subset n} {l : Fin n} {ins : l ∈ s} {f g : (∀ l → l ∈ s → Ty)} {ok : ∀ l' → (i : l' ∈ s) → Γ ⊢ f l' i} {ok' : ∀ l' → (i : l' ∈ s) → Γ ⊢ g l' i}
               → (Γ ⊢ f l ins ≡ᵀ' g l ins) → Γ ⊢ Case f (LabI l) ≡ᵀ' Case g (LabI l)

  -- Type environment equivalency for ≡ᵀ
  data _≡ᵀ_ {n} : TEnv {n} → TEnv {n} → Set where
    tzero : [] ≡ᵀ []
    tsuc : {Γ Δ : TEnv {n}} {T T' : Ty} {ok : Γ ⊢ T} {ok' : Δ ⊢ T'} → Γ ≡ᵀ Δ → Δ ⊢ T ≡ᵀ T' → ⟨ T , Γ ⟩ {ok}  ≡ᵀ ⟨ T' , Δ ⟩ {ok'}

  ≡ᵀ-tail : {n : ℕ} {Γ Δ : TEnv {n}} → (m : ℕ) → Γ ≡ᵀ Δ → env-tail Γ m ≡ᵀ env-tail Δ m
  ≡ᵀ-tail {n} {.[]} {.[]} m tzero = tzero
  ≡ᵀ-tail {n} {.(⟨ _ , _ ⟩)} {.(⟨ _ , _ ⟩)} zero (tsuc eq x) = eq
  ≡ᵀ-tail {n} {(⟨ T , Γ ⟩)} {(⟨ T' , Δ ⟩)} (ℕ.suc m) (tsuc eq x) = ≡ᵀ-tail m eq

  ≡ᵀ-length : {n : ℕ} {Γ Δ : TEnv {n}} → Γ ≡ᵀ Δ → length Γ ≡ length Δ
  ≡ᵀ-length {n} {.[]} {.[]} tzero = refl
  ≡ᵀ-length {n} {.(⟨ _ , _ ⟩)} {.(⟨ _ , _ ⟩)} (tsuc eq x) = cong ℕ.suc (≡ᵀ-length eq)

  env-tail-in : {n m : ℕ} {T : Ty {n}} {Γ : TEnv} → (ℕ.suc m) ∶ T ∈ Γ → 0 ∶ T ∈ env-tail Γ m
  env-tail-in {n} {.0} {T} {.(⟨ _ , ⟨ T , _ ⟩ ⟩)} (there here) = here
  env-tail-in {n} {(ℕ.suc m)} {T} {(⟨ T' , ⟨ T'' , Γ ⟩ ⟩)} (there (there ins)) = env-tail-in (there ins)

  -- DEFINITIONS
  ≡ᵀ-extr : {n m : ℕ} {Γ Δ : TEnv} {A : Ty {n}} → (m ∶ A ∈ Γ) → Γ ≡ᵀ Δ → ∃[ B ] (m ∶ B ∈ Δ × (env-tail Δ m) ⊢ A ≡ᵀ B)
  ⊢-envsub : {n : ℕ} {A : Ty {n}} {Γ Δ : TEnv {n}} → Γ ⊢ A → Γ ≡ᵀ Δ → Δ ⊢ A
  ⊢∶-envsub : {n : ℕ} {A : Ty {n}} {Γ Δ : TEnv {n}} {e : Exp} → Γ ⊢ e ∶ A → Γ ≡ᵀ Δ → Δ ⊢ e ∶ A
  ⊢≡ᵀ-envsub : {n : ℕ} {A B : Ty {n}} {Γ Δ : TEnv {n}} → Γ ⊢ A ≡ᵀ B → Γ ≡ᵀ Δ → Δ ⊢ A ≡ᵀ B

  -- IMPLEMENTATIONS
  ≡ᵀ-extr {n} {.0} {(⟨ A , Γ ⟩)} {(⟨ B , Δ ⟩)} {.A} here (tsuc eq x) = B , (here , x)
  ≡ᵀ-extr {n} {.(ℕ.suc _)} {.(⟨ _ , _ ⟩)} {.(⟨ _ , _ ⟩)} {A} (there j) (tsuc eq x)
    with ≡ᵀ-extr j eq
  ...  | fst , snd , snd₁ = fst , ((there snd) , snd₁)

  ⊢-envsub {n} {.(Label _)} {Γ} {Δ} TLabF eq = TLabF
  ⊢-envsub {n} {.(Pi _ _)} {Γ} {Δ} (TPiF j j₁) eq = TPiF (⊢-envsub j eq) (⊢-envsub j₁ (tsuc eq (CRefl{ok = ⊢-envsub j eq})))
  ⊢-envsub {n} {.(Sigma _ _)} {Γ} {Δ} (TSigmaF j j₁) eq = TSigmaF (⊢-envsub j eq) (⊢-envsub j₁ (tsuc eq (CRefl{ok = ⊢-envsub j eq})))
  ⊢-envsub {n} {.(Case _ _)} {Γ} {Δ} (TCaseF f' v x) eq = TCaseF (λ l i → ⊢-envsub (f' l i) eq) v (⊢∶-envsub x eq)

  ⊢∶-envsub {n} {A} {Γ} {Δ} {e} (TConv j x) eq = TConv (⊢∶-envsub j eq) (⊢≡ᵀ-envsub x eq)
  ⊢∶-envsub {n} {A} {Γ} {Δ} {Var m} (TVarE j eq') eq = TVarE (proj₁ (proj₂ (≡ᵀ-extr j eq))) (CTrans (⊢≡ᵀ-envsub eq' (≡ᵀ-tail m eq)) (proj₂ (proj₂ (≡ᵀ-extr j eq))))
  ⊢∶-envsub {n} {.(Pi _ _)} {Γ} {Δ} {.(Abs _)} (TPiI{ok = ok}{ok' = ok'} j) eq = TPiI{ok = ⊢-envsub ok eq}{ok' = ⊢-envsub ok' (tsuc eq (CRefl{ok = ⊢-envsub ok eq}))} (⊢∶-envsub j (tsuc eq (CRefl{ok = ⊢-envsub ok eq})))
  ⊢∶-envsub {n} {.([ 0 ↦ _ ]ᵀ _)} {Γ} {Δ} {.(App _ _)} (TPiE j j₁ x) eq = TPiE (⊢∶-envsub j eq) (⊢∶-envsub j₁ eq) (⊢-envsub x eq)
  ⊢∶-envsub {n} {.(Sigma _ _)} {Γ} {Δ} {.(Prod _ _)} (TSigmaI {ok = ok}{ok' = ok'} j j₁) eq = TSigmaI {ok = ⊢-envsub ok eq}{ok' =  ⊢-envsub ok' (tsuc eq (CRefl{ok = ⊢-envsub ok eq}))} (⊢∶-envsub j eq) (⊢∶-envsub j₁ (tsuc eq (CRefl{ok = ⊢-envsub ok eq})))
  ⊢∶-envsub {n} {A} {Γ} {Δ} {.(FakeLet _ _)} (TSigmaE {ok = ok} {ok' = ok'} j j₁) eq
    = TSigmaE{ok = ⊢-envsub ok eq}{ok' = ⊢-envsub ok' (tsuc eq (CRefl{ok = ⊢-envsub ok eq}))} (⊢∶-envsub j eq) (⊢∶-envsub j₁ (tsuc (tsuc eq (CRefl{ok = ⊢-envsub ok eq})) (CRefl{ok = ⊢-envsub ok' (tsuc eq (CRefl{ok = ⊢-envsub ok eq}))})))
  ⊢∶-envsub {n} {.(Label _)} {Γ} {Δ} {.(LabI _)} (TLabI ins) eq = TLabI ins
  ⊢∶-envsub {n} {A} {Γ} {Δ} {.(LabE _ (LabI _))} (TLabEl{scopecheck = scopecheck} j j₁) eq rewrite (≡ᵀ-length eq) = TLabEl{scopecheck = scopecheck} (⊢∶-envsub j eq) (⊢∶-envsub j₁ eq)
  ⊢∶-envsub {n} {A} {Γ} {Δ} {.(LabE _ (Var _))} (TLabEx f' j) eq = TLabEx (λ l i → ⊢∶-envsub (f' l i) eq) (⊢∶-envsub j eq)

  ⊢≡ᵀ-envsub {n} {A} {.A} {Γ} {Δ} (CRefl{ok = ok}) eq = CRefl{ok = ⊢-envsub ok eq}
  ⊢≡ᵀ-envsub {n} {A} {B} {Γ} {Δ} (CSym j) eq = CSym (⊢≡ᵀ-envsub j eq)
  ⊢≡ᵀ-envsub {n} {A} {B} {Γ} {Δ} (CTrans j j₁) eq = CTrans (⊢≡ᵀ-envsub j eq) (⊢≡ᵀ-envsub j₁ eq)
  ⊢≡ᵀ-envsub {n} {A} {.(Case (λ l i → A) (LabI _))} {Γ} {Δ} (CLabEta{ins = ins} x x₁) eq = CLabEta{ins = ins} (⊢∶-envsub x eq) (⊢-envsub x₁ eq)
  ⊢≡ᵀ-envsub {n} {(Case f (LabI l))} {.(f l ins)} {Γ} {Δ} (CLabBeta x ins) eq = CLabBeta ((⊢-envsub x eq)) ins
  ⊢≡ᵀ-envsub {n} {.(Pi _ _)} {.(Pi _ _)} {Γ} {Δ} (CPi{ok = ok} j j₁) eq = CPi{ok = ⊢-envsub ok eq} (⊢≡ᵀ-envsub j eq) (⊢≡ᵀ-envsub j₁ (tsuc eq (CRefl{ok = ⊢-envsub ok eq})))
  ⊢≡ᵀ-envsub {n} {.(Sigma _ _)} {.(Sigma _ _)} {Γ} {Δ} (CSigma{ok = ok} j j₁) eq = CSigma{ok = ⊢-envsub ok eq} (⊢≡ᵀ-envsub j eq) (⊢≡ᵀ-envsub j₁ (tsuc eq (CRefl{ok = ⊢-envsub ok eq})))
  ⊢≡ᵀ-envsub {n} {.(Case _ _)} {.(Case _ _)} {Γ} {Δ} (CLab v x) eq = CLab (⊢-envsub v eq) (λ l i → ⊢≡ᵀ-envsub (x l i) eq)


  -- uniqueness of judgements
  val-uniqueness : {n : ℕ} {e : Exp {n}} → (v v' : Val e) → v ≡ v'
  val-uniqueness {n} {.(Var n₁)} (VVar {n = n₁}) (VVar {n = .n₁}) = refl
  val-uniqueness {n} {.(LabI x)} (VLab {x = x}) (VLab {x = .x}) = refl
  val-uniqueness {n} {.(Abs e)} (VFun {e = e}) (VFun {e = .e}) = refl
  val-uniqueness {n} {.(Prod e e')} (VProd {e = e} {e' = e'}) (VProd {e = .e} {e' = .e'}) = refl

  ins-uniqueness : {n : ℕ} {s : Subset n} {l : Fin n} → (i i' : l ∈ s) → i ≡ i'
  ins-uniqueness {.(ℕ.suc _)} {.(true ∷ _)} {.zero} here here = refl
  ins-uniqueness {.(ℕ.suc _)} {.(_ ∷ _)} {.(Fin.suc _)} (there i) (there i') = cong there (ins-uniqueness i i')


  --  Type environment equivalency for ≡ᵀ'
  data _≡ᵀ'_ {n} : TEnv {n} → TEnv {n} → Set where
    tzero : [] ≡ᵀ' []
    tsuc : {Γ Δ : TEnv {n}} {T T' : Ty} {ok : Γ ⊢ T} {ok' : Δ ⊢ T'} → Γ ≡ᵀ' Δ → Δ ⊢ T ≡ᵀ' T' → ⟨ T , Γ ⟩ {ok}  ≡ᵀ' ⟨ T' , Δ ⟩ {ok'}

  ≡ᵀ'-refl : {n : ℕ} {Γ : TEnv {n}} → Γ ≡ᵀ' Γ
  ≡ᵀ'-refl {n} {[]} = tzero
  ≡ᵀ'-refl {n} {⟨ T , Γ ⟩ {ok = ok}} = tsuc ≡ᵀ'-refl (CRefl'{ok = ok})

  ≡ᵀ'-tail : {n : ℕ} {Γ Δ : TEnv {n}} → (m : ℕ) → Γ ≡ᵀ' Δ → env-tail Γ m ≡ᵀ' env-tail Δ m
  ≡ᵀ'-tail {n} {.[]} {.[]} m tzero = tzero
  ≡ᵀ'-tail {n} {.(⟨ _ , _ ⟩)} {.(⟨ _ , _ ⟩)} zero (tsuc eq x) = eq
  ≡ᵀ'-tail {n} {(⟨ T , Γ ⟩)} {(⟨ T' , Δ ⟩)} (ℕ.suc m) (tsuc eq x) = ≡ᵀ'-tail m eq

  ≡ᵀ'-length : {n : ℕ} {Γ Δ : TEnv {n}} → Γ ≡ᵀ' Δ → length Γ ≡ length Δ
  ≡ᵀ'-length {n} {.[]} {.[]} tzero = refl
  ≡ᵀ'-length {n} {.(⟨ _ , _ ⟩)} {.(⟨ _ , _ ⟩)} (tsuc eq x) = cong ℕ.suc (≡ᵀ'-length eq)

  -- DEFINITIONS
  ⊢∧≡ᵀ'⇒⊢ : {n : ℕ} {Γ : TEnv {n}} {T T' : Ty} → Γ ⊢ T → Γ ⊢ T ≡ᵀ' T' → Γ ⊢ T'
  ≡ᵀ'⇒⊢ : {n : ℕ} {Γ : TEnv {n}} {T T' : Ty} → Γ ⊢ T ≡ᵀ' T' → Γ ⊢ T × Γ ⊢ T'

  ≡ᵀ⊆≡ᵀ' : {n : ℕ} {A B : Ty {n}} {Γ : TEnv {n}} → Γ ⊢ A ≡ᵀ B → Γ ⊢ A ≡ᵀ' B
  ≡ᵀ'⊆≡ᵀ : {n : ℕ} {A B : Ty {n}} {Γ : TEnv {n}} → Γ ⊢ A ≡ᵀ' B → Γ ⊢ A ≡ᵀ B
  ≡ᵀ⊆≡ᵀ'-env : {n : ℕ} {Γ Δ : TEnv {n}} → Γ ≡ᵀ Δ → Γ ≡ᵀ' Δ
  ≡ᵀ'⊆≡ᵀ-env : {n : ℕ} {Γ Δ : TEnv {n}} → Γ ≡ᵀ' Δ → Γ ≡ᵀ Δ

  ≡ᵀ'-trans : {n : ℕ} {A B C : Ty {n}} {Γ : TEnv {n}} → Γ ⊢ A ≡ᵀ' B → Γ ⊢ B ≡ᵀ' C → Γ ⊢ A ≡ᵀ' C
  ≡ᵀ'-sym : {n : ℕ} {A B : Ty {n}} {Γ : TEnv {n}} → Γ ⊢ A ≡ᵀ' B → Γ ⊢ B ≡ᵀ' A

  ≡ᵀ-extr' : {n m : ℕ} {Γ Δ : TEnv} {A : Ty {n}} → (m ∶ A ∈ Γ) → Γ ≡ᵀ' Δ → ∃[ B ] (m ∶ B ∈ Δ × (env-tail Δ m) ⊢ A ≡ᵀ' B)
  ⊢-envsub' : {n : ℕ} {A : Ty {n}} {Γ Δ : TEnv {n}} → Γ ⊢ A → Γ ≡ᵀ' Δ → Δ ⊢ A
  ⊢∶-envsub' : {n : ℕ} {A : Ty {n}} {Γ Δ : TEnv {n}} {e : Exp} → Γ ⊢ e ∶ A → Γ ≡ᵀ' Δ → Δ ⊢ e ∶ A
  ⊢≡ᵀ-envsub' : {n : ℕ} {A B : Ty {n}} {Γ Δ : TEnv {n}} → Γ ⊢ A ≡ᵀ' B → Γ ≡ᵀ' Δ → Δ ⊢ A ≡ᵀ' B

  -- IMPLEMENTATIONS
  --- TRANSITIVITY
  ≡ᵀ'-trans {n} {A} {.A} {C} {Γ} CRefl' j' = j'
  ≡ᵀ'-trans {n} {Case f (LabI z)} {B} {.B} {Γ} (CLabBeta' x ins eq) CRefl' = CLabBeta' x ins eq
  ≡ᵀ'-trans {n} {Case f (LabI z)} {B} {C} {Γ} (CLabBeta' x ins eq) j = CLabBeta' x ins (≡ᵀ'-trans eq j)
  ≡ᵀ'-trans {n} {.(Pi _ _)} {.(Pi _ _)} {.(Pi _ _)} {Γ} (CPi' j j₁) CRefl' = CPi' j j₁
  ≡ᵀ'-trans {n} {.(Pi _ _)} {.(Pi _ _)} {.(Pi _ _)} {Γ} (CPi' {ok = ok} j j₁) (CPi' j' j'') = CPi' {ok = ok} (≡ᵀ'-trans j j') (≡ᵀ'-trans j₁ (⊢≡ᵀ-envsub' j'' (tsuc ≡ᵀ'-refl (≡ᵀ'-sym j))))
  ≡ᵀ'-trans {n} {.(Pi _ _)} {.(Pi _ _)} {.(Case _ (LabI _))} {Γ} (CPi' j j₁) (CLabEta' x x₁ j') = CLabEta' x x₁ (≡ᵀ'-trans j' (≡ᵀ'-sym (CPi' j j₁)))
  ≡ᵀ'-trans {n} {.(Sigma _ _)} {.(Sigma _ _)} {.(Sigma _ _)} {Γ} (CSigma' j j₁) CRefl' = CSigma' j j₁
  ≡ᵀ'-trans {n} {.(Sigma _ _)} {.(Sigma _ _)} {.(Sigma _ _)} {Γ} (CSigma' j j₁) (CSigma' j' j'') = CSigma' (≡ᵀ'-trans j j') (≡ᵀ'-trans j₁ (⊢≡ᵀ-envsub' j'' (tsuc ≡ᵀ'-refl (≡ᵀ'-sym j))))
  ≡ᵀ'-trans {n} {.(Sigma _ _)} {.(Sigma _ _)} {.(Case _ (LabI _))} {Γ} (CSigma' j j₁) (CLabEta' x x₁ j') = CLabEta' x x₁ (≡ᵀ'-trans j' (≡ᵀ'-sym (CSigma' j j₁)))
  ≡ᵀ'-trans {n} {.(Case _ _)} {.(Case _ _)} {.(Case _ _)} {Γ} (CLab' {ok = ok}{ok' = ok'} v x) CRefl' = CLab'{ok = ok}{ok' = ok'} v x
  ≡ᵀ'-trans {n} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {C} {Γ} (CLab' {ok = ok} v x) (CLabBeta'{x = x₂} x₁ ins j') = CLabBeta' (TCaseF ok VLab (TLabI ins)) ins (≡ᵀ'-trans (x x₂ ins) j')
  ≡ᵀ'-trans {n} {.(Case _ _)} {.(Case _ _)} {.(Case _ _)} {Γ} (CLab'{ok = ok} v x) (CLab'{ok' = ok'} v₁ x₁) = CLab'{ok = ok}{ok' = ok'}  v (λ l i → ≡ᵀ'-trans (x l i) (x₁ l i))
  ≡ᵀ'-trans {n} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {Γ} (CLab'{ok = ok} v x) (CLabSub'{l = l}{ins = ins}{ok' = ok'} x₁)
    = CLabSub'{ok = ok}{ok' = ok'} (≡ᵀ'-trans (x l ins) x₁)
  ≡ᵀ'-trans {n} {(Case f e)} {(Case f' .e)} {(Case f'' (LabI l))} {Γ} (CLab'{ok = ok}{ok' = ok'} (TCaseF u v w) x) (CLabEta'{ins = ins} x₁ x₂ j')
    = CLabEta'{ins = ins} x₁ x₂ (≡ᵀ'-trans j' (CLab'{ok = ok'}{ok' = ok} (TCaseF ok' v w) λ l₁ i → ≡ᵀ'-sym (x l₁ i))) 
  ≡ᵀ'-trans {n} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {Γ} (CLabSub'{ok = ok} {ok' = ok'} x) CRefl' = CLabSub'{ok = ok}{ok' = ok'} x
  ≡ᵀ'-trans {n} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {C} {Γ} (CLabSub' {ins = ins'} {ok = ok} x) (CLabBeta' x₁ ins j')
    rewrite (ins-uniqueness ins' ins)
    with (≡ᵀ'-trans x j')
  ...  | w
       rewrite (ins-uniqueness ins ins') = CLabBeta' (TCaseF ok VLab (TLabI ins')) ins' w
  ≡ᵀ'-trans {n} {(Case f (LabI l))} {(Case f' (LabI .l))} {(Case f'' (LabI .l))} {Γ} (CLabSub'{ins = ins}{ok = ok}{ok' = ok'} x) (CLab'{ok = ok''}{ok' = ok'''} v x₁)
    = CLabSub'{ok = ok}{ok' = ok'''} (≡ᵀ'-trans x (x₁ l ins))
  ≡ᵀ'-trans {n} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {Γ} (CLabSub'{ins = ins}{ok = ok}{ok' = ok'} x) (CLabSub'{ins = ins'}{ok = ok''}{ok' = ok'''} x')
    rewrite (ins-uniqueness ins ins')
          = CLabSub'{ins = ins'}{ok = ok}{ok' = ok'''} (≡ᵀ'-trans x x')
  ≡ᵀ'-trans {n} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {Γ} (CLabSub'{ok = ok}{ok' = ok'} x) (CLabEta' x₁ x₂ j')
    = CLabEta' x₁ x₂ (≡ᵀ'-trans j' (CLabSub'{ok = ok'}{ok' = ok} (≡ᵀ'-sym x)))
  ≡ᵀ'-trans {n} {A} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {Γ} (CLabEta' x x₁ x₂) CRefl' = CLabEta' x x₁ x₂
  ≡ᵀ'-trans {n} {A} {.(Case _ (LabI _))} {C} {Γ} (CLabEta' {ins = ins'} x x₁ x₂) (CLabBeta' x₃ ins j')
    rewrite (ins-uniqueness ins ins')
          =  ≡ᵀ'-trans (≡ᵀ'-sym x₂) j'
  ≡ᵀ'-trans {n} {A} {(Case f (LabI l))} {(Case f' (LabI .l))} {Γ} (CLabEta'{ins = ins} x x₁ x₂) (CLab'{ok' = ok'} v x₃) = CLabEta'{ins = ins} x ok' (≡ᵀ'-trans (≡ᵀ'-sym (x₃ l ins)) x₂)
  ≡ᵀ'-trans {n} {A} {(Case f (LabI l))} {(Case f' (LabI .l))} {Γ} (CLabEta'{ins = ins} x x₁ x₂) (CLabSub'{ins = ins'}{ok' = ok'} j')
    rewrite (ins-uniqueness ins ins')
    with (≡ᵀ'-trans (≡ᵀ'-sym j') x₂)
  ...  | w
       rewrite (ins-uniqueness ins' ins) = CLabEta'{ins = ins} x ok' w
  ≡ᵀ'-trans {n} {A} {(Case f (LabI l))} {(Case f' (LabI l'))} {Γ} (CLabEta'{ins = ins} x x₁ x₂) (CLabEta'{ins = ins'} x₃ x₄ j')
    =  CLabEta'{ins = ins'} x₃ x₄ (≡ᵀ'-trans j' (≡ᵀ'-trans (CLabBeta' (TCaseF x₁ VLab x) ins (CRefl'{ok = x₁ l ins})) x₂))

  --- SYMMETRY
  ≡ᵀ'-sym {n} {A} {.A} {Γ} (CRefl'{ok = ok}) = CRefl'{ok = ok}
  ≡ᵀ'-sym {n} {(Case f (LabI x₁))} {B} {Γ} (CLabBeta' (TCaseF f' v x) ins eq) = CLabEta' x f' eq
  ≡ᵀ'-sym {n} {.(Pi _ _)} {.(Pi _ _)} {Γ} (CPi'{ok = ok} j j₁) = CPi'{ok = ⊢∧≡ᵀ'⇒⊢ ok j} (≡ᵀ'-sym j) (⊢≡ᵀ-envsub' (≡ᵀ'-sym j₁) (tsuc ≡ᵀ'-refl j)) 
  ≡ᵀ'-sym {n} {.(Sigma _ _)} {.(Sigma _ _)} {Γ} (CSigma'{ok = ok} j j₁) = CSigma'{ok = ⊢∧≡ᵀ'⇒⊢ ok j} (≡ᵀ'-sym j) (⊢≡ᵀ-envsub' (≡ᵀ'-sym j₁) (tsuc ≡ᵀ'-refl j))
  ≡ᵀ'-sym {n} {.(Case _ _)} {.(Case _ _)} {Γ} (CLab'{ok = ok}{ok' = ok'} (TCaseF u v w) x) = CLab'{ok = ok'}{ok' = ok} (TCaseF ok' v w) (λ l i → ≡ᵀ'-sym (x l i))
  ≡ᵀ'-sym {n} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {Γ} (CLabSub'{ok = ok}{ok' = ok'} x) = CLabSub'{ok = ok'}{ok' = ok} (≡ᵀ'-sym x)
  ≡ᵀ'-sym {n} {A} {(Case f (LabI x'))} {Γ} (CLabEta'{ins = ins} x x₁ x₂) = CLabBeta' (TCaseF x₁ VLab x) ins x₂ -- CLabBeta' (TCaseF x₁ VLab x) ins refl 

  --- ⊢∧≡ᵀ'⇒⊢ ≡ᵀ'⇒⊢
  ⊢∧≡ᵀ'⇒⊢ {n} {Γ} {T} {.T} j CRefl' = j
  ⊢∧≡ᵀ'⇒⊢ {n} {Γ} {T} {.(Case _ (LabI _))} j (CLabEta' x x₁ eq) = TCaseF x₁ VLab x
  ⊢∧≡ᵀ'⇒⊢ {n} {Γ} {.(Pi _ _)} {.(Pi _ _)} (TPiF j j₁) (CPi'{ok = ok} eq eq₁) = TPiF (⊢∧≡ᵀ'⇒⊢ ok eq ) (⊢∧≡ᵀ'⇒⊢ (⊢-envsub' j₁ (tsuc ≡ᵀ'-refl eq)) (⊢≡ᵀ-envsub' eq₁ (tsuc ≡ᵀ'-refl eq)))
  ⊢∧≡ᵀ'⇒⊢ {n} {Γ} {.(Sigma _ _)} {.(Sigma _ _)} (TSigmaF j j₁) (CSigma'{ok = ok} eq eq₁) = TSigmaF (⊢∧≡ᵀ'⇒⊢ ok eq ) (⊢∧≡ᵀ'⇒⊢ (⊢-envsub' j₁ (tsuc ≡ᵀ'-refl eq)) (⊢≡ᵀ-envsub' eq₁ (tsuc ≡ᵀ'-refl eq)))
  ⊢∧≡ᵀ'⇒⊢ {n} {Γ} {(Case f (LabI l))} {T'} (TCaseF f' v x) (CLabBeta' x₁ ins eq) = ⊢∧≡ᵀ'⇒⊢ (f' l ins) eq 
  ⊢∧≡ᵀ'⇒⊢ {n} {Γ} {.(Case _ _)} {.(Case _ _)} (TCaseF f' v x) (CLab'{ok = ok}{ok' = ok'} z x₁) = TCaseF ok' v x
  ⊢∧≡ᵀ'⇒⊢ {n} {Γ} {.(Case _ (LabI _))} {.(Case _ (LabI _))} (TCaseF f' v x) (CLabSub'{ok = ok}{ok' = ok'} eq) = TCaseF ok' v x

  ≡ᵀ'⇒⊢ {n} {Γ} {T} {.T} (CRefl'{ok = ok}) = ok , ok
  ≡ᵀ'⇒⊢ {n} {Γ} {T} {(Case f (LabI l))} (CLabEta'{ins = ins} x x₁ j) = ⊢∧≡ᵀ'⇒⊢ (x₁ l ins) j , TCaseF x₁ VLab x
  ≡ᵀ'⇒⊢ {n} {Γ} {Case f (LabI l)} {T'} (CLabBeta' (TCaseF f' v x) ins j) = (TCaseF f' v x) , (⊢∧≡ᵀ'⇒⊢ (f' l ins) j)
  ≡ᵀ'⇒⊢ {n} {Γ} {.(Pi _ _)} {.(Pi _ _)} (CPi'{ok = ok} j j₁) = TPiF ok (proj₁ (≡ᵀ'⇒⊢ j₁)) , TPiF (⊢∧≡ᵀ'⇒⊢ ok j) (⊢-envsub' (proj₂ (≡ᵀ'⇒⊢ j₁)) (tsuc ≡ᵀ'-refl j))
  ≡ᵀ'⇒⊢ {n} {Γ} {.(Sigma _ _)} {.(Sigma _ _)} (CSigma'{ok = ok} j j₁) = TSigmaF ok (proj₁ (≡ᵀ'⇒⊢ j₁)) , TSigmaF (⊢∧≡ᵀ'⇒⊢ ok j) (⊢-envsub' (proj₂ (≡ᵀ'⇒⊢ j₁)) (tsuc ≡ᵀ'-refl j))
  ≡ᵀ'⇒⊢ {n} {Γ} {.(Case _ _)} {.(Case _ _)} (CLab' {ok = ok} {ok' = ok'} (TCaseF f' v x₁) x) = TCaseF ok v x₁ , TCaseF ok' v x₁
  ≡ᵀ'⇒⊢ {n} {Γ} {.(Case _ (LabI _))} {.(Case _ (LabI _))} (CLabSub'{ins = ins}{ok = ok}{ok' = ok'} j) = (TCaseF ok VLab (TLabI ins)) , TCaseF ok' VLab (TLabI ins)

  --- EQUIVALENCE ≡ᵀ & ≡ᵀ'
  ≡ᵀ⊆≡ᵀ' {n} {A} {.A} {Γ} (CRefl{ok = ok}) = CRefl'{ok = ok}
  ≡ᵀ⊆≡ᵀ' {n} {A} {B} {Γ} (CSym j) = ≡ᵀ'-sym (≡ᵀ⊆≡ᵀ' j)
  ≡ᵀ⊆≡ᵀ' {n} {A} {B} {Γ} (CTrans j j₁) = ≡ᵀ'-trans (≡ᵀ⊆≡ᵀ' j) (≡ᵀ⊆≡ᵀ' j₁)
  ≡ᵀ⊆≡ᵀ' {n} {A} {.(Case (λ l i → A) (LabI _))} {Γ} (CLabEta{ins = ins} x x₁) = CLabEta' {ins = ins} x (λ l ins₁ → x₁) (CRefl'{ok = x₁}) -- CLabEta' x x₁
  ≡ᵀ⊆≡ᵀ' {n} {Case f (LabI l)} {.(f l ins)} {Γ} (CLabBeta (TCaseF f' v x) ins) = CLabBeta' (TCaseF f' v x) ins (CRefl' {ok = f' l ins})
  ≡ᵀ⊆≡ᵀ' {n} {.(Pi _ _)} {.(Pi _ _)} {Γ} (CPi j j₁) = CPi' (≡ᵀ⊆≡ᵀ' j) (≡ᵀ⊆≡ᵀ' j₁)
  ≡ᵀ⊆≡ᵀ' {n} {.(Sigma _ _)} {.(Sigma _ _)} {Γ} (CSigma j j₁) = CSigma' (≡ᵀ⊆≡ᵀ' j) (≡ᵀ⊆≡ᵀ' j₁)
  ≡ᵀ⊆≡ᵀ' {n} {.(Case _ _)} {.(Case _ _)} {Γ} (CLab v x)
    = CLab'{ok = λ l' i → proj₁ (≡ᵀ'⇒⊢ (≡ᵀ⊆≡ᵀ' (x l' i)))}{ok' = λ l' i → proj₂ (≡ᵀ'⇒⊢ (≡ᵀ⊆≡ᵀ' (x l' i)))} v (λ l i → ≡ᵀ⊆≡ᵀ' (x l i))

  ≡ᵀ'⊆≡ᵀ {n} {A} {.A} {Γ} (CRefl'{ok = ok}) = CRefl{ok = ok}
  ≡ᵀ'⊆≡ᵀ {n} {A} {(Case f (LabI l))} {Γ} (CLabEta'{ins = ins} x x₁ eq) = CSym (CTrans (CLabBeta (TCaseF x₁ VLab x) ins) (≡ᵀ'⊆≡ᵀ eq)) -- CSym (CLabBeta{f = f} (TCaseF x₁ VLab x) ins)
  ≡ᵀ'⊆≡ᵀ {n} {(Case f (LabI l))} {B} {Γ} (CLabBeta' x ins eq) = CTrans (CLabBeta x ins) (≡ᵀ'⊆≡ᵀ eq) -- CLabBeta x ins -- CLabBeta x ins
  ≡ᵀ'⊆≡ᵀ {n} {.(Pi _ _)} {.(Pi _ _)} {Γ} (CPi' j j₁) = CPi (≡ᵀ'⊆≡ᵀ j ) (≡ᵀ'⊆≡ᵀ j₁)
  ≡ᵀ'⊆≡ᵀ {n} {.(Sigma _ _)} {.(Sigma _ _)} {Γ} (CSigma' j j₁) = CSigma (≡ᵀ'⊆≡ᵀ j) (≡ᵀ'⊆≡ᵀ j₁)
  ≡ᵀ'⊆≡ᵀ {n} {.(Case _ _)} {.(Case _ _)} {Γ} (CLab' v x) = CLab v (λ l i → ≡ᵀ'⊆≡ᵀ (x l i))
  ≡ᵀ'⊆≡ᵀ {n} {Case f (LabI l)} {Case g (LabI .l)} {Γ} (CLabSub'{ins = ins}{ok = ok}{ok'} eq)
    with (CLabBeta{f = f} (TCaseF ok VLab (TLabI ins)) ins) | (CSym (CLabBeta{f = g} (TCaseF ok' VLab (TLabI ins)) ins))
  ...  | w | w'  = CTrans (CTrans w (≡ᵀ'⊆≡ᵀ eq)) w' -- CTrans w w'

  ≡ᵀ⊆≡ᵀ'-env {n} {.[]} {.[]} tzero = tzero
  ≡ᵀ⊆≡ᵀ'-env {n} {.(⟨ _ , _ ⟩)} {.(⟨ _ , _ ⟩)} (tsuc eq x) = tsuc (≡ᵀ⊆≡ᵀ'-env eq) (≡ᵀ⊆≡ᵀ' x)

  ≡ᵀ'⊆≡ᵀ-env {n} {.[]} {.[]} tzero = tzero
  ≡ᵀ'⊆≡ᵀ-env {n} {.(⟨ _ , _ ⟩)} {.(⟨ _ , _ ⟩)} (tsuc eq x) = tsuc (≡ᵀ'⊆≡ᵀ-env eq) (≡ᵀ'⊆≡ᵀ x)

  --- ENVIRONMENT EQUIVALENCE
  ≡ᵀ-extr' {n} {.0} {(⟨ A , Γ ⟩)} {(⟨ T' , Δ ⟩)} {A}  here (tsuc{T' = .T'} eq x) = T' , (here , x)
  ≡ᵀ-extr' {n} {(ℕ.suc m)} {(⟨ T , Γ ⟩)} {⟨ T' , Δ ⟩} {A} (there ins) (tsuc eq x)
    with ≡ᵀ-extr' {m = m} {Γ} {Δ} ins eq
  ...  | fst , snd , snd₁ = fst , ((there snd) , snd₁)

  ⊢-envsub' {n} {.(Label _)} {Γ} {Δ} TLabF eq = TLabF
  ⊢-envsub' {n} {.(Pi _ _)} {Γ} {Δ} (TPiF j j₁) eq = TPiF (⊢-envsub' j eq) (⊢-envsub' j₁ (tsuc eq (CRefl'{ok = ⊢-envsub' j eq})))
  ⊢-envsub' {n} {.(Sigma _ _)} {Γ} {Δ} (TSigmaF j j₁) eq = TSigmaF (⊢-envsub' j eq) (⊢-envsub' j₁ (tsuc eq (CRefl'{ok = ⊢-envsub' j eq})))
  ⊢-envsub' {n} {.(Case _ _)} {Γ} {Δ} (TCaseF f' v x) eq = TCaseF (λ l i → ⊢-envsub' (f' l i) eq) v (⊢∶-envsub' x eq)

  ⊢∶-envsub' {n} {A} {Γ} {Δ} {e} (TConv j x₁) eq = TConv (⊢∶-envsub' j eq) (⊢≡ᵀ-envsub x₁ (≡ᵀ'⊆≡ᵀ-env eq))
  ⊢∶-envsub' {n} {A} {Γ} {Δ} {Var m} (TVarE j q) eq = TVarE (proj₁ (proj₂ (≡ᵀ-extr' j eq))) (CTrans (⊢≡ᵀ-envsub q (≡ᵀ-tail m (≡ᵀ'⊆≡ᵀ-env eq))) (≡ᵀ'⊆≡ᵀ (proj₂ (proj₂ (≡ᵀ-extr' j eq)))))
  ⊢∶-envsub' {n} {.(Pi _ _)} {Γ} {Δ} {Abs e} (TPiI{ok = ok}{ok' = ok'} j) eq = TPiI{ok = ⊢-envsub' ok eq}{ok' = ⊢-envsub' ok' (tsuc eq (CRefl'{ok = ⊢-envsub ok (≡ᵀ'⊆≡ᵀ-env eq) }))} (⊢∶-envsub' j (tsuc eq (CRefl'{ok = ⊢-envsub' ok eq})))
  ⊢∶-envsub' {n} {.([ 0 ↦ e₁ ]ᵀ _)} {Γ} {Δ} {App e e₁} (TPiE j j₁ x) eq = TPiE (⊢∶-envsub' j eq) (⊢∶-envsub' j₁ eq) (⊢-envsub' x eq)
  ⊢∶-envsub' {n} {.(Label _)} {Γ} {Δ} {LabI x} (TLabI ins) eq = TLabI ins
  ⊢∶-envsub' {n} {A} {Γ} {Δ} {LabE f .(LabI _)} (TLabEl{scopecheck = sc} j j₁) eq rewrite (≡ᵀ'-length eq) = TLabEl{scopecheck = sc} (⊢∶-envsub' j eq) (⊢∶-envsub' j₁ eq)
  ⊢∶-envsub' {n} {A} {Γ} {Δ} {LabE f .(Var _)} (TLabEx f' j) eq = TLabEx (λ l i → ⊢∶-envsub' (f' l i) eq) (⊢∶-envsub' j eq)
  ⊢∶-envsub' {n} {.(Sigma _ _)} {Γ} {Δ} {Prod e e₁} (TSigmaI{ok = ok}{ok' = ok'} j j₁) eq = TSigmaI{ok = ⊢-envsub' ok eq}{ok' = ⊢-envsub' ok' (tsuc eq (CRefl'{ok = ⊢-envsub ok (≡ᵀ'⊆≡ᵀ-env eq)}))} (⊢∶-envsub' j eq) (⊢∶-envsub' j₁ (tsuc eq (CRefl'{ok = ⊢-envsub' ok eq})))
  ⊢∶-envsub' {n} {A} {Γ} {Δ} {FakeLet e e₁} (TSigmaE{ok = ok}{ok' = ok'} j j₁) eq = TSigmaE{ok = ⊢-envsub' ok eq}{ok' = ⊢-envsub' ok' (tsuc eq (CRefl'{ok = ⊢-envsub' ok eq}))} (⊢∶-envsub' j eq) (⊢∶-envsub' j₁ (tsuc (tsuc eq (CRefl'{ok = ⊢-envsub' ok eq})) (CRefl'{ok = ⊢-envsub' ok' (tsuc eq (CRefl'{ok = ⊢-envsub' ok eq}))})))

  ⊢≡ᵀ-envsub' {n} {A} {.A} {Γ} {Δ} (CRefl'{ok = ok}) eq = CRefl'{ok = ⊢-envsub' ok eq}
  ⊢≡ᵀ-envsub' {n} {A} {.(Case _ (LabI _))} {Γ} {Δ} (CLabEta' x x₁ j) eq = CLabEta' (⊢∶-envsub' x eq) (λ l ins' → ⊢-envsub' (x₁ l ins') eq) (⊢≡ᵀ-envsub' j eq)
  ⊢≡ᵀ-envsub' {n} {.(Case _ (LabI _))} {B} {Γ} {Δ} (CLabBeta' x ins j) eq = CLabBeta' (⊢-envsub'  x eq) ins (⊢≡ᵀ-envsub' j eq)
  ⊢≡ᵀ-envsub' {n} {.(Pi _ _)} {.(Pi _ _)} {Γ} {Δ} (CPi'{ok = ok} j j₁) eq = CPi'{ok = ⊢-envsub' ok eq} (⊢≡ᵀ-envsub' j eq) (⊢≡ᵀ-envsub' j₁ (tsuc eq (CRefl'{ok = ⊢-envsub' ok eq})))
  ⊢≡ᵀ-envsub' {n} {.(Sigma _ _)} {.(Sigma _ _)} {Γ} {Δ} (CSigma'{ok = ok} j j₁) eq = CSigma'{ok = ⊢-envsub' ok eq} (⊢≡ᵀ-envsub' j eq) (⊢≡ᵀ-envsub' j₁ (tsuc eq (CRefl'{ok = ⊢-envsub' ok eq})))
  ⊢≡ᵀ-envsub' {n} {.(Case _ _)} {.(Case _ _)} {Γ} {Δ} (CLab'{ok = ok}{ok' = ok'} v x) eq = CLab'{ok = λ l' i → ⊢-envsub' (ok l' i) eq}{ok' = λ l' i → ⊢-envsub' (ok' l' i) eq} (⊢-envsub' v eq) (λ l i → ⊢≡ᵀ-envsub' (x l i) eq)
  ⊢≡ᵀ-envsub' {n} {.(Case _ (LabI _))} {.(Case _ (LabI _))} {Γ} {Δ} (CLabSub'{ok = ok}{ok' = ok'} j) eq = CLabSub'{ok = λ l' i → ⊢-envsub' (ok l' i) eq}{ok' = λ l' i → ⊢-envsub' (ok' l' i) eq} (⊢≡ᵀ-envsub' j eq)


  --- COROLLARIES
  ≢ᵀ'⇒≢ᵀ : {n : ℕ} {A B : Ty {n}} {Γ : TEnv {n}} → ¬ (Γ ⊢ A ≡ᵀ' B) → ¬ (Γ ⊢ A ≡ᵀ B)
  ≢ᵀ'⇒≢ᵀ {n} {A} {B} {Γ} = contraposition ≡ᵀ⊆≡ᵀ'


  -- Normalform of types; no redex possible
  data Nf {n : ℕ} : Ty → Set where
    NLab : {s : Subset n} → Nf (Label s)
    NPi : {A B : Ty {n}} → Nf (Pi A B)
    NSigma : {A B : Ty {n}} → Nf (Sigma A B)
   
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
-}

-- operational semantics (call-by-value)
module operational where
  open defs


  -- reduction relation
  data _⇒_ {n : ℕ} : Exp {n} → Exp {n} → Set where
    ξ-App1 : {e₁ e₁' e₂ : Exp} → e₁ ⇒ e₁' → App e₁ e₂ ⇒ App e₁' e₂
    ξ-App2 : {e e' v : Exp} → Val v → e ⇒ e' → App v e ⇒ App v e'
    ξ-FakeLet : {e₁ e₁' e₂ : Exp} → e₁ ⇒ e₁' → FakeLet e₁ e₂ ⇒ FakeLet e₁' e₂
    β-App : {e v : Exp} → Val v → (App (Abs e) v) ⇒ (↑⁻¹[ ([ 0 ↦ ↑¹[ v ] ] e) ])
    β-FakeLet : {e e' e'' : Exp} → FakeLet (Prod e e') e'' ⇒ ↑ (ℤ.negsuc 1) , 0 [ ([ 0 ↦ ↑ (ℤ.pos 1) , 0 [ e ] ] ([ 0 ↦ ↑ (ℤ.pos 1) , 1 [ e' ] ] e'')) ]
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
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {n} {Prod e e'} = cong₂ Prod ↑⁻¹ₖ[↑¹ₖ[s]]≡s ↑⁻¹ₖ[↑¹ₖ[s]]≡s
  ↑⁻¹ₖ[↑¹ₖ[s]]≡s {n} {FakeLet e e'} = cong₂ FakeLet ↑⁻¹ₖ[↑¹ₖ[s]]≡s ↑⁻¹ₖ[↑¹ₖ[s]]≡s

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
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {Prod e e'} le = cong₂ Prod (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] le) (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] le)
  ↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] {n} {k} {l} {c} {FakeLet e e'} le = cong₂ FakeLet (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] le) (↑ᵏ[↑ˡ[s]]≡↑ᵏ⁺ˡ[s] le)
  

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
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {Prod e e'} ge₁ ge₂ = cong₂ Prod (↑k,q[↑l,c[s]]≡↑l+k,c[s] ge₁ ge₂) (↑k,q[↑l,c[s]]≡↑l+k,c[s] ((+q≤+c+l⇒+1q≤+1c+l{q}{c}{l} ge₁)) (s≤s ge₂))
  ↑k,q[↑l,c[s]]≡↑l+k,c[s] {n} {k} {l} {q} {c} {FakeLet e e'} ge₁ ge₂ = cong₂ FakeLet (↑k,q[↑l,c[s]]≡↑l+k,c[s] ge₁ ge₂)
                                                                                     (↑k,q[↑l,c[s]]≡↑l+k,c[s] ((+q≤+c+l⇒+1q≤+1c+l{ℕ.suc q}{ℕ.suc c}{l} (+q≤+c+l⇒+1q≤+1c+l{q}{c}{l} ge₁))) (s≤s (s≤s ge₂)))

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
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {Prod e e'} le le' = cong₂ Prod (↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] le le') (↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] (s≤s le) le')
  ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] {n} {k} {q} {c} {l} {FakeLet e e'} le le' = cong₂ FakeLet (↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] le le') (↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]] (s≤s (s≤s le)) le')

  -- corollaries
  ↑k,sucq[↑1,c[s]]≡↑1,c[↑k,q[s]] : {n : ℕ} {k : ℤ} {q c : ℕ} {s : Exp {n}} → c ≤ᴺ q → + 0 <ᶻ k →  ↑ k , ℕ.suc q [ ↑ + 1 , c [ s ] ] ≡ ↑ + 1 , c [ ↑ k , q [ s ] ]
  ↑k,sucq[↑1,c[s]]≡↑1,c[↑k,q[s]] {n} {k} {q} {c} {s} le le'
    rewrite (sym (n+1≡sucn{q}))
          = ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]]{n}{k}{q}{c}{1}{s} le le'

  ↑k,sucsucq[↑2,c[s]]≡↑2,c[↑k,q[s]] : {n : ℕ} {k : ℤ} {q c : ℕ} {s : Exp {n}} → c ≤ᴺ q → + 0 <ᶻ k →  ↑ k , ℕ.suc (ℕ.suc q) [ ↑ + 2 , c [ s ] ] ≡ ↑ + 2 , c [ ↑ k , q [ s ] ]
  ↑k,sucsucq[↑2,c[s]]≡↑2,c[↑k,q[s]] {n} {k} {q} {c} {s} le le'
    rewrite (sym (n+2≡sucsucn{q}))
          = ↑k,q+l[↑l,c[s]]≡↑l,c[↑k,q[s]]{n}{k}{q}{c}{2}{s} le le' 
    

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
  ↑⁰-refl {n} {c} {Prod e e'} = cong₂ Prod ↑⁰-refl ↑⁰-refl
  ↑⁰-refl {n} {c} {FakeLet e e'} = cong₂ FakeLet ↑⁰-refl ↑⁰-refl

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
  notin-shift {N} {n} {k} {q} {Prod e e'} geq j (in-Prod (inj₁ x)) = notin-shift geq (λ x₁ → contradiction (in-Prod (inj₁ x₁)) j) x
  notin-shift {N} {n} {k} {q} {Prod e e'} geq j (in-Prod (inj₂ y)) = notin-shift (s≤s geq) (λ x → contradiction (in-Prod (inj₂ x)) j) y
  notin-shift {N} {n} {k} {q} {FakeLet e e'} geq j (in-FakeLet (inj₁ x)) = notin-shift geq (λ x₁ → contradiction (in-FakeLet (inj₁ x₁)) j) x
  notin-shift {N} {n} {k} {q} {FakeLet e e'} geq j (in-FakeLet (inj₂ y)) = notin-shift (s≤s (s≤s geq)) (λ x → contradiction (in-FakeLet (inj₂ x)) j) y


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
  subst-refl-notin {N} {n} {Prod e e'} {e''} nin = cong₂ Prod (subst-refl-notin (λ x → contradiction (in-Prod (inj₁ x)) nin)) (subst-refl-notin (λ x → contradiction (in-Prod (inj₂ x)) nin))
  subst-refl-notin {N} {n} {FakeLet e e'} {e''} nin = cong₂ FakeLet (subst-refl-notin (λ x → contradiction (in-FakeLet (inj₁ x)) nin)) (subst-refl-notin (λ x → contradiction (in-FakeLet (inj₂ x)) nin))

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
  --   notin-shift : {N n k q : ℕ} {e : Exp {N}} → n ≥ᴺ q → ¬ n ∈` e → ¬ ((n +ᴺ k) ∈` ↑ + k , q [ e ])
  notin-subst {N} {n} {Prod e e'} {e''} nin (in-Prod (inj₁ x)) = notin-subst{e = e} nin x
  notin-subst {N} {n} {Prod e e'} {e''} nin (in-Prod (inj₂ y))
    with notin-shift{k = 1} z≤n nin
  ...  | w rewrite (n+1≡sucn{n}) =  notin-subst {n = ℕ.suc n}{e = e'}{e' = ↑¹[ e'' ]} w y 
  notin-subst {N} {n} {FakeLet e e'} {e''} nin (in-FakeLet (inj₁ x)) = notin-subst{e = e} nin x
  notin-subst {N} {n} {FakeLet e e'} {e''} nin (in-FakeLet (inj₂ y))
    with notin-shift{k = 2} z≤n nin
  ...  | w rewrite (n+2≡sucsucn{n}) = notin-subst {n = ℕ.suc (ℕ.suc n)} {e = e'} {e' = ↑ + 2 , 0 [ e'' ]} w y

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
  subst-in-neq {N} {n} {m} {Prod e e'} {s} nin (in-Prod (inj₁ x)) = subst-in-neq{e = e} nin x
  subst-in-neq {N} {n} {m} {Prod e e'} {s} nin (in-Prod (inj₂ y)) = sucn≢sucm⇒n≢m (subst-in-neq{e = e'} (notin-shift-one nin) y) 
  subst-in-neq {N} {n} {m} {FakeLet e e'} {s} nin (in-FakeLet (inj₁ x)) = subst-in-neq{e = e} nin x
  subst-in-neq {N} {n} {m} {FakeLet e e'} {s} nin (in-FakeLet (inj₂ y))
    with notin-shift{k = 2} z≤n nin
  ...  | w rewrite (n+2≡sucsucn{n}) = sucn≢sucm⇒n≢m (sucn≢sucm⇒n≢m (subst-in-neq{e = e'} w y))

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
  subst-in {N} {n} {m} {Prod e e'} {e''} neq (in-Prod (inj₁ x)) = in-Prod (inj₁ (subst-in neq x))
  subst-in {N} {n} {m} {Prod e e'} {e''} neq (in-Prod (inj₂ y)) = in-Prod (inj₂ (subst-in (n≢m⇒sucn≢sucm neq) y))
  subst-in {N} {n} {m} {FakeLet e e'} {e''} neq (in-FakeLet (inj₁ x)) = in-FakeLet (inj₁ (subst-in neq x))
  subst-in {N} {n} {m} {FakeLet e e'} {e''} neq (in-FakeLet (inj₂ y)) = in-FakeLet (inj₂ (subst-in (n≢m⇒sucn≢sucm (n≢m⇒sucn≢sucm neq)) y))

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
  subst-in-reverse {N} {n} {m} {Prod e e'} {e''} neq nin (in-Prod (inj₁ x)) = in-Prod (inj₁ (subst-in-reverse neq nin x))
  subst-in-reverse {N} {n} {m} {Prod e e'} {e''} neq nin (in-Prod (inj₂ y)) = in-Prod (inj₂ (subst-in-reverse (n≢m⇒sucn≢sucm neq) (notin-shift-one{e = e''} nin) y))
  subst-in-reverse {N} {n} {m} {FakeLet e e'} {e''} neq nin (in-FakeLet (inj₁ x)) = in-FakeLet (inj₁ (subst-in-reverse neq nin x))
  subst-in-reverse {N} {n} {m} {FakeLet e e'} {e''} neq nin (in-FakeLet (inj₂ y))
    with notin-shift{k = 2} z≤n nin
  ...  | w rewrite (n+2≡sucsucn{n}) = in-FakeLet (inj₂ (subst-in-reverse (n≢m⇒sucn≢sucm (n≢m⇒sucn≢sucm neq)) w y))

  var-env-< : {N : ℕ} {Γ : TEnv {N}} {T : Ty} {n : ℕ} (j : n ∶ T ∈ Γ) → n <ᴺ (length Γ)
  var-env-< {N} {.(⟨ T , _ ⟩)} {T} {.0} here = s≤s z≤n
  var-env-< {N} {.(⟨ _ , _ ⟩)} {T} {.(ℕ.suc _)} (there j) = s≤s (var-env-< j)

  -- variables contained in a term are < length of env.
  free-vars-env-< : {N : ℕ} {e : Exp {N}} {Γ : TEnv {N}} {T : Ty {N}} → Γ ⊢ e ∶ T → (∀ n → n ∈` e → n <ᴺ length Γ)
  free-vars-env-< {N} {Var x₁} {Γ} {T} (TConv j x) .x₁ in-Var = free-vars-env-< j x₁ in-Var
  free-vars-env-< {N} {Var x₁} {Γ} {T} (TVarE x eq) .x₁ in-Var = var-env-< x
  free-vars-env-< {N} {Abs e} {Γ} {T} (TConv j x₁) n x = free-vars-env-< j n x
  free-vars-env-< {N} {Abs e} {Γ} {.(Pi _ _)} (TPiI j) n (in-Abs x) = ≤-pred (free-vars-env-< j (ℕ.suc n) x)
  free-vars-env-< {N} {App e e₁} {Γ} {T} (TConv j x₁) n x = free-vars-env-< j n x
  free-vars-env-< {N} {App e e₁} {Γ} {.([ 0 ↦ e₁ ]ᵀ _)} (TPiE j j₁ x₁) n (in-App (inj₁ x)) = free-vars-env-< j n x
  free-vars-env-< {N} {App e e₁} {Γ} {.([ 0 ↦ e₁ ]ᵀ _)} (TPiE j j₁ x₁) n (in-App (inj₂ y)) = free-vars-env-< j₁ n y
  free-vars-env-< {N} {LabE f e} {Γ} {T} (TConv j x₁) n x = free-vars-env-< j n x
  free-vars-env-< {N} {LabE f .(LabI _)} {Γ} {T} (TLabEl{scopecheck = s} j j₁) n (in-LabE (inj₁ (fst , fst₁ , snd))) = s fst fst₁ n snd
  free-vars-env-< {N} {LabE f (Var m)} {Γ} {T} (TLabEx f' j) n x
    with n ≟ᴺ m
  ...  | yes p rewrite p = free-vars-env-< j m in-Var
  free-vars-env-< {N} {LabE f (Var m)} {Γ} {T} (TLabEx f' j) n (in-LabE (inj₁ (fst , fst₁ , snd))) | no ¬p = free-vars-env-< (f' fst fst₁) n (subst-in ¬p snd)
  free-vars-env-< {N} {LabE f (Var m)} {Γ} {T} (TLabEx f' j) n (in-LabE (inj₂ y)) | no ¬p = contradiction (inv-in-var y) ¬p
  free-vars-env-< {N} {Prod e e₁} {Γ} {T} (TConv j x₁) n x = free-vars-env-< j n x
  free-vars-env-< {N} {Prod e e₁} {Γ} {.(Sigma _ _)} (TSigmaI j j₁) n (in-Prod (inj₁ x)) = free-vars-env-< j n x
  free-vars-env-< {N} {Prod e e₁} {Γ} {.(Sigma _ _)} (TSigmaI j j₁) n (in-Prod (inj₂ y)) = ≤-pred (free-vars-env-< j₁ (ℕ.suc n) y)
  free-vars-env-< {N} {FakeLet e e₁} {Γ} {T} (TConv j x₁) n x = free-vars-env-< j n x
  free-vars-env-< {N} {FakeLet e e₁} {Γ} {T} (TSigmaE j j₁) n (in-FakeLet (inj₁ x)) = free-vars-env-< j n x
  free-vars-env-< {N} {FakeLet e e₁} {Γ} {T} (TSigmaE j j₁) n (in-FakeLet (inj₂ y)) = ≤-pred (≤-pred (free-vars-env-< j₁ (ℕ.suc (ℕ.suc n)) y))

  -- closed expressions have no free variables
  closed-free-vars : {N : ℕ} {e : Exp {N}} {T : Ty {N}} → [] ⊢ e ∶ T → (∀ n → ¬ (n ∈` e))
  closed-free-vars {N} {Var x} {T} j n z = contradiction (free-vars-env-< j n z) (λ ())
  closed-free-vars {N} {Abs e} {T} (TConv j x) n = closed-free-vars j n
  closed-free-vars {N} {Abs e} {.(Pi _ _)} (TPiI j) n (in-Abs x) = contradiction ((free-vars-env-< j (ℕ.suc n) x)) (≤⇒≯ (s≤s z≤n))
  closed-free-vars {N} {LabI x} {T} (TConv j x₁) n = closed-free-vars j n
  closed-free-vars {N} {LabI x} {.(Label _)} (TLabI ins) n = λ ()
  closed-free-vars {N} {Prod e e₁} {T} (TConv j x) n = closed-free-vars j n
  closed-free-vars {N} {Prod e e₁} {.(Sigma _ _)} (TSigmaI j j₁) n (in-Prod (inj₁ x)) = closed-free-vars j n x
  closed-free-vars {N} {Prod e e₁} {.(Sigma _ _)} (TSigmaI j j₁) n (in-Prod (inj₂ y)) = contradiction (free-vars-env-< j₁ (ℕ.suc n) y) (≤⇒≯ (s≤s z≤n))
  closed-free-vars {N} {FakeLet e e₁} {T} (TConv j x) n = closed-free-vars j n
  closed-free-vars {N} {FakeLet e e₁} {T} (TSigmaE j j₁) n (in-FakeLet (inj₁ x)) = closed-free-vars j n x
  closed-free-vars {N} {FakeLet e e₁} {T} (TSigmaE j j₁) n (in-FakeLet (inj₂ y)) = contradiction (free-vars-env-< j₁ (ℕ.suc (ℕ.suc n)) y) (≤⇒≯ (s≤s (s≤s z≤n)))
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
  shift-env-size {n} {k} {q} {Prod e e'} lmap = cong₂ Prod (shift-env-size (extr lmap)) (shift-env-size (extr' lmap))
    where extr : (∀ n → n ∈` Prod e e' → n <ᴺ q) → (∀ n → n ∈` e → n <ᴺ q)
          extr lmap n ins = lmap n (in-Prod (inj₁ ins))
          extr' : (∀ n → n ∈` Prod e e' → n <ᴺ q) → (∀ n → n ∈` e' → n <ᴺ ℕ.suc q)
          extr' lmap zero ins = s≤s z≤n
          extr' lmap (ℕ.suc n) ins = s≤s (lmap n (in-Prod (inj₂ ins)))
  shift-env-size {n} {k} {q} {FakeLet e e'} lmap = cong₂ FakeLet (shift-env-size (extr lmap)) (shift-env-size (extr' lmap))
    where extr : (∀ n → n ∈` FakeLet e e' → n <ᴺ q) → (∀ n → n ∈` e → n <ᴺ q)
          extr lmap n ins = lmap n (in-FakeLet (inj₁ ins))
          extr' : (∀ n → n ∈` FakeLet e e' → n <ᴺ q) → (∀ n → n ∈` e' → n <ᴺ ℕ.suc (ℕ.suc q))
          extr' lmap zero ins = s≤s z≤n
          extr' lmap (ℕ.suc zero) ins = s≤s (s≤s z≤n)
          extr' lmap (ℕ.suc (ℕ.suc n)) ins = s≤s (s≤s (lmap n (in-FakeLet (inj₂ ins))))
 
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
  subst-change-in {N} {n} {m} {Prod e e'} {s} {s'} p (in-Prod (inj₁ x)) = in-Prod (inj₁ (subst-change-in{m = m}{e} p x))
  subst-change-in {N} {n} {m} {Prod e e'} {s} {s'} (fst , snd) (in-Prod (inj₂ y)) = in-Prod (inj₂ (subst-change-in {N} {ℕ.suc n} {ℕ.suc m} {e'}
                                                                                                    (notin-shift-one{N}{n}{s} fst , notin-shift-one {N} {n} {s'} snd) y))
  subst-change-in {N} {n} {m} {FakeLet e e'} {s} {s'} p (in-FakeLet (inj₁ x)) = in-FakeLet (inj₁ (subst-change-in {N} {n} {m} {e} p x))
  subst-change-in {N} {n} {m} {FakeLet e e'} {s} {s'} (fst , snd) (in-FakeLet (inj₂ y))
    with notin-shift{k = 2} z≤n fst |  notin-shift{k = 2} z≤n snd
  ...  | w | w' rewrite (n+2≡sucsucn{n}) = in-FakeLet (inj₂ (subst-change-in {N} {ℕ.suc (ℕ.suc n)} {ℕ.suc (ℕ.suc m)} {e'} (w , w') y))

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
  subst-subst-swap {N} {n} {m} {e} {e'} {Prod s s'} neq nin nin'
    with (notin-shift-one nin) | (notin-shift-one nin')
  ...  | w | w' = cong₂ Prod (subst-subst-swap{s = s} neq nin nin') (subst-subst-swap{s = s'} (n≢m⇒sucn≢sucm neq) w w')
  subst-subst-swap {N} {n} {m} {e} {e'} {FakeLet s s'} neq nin nin'
    with notin-shift{k = 2} z≤n nin |  notin-shift{k = 2} z≤n nin'
  ...  | w | w' rewrite (n+2≡sucsucn{n}) | (n+2≡sucsucn{m}) = cong₂ FakeLet (subst-subst-swap{s = s} neq nin nin') (subst-subst-swap{s = s'} (n≢m⇒sucn≢sucm (n≢m⇒sucn≢sucm neq)) w w')

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
  subst-shift-swap {n} {k} {x} {q} {Prod s s'} {e} gt
    with (subst-shift-swap{n}{k}{ℕ.suc x}{ℕ.suc q}{s'}{↑¹[ e ]} gt)
  ...  | w
       rewrite (↑k,sucq[↑1,c[s]]≡↑1,c[↑k,q[s]] {n} {k} {q} {0} {e} z≤n gt)
             | (suc[↑ᴺk,l[x]]≡↑ᴺk,sucl[sucx] {k} {q} {x} gt)
             = cong₂ Prod (subst-shift-swap {n} {k} {x} {q} {s} {e} gt) w
  subst-shift-swap {n} {k} {x} {q} {FakeLet s s'} {e} gt
    with (subst-shift-swap{n}{k}{ℕ.suc (ℕ.suc x)}{ℕ.suc (ℕ.suc q)}{s'}{↑ + 2 , 0 [ e ]} gt)
  ...  | w
       rewrite (↑k,sucsucq[↑2,c[s]]≡↑2,c[↑k,q[s]] {n} {k} {q} {0} {e} z≤n gt)
             | sym (suc[↑ᴺk,l[x]]≡↑ᴺk,sucl[sucx] {k} {(ℕ.suc q)} {(ℕ.suc x)} gt )
             | sym (suc[↑ᴺk,l[x]]≡↑ᴺk,sucl[sucx] {k} {q} {x} gt )
               = cong₂ FakeLet (subst-shift-swap {n} {k} {x} {q} {s} {e} gt) w


  --- typing: canonical forms, inequalities
  case-redex-eq : {n : ℕ} {s : Subset n} {f : (l : Fin n) → l ∈ s → Ty} {e : Exp} {T T' : Ty} → (([] ⊢ Case f e ≡ᵀ T) × ([] ⊢ Case f e ≡ᵀ T')) → [] ⊢ T ≡ᵀ T'
  case-redex-eq {n} {s} {f} {e} {T} {T'} (fst , snd) = CTrans (CSym fst) snd
 
  type-lab : {n : ℕ} {T : Ty {n}} {x : Fin n} → [] ⊢ LabI x ∶ T → ∃[ s ]( [] ⊢ T ≡ᵀ Label s × x ∈ s )
  type-lab {n} {Label x₁} {x} (TLabI ins) = x₁ , (CRefl{ok = TLabF}) , ins
  type-lab {n} {e} {x} (TConv j y)
    with type-lab j
  ...  | fst , snd , snd' = fst , CTrans (CSym y) snd , snd'

  type-prod : {n : ℕ} {T : Ty {n}} {e e' : Exp} → [] ⊢ Prod e e' ∶ T → ∃[ A ](∃[ B ]( [] ⊢ T ≡ᵀ Sigma A B ))
  type-prod {n} {T} {x} (TSigmaI{A = A}{B = B}{ok = ok}{ok' = ok'} y y') = A , (B , (CRefl{ok = TSigmaF ok ok'}))
  type-prod {n} {T} {x} (TConv j y)
    with type-prod j
  ...  | fst , fst₁ , snd = fst , (fst₁ , (CTrans (CSym y) snd))

  type-abs : {n : ℕ} {T : Ty {n}} {e : Exp} → [] ⊢ Abs e ∶ T → ∃[ A ](∃[ B ]( [] ⊢ T ≡ᵀ Pi A B))
  type-abs {n} {.(Pi _ _)} {e} (TPiI{A = A}{B = B}{ok = ok}{ok' = ok'} j) = A , (B , (CRefl{ok = TPiF ok ok'}))
  type-abs {n} {T} {e} (TConv j x)
    with type-abs j
  ...  | fst , fst₁ , snd = fst , fst₁ , CTrans (CSym x) snd

 
  canonical-forms-pi : {n : ℕ} {A B : Ty {n}} {e : Exp {n}} → [] ⊢ e ∶ Pi A B → Val e → ∃[ e' ]( e ≡ Abs e' )
  canonical-forms-pi {n} {A} {B} {Var x} j VVar = contradiction (in-Var) (closed-free-vars j x)
  canonical-forms-pi {n} {A} {B} {Abs e} j v = e , refl
  canonical-forms-pi {n} {A} {B} {LabI x} (TConv {T = Label x₂} j x₁) v = contradiction x₁ (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-pi {n} {A} {B} {LabI x} (TConv {T = Pi T T₁} j x₁) v = (proj₁ (canonical-forms-pi j v)) , (≡-trans refl (proj₂ (canonical-forms-pi j v)))
  canonical-forms-pi {n} {A} {B} {LabI x} (TConv {T = Sigma T T₁} j x₁) v = contradiction x₁ (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-pi {n} {A} {B} {LabI x} (TConv {T = Case f x₂} j x₁) v = contradiction (case-redex-eq (proj₁ (proj₂ (type-lab j)) , x₁)) (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-pi {n} {A} {B} {Prod e e'} (TConv {T = Label x₁} j x) v = contradiction x (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-pi {n} {A} {B} {Prod e e'} (TConv {T = Pi T' T''} j x) v = (proj₁ (canonical-forms-pi j v)) , (≡-trans refl (proj₂ (canonical-forms-pi j v)))
  canonical-forms-pi {n} {A} {B} {Prod e e'} (TConv {T = Sigma T' T''} j x) v = contradiction x (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-pi {n} {A} {B} {Prod e e'} (TConv {T = Case f x₁} j x) v = contradiction (case-redex-eq (proj₂ (proj₂ (type-prod j)) , x)) (≢ᵀ'⇒≢ᵀ (λ ()))

  canonical-forms-sigma : {n : ℕ} {A B : Ty {n}} {e : Exp {n}} → [] ⊢ e ∶ Sigma A B → Val e → ∃[ e₁ ]( ∃[ e₂ ] ( e ≡ Prod e₁ e₂ ))
  canonical-forms-sigma {n} {A} {B} {Var x} j VVar = contradiction (in-Var) (closed-free-vars j x)
  canonical-forms-sigma {n} {A} {B} {Abs e} (TConv {T = Label x₁} j x) v = contradiction x (≢ᵀ'⇒≢ᵀ (λ ())) 
  canonical-forms-sigma {n} {A} {B} {Abs e} (TConv {T = Pi T T₁} j x) v = contradiction x (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-sigma {n} {A} {B} {Abs e} (TConv {T = Sigma T T₁} j x) v = (proj₁ (canonical-forms-sigma j v)) , (proj₂ (canonical-forms-sigma j v))
  canonical-forms-sigma {n} {A} {B} {Abs e} (TConv {T = Case f x₁} j x) v = contradiction (case-redex-eq (proj₂ (proj₂ (type-abs j)) , x)) (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-sigma {n} {A} {B} {LabI x} (TConv {T = Label x₁} j y) v = contradiction y (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-sigma {n} {A} {B} {LabI x} (TConv {T = Pi T T₁} j y) v = contradiction y (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-sigma {n} {A} {B} {LabI x} (TConv {T = Sigma T T₁} j y) v = (proj₁ (canonical-forms-sigma j v)) , (proj₂ (canonical-forms-sigma j v))
  canonical-forms-sigma {n} {A} {B} {LabI x} (TConv {T = Case f x₁} j y) v = contradiction (case-redex-eq (proj₁ (proj₂ (type-lab j)) , y)) (≢ᵀ'⇒≢ᵀ (λ ()))
  canonical-forms-sigma {n} {A} {B} {Prod e e₁} j v = e , e₁ , refl

  ---- progress and preservation

  -- progress theorem, i.e. a well-typed closed expression is either a value
  -- or can be reduced further
  data Progress {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ∶ T} : Set where
    step : {e' : Exp{n}} → e ⇒ e' → Progress e
    value : Val e → Progress e

  progress : {n : ℕ} (e : Exp {n}) {T : Ty} {j : [] ⊢ e ∶ T} → Progress e {T} {j}
  progress {n} e {T} {TConv{T = T'}{T' = .T} j x}
    with progress e {j = j}
  ... | step {e' = e'} x₁ = step x₁
  ... | value x₁ = value x₁
  progress {n} .(Abs _) {.(Pi _ _)} {TPiI j} = value VFun
  progress {n} .(App e e') {T} {TPiE{e = e} {e' = e'} j j₁ x}
    with progress e {j = j}
  ... | step x₁ = step (ξ-App1 x₁)
  ... | value x₁
      with progress e' {j = j₁}
  ...    | step x₂ = step (ξ-App2 x₁ x₂)
  ...    | value x₂
         with canonical-forms-pi j x₁
  ...       | fst , snd rewrite snd = step (β-App x₂)
  progress {n} .(Prod _ _) {.(Sigma _ _)} {TSigmaI j j₁} = value VProd
  progress {n} .(FakeLet _ _) {T} {TSigmaE{e = e} {e' = e'} j j₁}
    with progress e {j = j}
  ...  | step x = step (ξ-FakeLet x)
  ...  | value x
       with canonical-forms-sigma j x
  ...     | fst , snd , snd₁ rewrite snd₁ = step β-FakeLet
  progress {n} .(LabI _) {.(Label _)} {TLabI ins} = value VLab
  progress {n} .(LabE _ (LabI _)) {T} {TLabEl{ins = ins} j j₁} = step (β-LabE ins)
  progress {n} (LabE f (Var m)) {T} {TLabEx f' j} = contradiction (free-vars-env-< j m in-Var) λ ()


{-

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
  --- properties and manipulation of environments
  {-
  _++_ : {n : ℕ} → TEnv {n} → TEnv {n} → TEnv {n}
  type-ok-env-ext : {n : ℕ} {Δ Γ : TEnv {n}} {T : Ty {n}} → Δ ⊢ T → (Δ ++ Γ) ⊢ T
  type-conv-env-ext : {n : ℕ} {Δ Γ : TEnv {n}} {T T' : Ty {n}} → Δ ⊢ T ≡ᵀ T' → (Δ ++ Γ) ⊢ T ≡ᵀ T'
  ext-behind : {n : ℕ} {Δ Γ : TEnv {n}} {T : Ty {n}} {e : Exp {n}} → Δ ⊢ e ∶ T → (Δ ++ Γ) ⊢ e ∶ T
  var-ext-behind : {n : ℕ} {Δ Γ : TEnv {n}} {T : Ty} {x : ℕ} → x ∶ T ∈ Δ → x ∶ T ∈ (Δ ++ Γ)

  [] ++ Γ = Γ
  ⟨ T , Δ ⟩ {ok} ++ Γ = ⟨ T , (Δ ++ Γ) ⟩ {{!!}} -- {type-ok-env-ext ok}

  env-tail-< : {n m : ℕ} {Δ Γ : TEnv {n}} → m <ᴺ length Δ → env-tail (Δ ++ Γ) m ≡ᵀ (env-tail Δ m ++ Γ)
  env-tail-< {n} {m} {Δ} {Γ} leq = {!!}
  {-
  env-tail-< {n} {zero} {⟨ T , Δ ⟩} {Γ} leq = refl
  env-tail-< {n} {ℕ.suc m} {⟨ T , Δ ⟩} {Γ} (s≤s leq) = env-tail-< leq 
  -}

  var-ext-behind {n} {⟨ T , Δ ⟩} {Γ} {.T} (here {ok = ok}) = here {ok = type-ok-env-ext ok}
  var-ext-behind {n} {⟨ T' , Δ ⟩} {Γ} {T} (there {ok = ok} j) =  there {ok = type-ok-env-ext ok} (var-ext-behind j) 

  var-ext-front : {n m : ℕ} {Γ : TEnv {n}} {T T' : Ty {n}} {ok : Γ ⊢ T'} → Γ ⊢ Var m ∶ T → (⟨ T' , Γ ⟩{ok}) ⊢ Var (ℕ.suc m) ∶ T
  var-ext-front {n} {m} {Γ} {T} {T'} {ok} (TConv j x) = {!!}
  {-
    with var-ext-front j
  ... | TConv w x₁ = {!TConv w x₁!}
  ... | TVarE x₁ x₂ = {!!}
  -}
  var-ext-front {n} {.0} {.(⟨ _ , _ ⟩)} {T} {T'} {ok} (TVarE here x₁) = TVarE (there (here)) x₁
  var-ext-front {n} {.(ℕ.suc _)} {.(⟨ _ , _ ⟩)} {T} {T'} {ok} (TVarE (there x) x₁) = TVarE (there (there x)) x₁

  type-ok-env-ext {n} {Δ} {Γ} {.(Label _)} TLabF = TLabF
  type-ok-env-ext {n} {Δ} {Γ} {.(Pi _ _)} (TPiF j j₁) = TPiF (type-ok-env-ext j) (type-ok-env-ext j₁)
  type-ok-env-ext {n} {Δ} {Γ} {.(Sigma _ _)} (TSigmaF j j₁) = TSigmaF (type-ok-env-ext j) (type-ok-env-ext j₁)
  type-ok-env-ext {n} {Δ} {Γ} {.(Case _ _)} (TCaseF f' v x) = TCaseF (λ l i → type-ok-env-ext (f' l i)) v (ext-behind x)

  type-conv-env-ext {n} {Δ} {Γ} {T} {.T} (CRefl{ok = ok}) = CRefl{ok = type-ok-env-ext ok}
  type-conv-env-ext {n} {Δ} {Γ} {T} {T'} (CSym j) = CSym (type-conv-env-ext j)
  type-conv-env-ext {n} {Δ} {Γ} {T} {T'} (CTrans j j₁) = CTrans (type-conv-env-ext j) (type-conv-env-ext j₁)
  type-conv-env-ext {n} {Δ} {Γ} {T} {.(Case (λ l i → T) (LabI _))} (CLabEta{ins = ins} x x₁) = CLabEta{ins = ins} (ext-behind{n}{Δ}{Γ} x) (type-ok-env-ext x₁)
  type-conv-env-ext {n} {Δ} {Γ} {.(Case _ (LabI _))} {.(f y ins)} (CLabBeta{x = y}{f = f} x ins) = CLabBeta (type-ok-env-ext{n}{Δ}{Γ} x) ins
  type-conv-env-ext {n} {Δ} {Γ} {(Pi A B)} {.(Pi _ _)} (CPi{ok = ok} j j₁) = CPi{ok = type-ok-env-ext ok} (type-conv-env-ext j) (type-conv-env-ext{n}{⟨ A , Δ ⟩}{Γ} j₁)
  type-conv-env-ext {n} {Δ} {Γ} {(Sigma A B)} {.(Sigma _ _)} (CSigma{ok = ok} j j₁) = CSigma{ok = type-ok-env-ext ok} (type-conv-env-ext j) (type-conv-env-ext{n}{⟨ A , Δ ⟩}{Γ} j₁)
  type-conv-env-ext {n} {Δ} {Γ} {.(Case _ _)} {.(Case _ _)} (CLab v x) = CLab (type-ok-env-ext v) (λ l i → type-conv-env-ext (x l i))

  length[A++B]≡length[A]+length[B] : {n : ℕ} {A B : TEnv {n}} → length (A ++ B) ≡ length A +ᴺ length B
  length[A++B]≡length[A]+length[B] {n} {[]} {B} = refl
  length[A++B]≡length[A]+length[B] {n} {⟨ T , A ⟩} {B} = cong ℕ.suc (length[A++B]≡length[A]+length[B]{A = A}{B = B})
  {-
    Goal: env-tail (Δ ++ Γ) m ⊢ T ≡ᵀ T₁
    Have: (env-tail Δ m ++ _Γ_6761) ⊢ T ≡ᵀ T₁
  -}
  
  ext-behind {n} {Δ} {Γ} {T} {e} (TConv j x) = TConv (ext-behind{n}{Δ}{Γ} j) (type-conv-env-ext x)
  ext-behind {n} {Δ} {Γ} {T} {Var m} (TVarE {m = m} j eq) = TVarE (var-ext-behind j) (⊢≡ᵀ-envsub ((type-conv-env-ext{Δ = env-tail Δ m}{Γ = Γ} eq)) {!!})
  {-
  ext-behind {n} {⟨ T₁ , Δ ⟩} {Γ} {T} {.(Var 0)} (TVarE {m = zero} here eq) = TVarE here (type-conv-env-ext eq)
  ext-behind {n} {⟨ T₁ , Δ ⟩} {Γ} {T} {.(Var (ℕ.suc m))} (TVarE {m = ℕ.suc m} (there x) eq)
    with (type-conv-env-ext{Γ = Γ} eq) | (var-env-< x)
  ...  | w | w' = TVarE (there (var-ext-behind x)) (type-conv-env-ext (⊢≡ᵀ-envsub w (env-tail-< {!w'!})))
  -}
  {-
    with ext-behind {n} {Δ} {Γ} {T} {Var m} (TVarE {m = m} x eq)
  ... | w  = {!!} 
  -}
  {-
    with (type-conv-env-ext{Γ = Γ} eq) | (var-env-< x)
  ...  | w | w' rewrite (env-tail-<{n}{m}{Δ}{Γ} w')
           = TVarE (var-ext-behind x) {!!} -- rewrite (env-tail-<{n}{m}{Δ}{Γ} ) rewrite  = TVarE (var-ext-behind x) {!type-conv-env-ext eq!} -- TVarE (var-ext-behind x)
  -}
  ext-behind {n} {Δ} {Γ} {.(Pi _ _)} {.(Abs _)} (TPiI{ok = ok} j) = TPiI{ok = type-ok-env-ext ok} (ext-behind j)
  ext-behind {n} {Δ} {Γ} {.([ 0 ↦ _ ]ᵀ _)} {.(App _ _)} (TPiE j j₁ x) = TPiE (ext-behind j) (ext-behind j₁) (type-ok-env-ext x)
  ext-behind {n} {Δ} {Γ} {.(Sigma _ _)} {.(Prod _ _)} (TSigmaI{ok = ok} j j₁) = TSigmaI{ok = type-ok-env-ext ok} (ext-behind j) (ext-behind j₁)
  ext-behind {n} {Δ} {Γ} {T} {.(FakeLet _ _)} (TSigmaE{ok = ok}{ok' = ok'} j j₁) = TSigmaE{ok = type-ok-env-ext ok}{ok' = type-ok-env-ext ok'} (ext-behind j) (ext-behind j₁)
  ext-behind {n} {Δ} {Γ} {.(Label _)} {.(LabI _)} (TLabI ins) = TLabI ins
  ext-behind {n} {Δ} {Γ} {T} {.(LabE _ (LabI _))} (TLabEl{s = s}{f = f}{scopecheck = sc} j j₁) = TLabEl{scopecheck = sc'} (ext-behind j) (ext-behind j₁)
    where sc' : (l : Fin n) (i : l ∈ s) (m : ℕ) → m ∈` f l i → m <ᴺ length (Δ ++ Γ)
          sc' l i m ins
            with sc l i m ins
          ...  | w rewrite (length[A++B]≡length[A]+length[B]{n}{Δ}{Γ}) = a<b≤c⇒a<c w (m≤m+n (length Δ) (length Γ))
  ext-behind {n} {Δ} {Γ} {T} {.(LabE _ (Var _))} (TLabEx f' j) = TLabEx (λ l i → ext-behind (f' l i)) (ext-behind j)

  -}


  {-
  conv-nf : {n : ℕ} {e : Exp {n}} {T : Ty} → [] ⊢ e ∶ T → ∃[ T' ]( (Nf T') × ([] ⊢ T ≡ᵀ T'))
  conv-nf {n} {e} {T} (TConv j x) = {!!}
  conv-nf {n} {.(Abs _)} {.(Pi _ _)} (TPiI j) = {!!}
  conv-nf {n} {.(App _ _)} {.([ 0 ↦ _ ]ᵀ _)} (TPiE j j₁ x) = {!!}
  conv-nf {n} {.(Prod _ _)} {.(Sigma _ _)} (TSigmaI j j₁) = {!!}
  conv-nf {n} {.(FakeLet _ _)} {T} (TSigmaE j j₁) = {!!}
  conv-nf {n} {.(LabI _)} {.(Label _)} (TLabI ins) = {!!}
  conv-nf {n} {.(LabE _ (LabI _))} {T} (TLabEl j j₁) = {!!}
  conv-nf {n} {.(LabE _ (Var _))} {T} (TLabEx f' j) = {!!}
  
  -- no. x ∈ s, x ∈ s', s ≠ s'; [] ⊢ LabI x ∶ Label s, [] ⊢ LabI x ∶ Label s', yet ¬ ([] ⊢ Label s ≡ᵀ Label s')
  type-eq : {n : ℕ} {T T' : Ty {n}} {e : Exp} → [] ⊢ e ∶ T → [] ⊢ e ∶ T' → [] ⊢ T ≡ᵀ T'
  type-eq {n} {T} {T'} {e} j j' = {!!}
  -- no. same as above.
  type-endure : {n : ℕ} {T T' : Ty {n}} {e : Exp} → [] ⊢ e ∶ T → ¬ ([] ⊢ T ≡ᵀ T') → ¬ ([] ⊢ e ∶ T')
  type-endure {n} {T} {T'} {e} j neq j' = contraposition type-eq (λ x → contradiction (x j') neq) j
  -}



{- "within"-ext not required


  -- type to determine whether var type judgement in env. (Δ ++ Γ) is in Δ or Γ
  data extract-env-or {n : ℕ} {Δ Γ : TEnv {n}} {T : Ty} {x : ℕ} : Set where
    in-Δ : x ∶ T ∈ Δ → extract-env-or
    -- x ≥ length Δ makes sure that x really is in Γ; e.g.
    -- x = 1, Δ = (S ∷ T), Γ = (T ∷ Γ'); here 1 ∶ T ∈ Δ as well as (1 ∸ 2) ≡ 0 ∶ T ∈ Γ
    in-Γ : (x ≥ᴺ length Δ) → (x ∸ length Δ) ∶ T ∈ Γ → extract-env-or

  extract : {n : ℕ} {Δ Γ : TEnv {n}} {T : Ty} {x : ℕ} (j : x ∶ T ∈ (Δ ++ Γ)) → extract-env-or{n}{Δ}{Γ}{T}{x}
  extract {n} {Δ} {Γ} {T} {x} j = {!!}
--  extract {n} {[]} {Γ} {T} {x} j = in-Γ z≤n j
--  extract {n} {x₁ ∷ Δ} {Γ} {.x₁} {.0} here = in-Δ here
--  extract {n} {x₁ ∷ Δ} {Γ} {T} {ℕ.suc x} (there j)
--    with extract {n} {Δ} {Γ} {T} {x} j
--  ...  | in-Δ j'  = in-Δ (there j')
--  ...  | in-Γ ge j'' = in-Γ (s≤s ge) j''


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
-}

{-
  {-
  ≡ᵀ⇒⊢ : {n : ℕ} {A B : Ty{n}} → [] ⊢ A ≡ᵀ B → [] ⊢ A × [] ⊢ B
  ≡ᵀ⇒⊢ {n} {A} {.A} (CRefl{ok = ok}) = ok , ok
  ≡ᵀ⇒⊢ {n} {A} {B} (CSym j) = {!!}
  ≡ᵀ⇒⊢ {n} {A} {B} (CTrans j j₁) = {!!}
  ≡ᵀ⇒⊢ {n} {A} {.(Case (λ l i → A) (LabI _))} (CLabEta x x₁) = x₁ , (TCaseF (λ l i → x₁) VLab x)
  ≡ᵀ⇒⊢ {n} {.(Case _ (LabI _))} {.(_ _ ins)} (CLabBeta x ins) = x , {!!}
  ≡ᵀ⇒⊢ {n} {.(Pi _ _)} {.(Pi _ _)} (CPi j j₁) = {!!}
  ≡ᵀ⇒⊢ {n} {.(Sigma _ _)} {.(Sigma _ _)} (CSigma j j₁) = {!!}
  ≡ᵀ⇒⊢ {n} {.(Case _ _)} {.(Case _ _)} (CLab v x) = {!!} -- apply lemma on x

  ≢ᵀ-trans : {n : ℕ} {A B C : Ty {n}} → [] ⊢ A ≡ᵀ B → ¬ ([] ⊢ B ≡ᵀ C) → ¬ ([] ⊢ A ≡ᵀ C)
  ≢ᵀ-trans {n} {A} {B} {C} j not l = contradiction (CTrans (CSym j) l) not


  
  conv-nf : {n : ℕ} {T : Ty {n}} → [] ⊢ T → ∃[ T' ]( (Nf T') × ([] ⊢ T ≡ᵀ T'))
  conv-nf {n} {(Label s)} TLabF = Label s , NLab , CRefl
  conv-nf {n} {(Pi A B)} (TPiF q q₁) = (Pi A B) , (NPi , CRefl)
  conv-nf {n} {(Sigma A B)} (TSigmaF q q₁) = (Sigma A B) , (NSigma , CRefl)
  conv-nf {n} {(Case f e)} (TCaseF f' v x)
    with canonical-forms-lab {n} {e = e} x v
  ... | fst , fst₁ , snd
        with conv-nf (f' fst snd)
  ...      | fst' , fst₁' , snd' rewrite fst₁ = fst' , (fst₁' , (CTrans (CLabBeta (TCaseF f' v x) snd) snd'))


  nf-uniq' : {n : ℕ} {A B : Ty {n}} → Nf A → Nf B → ([] ⊢ A ≡ᵀ B) → A ≡ B
  nf-uniq' {n} {A} {.A} nf nf' CRefl = refl
  nf-uniq' {n} {A} {B} nf nf' (CSym eq) = sym (nf-uniq' nf' nf eq)
  nf-uniq' {n} {A} {B} nf nf' (CTrans{T' = T'} eq eq₁) = {!!}   -- conv-nf => req. transitivity
  nf-uniq' {n} {.(Pi _ _)} {.(Pi _ _)} NPi NPi (CPi eq eq₁) = {!!}
  nf-uniq' {n} {.(Sigma _ _)} {.(Sigma _ _)} nf nf' (CSigma eq eq₁) = {!!}

  nf-uniqueness : {n : ℕ} {A : Ty {n}} → Nf A → (∀ B → A ≢ B → Nf B → ¬ ([] ⊢ A ≡ᵀ B))
  nf-uniqueness {n} {Label x} nf (Label x₁) neq nfb' eq = {!!}
  nf-uniqueness {n} {Label x} nf (Pi B B₁) neq nfb' eq = {!!}
  nf-uniqueness {n} {Label x} nf (Sigma B B₁) neq nfb' eq = {!!}
  nf-uniqueness {n} {Pi A A₁} nf B neq nfb' eq = {!!}
  nf-uniqueness {n} {Sigma A A₁} nf B neq nfb' eq = {!!}

  nf-uniqueness-alt : {n : ℕ} {A : Ty {n}} → Nf A → (∀ B → (¬ (Nf B) ⊎ ¬ (B ≢ A) ⊎ ¬ ([] ⊢ A ≡ᵀ B)))
  nf-uniqueness-alt {n} {A} nf B = {!nf-uniqueness nf B!}

  nf-uniqueness : {n : ℕ} {A : Ty {n}} → Nf A → (∄[ B ](Nf B × B ≢ A × [] ⊢ A ≡ᵀ B))
  nf-uniqueness {n} {Label x} nf (Label x₁ , fst₁ , fst₂ , snd) = {!!}
  nf-uniqueness {n} {Label x} nf (Pi fst fst₃ , fst₁ , fst₂ , snd) = {!!}
  nf-uniqueness {n} {Label x} nf (Sigma fst fst₃ , fst₁ , fst₂ , snd) = {!!}
  nf-uniqueness {n} {Pi A A₁} nf (fst , fst₁ , fst₂ , snd) = {!!}
  nf-uniqueness {n} {Sigma A A₁} nf (fst , fst₁ , fst₂ , snd) = {!!}

  nf-uniqueness-alt {n} {Label x₁} nf (Label x) = {!!}
--    with 
  nf-uniqueness-alt {n} {Pi A A₁} nf (Label x) = inj₂ {!inj₁!}
  nf-uniqueness-alt {n} {Sigma A A₁} nf (Label x) = {!!}
  nf-uniqueness-alt {n} {A} nf (Pi B B₁) = {!!}
  nf-uniqueness-alt {n} {A} nf (Sigma B B₁) = {!!}
  nf-uniqueness-alt {n} {A} nf (Case f x) = inj₁ (λ ())

  postulate -- law of the excluded middle
    not-ineq : {a : Set} {A B : a} → ¬ (A ≢ B) → A ≡ B

  case-nf-uniqueness : {n : ℕ} {s : Subset n} {B : Ty {n}} {f : ∀ l → l ∈ s → Ty {n}} {e : Exp {n}} → [] ⊢ Case f e ≡ᵀ B × Nf B → (∀ B' → B ≢ B' → Nf B' → ¬ ([] ⊢ Case f e ≡ᵀ B'))
  case-nf-uniqueness {n} {s} {B} {f} {e} (fst , snd) B' neq nfb' eq = nf-uniqueness snd B' neq nfb' (CTrans (CSym fst) eq)

  case-nf' : {n : ℕ} {s : Subset n} {B : Ty {n}} {f : ∀ l → l ∈ s → Ty {n}} {l : Fin n} {ins : l ∈ s} → [] ⊢ Case f (LabI l) ≡ᵀ B × Nf B → f l ins ≡ B
  case-nf' {n} {s} {B} {f} {l} {ins} (j , nf)
    with f l ins
  ...  | B' = {!!}
    with nf-uniqueness-alt snd B'
  ... | inj₁ x = contradiction nfb' x
  ... | inj₂ (inj₁ x) = contradiction (sym (not-ineq x)) neq
  ... | inj₂ (inj₂ y) = contradiction (CTrans (CSym fst) eq) y -}

  nf-eq : {n : ℕ} {A B : Ty{n}} (a : [] ⊢ A) (b : [] ⊢ B) → [] ⊢ A ≡ᵀ B → proj₁ (conv-nf a) ≡ proj₁ (conv-nf b)
  nf-eq {n} {A} {.A} a b CRefl = {!!}
  nf-eq {n} {A} {B} a b (CSym eq) = sym (nf-eq b a eq)
  nf-eq {n} {A} {B} a b (CTrans eq eq₁) = ≡-trans {!nf-eq !} {!!}
  nf-eq {n} {A} {.(Case (λ l i → A) (LabI _))} a b (CLabEta x x₁) = {!!}
  nf-eq {n} {.(Case _ (LabI _))} {.(_ _ ins)} a b (CLabBeta x ins) = {!!}
  nf-eq {n} {.(Pi _ _)} {.(Pi _ _)} a b (CPi eq eq₁) = {!!}
  nf-eq {n} {.(Sigma _ _)} {.(Sigma _ _)} a b (CSigma eq eq₁) = {!!}
  nf-eq {n} {.(Case _ _)} {.(Case _ _)} a b (CLab v x) = {!!}
 
  
  Pi≢ᵀLab {n} {A} {B} {s} (CSym j) = Lab≢ᵀPi j
  Pi≢ᵀLab {n} {A} {B} {s} (CTrans {T' = Label x} j j₁) = Pi≢ᵀLab j
  Pi≢ᵀLab {n} {A} {B} {s} (CTrans {T' = Pi T' T''} j j₁) = Pi≢ᵀLab j₁
  Pi≢ᵀLab {n} {A} {B} {s} (CTrans {T' = Sigma T' T''} j j₁) = contradiction j {!!}
  Pi≢ᵀLab {n} {A} {B} {s} (CTrans {T' = Case f e} j j₁) = contradiction (CSym j) (case-nf-uniqueness (j₁ , NLab) (Pi A B) (λ ()) NPi)

{-    requires CTrans for contradiction
    with (≡ᵀ⇒⊢ j)
  ...  | w
       with conv-nf {n} {Case f x} (proj₂ w)
  ...     | Label x' , fst , snd = {!!}
  ...     | Pi fst fst₁ , fst' , snd' = {!!}
  ...     | Sigma fst fst₁ , fst' , snd' = {!!}
-}


  -- conv-nf : {n : ℕ} {T : Ty {n}} → [] ⊢ T → ∃[ T' ]( (Nf T') × ([] ⊢ T ≡ᵀ T'))
  Lab≢ᵀPi {n} {A} {B} {s} (CSym j) = Pi≢ᵀLab j

  Lab≢ᵀPi {n} {A} {B} {s} (CTrans {T' = T'} j j₁)
    with (≡ᵀ⇒⊢ j)
  ...  | w
       with conv-nf {n} {T'} (proj₂ w)
  ...     | Label x , fst , snd = {!!} -- contradiction (CTrans (CSym j₁) (CSym j)) Pi≢ᵀLab
  ...     | Pi fst fst₁ , fst' , snd' = {!!}
  ...     | Sigma fst fst₁ , fst' , snd' = {!!}

  Lab≢ᵀPi {n} {A} {B} {s} (CTrans {T' = Label x} j j₁) = Lab≢ᵀPi j₁
  Lab≢ᵀPi {n} {A} {B} {s} (CTrans {T' = Pi T' T''} j j₁) = Lab≢ᵀPi j
  Lab≢ᵀPi {n} {A} {B} {s} (CTrans {T' = Sigma T' T''} j j₁) = contradiction j {!!}
  Lab≢ᵀPi {n} {A} {B} {s} (CTrans {T' = Case f x} j j') = contradiction (CSym j) (case-nf-uniqueness (j' , NPi) (Label s) (λ ()) NLab)
{-
    with (≡ᵀ⇒⊢ j)
  ... | w
      with conv-nf {n} {Case f x} (proj₂ w)
  ...    | w' = {!!}
-}
  

  subset-eq {n} {s} {.s} CRefl = refl
  subset-eq {n} {s} {s'} (CSym j) = sym (subset-eq j)
  subset-eq {n} {s} {s'} (CTrans {T' = T'} j j')
    with (proj₂ (≡ᵀ⇒⊢ j))
  ... | k
      with conv-nf k
  ...    | Label x , fst₁ , snd = ≡-trans {!CTRans !} {!!}
  ...    | Pi fst fst₂ , fst₁ , snd = contradiction (CTrans j snd) Lab≢ᵀPi 
  ...    | Sigma fst fst₂ , fst₁ , snd = contradiction (CTrans j snd) {!!}


  subset-eq {n} {s} {s'} (CTrans {T' = Label x} j j') = ≡-trans (subset-eq j) (subset-eq j')
  subset-eq {n} {s} {s'} (CTrans {T' = Pi T' T''} j j') = contradiction j Lab≢ᵀPi
  subset-eq {n} {s} {s'} (CTrans {T' = Sigma T' T''} j j') = {!contradiction j  Lab≢ᵀSigma!}
  subset-eq {n} {s} {s'} (CTrans {T' = Case f x} (CSym j) j') = {!!}
  subset-eq {n} {s} {s'} (CTrans {T' = Case f x} (CTrans j j₁) j') = {!!}
  subset-eq {n} {s} {s'} (CTrans {T' = Case .(λ l i → Label s) .(LabI _)} (CLabEta x x₁) (CSym j')) = {!!}
  subset-eq {n} {s} {s'} (CTrans {T' = Case .(λ l i → Label s) .(LabI _)} (CLabEta x x₁) (CTrans j' j'')) = {!!}
  subset-eq {n} {s} {.s} (CTrans {T' = Case .(λ l i → Label s) .(LabI _)} (CLabEta x x₁) (CLabBeta x₂ ins)) = refl


  subset-eq {n} {s} {s'} (CTrans CRefl j₁) = subset-eq j₁
  subset-eq {n} {s} {s'} (CTrans (CSym j) j₁) = {!!}
  subset-eq {n} {s} {s'} (CTrans (CTrans j j₂) j₁) = {!!}
  subset-eq {n} {s} {s'} (CTrans j (CSym j₁)) = {!!}
  subset-eq {n} {s} {s'} (CTrans j (CTrans j₁ j₂)) = {!!}
  subset-eq {n} {s} {.s} (CTrans (CLabEta x x₁) (CLabBeta x₂ ins)) = refl

  subset-eq : {n : ℕ} {s s' : Subset n} → [] ⊢ Label s ≡ᵀ Label s' → Label s ≡ Label s'
  subset-eq {n} {s} {s'} j
    with (nf-uniqueness-alt {n} {Label s} NLab (Label s'))
  ... | inj₁ x = contradiction NLab x
  ... | inj₂ (inj₁ x) = sym (not-ineq x) -- ¬ (¬ a) = a
  ... | inj₂ (inj₂ y) = contradiction j y
-}

