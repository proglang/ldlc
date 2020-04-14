module Auxiliary where

open import Agda.Primitive
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Integer
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

length[A]≥0 : {a : Level} {s : Set a} {A : List s} → length A Data.Nat.≥ 0
length[A]≥0 {a} {s} {A} = z≤n

A++[]≡A : {a : Level} {s : Set a} {A : List s} → A ++ [] ≡ A
A++[]≡A {a} {s} {[]} = refl
A++[]≡A {a} {s} {x ∷ A} = cong (_∷_ x) (A++[]≡A {a} {s} {A})

n+length[]≡n : {a : Level} {A : Set a} {n : ℕ} → n Data.Nat.+ length{a}{A} [] ≡ n
n+length[]≡n {a} {A} {zero} = refl
n+length[]≡n {a} {A} {ℕ.suc n} = cong ℕ.suc (n+length[]≡n{a}{A})

length[A∷B]≡suc[length[B]] : {a : Level} {s : Set a} {A : s} {B : List s} → length (A ∷ B) ≡ ℕ.suc (length B)
length[A∷B]≡suc[length[B]] {a} {s} {A} {B} = refl

n+1≡sucn : {n : ℕ} → n Data.Nat.+ 1 ≡ ℕ.suc n
n+1≡sucn {zero} = refl
n+1≡sucn {ℕ.suc n} = cong ℕ.suc (n+1≡sucn{n})

n≤sucn : {n : ℕ} → n Data.Nat.≤ ℕ.suc n
n≤sucn {zero} = z≤n
n≤sucn {ℕ.suc n} = s≤s n≤sucn

a<b≤c⇒a<c : {a b c : ℕ} → a Data.Nat.< b → b Data.Nat.≤ c → a Data.Nat.< c
a<b≤c⇒a<c {a} {b} {c} lt le = ≤-trans lt le

n≤m⇒n≤sucm : {n m : ℕ} → n Data.Nat.≤ m → n Data.Nat.≤ ℕ.suc m
n≤m⇒n≤sucm {.0} {m} z≤n = z≤n
n≤m⇒n≤sucm {.(ℕ.suc _)} {.(ℕ.suc _)} (s≤s le) = s≤s (n≤m⇒n≤sucm le)

∣nℕ+1⊖1∣≡n : {n : ℕ} → ∣ n Data.Nat.+ 1 ⊖ 1 ∣ ≡ n
∣nℕ+1⊖1∣≡n {zero} = refl
∣nℕ+1⊖1∣≡n {ℕ.suc n} = n+1≡sucn

-- to save me some ugly rewriting two definitions
[k<x]⇒[k<x+1] : {x : ℕ} {k : ℕ} → (k Data.Nat.< x) → (k Data.Nat.< x Data.Nat.+ 1)
[k<x]⇒[k<x+1]{x} {k} le = <-trans le (m<m+n x (s≤s z≤n))

[k<x]⇒[k<sucx] : {x : ℕ} {k : ℕ} → (k Data.Nat.< x) → (k Data.Nat.< ℕ.suc (x))
[k<x]⇒[k<sucx] {x} {k} le = <-trans le (s≤s ≤-refl)

¬[x≤k]⇒¬[sucx≤k] : {x : ℕ} {k : ℕ} → ¬ (x Data.Nat.≤ k) → ¬ ((x Data.Nat.+ 1) Data.Nat.≤ k)
¬[x≤k]⇒¬[sucx≤k] {x} {k} nle = <⇒≱ ([k<x]⇒[k<x+1] (≰⇒> nle))
