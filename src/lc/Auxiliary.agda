module Auxiliary where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Integer
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

n+1≡sucn : {n : ℕ} → n Data.Nat.+ 1 ≡ ℕ.suc n
n+1≡sucn {zero} = refl
n+1≡sucn {ℕ.suc n} = cong ℕ.suc (n+1≡sucn{n})

∣nℕ+1⊖1∣≡n : {n : ℕ} → ∣ n Data.Nat.+ 1 ⊖ 1 ∣ ≡ n
∣nℕ+1⊖1∣≡n {zero} = refl
∣nℕ+1⊖1∣≡n {ℕ.suc n} = n+1≡sucn

[k<x]⇒[k<sucx] : {x : ℕ} {k : ℕ} → (k Data.Nat.< x) → (k Data.Nat.< x Data.Nat.+ 1)
[k<x]⇒[k<sucx] {x} {k} le = <-trans le (m<m+n x (s≤s z≤n))

¬[x≤k]⇒¬[sucx≤k] : {x : ℕ} {k : ℕ} → ¬ (x Data.Nat.≤ k) → ¬ ((x Data.Nat.+ 1) Data.Nat.≤ k)
¬[x≤k]⇒¬[sucx≤k] {x} {k} nle = <⇒≱ ([k<x]⇒[k<sucx] (≰⇒> nle))
