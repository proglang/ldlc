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


++-assoc : {a : Level} {s : Set a} {Δ ∇ Γ : List s} → ((Δ ++ ∇) ++ Γ) ≡ (Δ ++ (∇ ++ Γ))
++-assoc {a} {s} {[]} {∇} {Γ} = refl
++-assoc {a} {s} {x ∷ Δ} {∇} {Γ} = cong (_∷_ x) (++-assoc{a}{s}{Δ}{∇}{Γ})

length[A∷B]≡suc[length[B]] : {a : Level} {s : Set a} {A : s} {B : List s} → length (A ∷ B) ≡ ℕ.suc (length B)
length[A∷B]≡suc[length[B]] {a} {s} {A} {B} = refl

length[A∷B]≥1 : {a : Level} {s : Set a} {A : s} {B : List s} → length (A ∷ B) Data.Nat.≥ 1
length[A∷B]≥1 {a} {s} {A} {B} = s≤s z≤n

length[A++B]≡length[A]+length[B] : {a : Level} {s : Set a} {A B : List s} → length (A ++ B) ≡ length A Data.Nat.+ length B
length[A++B]≡length[A]+length[B] {a} {s} {[]} {B} = refl
length[A++B]≡length[A]+length[B] {a} {s} {x ∷ A} {B} rewrite length[A∷B]≡suc[length[B]]{a}{s}{x}{A ++ B} = cong ℕ.suc (length[A++B]≡length[A]+length[B]{a}{s}{A}{B})

A++B∷[]++C≡A++B∷C : {a : Level} {s : Set a} {A C : List s} {B : s} → ((A ++ B ∷ []) ++ C) ≡ (A ++ B ∷ C)
A++B∷[]++C≡A++B∷C {a} {s} {[]} {C} {B} = refl
A++B∷[]++C≡A++B∷C {a} {s} {x ∷ A} {C} {B} = cong (_∷_ x) A++B∷[]++C≡A++B∷C

A++B++D∷[]++C≡A++B++D∷C : {a : Level} {s : Set a} { A B C : List s} {D : s} → (A ++ B ++ D ∷ []) ++ C ≡ (A ++ B ++ D ∷ C)
A++B++D∷[]++C≡A++B++D∷C {a} {s} {[]} {B} {C} {D} = A++B∷[]++C≡A++B∷C
A++B++D∷[]++C≡A++B++D∷C {a} {s} {x ∷ A} {B} {C} {D} = cong (_∷_ x) (A++B++D∷[]++C≡A++B++D∷C{a}{s}{A}{B}{C}{D})

n+1≡sucn : {n : ℕ} → n Data.Nat.+ 1 ≡ ℕ.suc n
n+1≡sucn {zero} = refl
n+1≡sucn {ℕ.suc n} = cong ℕ.suc (n+1≡sucn{n})

n≤sucn : {n : ℕ} → n Data.Nat.≤ ℕ.suc n
n≤sucn {zero} = z≤n
n≤sucn {ℕ.suc n} = s≤s n≤sucn

n<sucn : {n : ℕ} → n Data.Nat.< ℕ.suc n
n<sucn {zero} = s≤s z≤n
n<sucn {ℕ.suc n} = s≤s n<sucn

m<n⇒m+o<n+o : {m n o : ℕ} → m Data.Nat.< n → m Data.Nat.+ o Data.Nat.< n Data.Nat.+ o
m<n⇒m+o<n+o {zero} {n} {o} le = m<n+m o le
m<n⇒m+o<n+o {ℕ.suc m} {ℕ.suc n} {o} (s≤s le) = s≤s (m<n⇒m+o<n+o le)

m≤n⇒m+o≤n+o : {m n o : ℕ} → m Data.Nat.≤ n → m Data.Nat.+ o Data.Nat.≤ n Data.Nat.+ o
m≤n⇒m+o≤n+o {zero} {n} {o} le = m≤n+m o n
m≤n⇒m+o≤n+o {ℕ.suc m} {ℕ.suc n} {o} (s≤s le) = s≤s (m≤n⇒m+o≤n+o le)

≤-refl-+-comm : {m n : ℕ} → m Data.Nat.+ n Data.Nat.≤ n Data.Nat.+ m
≤-refl-+-comm {m} {n} rewrite (+-comm m n) = ≤-refl

a<b≤c⇒a<c : {a b c : ℕ} → a Data.Nat.< b → b Data.Nat.≤ c → a Data.Nat.< c
a<b≤c⇒a<c {a} {b} {c} lt le = ≤-trans lt le

m≤n∧m≡q⇒q≤n : {m n q : ℕ} → m Data.Nat.≤ n → m ≡ q → q Data.Nat.≤ n
m≤n∧m≡q⇒q≤n {m} {n} {q} le eq rewrite eq = le

m≤n∧n≡q⇒m≤q : {m n q : ℕ} → m Data.Nat.≤ n → n ≡ q → m Data.Nat.≤ q
m≤n∧n≡q⇒m≤q le eq rewrite eq = le

n≤m⇒n≤sucm : {n m : ℕ} → n Data.Nat.≤ m → n Data.Nat.≤ ℕ.suc m
n≤m⇒n≤sucm {.0} {m} z≤n = z≤n
n≤m⇒n≤sucm {.(ℕ.suc _)} {.(ℕ.suc _)} (s≤s le) = s≤s (n≤m⇒n≤sucm le)

sucn≤m⇒n≤m : {n m : ℕ} → ℕ.suc n Data.Nat.≤ m → n Data.Nat.≤ m
sucn≤m⇒n≤m {n} {.(ℕ.suc _)} (s≤s le) = ≤-trans le n≤sucn

n+m≤n+q+m : {n m q : ℕ} → n Data.Nat.+ m Data.Nat.≤ n Data.Nat.+ (q Data.Nat.+ m)
n+m≤n+q+m {n} {m} {q} rewrite (+-comm q m) | (sym (+-assoc n m q)) = m≤m+n (n Data.Nat.+ m) q

n>0⇒n>∣n⊖1∣ : {n : ℕ} → n Data.Nat.≥ 1 → n Data.Nat.> ∣ n ⊖ 1 ∣
n>0⇒n>∣n⊖1∣ {.(ℕ.suc _)} (s≤s le) = n<sucn

∣nℕ+1⊖1∣≡n : {n : ℕ} → ∣ n Data.Nat.+ 1 ⊖ 1 ∣ ≡ n
∣nℕ+1⊖1∣≡n {zero} = refl
∣nℕ+1⊖1∣≡n {ℕ.suc n} = n+1≡sucn

m>n⇒m∸n≥1 : {m n : ℕ} → n Data.Nat.< m → m ∸ n Data.Nat.≥ 1
m>n⇒m∸n≥1 {ℕ.suc m} {zero} le = s≤s z≤n
m>n⇒m∸n≥1 {ℕ.suc m} {ℕ.suc n} (s≤s le) = m>n⇒m∸n≥1 le

m∸n≥q⇒m≥q : {m n q : ℕ} → m ∸ n Data.Nat.≥ q → m Data.Nat.≥ q
m∸n≥q⇒m≥q {m} {n} {q} ge = ≤-trans ge (m∸n≤m m n)

-- to save me some ugly rewriting two definitions
[k<x]⇒[k<x+1] : {x : ℕ} {k : ℕ} → (k Data.Nat.< x) → (k Data.Nat.< x Data.Nat.+ 1)
[k<x]⇒[k<x+1]{x} {k} le = <-trans le (m<m+n x (s≤s z≤n))

[k<x]⇒[k<sucx] : {x : ℕ} {k : ℕ} → (k Data.Nat.< x) → (k Data.Nat.< ℕ.suc (x))
[k<x]⇒[k<sucx] {x} {k} le = <-trans le (s≤s ≤-refl)

¬[x≤k]⇒¬[sucx≤k] : {x : ℕ} {k : ℕ} → ¬ (x Data.Nat.≤ k) → ¬ ((x Data.Nat.+ 1) Data.Nat.≤ k)
¬[x≤k]⇒¬[sucx≤k] {x} {k} nle = <⇒≱ ([k<x]⇒[k<x+1] (≰⇒> nle))


