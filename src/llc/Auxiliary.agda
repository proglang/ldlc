module Auxiliary where

open import Agda.Primitive
open import Data.List
open import Data.Nat renaming (_+_ to _+ᴺ_ ; _≤_ to _≤ᴺ_ ; _≥_ to _≥ᴺ_ ; _<_ to _<ᴺ_ ; _>_ to _>ᴺ_)
open import Data.Nat.Properties 
open import Data.Integer renaming (_+_ to _+ᶻ_ ; _≤_ to _≤ᶻ_ ; _≥_ to _≥ᶻ_ ; _<_ to _<ᶻ_ ; _>_ to _>ᶻ_)
import Data.Integer.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Product
open import Data.Sum


-- natural numbers

n≢m⇒sucn≢sucm : {n m : ℕ} → n ≢ m → ℕ.suc n ≢ ℕ.suc m
n≢m⇒sucn≢sucm {n} {m} neq = λ x → contradiction (cong Data.Nat.pred x) neq

sucn≢sucm⇒n≢m : {n m : ℕ} → ℕ.suc n ≢ ℕ.suc m → n ≢ m
sucn≢sucm⇒n≢m {n} {m} neq = λ x → contradiction (cong ℕ.suc x) neq

n+1≡sucn : {n : ℕ} → n +ᴺ 1 ≡ ℕ.suc n
n+1≡sucn {zero} = refl
n+1≡sucn {ℕ.suc n} = cong ℕ.suc (n+1≡sucn{n})

n≤sucn : {n : ℕ} → n ≤ᴺ ℕ.suc n
n≤sucn {zero} = z≤n
n≤sucn {ℕ.suc n} = s≤s n≤sucn

n<sucn : {n : ℕ} → n <ᴺ ℕ.suc n
n<sucn {zero} = s≤s z≤n
n<sucn {ℕ.suc n} = s≤s n<sucn

m<n⇒m+o<n+o : {m n o : ℕ} → m <ᴺ n → m +ᴺ o <ᴺ n +ᴺ o
m<n⇒m+o<n+o {zero} {n} {o} le = m<n+m o le
m<n⇒m+o<n+o {ℕ.suc m} {ℕ.suc n} {o} (s≤s le) = s≤s (m<n⇒m+o<n+o le)

m≤n⇒m+o≤n+o : {m n o : ℕ} → m ≤ᴺ n → m +ᴺ o ≤ᴺ n +ᴺ o
m≤n⇒m+o≤n+o {zero} {n} {o} le = m≤n+m o n
m≤n⇒m+o≤n+o {ℕ.suc m} {ℕ.suc n} {o} (s≤s le) = s≤s (m≤n⇒m+o≤n+o le)


≤-refl-+-comm : {m n : ℕ} → m +ᴺ n ≤ᴺ n +ᴺ m
≤-refl-+-comm {m} {n} rewrite (+-comm m n) = ≤-refl

a<b≤c⇒a<c : {a b c : ℕ} → a <ᴺ b → b ≤ᴺ c → a <ᴺ c
a<b≤c⇒a<c {a} {b} {c} lt le = ≤-trans lt le

a≤b<c⇒a<c : {a b c : ℕ} → a ≤ᴺ b → b <ᴺ c → a <ᴺ c
a≤b<c⇒a<c {.0} {zero} {c} z≤n lt = lt
a≤b<c⇒a<c {.0} {ℕ.suc b} {ℕ.suc c} z≤n (s≤s lt) = s≤s z≤n
a≤b<c⇒a<c {.(ℕ.suc _)} {.(ℕ.suc _)} {ℕ.suc c} (s≤s le) (s≤s lt) = s≤s (a≤b<c⇒a<c le lt)

m≤n∧m≡q⇒q≤n : {m n q : ℕ} → m ≤ᴺ n → m ≡ q → q ≤ᴺ n
m≤n∧m≡q⇒q≤n {m} {n} {q} le eq rewrite eq = le

m≤n∧n≡q⇒m≤q : {m n q : ℕ} → m ≤ᴺ n → n ≡ q → m ≤ᴺ q
m≤n∧n≡q⇒m≤q le eq rewrite eq = le

n≤m⇒n≤sucm : {n m : ℕ} → n ≤ᴺ m → n ≤ᴺ ℕ.suc m
n≤m⇒n≤sucm {.0} {m} z≤n = z≤n
n≤m⇒n≤sucm {.(ℕ.suc _)} {.(ℕ.suc _)} (s≤s le) = s≤s (n≤m⇒n≤sucm le)

n≤m⇒n<sucm : {n m : ℕ} → n ≤ᴺ m → n <ᴺ ℕ.suc m
n≤m⇒n<sucm {n} {m} le = s≤s le

sucn≤m⇒n≤m : {n m : ℕ} → ℕ.suc n ≤ᴺ m → n ≤ᴺ m
sucn≤m⇒n≤m {n} {.(ℕ.suc _)} (s≤s le) = ≤-trans le n≤sucn

[k<x]⇒[k<x+1] : {x : ℕ} {k : ℕ} → (k <ᴺ x) → (k <ᴺ x +ᴺ 1)
[k<x]⇒[k<x+1]{x} {k} le = <-trans le (m<m+n x (s≤s z≤n))

[k<x]⇒[k<sucx] : {x : ℕ} {k : ℕ} → (k <ᴺ x) → (k <ᴺ ℕ.suc (x))
[k<x]⇒[k<sucx] {x} {k} le = <-trans le (s≤s ≤-refl)

¬[x≤k]⇒¬[sucx≤k] : {x : ℕ} {k : ℕ} → ¬ (x ≤ᴺ k) → ¬ ((x +ᴺ 1) ≤ᴺ k)
¬[x≤k]⇒¬[sucx≤k] {x} {k} nle = <⇒≱ ([k<x]⇒[k<x+1] (≰⇒> nle))

n+m≤n+q+m : {n m q : ℕ} → n +ᴺ m ≤ᴺ n +ᴺ (q +ᴺ m)
n+m≤n+q+m {n} {m} {q} rewrite (+-comm q m) | (sym (+-assoc n m q)) = m≤m+n (n +ᴺ m) q

m>n⇒m∸n≥1 : {m n : ℕ} → n <ᴺ m → m ∸ n ≥ᴺ 1
m>n⇒m∸n≥1 {ℕ.suc m} {zero} le = s≤s z≤n
m>n⇒m∸n≥1 {ℕ.suc m} {ℕ.suc n} (s≤s le) = m>n⇒m∸n≥1 le

m∸n≥q⇒m≥q : {m n q : ℕ} → m ∸ n ≥ᴺ q → m ≥ᴺ q
m∸n≥q⇒m≥q {m} {n} {q} ge = ≤-trans ge (m∸n≤m m n)


-- lists & length

++-assoc : {a : Level} {s : Set a} {Δ ∇ Γ : List s} → ((Δ ++ ∇) ++ Γ) ≡ (Δ ++ (∇ ++ Γ))
++-assoc {a} {s} {[]} {∇} {Γ} = refl
++-assoc {a} {s} {x ∷ Δ} {∇} {Γ} = cong (_∷_ x) (++-assoc{a}{s}{Δ}{∇}{Γ})

length[A]≥0 : {a : Level} {s : Set a} {A : List s} → length A ≥ᴺ 0
length[A]≥0 {a} {s} {A} = z≤n

A++[]≡A : {a : Level} {s : Set a} {A : List s} → A ++ [] ≡ A
A++[]≡A {a} {s} {[]} = refl
A++[]≡A {a} {s} {x ∷ A} = cong (_∷_ x) (A++[]≡A {a} {s} {A})

n+length[]≡n : {a : Level} {A : Set a} {n : ℕ} → n +ᴺ length{a}{A} [] ≡ n
n+length[]≡n {a} {A} {zero} = refl
n+length[]≡n {a} {A} {ℕ.suc n} = cong ℕ.suc (n+length[]≡n{a}{A})

length[A∷B]≡suc[length[B]] : {a : Level} {s : Set a} {A : s} {B : List s} → length (A ∷ B) ≡ ℕ.suc (length B)
length[A∷B]≡suc[length[B]] {a} {s} {A} {B} = refl

length[A∷B]≥1 : {a : Level} {s : Set a} {A : s} {B : List s} → length (A ∷ B) ≥ᴺ 1
length[A∷B]≥1 {a} {s} {A} {B} = s≤s z≤n

length[A++B]≡length[A]+length[B] : {a : Level} {s : Set a} {A B : List s} → length (A ++ B) ≡ length A +ᴺ length B
length[A++B]≡length[A]+length[B] {a} {s} {[]} {B} = refl
length[A++B]≡length[A]+length[B] {a} {s} {x ∷ A} {B} rewrite length[A∷B]≡suc[length[B]]{a}{s}{x}{A ++ B} = cong ℕ.suc (length[A++B]≡length[A]+length[B]{a}{s}{A}{B})

length[A++B∷[]]≡suc[length[A]] : {a : Level} {s : Set a} {A : List s} {B : s} → length (A ++ B ∷ []) ≡ ℕ.suc (length A)
length[A++B∷[]]≡suc[length[A]] {a} {s} {A} {B} rewrite (length[A++B]≡length[A]+length[B]{a}{s}{A}{B ∷ []}) = n+1≡sucn

A++B∷[]++C≡A++B∷C : {a : Level} {s : Set a} {A C : List s} {B : s} → ((A ++ B ∷ []) ++ C) ≡ (A ++ B ∷ C)
A++B∷[]++C≡A++B∷C {a} {s} {[]} {C} {B} = refl
A++B∷[]++C≡A++B∷C {a} {s} {x ∷ A} {C} {B} = cong (_∷_ x) A++B∷[]++C≡A++B∷C

A++B++D∷[]++C≡A++B++D∷C : {a : Level} {s : Set a} { A B C : List s} {D : s} → (A ++ B ++ D ∷ []) ++ C ≡ (A ++ B ++ D ∷ C)
A++B++D∷[]++C≡A++B++D∷C {a} {s} {[]} {B} {C} {D} = A++B∷[]++C≡A++B∷C
A++B++D∷[]++C≡A++B++D∷C {a} {s} {x ∷ A} {B} {C} {D} = cong (_∷_ x) (A++B++D∷[]++C≡A++B++D∷C{a}{s}{A}{B}{C}{D})

-- integers

m≥0⇒n+m≥0 : {n : ℕ} {m : ℤ} → m ≥ᶻ +0 → + n +ᶻ m ≥ᶻ +0
m≥0⇒n+m≥0 {n} {+_ m} ge = +≤+ z≤n

n>0⇒n>∣n⊖1∣ : {n : ℕ} → n ≥ᴺ 1 → n >ᴺ ∣ n ⊖ 1 ∣
n>0⇒n>∣n⊖1∣ {.(ℕ.suc _)} (s≤s le) = n<sucn

∣nℕ+1⊖1∣≡n : {n : ℕ} → ∣ n +ᴺ 1 ⊖ 1 ∣ ≡ n
∣nℕ+1⊖1∣≡n {zero} = refl
∣nℕ+1⊖1∣≡n {ℕ.suc n} = n+1≡sucn

m≥0⇒∣n+m∣≥n : {n : ℕ} {m : ℤ} → m ≥ᶻ +0 → ∣ +_ n +ᶻ m ∣ ≥ᴺ n 
m≥0⇒∣n+m∣≥n {n} {+_ m} ge = m≤m+n n m

m>0⇒∣n+m∣>n : {n : ℕ} {m : ℤ} → m >ᶻ +0 → ∣ +_ n +ᶻ m ∣ >ᴺ n 
m>0⇒∣n+m∣>n {n} {(+ m)} (+<+ m<n) = m<m+n n m<n

∣n∣≥n : {n : ℤ} → + ∣ n ∣ ≥ᶻ n
∣n∣≥n {+_ n} = +≤+ ≤-refl
∣n∣≥n { -[1+_] n} = -≤+

+a≤b⇒a≤∣b∣ : {a : ℕ} {b : ℤ} → + a ≤ᶻ b → a ≤ᴺ ∣ b ∣
+a≤b⇒a≤∣b∣ {zero} {b} le = z≤n
+a≤b⇒a≤∣b∣ {ℕ.suc a} {(+ b)} (+≤+ m≤n) = m≤n

+[1+q]≡q+1 : {q : ℕ} → +[1+ q ] ≡ + q +ᶻ + 1
+[1+q]≡q+1 {zero} = refl
+[1+q]≡q+1 {ℕ.suc q} = cong +[1+_] (sym n+1≡sucn)

+q≤+c+l⇒+1q≤+1c+l : {q c : ℕ} {l : ℤ} → + q ≤ᶻ + c +ᶻ l → +[1+ q ] ≤ᶻ +[1+ c ] +ᶻ l
+q≤+c+l⇒+1q≤+1c+l {q} {c} {l} le
  rewrite (+[1+q]≡q+1{q})
        | (+[1+q]≡q+1{c})
        | (Data.Integer.Properties.+-assoc (+ c) (+ 1) l)
        | (Data.Integer.Properties.+-comm (+ 1) l)
        | (sym (Data.Integer.Properties.+-assoc (+ c) (l) (+ 1)))
        = Data.Integer.Properties.+-monoˡ-≤ (+ 1) le


ℤ-m≤n⇒m+o≤n+o : {m n o : ℤ} → m ≤ᶻ n → m +ᶻ o ≤ᶻ n +ᶻ o
ℤ-m≤n⇒m+o≤n+o {m} {n} {o} le = Data.Integer.Properties.+-monoˡ-≤ o le

minus-1 : {y x : ℕ} {lt : x <ᴺ y} → ∣ y ∸ x ⊖ 1 ∣ +ᴺ x ≡ ∣ y ⊖ 1 ∣
minus-1 {y} {x} {lt}
  rewrite (Data.Integer.Properties.⊖-≥{y ∸ x}{1} (m>n⇒m∸n≥1 lt))
        | (sym (+-∸-comm {y ∸ x} x {1} (m>n⇒m∸n≥1 lt)))
        | (m∸n+n≡m {y} {x} (sucn≤m⇒n≤m lt))
        | (Data.Integer.Properties.⊖-≥{y}{1} ((m∸n≥q⇒m≥q{y}{x} (m>n⇒m∸n≥1{y}{x} lt))))
        = refl

k≥0⇒∣+x+k∣≡x+k : {x k : ℕ} → ∣ + x +ᶻ + k ∣ ≡ x +ᴺ k
k≥0⇒∣+x+k∣≡x+k {x} {k} = refl


-- products & sums

-- deMorgan on products and sums
dm1 : {P Q : Set} → (¬ P × ¬ Q) → ¬ (P ⊎ Q)
dm1 {P} {Q} (fst , snd) (inj₁ x) = contradiction x fst
dm1 {P} {Q} (fst , snd) (inj₂ y) = contradiction y snd

dm2 : {P Q : Set} → ¬ (P ⊎ Q) → (¬ P × ¬ Q)
dm2 {P} {Q} d = (λ x → contradiction (inj₁ x) d) , λ x → contradiction (inj₂ x) d
