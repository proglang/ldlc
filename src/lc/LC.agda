-- simply-typed λ-calculus

module LC where

open import Data.Nat
open import Agda.Builtin.Bool

-- definitions

data Exp : Set where
  Var : ℕ → Exp
  Abs : Exp → Exp
  App : Exp → Exp → Exp

-- shifting, required to avoid variable-capturing in substitution
-- see Pierce 2002, pg. 78/79

↑_,_[_] : ℕ → ℕ → Exp → Exp
↑ d , c [ Var x ] with (_<ᵇ_ x c)
... | false = Var x
... | true = Var (x + d)
↑ d , c [ Abs t ] = Abs (↑ d , (suc c) [ t ])
↑ d , c [ App t t₁ ] = App (↑ d , c [ t ]) (↑ d , c [ t₁ ])

-- substitution
-- see Pierce 2002, pg. 80

[_↦_]_ : ℕ → Exp → Exp → Exp
[ k ↦ s ] Var x with (_≡ᵇ_ x k)
... | false = Var x
... | true = s
[ k ↦ s ] Abs t = Abs ([ suc k ↦ ↑ 1 , 0 [ s ] ] t)
[ k ↦ s ] App t t₁ = App ([ k ↦ s ] t) ([ k ↦ s ] t₁)
