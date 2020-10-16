module Extensionality where

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

postulate
  f-ext : {A : Set}{B : A → Set}{f : (x : A) → B x} {g : (x : A) → B x} →
    (∀ x → f x ≡ g x) → f ≡ g
