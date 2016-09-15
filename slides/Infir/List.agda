open import Data.Nat
open import Infir.Nat
module Infir.List where

----------------------------------------------------------------------

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

----------------------------------------------------------------------

data PathL₁ {A : Set} : List A → Set where
  here : ∀{x xs} → PathL₁ (cons x xs)
  there : ∀{x xs}
    → PathL₁ xs
    → PathL₁ (cons x xs)

updateL₁ : {A : Set} (xs : List A) → PathL₁ xs → A → List A
updateL₁ (cons x xs) here y = cons y xs
updateL₁ (cons x xs) (there i) y = cons x (updateL₁ xs i y)

----------------------------------------------------------------------

data PathL₂ {A : Set} : List A → Set where
  here : ∀{xs} → PathL₂ xs
  there : ∀{x xs}
    → PathL₂ xs
    → PathL₂ (cons x xs)

updateL₂ : {A : Set} (xs : List A) → PathL₂ xs → List A → List A
updateL₂ xs here ys = ys
updateL₂ (cons x xs) (there i) ys = cons x (updateL₂ xs i ys)

----------------------------------------------------------------------

data PathL {A : Set} : List A → Set where
  here : ∀{xs} → PathL xs
  there₁ : ∀{x xs} → PathL (cons x xs)
  there₂ : ∀{x xs}
    → PathL xs
    → PathL (cons x xs)

UpdateL : {A : Set} (xs : List A) → PathL xs → Set
UpdateL {A} xs here = List A
UpdateL {A} (cons x xs) there₁ = A
UpdateL (cons x xs) (there₂ i) = UpdateL xs i

updateL : {A : Set} (xs : List A) (i : PathL xs) → UpdateL xs i → List A
updateL xs here ys = ys
updateL (cons x xs) there₁ y = cons y xs
updateL (cons x xs) (there₂ i) ys = cons x (updateL xs i ys)

----------------------------------------------------------------------

