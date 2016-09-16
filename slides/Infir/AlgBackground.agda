open import Data.Nat
module Infir.AlgBackground where

----------------------------------------------------------------------

data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

data Fin : ℕ → Set where
  here : {n : ℕ} → Fin (suc n)
  there : {n : ℕ} → Fin n → Fin (suc n)

update : {A : Set} {n : ℕ} → Vec A n → Fin n → A → Vec A n
update (cons x xs) here y = cons y xs
update (cons x xs) (there i) y = cons x (update xs i y)

----------------------------------------------------------------------

append : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)

snoc : {A : Set} {n : ℕ} → Vec A n → A → Vec A (suc n)
snoc nil y = cons y nil
snoc (cons x xs) y = cons x (snoc xs y)

----------------------------------------------------------------------
