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
