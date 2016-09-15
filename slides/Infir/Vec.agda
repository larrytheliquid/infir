open import Data.Nat
open import Infir.Nat
module Infir.Vec where

----------------------------------------------------------------------

data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : A → (n : ℕ) → Vec A n → Vec A (suc n)

----------------------------------------------------------------------

data PathV {A : Set} : {n : ℕ} → Vec A n → Set where
  here : ∀{n} {xs : Vec A n} → PathV xs
  there₁ : ∀{x n} {xs : Vec A n} → PathV (cons x n xs)
  there₂ : ∀{x n} {xs : Vec A n}
    → Pathℕ n
    → PathV (cons x n xs)
  there₃ : ∀{x n} {xs : Vec A n}
    → PathV xs
    → PathV (cons x n xs)

UpdateV : {A : Set} {n : ℕ} (xs : Vec A n) → PathV xs → Set
UpdateV {A} {n} xs here = Vec A n
UpdateV {A = A} (cons x n xs) there₁ = A
UpdateV (cons x n xs) (there₂ i) = ℕ
UpdateV (cons x n xs) (there₃ i) = UpdateV xs i

updateV : {A : Set} {n : ℕ} (xs : Vec A n) (i : PathV xs) → UpdateV xs i → Vec A n
updateV xs here ys = ys
updateV (cons x n xs) there₁ y = cons y n xs
updateV (cons x n xs) (there₂ i) m = {!!}
updateV (cons x n xs) (there₃ i) ys = cons x n (updateV xs i ys)

----------------------------------------------------------------------

