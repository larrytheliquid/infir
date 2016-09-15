open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Sum
open import Data.Nat
module Infir.CompBackground where

----------------------------------------------------------------------

Vec : (A : Set) → ℕ → Set
Vec A zero = ⊤
Vec A (suc n) = A × Vec A n

Fin : ℕ → Set
Fin zero = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

update : {A : Set} {n : ℕ} → Vec A n → Fin n → A → Vec A n
update {n = zero} tt () y
update {n = suc n} (x , xs) (inj₁ tt) y = y , xs
update {n = suc n} (x , xs) (inj₂ i) y = x , update xs i y

----------------------------------------------------------------------
