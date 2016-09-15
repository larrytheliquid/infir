open import Data.Nat
module Infir.Nat where

----------------------------------------------------------------------

data Pathℕ : ℕ → Set where
  here : {n : ℕ} → Pathℕ n
  there : {n : ℕ}
    → Pathℕ n
    → Pathℕ (suc n)

updateℕ : (n : ℕ) → Pathℕ n → ℕ → ℕ
updateℕ n here m = m
updateℕ (suc n) (there i) m = suc (updateℕ n i m)

----------------------------------------------------------------------
