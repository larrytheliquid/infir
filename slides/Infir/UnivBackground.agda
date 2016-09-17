open import Data.Nat
module Infir.UnivBackground where

mutual
  data Type : Set where
    `Nat : Type
    `Fun : (A : Type) (B : ⟦ A ⟧ → Type) → Type
  
  ⟦_⟧ : Type → Set
  ⟦ `Nat ⟧ = ℕ
  ⟦ `Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
