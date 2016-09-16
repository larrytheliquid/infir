open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Bool
module Infir.Desc where

----------------------------------------------------------------------

data Desc : Set₁ where
  End : Desc
  Arg : (A : Set) (B : A → Desc) → Desc
  Rec : (A : Set) (B : Desc) → Desc

mutual
  data Data (D : Desc) : Set where
    con : Data' D D → Data D

  Data' : (R D : Desc) → Set
  Data' R End = ⊤
  Data' R (Arg A B) = Σ A (λ a → Data' R (B a))
  Data' R (Rec A B) = (A → Data R) × Data' R B

----------------------------------------------------------------------

mutual
  data `Set : Set where
    `Empty `Unit `Bool : `Set
    `Fun : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `Data : (D : `Desc) → `Set 

  ⟦_⟧ : `Set → Set
  ⟦ `Empty ⟧ = ⊥
  ⟦ `Unit ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `Data D ⟧ = Data ⟪ D ⟫

  data `Desc : Set where
    `End : `Desc
    `Arg : (A : `Set) (B : ⟦ A ⟧ → `Desc) → `Desc
    `Rec : (A : `Set) (B : `Desc) → `Desc

  ⟪_⟫ : `Desc → Desc
  ⟪ `End ⟫ = End
  ⟪ `Arg A B ⟫ = Arg ⟦ A ⟧ (λ a → ⟪ B a ⟫)
  ⟪ `Rec A B ⟫ = Rec ⟦ A ⟧ ⟪ B ⟫

mutual
  data Path : (A : `Set) → ⟦ A ⟧ → Set where
    here : ∀{A a} → Path A a
    thereFun : ∀{A B f}
      (g : (a : ⟦ A ⟧) → Path (B a) (f a))
      → Path (`Fun A B) f
    thereData : ∀{D} {xs : Data' ⟪ D ⟫ ⟪ D ⟫}
      (i : Path′ D D xs)
      → Path (`Data D) (con xs)

  data Path′ (R : `Desc) : (D : `Desc) → Data' ⟪ R ⟫ ⟪ D ⟫ → Set where
    thereArg₁ : ∀{A B a xs}
      (i : Path A a)
      → Path′ R (`Arg A B) (a , xs)
    thereArg₂ : ∀{A B a xs}
      (i : Path′ R (B a) xs)
      → Path′ R (`Arg A B) (a , xs)
    thereRec₁ : ∀{A B f} {xs : Data' ⟪ R ⟫ ⟪ B ⟫}
      (g : (a : ⟦ A ⟧) → Path (`Data R) (f a))
      → Path′ R (`Rec A B) (f , xs)
    thereRec₂ : ∀{A D f xs}
      (i : Path′ R D xs)
      → Path′ R (`Rec A D) (f , xs)

----------------------------------------------------------------------
