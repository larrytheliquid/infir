open import Function
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Infir.Nat
module Infir.Rose2 where

----------------------------------------------------------------------

module Alg where
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A

  data Rose (A : Set) : Set where
    rose : A → List (Rose A) → Rose A

data Rose (A : Set) : Set where
  rose : (a : A) (n : ℕ) (f : Fin n → Rose A) → Rose A

----------------------------------------------------------------------

data PathR {A : Set} : Rose A → Set where
  here : ∀{xs} → PathR xs
  there₁ : ∀{x n f} → PathR (rose x n f)
  there₂ : ∀{x n f}
    (i : Pathℕ n)
    → PathR (rose x n f)
  there₃ : ∀{x n f}
    (g : (i : Fin n) → PathR (f i))
    → PathR (rose x n f)

UpdateR : {A : Set} (xs : Rose A) → PathR xs → Set
updateR : {A : Set} (xs : Rose A) (i : PathR xs) → UpdateR xs i → Rose A

UpdateR {A} xs here = Rose A
UpdateR {A} (rose x n f) there₁ = A
UpdateR (rose x n f) (there₂ i) = Σ ℕ (λ m → Fin (updateℕ n i m) → Fin n)
UpdateR (rose x n f) (there₃ g) = (i : Fin n) → UpdateR (f i) (g i)

updateR xs here ys = ys
updateR (rose x n f) there₁ y = rose y n f
updateR (rose x n f) (there₂ i) (m , g) = rose x (updateℕ n i m) (f ∘ g)
updateR (rose x n f) (there₃ g) h = rose x n (λ i → updateR (f i) (g i) (h i))

----------------------------------------------------------------------

