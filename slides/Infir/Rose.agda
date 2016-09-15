open import Data.Nat
open import Data.Fin
open import Infir.Nat
module Infir.Rose where

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
UpdateR {A} xs here = Rose A
UpdateR {A} (rose x n f) there₁ = A
UpdateR (rose x n f) (there₂ i) = {!!}
UpdateR (rose x n f) (there₃ g) = {!!}

updateR : {A : Set} (xs : Rose A) (i : PathR xs) → UpdateR xs i → Rose A
updateR xs here ys = ys
updateR (rose x n f) there₁ y = rose y n f
updateR (rose x n f) (there₂ i) m =
  rose x (updateℕ n i m) {!!}
  -- Goal: Fin (updateℕ n i m) → Rose A
  -- ——————————————————————————————————
  -- f  : Fin n → Rose A
updateR (rose x n f) (there₃ g) h =
  rose x n {!!}
  -- Goal: Fin n → Rose A

----------------------------------------------------------------------

