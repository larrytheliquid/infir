open import Function
open import Data.Char
open import Data.String
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding ( _+_ ) renaming ( zero to here ; suc to there)
open import Data.Maybe hiding ( All )
open import Data.Product
open import Relation.Binary.PropositionalEquality
module Infir.Rose where

data Rose (A : Set) : Set where
  rose : (a : A) (n : ℕ) (f : Fin n → Rose A) → Rose A

----------------------------------------------------------------------

data Path {A : Set} : Rose A → Set where
  here : ∀{xs} → Path xs
  there₁ : ∀{x n f} → Path (rose x n f)
  -- there₂ : ∀{x n f} → Path (rose x n f)
  there₃ : ∀{x n f} (i : Fin n)
    (p : Path (f i))
    → Path (rose x n f)

----------------------------------------------------------------------

Update : {A : Set} (xs : Rose A) → Path xs → Set
update : {A : Set} (xs : Rose A) (i : Path xs) → Update xs i → Rose A

Update {A} xs here = Maybe (Rose A)
Update {A} (rose x n f) there₁ = A
-- Update {A} (rose x n f) there₂ = {!!}
Update (rose x n f) (there₃ i p) =
  (j : Fin n) → i ≡ j → Update (f i) p

update xs here ys = maybe id xs ys
update (rose x n f) there₁ y = rose y n f
-- update (rose x n f) there₂ (m , g) = {!!} -- rose x (updateℕ n i m) (g f)
update (rose x n f) (there₃ i p) h = rose x n (λ j → {!!})
-- rose x n (λ i → update (f i) (g i) (h i))

----------------------------------------------------------------------

