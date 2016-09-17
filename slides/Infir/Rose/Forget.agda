open import Function
open import Data.Char
open import Data.String
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding ( _+_ ) renaming ( zero to here ; suc to there)
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Infir.Nat
open import Infir.Char
open import Infir.Rose
module Infir.Rose.Forget where

----------------------------------------------------------------------

UpdateR : {A : Set} (xs : Rose A) → PathR xs → Set
updateR : {A : Set} (xs : Rose A) (i : PathR xs) → UpdateR xs i → Rose A

UpdateR {A} xs here = Maybe (Rose A)
UpdateR {A} (rose x n f) there₁ = A
UpdateR (rose x n f) (there₂ i) = Σ ℕ (λ m → Fin (updateℕ n i m) → Fin n)
UpdateR (rose x n f) (there₃ g) = (i : Fin n) → UpdateR (f i) (g i)

updateR xs here ys = maybe id xs ys
updateR (rose x n f) there₁ y = rose y n f
updateR (rose x n f) (there₂ i) (m , g) = rose x (updateℕ n i m) (f ∘ g)
-- Goal: Fin (updateℕ n i m) → Rose A
-- ——————————————————————————————————
-- g  : Fin (updateℕ n i m) → Fin n
-- f  : Fin n → Rose A
updateR (rose x n f) (there₃ g) h = rose x n (λ i → updateR (f i) (g i) (h i))
-- Goal: Fin n → Rose A
-- ——————————————————————————————————————
-- h  : (i : Fin n) → UpdateR (f i) (g i)
-- g  : (i : Fin n) → PathR (f i)
-- f  : Fin n → Rose A

----------------------------------------------------------------------

pathD : PathR branchD
pathD = there₂ here

pathA : PathR branchA
pathA = there₃ pathsA
  where
  pathsA : PathsR branchA
  pathsA here = here
  pathsA (there here) = here
  pathsA (there (there here)) = pathD
  pathsA (there (there (there ())))

patchD : Fin 1 → Fin 2
patchD = raise 1

patchA : UpdateR branchA pathA
patchA here = nothing
patchA (there here) = nothing
patchA (there (there here)) = 1 , patchD
patchA (there (there (there ())))

branchA' : Rose Char
branchA' = updateR branchA pathA patchA

test-updateR : showR branchA' ≡ "a[b[e],c,d[g]]"
test-updateR = refl

----------------------------------------------------------------------

