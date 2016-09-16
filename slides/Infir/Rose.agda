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
module Infir.Rose where

----------------------------------------------------------------------

module Alg where
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A

  data Rose (A : Set) : Set where
    rose : A → List (Rose A) → Rose A

  showR : Rose Char → String
  showR' : List (Rose Char) → String
  showR (rose x xss) = "rose " ++ (showC x) ++ " (" ++ showR' xss ++ ")"
  showR' nil = "[]"
  showR' (cons xs xss) = showR xs ++ ", " ++ showR' xss

data Rose (A : Set) : Set where
  rose : (a : A) (n : ℕ) (f : Fin n → Rose A) → Rose A

----------------------------------------------------------------------

Vec : Set → ℕ → Set
Vec A n = Fin n → A

nil : {A : Set} → Vec A zero
nil ()

cons : {A : Set} {n : ℕ} → A → Vec A n → Vec A (suc n)
cons x f here = x
cons x f (there i) = f i

append : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
append {n = zero} f g i = g i
append {n = suc n} f g here = f here
append {n = suc n} f g (there i) = append (f ∘ there) g i

snoc : {A : Set} {n : ℕ} → Vec A n → A → Vec A (suc n)
snoc {n = zero} f x = cons x nil
snoc {n = suc n} f x = cons (f here) (snoc (f ∘ there) x)

{-# NO_TERMINATION_CHECK #-}
showR : Rose Char → String
showR' : (n : ℕ) → Vec (Rose Char) n → String

showR (rose x zero f) = showC x
showR (rose x n f) = showC x ++ "[" ++ showR' n f ++ "]"
showR' zero f = ""
showR' (suc zero) f = showR (f here)
showR' (suc n) f =
  showR (f here) ++ "," ++ showR' n (f ∘ there)

----------------------------------------------------------------------

leafE leafC leafF leafG : Rose Char
leafE = rose 'e' 0 nil
leafC = rose 'c' 0 nil
leafF = rose 'f' 0 nil
leafG = rose 'g' 0 nil
leafH = rose 'h' 0 nil

branchB branchD branchA : Rose Char
branchB = rose 'b' 1 (cons leafE nil)
branchD = rose 'd' 2 (cons leafF (cons leafG nil))
branchA = rose 'a' 3 (cons branchB (cons leafC (cons branchD nil)))

test-showR : showR branchA ≡ "a[b[e],c,d[f,g]]"
test-showR = refl

----------------------------------------------------------------------

module MaybeInUpdate where

  data PathR {A : Set} : Rose A → Set where
    here : ∀{xs} → PathR xs
    there₁ : ∀{x n f} → PathR (rose x n f)
    there₂ : ∀{x n f}
      (i : Pathℕ n)
      → PathR (rose x n f)
    there₃ : ∀{x n f}
      (g : (i : Fin n) → PathR (f i))
      → PathR (rose x n f)
  
  PathsR : {A : Set} → Rose A → Set
  PathsR (rose x n f) = (i : Fin n) → PathR (f i)
  
  module Forget where
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
    -- f  : Fin n → Rose A
    updateR (rose x n f) (there₃ g) h = rose x n (λ i → updateR (f i) (g i) (h i))
    -- Goal: Fin n → Rose A
  
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
  
  module Replace where
    UpdateR : {A : Set} (xs : Rose A) → PathR xs → Set
    updateR : {A : Set} (xs : Rose A) (i : PathR xs) → UpdateR xs i → Rose A
    
    UpdateR {A} xs here = Maybe (Rose A)
    UpdateR {A} (rose x n f) there₁ = A
    UpdateR {A} (rose x n f) (there₂ i) =
      Σ ℕ (λ m → (Fin n → Rose A) → Fin (updateℕ n i m) → Rose A)
    UpdateR (rose x n f) (there₃ g) = (i : Fin n) → UpdateR (f i) (g i)
    
    updateR xs here ys = maybe id xs ys
    updateR (rose x n f) there₁ y = rose y n f
    updateR (rose x n f) (there₂ i) (m , g) = rose x (updateℕ n i m) (g f)
    updateR (rose x n f) (there₃ g) h = rose x n (λ i → updateR (f i) (g i) (h i))

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

    patchD : Vec (Rose Char) 2 → Vec (Rose Char) 3
    patchD xs = snoc xs leafH

    patchA : UpdateR branchA pathA
    patchA here = nothing
    patchA (there here) = nothing
    patchA (there (there here)) = 3 , patchD
    patchA (there (there (there ())))
  
    branchA' : Rose Char
    branchA' = updateR branchA pathA patchA

    test-updateR : showR branchA' ≡ "a[b[e],c,d[f,g,h]]"
    test-updateR = refl

  ----------------------------------------------------------------------

module MaybeInPath where

  data PathR {A : Set} : Rose A → Set where
    here : ∀{xs} → PathR xs
    there₁ : ∀{x n f} → PathR (rose x n f)
    there₂ : ∀{x n f}
      (i : Pathℕ n)
      → PathR (rose x n f)
    there₃ : ∀{x n f}
      (g : (i : Fin n) → Maybe (PathR (f i)))
      → PathR (rose x n f)
  
  PathsR : {A : Set} → Rose A → Set
  PathsR (rose x n f) = (i : Fin n) → Maybe (PathR (f i))
  
  module Forget where
    UpdateR : {A : Set} (xs : Rose A) → PathR xs → Set
    updateR : {A : Set} (xs : Rose A) (i : PathR xs) → UpdateR xs i → Rose A
    
    UpdateR {A} xs here = Rose A
    UpdateR {A} (rose x n f) there₁ = A
    UpdateR (rose x n f) (there₂ i) = Σ ℕ (λ m → Fin (updateℕ n i m) → Fin n)
    UpdateR (rose x n f) (there₃ g) = (i : Fin n) →
      maybe (UpdateR (f i)) ⊤ (g i)
    
    updateR xs here ys = ys
    updateR (rose x n f) there₁ y = rose y n f
    updateR (rose x n f) (there₂ i) (m , g) = rose x (updateℕ n i m) (f ∘ g)
    updateR {A = A} (rose x n f) (there₃ g) h = rose x n xs where
      xs : Fin n → Rose A
      xs i with g i | h i
      ... | nothing | tt = f i
      ... | just j | hi = updateR (f i) j hi
  
    ----------------------------------------------------------------------
  
  module Replace where
    UpdateR : {A : Set} (xs : Rose A) → PathR xs → Set
    updateR : {A : Set} (xs : Rose A) (i : PathR xs) → UpdateR xs i → Rose A
    
    UpdateR {A} xs here = Rose A
    UpdateR {A} (rose x n f) there₁ = A
    UpdateR {A} (rose x n f) (there₂ i) =
      Σ ℕ (λ m → (Fin n → Rose A) → Fin (updateℕ n i m) → Rose A)
    UpdateR (rose x n f) (there₃ g) = (i : Fin n) →
      maybe (UpdateR (f i)) ⊤ (g i)
    
    updateR xs here ys = ys
    updateR (rose x n f) there₁ y = rose y n f
    updateR (rose x n f) (there₂ i) (m , g) = rose x (updateℕ n i m) (g f)
    updateR {A} (rose x n f) (there₃ g) h = rose x n xs where
      xs : Fin n → Rose A
      xs i with g i | h i
      ... | nothing | tt = f i
      ... | just j | hi = updateR (f i) j hi
  
  ----------------------------------------------------------------------
