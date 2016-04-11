open import Data.List
module Infir.ListLookup where

data PathG (A : Set) : A → Set where
  here : {a : A} → PathG A a

data PathL {A : Set} : List A → Set where
  here : ∀{xs} → PathL xs
  there₁ : ∀{x xs}
    → PathG A x
    → PathL (x ∷ xs)
  there₂ : ∀{x xs}
    → PathL xs
    → PathL (x ∷ xs)

LookupG : {A : Set} (x : A) → PathG A x → Set
LookupG {A = A} x here = A

LookupL : {A : Set} (xs : List A) → PathL xs → Set
LookupL {A = A} xs here = List A
LookupL {A = A} (x ∷ xs) (there₁ i) = LookupG x i
LookupL (x ∷ xs) (there₂ i) = LookupL xs i

lookupG : {A : Set} (x : A) (i : PathG A x) → LookupG x i
lookupG x here = x

lookupL : {A : Set} (xs : List A) (i : PathL xs) → LookupL xs i
lookupL xs here = xs
lookupL (x ∷ xs) (there₁ i) = lookupG x i
lookupL (x ∷ xs) (there₂ i) = lookupL xs i


  
