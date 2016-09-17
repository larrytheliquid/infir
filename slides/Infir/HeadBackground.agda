open import Data.Unit
open import Data.Maybe
module Infir.HeadBackground where

----------------------------------------------------------------------

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

postulate head : {A : Set} → List A → A

----------------------------------------------------------------------

head₁ : {A : Set} → List A → A → A
head₁ nil y = y
head₁ (cons x xs) y = x

head₂ : {A : Set} → List A → Maybe A
head₂ nil = nothing
head₂ (cons x xs) = just x

----------------------------------------------------------------------

HeadArg : {A : Set} → List A → Set
HeadArg {A = A} nil = A
HeadArg (cons x xs) = ⊤

head₃ : {A : Set} (xs : List A) → HeadArg xs → A
head₃ nil y = y
head₃ (cons x xs) tt = x

----------------------------------------------------------------------

HeadRet : {A : Set} → List A → Set
HeadRet nil = ⊤
HeadRet {A = A} (cons x xs) = A

head₄ : {A : Set} (xs : List A) → HeadRet xs
head₄ nil = tt
head₄ (cons x xs) = x

----------------------------------------------------------------------
