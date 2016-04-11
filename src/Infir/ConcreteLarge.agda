open import Data.String hiding ( show )
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Maybe hiding ( Eq )
open import Relation.Binary.PropositionalEquality
module Infir.ConcreteLarge where

----------------------------------------------------------------------

postulate
  ext : {A : Set} {B : A → Set}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

--------------------------------------------------------------------------------

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

----------------------------------------------------------------------

mutual
  data Type : Set where
    `Bool : Type
    `Π : (A : Type) (B : ⟦ A ⟧ → Type) → Type

  ⟦_⟧ : Type → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Π A B ⟧ = Π ⟦ A ⟧ λ a → ⟦ B a ⟧

----------------------------------------------------------------------

data Path : Type → Set where
  here : {A : Type} → Path A
  there₁ : {A : Type} {B : ⟦ A ⟧ → Type}
    (i : Path A)
    → Path (`Π A B)
  there₂ : {A : Type} {B : ⟦ A ⟧ → Type}
    (f : (a : ⟦ A ⟧) → Path (B a))
    → Path (`Π A B)

----------------------------------------------------------------------

Lookup : (A : Type) → Path A → Set
Lookup A here = Type
Lookup (`Π A B) (there₁ i) = Lookup A i
Lookup (`Π A B) (there₂ f) = (a : ⟦ A ⟧) → Lookup (B a) (f a)

----------------------------------------------------------------------

lookup : (A : Type) (i : Path A) → Lookup A i
lookup A here = A
lookup (`Π A B) (there₁ i) = lookup A i
lookup (`Π A B) (there₂ f) = λ a → lookup (B a) (f a)

----------------------------------------------------------------------

Update : (A : Type) → Path A → Set
update : (A : Type) (i : Path A) (X : Update A i) → Type

Update A here = Type
Update (`Π A B) (there₁ i) = Σ (Update A i) λ X → ⟦ update A i X ⟧ → ⟦ A ⟧
Update (`Π A B) (there₂ f) = (a : ⟦ A ⟧) → Update (B a) (f a)

update A here X = X
update (`Π A B) (there₁ i) (X , f) = `Π (update A i X) (λ a → B (f a))
update (`Π A B) (there₂ f) F = `Π A λ a → update (B a) (f a) (F a)

----------------------------------------------------------------------

lift : (A : Type) (i : Path A) → Lookup A i → Update A i
lem : (A : Type) (i : Path A) (p : Lookup A i) → A ≡ update A i (lift A i p)

lift A here p = A
lift (`Π A B) (there₁ i) p =
  lift A i p
  , subst ⟦_⟧ (sym (lem A i p))
lift (`Π A B) (there₂ f) F = λ a → lift (B a) (f a) (F a)

----------------------------------------------------------------------

lem A here p = refl
lem (`Π A B) (there₁ i) p
  rewrite sym (lem A i p) = refl
lem (`Π A B) (there₂ f) F
  = cong (λ X → `Π A X) (ext (λ a → lem (B a) (f a) (F a)))

thm : (A : Type) (i : Path A) → A ≡ update A i (lift A i (lookup A i))
thm A i = lem A i (lookup A i)

----------------------------------------------------------------------
