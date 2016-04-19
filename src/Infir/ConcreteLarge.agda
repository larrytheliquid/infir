open import Function
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
  ext : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

----------------------------------------------------------------------

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

----------------------------------------------------------------------

mutual
  data Type : Set₁ where
    `Base : Set → Type
    `Π : (A : Type) (B : ⟦ A ⟧ → Type) → Type

  ⟦_⟧ : Type → Set
  ⟦ `Base A ⟧ = A
  ⟦ `Π A B ⟧ = Π ⟦ A ⟧ λ a → ⟦ B a ⟧

----------------------------------------------------------------------

data Path : Type → Set₁ where
  here : {A : Type} → Path A
  thereBase : {A : Set} → Path (`Base A)
  thereΠ₁ : {A : Type} {B : ⟦ A ⟧ → Type}
    (i : Path A)
    → Path (`Π A B)
  thereΠ₂ : {A : Type} {B : ⟦ A ⟧ → Type}
    (f : (a : ⟦ A ⟧) → Path (B a))
    → Path (`Π A B)

----------------------------------------------------------------------

Lookup : (A : Type) → Path A → Set₁
Lookup A here = Type
Lookup (`Base A) thereBase = Set
Lookup (`Π A B) (thereΠ₁ i) = Lookup A i
Lookup (`Π A B) (thereΠ₂ f) = (a : ⟦ A ⟧) → Lookup (B a) (f a)

----------------------------------------------------------------------

lookup : (A : Type) (i : Path A) → Lookup A i
lookup A here = A
lookup (`Base A) thereBase = A
lookup (`Π A B) (thereΠ₁ i) = lookup A i
lookup (`Π A B) (thereΠ₂ f) = λ a → lookup (B a) (f a)

----------------------------------------------------------------------

Update : (A : Type) → Path A → Set₁
update : (A : Type) (i : Path A) (X : Update A i) → Type

Update A here = Maybe Type
Update (`Base A) thereBase = Maybe Set
Update (`Π A B) (thereΠ₁ i) = Σ (Update A i) λ X → ⟦ update A i X ⟧ → ⟦ A ⟧
Update (`Π A B) (thereΠ₂ f) = (a : ⟦ A ⟧) → Update (B a) (f a)

update A here X = maybe id A X
update (`Base A) thereBase X = maybe `Base (`Base A) X
update (`Π A B) (thereΠ₁ i) (X , f) = `Π (update A i X) (λ a → B (f a))
update (`Π A B) (thereΠ₂ f) F = `Π A λ a → update (B a) (f a) (F a)

----------------------------------------------------------------------

lift : (A : Type) (i : Path A) → Update A i
lem : (A : Type) (i : Path A) → A ≡ update A i (lift A i)

lift A here = nothing
lift (`Base A) thereBase = nothing
lift (`Π A B) (thereΠ₁ i) =
  lift A i
  , subst ⟦_⟧ (sym (lem A i))
lift (`Π A B) (thereΠ₂ f) = λ a → lift (B a) (f a)

----------------------------------------------------------------------

lem A here = refl
lem (`Base A) thereBase = refl
lem (`Π A B) (thereΠ₁ i)
  rewrite sym (lem A i) = refl
lem (`Π A B) (thereΠ₂ f)
  = cong (λ X → `Π A X) (ext (λ a → lem (B a) (f a)))

----------------------------------------------------------------------

forget : (A : Type) (i : Path A) → Update A i → Lookup A i
forget A here X = maybe id A X
forget (`Base A) thereBase X = maybe id A X
forget (`Π A B) (thereΠ₁ i) (X , f) = forget A i X
forget (`Π A B) (thereΠ₂ f) h = λ a → forget (B a) (f a) (h a)

----------------------------------------------------------------------

thm : (A : Type) (i : Path A) → lookup A i ≡ forget A i (lift A i)
thm A here = refl
thm (`Base A) thereBase = refl
thm (`Π A B) (thereΠ₁ i) = thm A i
thm (`Π A B) (thereΠ₂ f) = ext (λ a → thm (B a) (f a))

----------------------------------------------------------------------
