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

Dyn : Set₁
Dyn = Σ Set (λ A → A)

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

drop : (A : Type) (i : Path A) → Dyn
drop A here = Type , A
drop (`Π A B) (there₁ i) = drop A i
drop (`Π A B) (there₂ f) =
  Π ⟦ A ⟧ (λ a → proj₁ (drop (B a) (f a)))
  , (λ a → proj₂ (drop (B a) (f a)))

----------------------------------------------------------------------

update : (A : Type) (i : Path A) → Σ Set (λ A → A → Type)
update A here = Type , (λ A → A)
update (`Π A B) (there₁ i) =
  Σ (proj₁ (update A i)) (λ X → ⟦ proj₂ (update A i) X ⟧ → ⟦ A ⟧)
  , (λ { (X , f) → `Π (proj₂ (update A i) X) (λ a → B (f a)) })
update (`Π A B) (there₂ f) =
  Π ⟦ A ⟧ (λ a → proj₁ (update (B a) (f a)))
  , (λ F → `Π A (λ a → proj₂ (update (B a) (f a)) (F a)))

----------------------------------------------------------------------

liftD : (A : Type) (i : Path A) → proj₁ (drop A i) → proj₁ (update A i)
lem : (A : Type) (i : Path A) (p : proj₁ (drop A i)) → A ≡ proj₂ (update A i) (liftD A i p)

liftD A here p = A
liftD (`Π A B) (there₁ i) p = (liftD A i p) , id where
  id : ⟦ proj₂ (update A i) (liftD A i p) ⟧ → ⟦ A ⟧
  id a = subst ⟦_⟧ (sym (lem A i p)) a
liftD (`Π A B) (there₂ f) F = λ a → liftD (B a) (f a) (F a)

----------------------------------------------------------------------

lem A here p = refl
lem (`Π A B) (there₁ i) p
  rewrite sym (lem A i p) = refl
lem (`Π A B) (there₂ f) F
  = cong (λ X → `Π A X) (ext (λ a → lem (B a) (f a) (F a)))

thm : (A : Type) (i : Path A) → A ≡ proj₂ (update A i) (liftD A i (proj₂ (drop A i)))
thm A i = lem A i (proj₂ (drop A i))

----------------------------------------------------------------------
