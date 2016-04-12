open import Function
open import Data.String hiding ( show )
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding ( lift )
open import Data.Product
open import Data.Sum
open import Data.Maybe hiding ( Eq )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; refl )
module Infir.ConcreteSmall where

----------------------------------------------------------------------

postulate
  ext : {A : Set} {B : A → Set}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

Dyn : Set₁
Dyn = Σ Set id

DynCon : Set → Set₁
DynCon B = Σ Set (λ A → A → B)

eqpair : {A : Set} {B : A → Set}
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (q : a₁ ≡ a₂) → b₁ ≅ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
eqpair refl refl = refl

subst-id : {A : Set} {x y : A} (P : A → Set) (q : x ≡ y) (p : P x) → p ≅ subst P q p
subst-id P refl p = refl

----------------------------------------------------------------------

prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (λ x → f (suc x))

mutual
  data Arith : Set where
    `Num : ℕ → Arith
    `Π : (A : Arith) (f : Fin (eval A) → Arith) → Arith

  eval : Arith → ℕ
  eval (`Num n) = n
  eval (`Π A f) = prod (eval A) λ a → prod (toℕ a) λ b → eval (f (inject b))

⟦_⟧ : Arith → Set
⟦ A ⟧ = Fin (eval A)

----------------------------------------------------------------------

data Path : Arith → Set where
  here : {A : Arith} → Path A
  -- thereNum : {n : ℕ} → Fin n → Path `[ n ]
  thereΠ₁ : {A : Arith} {B : ⟦ A ⟧ → Arith}
    (i : Path A)
    → Path (`Π A B)
  thereΠ₂ : {A : Arith} {B : ⟦ A ⟧ → Arith}
    (f : (a : ⟦ A ⟧) → Path (B a))
    → Path (`Π A B)

----------------------------------------------------------------------

lookup' : (A : Arith) → Path A → Dyn

Lookup : (A : Arith) → Path A → Set
Lookup A i = proj₁ (lookup' A i)

lookup : (A : Arith) (i : Path A) → Lookup A i
lookup A i = proj₂ (lookup' A i)

----------------------------------------------------------------------

lookup' A here = Arith , A
lookup' (`Π A B) (thereΠ₁ i) = lookup' A i
lookup' (`Π A B) (thereΠ₂ f) =
  Π ⟦ A ⟧ (λ a → Lookup (B a) (f a))
  , (λ a → lookup (B a) (f a))

----------------------------------------------------------------------

update' : (A : Arith) → Path A → DynCon Arith

Update : (A : Arith) → Path A → Set
Update A i = proj₁ (update' A i)

update : (A : Arith) (i : Path A) (X : Update A i) → Arith
update A i X = proj₂ (update' A i) X

----------------------------------------------------------------------

update' A here = Maybe Arith , maybe id A
update' (`Π A B) (thereΠ₁ i) =
  Σ (Update A i) (λ X → ⟦ update A i X ⟧ → ⟦ A ⟧)
  , λ { (X , f) → `Π (update A i X) (λ a → B (f a)) }
update' (`Π A B) (thereΠ₂ f) =
  Π ⟦ A ⟧ (λ a → Update (B a) (f a))
  , (λ F → `Π A λ a → update (B a) (f a) (F a))

----------------------------------------------------------------------

lift : (A : Arith) (i : Path A) → Update A i
lem : (A : Arith) (i : Path A) → A ≡ update A i (lift A i)

lift A here = nothing
lift (`Π A B) (thereΠ₁ i) =
  lift A i
  , subst ⟦_⟧ (sym (lem A i))
lift (`Π A B) (thereΠ₂ f) = λ a → lift (B a) (f a)

----------------------------------------------------------------------

lem A here = refl
lem (`Π A B) (thereΠ₁ i)
  rewrite sym (lem A i) = refl
lem (`Π A B) (thereΠ₂ f)
  = cong (λ X → `Π A X) (ext (λ a → lem (B a) (f a)))

----------------------------------------------------------------------

forget : (A : Arith) (i : Path A) → Update A i → Lookup A i
forget A here X = maybe id A X
forget (`Π A B) (thereΠ₁ i) (X , f) = forget A i X
forget (`Π A B) (thereΠ₂ f) h = λ a → forget (B a) (f a) (h a)

----------------------------------------------------------------------

thm : (A : Arith) (i : Path A) → lookup A i ≡ forget A i (lift A i)
thm A here = refl
thm (`Π A B) (thereΠ₁ i) = thm A i
thm (`Π A B) (thereΠ₂ f) = ext (λ a → thm (B a) (f a))

----------------------------------------------------------------------
