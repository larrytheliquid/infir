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

eqpair : {A : Set} {B : A → Set}
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (q : a₁ ≡ a₂) → b₁ ≅ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
eqpair refl refl = refl

subst-id : {A : Set} {x y : A} (P : A → Set) (q : x ≡ y) (p : P x) → p ≅ subst P q p
subst-id P refl p = refl


----------------------------------------------------------------------

data Pathℕ : ℕ → Set where
  here : {n : ℕ} → Pathℕ n
  there : {n : ℕ}
    → Pathℕ n
    → Pathℕ (suc n)

lookupℕ : (n : ℕ) → Pathℕ n → ℕ
lookupℕ n here = n
lookupℕ (suc n) (there i) = lookupℕ n i

updateℕ : (n : ℕ) → Pathℕ n → Maybe ℕ → ℕ
updateℕ n here x = maybe id n x
updateℕ (suc n) (there i) x = suc (updateℕ n i x)

lemℕ : (n : ℕ) (i : Pathℕ n)
  → n ≡ updateℕ n i (just (lookupℕ n i))
lemℕ n here = refl
lemℕ (suc n) (there i) = cong suc (lemℕ n i)

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
  thereNum : {n : ℕ} → Pathℕ n → Path (`Num n)
  thereΠ₁ : {A : Arith} {B : ⟦ A ⟧ → Arith}
    (i : Path A)
    → Path (`Π A B)
  thereΠ₂ : {A : Arith} {B : ⟦ A ⟧ → Arith}
    (f : (a : ⟦ A ⟧) → Path (B a))
    → Path (`Π A B)

----------------------------------------------------------------------

Lookup : (A : Arith) → Path A → Set
Lookup A here = Arith
Lookup (`Num n) (thereNum i) = ℕ 
Lookup (`Π A B) (thereΠ₁ i) = Lookup A i
Lookup (`Π A B) (thereΠ₂ f) = Π ⟦ A ⟧ (λ a → Lookup (B a) (f a))

----------------------------------------------------------------------

lookup : (A : Arith) (i : Path A) → Lookup A i
lookup A here = A
lookup (`Num n) (thereNum i) = lookupℕ n i
lookup (`Π A B) (thereΠ₁ i) = lookup A i
lookup (`Π A B) (thereΠ₂ f) = λ a → lookup (B a) (f a)

----------------------------------------------------------------------

Update : (A : Arith) → Path A → Set
update : (A : Arith) (i : Path A) (X : Update A i) → Arith

Update A here = Maybe Arith
Update (`Num n) (thereNum i) = Maybe ℕ
Update (`Π A B) (thereΠ₁ i) =
  Σ (Update A i) (λ X → ⟦ update A i X ⟧ → ⟦ A ⟧)
Update (`Π A B) (thereΠ₂ f) =
  Π ⟦ A ⟧ (λ a → Update (B a) (f a))

update A here X = maybe id A X
update (`Num n) (thereNum i) X = `Num (updateℕ n i X)
update (`Π A B) (thereΠ₁ i) (X , f) =
  `Π (update A i X) (B ∘ f)
update (`Π A B) (thereΠ₂ f) g =
  `Π A (λ a → update (B a) (f a) (g a))

----------------------------------------------------------------------

lift : (A : Arith) (i : Path A) → Update A i
lem : (A : Arith) (i : Path A) → A ≡ update A i (lift A i)

lift A here = nothing
lift (`Num n) (thereNum i) =
  just (lookupℕ n i)
lift (`Π A B) (thereΠ₁ i) =
  lift A i
  , subst ⟦_⟧ (sym (lem A i))
lift (`Π A B) (thereΠ₂ f) = λ a → lift (B a) (f a)

lem A here = refl
lem (`Num n) (thereNum i) =
  cong `Num (lemℕ n i)
lem (`Π A B) (thereΠ₁ i)
  rewrite sym (lem A i) = refl
lem (`Π A B) (thereΠ₂ f)
  = cong (λ X → `Π A X) (ext (λ a → lem (B a) (f a)))

----------------------------------------------------------------------

forget : (A : Arith) (i : Path A) → Update A i → Lookup A i
forget A here X = maybe id A X
forget (`Num n) (thereNum i) X = maybe id n X
forget (`Π A B) (thereΠ₁ i) (X , f) = forget A i X
forget (`Π A B) (thereΠ₂ f) h = λ a → forget (B a) (f a) (h a)

----------------------------------------------------------------------

thm : (A : Arith) (i : Path A) → lookup A i ≡ forget A i (lift A i)
thm A here = refl
thm (`Num n) (thereNum i) = refl
thm (`Π A B) (thereΠ₁ i) = thm A i
thm (`Π A B) (thereΠ₂ f) = ext (λ a → thm (B a) (f a))

----------------------------------------------------------------------
