open import Data.String hiding ( show )
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Maybe hiding ( Eq )
open import Relation.Binary.PropositionalEquality
module Infir.ConcreteSmall where

----------------------------------------------------------------------

postulate
  ext : {A : Set} {B : A → Set}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

----------------------------------------------------------------------

prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (λ x → f (suc x))

mutual
  data Arith : Set where
    `[_] : ℕ → Arith
    `Π : (A : Arith) (f : Fin (eval A) → Arith) → Arith

  eval : Arith → ℕ
  eval `[ n ] = n
  eval (`Π A f) = prod (eval A) λ a → prod (toℕ a) λ b → eval (f (inject b))

⟦_⟧ : Arith → Set
⟦ A ⟧ = Fin (eval A)

----------------------------------------------------------------------

data Path : Arith → Set where
  here : {A : Arith} → Path A
  -- there₀ : {n : ℕ} → Pathℕ n → Path `[ n ]
  there₁ : {A : Arith} {B : ⟦ A ⟧ → Arith}
    (i : Path A)
    → Path (`Π A B)
  there₂ : {A : Arith} {B : ⟦ A ⟧ → Arith}
    (f : (a : ⟦ A ⟧) → Path (B a))
    → Path (`Π A B)

----------------------------------------------------------------------

Drop : (A : Arith) → Path A → Set
Drop A here = Arith
Drop (`Π A B) (there₁ i) = Drop A i
Drop (`Π A B) (there₂ f) = (a : ⟦ A ⟧) → Drop (B a) (f a)

----------------------------------------------------------------------

drop : (A : Arith) (i : Path A) → Drop A i
drop A here = A
drop (`Π A B) (there₁ i) = drop A i
drop (`Π A B) (there₂ f) = λ a → drop (B a) (f a)

----------------------------------------------------------------------

Sub : (A : Arith) → Path A → Set
update : (A : Arith) (i : Path A) (X : Sub A i) → Arith

Sub A here = Arith
Sub (`Π A B) (there₁ i) = Σ (Sub A i) λ X → ⟦ update A i X ⟧ → ⟦ A ⟧
Sub (`Π A B) (there₂ f) = (a : ⟦ A ⟧) → Sub (B a) (f a)

update A here X = X
update (`Π A B) (there₁ i) (X , f) = `Π (update A i X) (λ a → B (f a))
update (`Π A B) (there₂ f) F = `Π A λ a → update (B a) (f a) (F a)

----------------------------------------------------------------------

liftD : (A : Arith) (i : Path A) → Drop A i → Sub A i
lem : (A : Arith) (i : Path A) (p : Drop A i) → A ≡ update A i (liftD A i p)

liftD A here p = A
liftD (`Π A B) (there₁ i) p = liftD A i p , id where
  id : ⟦ update A i (liftD A i p) ⟧ → ⟦ A ⟧
  id a = subst ⟦_⟧ (sym (lem A i p)) a
liftD (`Π A B) (there₂ f) F = λ a → liftD (B a) (f a) (F a)

----------------------------------------------------------------------

lem A here p = refl
lem (`Π A B) (there₁ i) p
  rewrite sym (lem A i p) = refl
lem (`Π A B) (there₂ f) F
  = cong (λ X → `Π A X) (ext (λ a → lem (B a) (f a) (F a)))

thm : (A : Arith) (i : Path A) → A ≡ update A i (liftD A i (drop A i))
thm A i = lem A i (drop A i)

----------------------------------------------------------------------
