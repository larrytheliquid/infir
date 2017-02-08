open import Data.String hiding ( show )
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding ( lift )
open import Data.Product
open import Data.Sum
open import Data.Maybe hiding ( Eq )
open import Relation.Binary.PropositionalEquality
module Infir.GenericClosed2 where

----------------------------------------------------------------------

postulate
  ext : {A : Set} {B : A → Set}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

----------------------------------------------------------------------

data Desc (O : Set) : Set₁ where
  ι : (o : O) → Desc O
  σ : (A : Set) (D : (a : A) → Desc O) → Desc O
  δ : (A : Set) (D : (o : A → O) → Desc O) → Desc O

mutual
  data μ {O : Set} (D : Desc O) : Set where
    init : Args D D → μ D

  Args : {O : Set} (R D : Desc O) → Set
  Args R (ι o) = ⊤
  Args R (σ A D) = Σ A (λ a → Args R (D a))
  Args R (δ A D) = Σ (A → μ R) (λ f → Args R (D (out R ∘ f)))
  
  out : {O : Set} (D : Desc O) → μ D → O
  out D (init xs) = out' D D xs

  out' : {O : Set} (R D : Desc O) → Args R D → O
  out' R (ι o) tt = o
  out' R (σ A D) (a , xs) = out' R (D a) xs
  out' R (δ A D) (f , xs) = out' R (D (λ a → out R (f a))) xs

----------------------------------------------------------------------

mutual
  data `Set : Set where
    `⊥ `⊤ `Bool : `Set
    `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `μ : {O : `Set} (D : `Desc O) → `Set 

  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `μ D ⟧ = μ ⟪ D ⟫

  data `Desc (O : `Set) : Set where
    `ι : (o : ⟦ O ⟧) → `Desc O
    `σ : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
    `δ : (A : `Set) (D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O)
      → `Desc O

  ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
  ⟪ `ι o ⟫ = ι o
  ⟪ `σ A D ⟫ = σ ⟦ A ⟧ (λ a → ⟪ D a ⟫)
  ⟪ `δ A D ⟫ = δ ⟦ A ⟧ (λ o → ⟪ D o ⟫)

----------------------------------------------------------------------

mutual
  data Path : (A : `Set) → ⟦ A ⟧ → Set where
    here : ∀{A a} → Path A a
    thereΠ : ∀{A B f}
      (g : (a : ⟦ A ⟧) → Path (B a) (f a))
      → Path (`Π A B) f
    thereμ : ∀{O} {D : `Desc O} {xs}
      (i : Path' D D xs)
      → Path (`μ D) (init xs)

  data Path' {O : `Set} (R : `Desc O)
    : (D : `Desc O) → Args ⟪ R ⟫ ⟪ D ⟫ → Set where
    thereσ₁ : ∀{A D a xs}
      (i : Path A a)
      → Path' R (`σ A D) (a , xs)
    thereσ₂ : ∀{A D a xs}
      (i : Path' R (D a) xs)
      → Path' R (`σ A D) (a , xs)
    thereδ₁ : ∀{A D f xs}
      (g : (a : ⟦ A ⟧) → Path (`μ R) (f a))
      → Path' R (`δ A D) (f , xs)
    thereδ₂ : ∀{A D f xs}
      (i : Path' R (D (out ⟪ R ⟫ ∘ f)) xs)
      → Path' R (`δ A D) (f , xs)

----------------------------------------------------------------------

mutual
  Lookup : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
  Lookup A a here = ⟦ A ⟧
  Lookup (`Π A B) f (thereΠ g) =
    (a : ⟦ A ⟧) → Lookup (B a) (f a) (g a)
  Lookup (`μ D) (init xs) (thereμ i) =
    Lookup' D D xs i

  lookup : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Lookup A a i
  lookup A a here = a
  lookup (`Π A B) f (thereΠ g) =
    λ a → lookup (B a) (f a) (g a)
  lookup (`μ D) (init xs) (thereμ i) =
    lookup' D D xs i

  Lookup' : {O : `Set} (R D : `Desc O) (xs : Args ⟪ R ⟫ ⟪ D ⟫)
    → Path' R D xs → Set
  Lookup' R (`σ A D) (a , xs) (thereσ₁ i) =
    Lookup A a i
  Lookup' R (`σ A D) (a , xs) (thereσ₂ i) =
    Lookup' R (D a) xs i
  Lookup' R (`δ A D) (f , xs) (thereδ₁ g) =
    (a : ⟦ A ⟧) → Lookup (`μ R) (f a) (g a)
  Lookup' R (`δ A D) (f , xs) (thereδ₂ i) =
    Lookup' R (D (out ⟪ R ⟫ ∘ f)) xs i

  lookup' : {O : `Set} (R D : `Desc O) (xs : Args ⟪ R ⟫ ⟪ D ⟫)
    (i : Path' R D xs) → Lookup' R D xs i
  lookup' R (`σ A D) (a , xs) (thereσ₁ i) =
    lookup A a i
  lookup' R (`σ A D) (a , xs) (thereσ₂ i) =
    lookup' R (D a) xs i
  lookup' R (`δ A D) (f , xs) (thereδ₁ g) =
    λ a → lookup (`μ R) (f a) (g a)
  lookup' R (`δ A D) (f , xs) (thereδ₂ i) =
    lookup' R (D (out ⟪ R ⟫ ∘ f)) xs i

----------------------------------------------------------------------

mutual
  Update : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
  Update A a here = Maybe ⟦ A ⟧
  Update (`Π A B) f (thereΠ g) =
    (a : ⟦ A ⟧) → Update (B a) (f a) (g a)
  Update (`μ D) (init xs) (thereμ i) =
    Update' D D xs i

  update : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
    → Update A a i → ⟦ A ⟧
  update A a here X = maybe id a X
  update (`Π A B) f (thereΠ g) h =
    λ a → update (B a) (f a) (g a) (h a)
  update (`μ D) (init xs) (thereμ i) X =
    init (update' D D xs i X)
  
  Update' : {O : `Set} (R D : `Desc O) (xs : Args ⟪ R ⟫ ⟪ D ⟫)
    → Path' R D xs → Set
  Update' R (`σ A D) (a , xs) (thereσ₁ i) =
    Σ (Update A a i)
      (λ a' → Args ⟪ R ⟫ ⟪ D a ⟫
            → Args ⟪ R ⟫ ⟪ D (update A a i a') ⟫)
  Update' R (`σ A D) (a , xs) (thereσ₂ i) =
    Update' R (D a) xs i
  Update' R (`δ A D) (f , xs) (thereδ₁ g) =
    Σ ((a : ⟦ A ⟧) → Update (`μ R) (f a) (g a))
      (λ h → let f' = λ a → update (`μ R) (f a) (g a) (h a)
          in Args ⟪ R ⟫ ⟪ D (out ⟪ R ⟫ ∘ f) ⟫
          →  Args ⟪ R ⟫ ⟪ D (out ⟪ R ⟫ ∘ f') ⟫)
  Update' R (`δ A D) (f , xs) (thereδ₂ i) =
    Update' R (D (out ⟪ R ⟫ ∘ f)) xs i

  update' : {O : `Set} (R D : `Desc O) (xs : Args ⟪ R ⟫ ⟪ D ⟫)
    (i : Path' R D xs) → Update' R D xs i → Args ⟪ R ⟫ ⟪ D ⟫
  update' R (`σ A D) (a , xs) (thereσ₁ i) (X , f) =
    update A a i X , f xs
  update' R (`σ A D) (a , xs) (thereσ₂ i) X =
    a , update' R (D a) xs i X
  update' R (`δ A D) (f , xs) (thereδ₁ g) (h , F) =
    (λ a → update (`μ R) (f a) (g a) (h a)) , F xs
  update' R (`δ A D) (f , xs) (thereδ₂ i) X =
    f , update' R (D (out ⟪ R ⟫ ∘ f)) xs i X

----------------------------------------------------------------------

