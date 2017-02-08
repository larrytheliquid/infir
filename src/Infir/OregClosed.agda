open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool renaming ( true to tt ; false to ff )
open import Data.Product
open import Data.Maybe
module Infir.OregClosed where

----------------------------------------------------------------------

mutual
  data Desc (I : Set) (O : I → Set) : Bool → Set₁ where
    ι : (i : I) (o : O i) → Desc I O tt
    δ : (i : I) → Desc I O ff
    κ : (A : Set) → Desc I O ff
    σ : ∀{τ} (D : Desc I O ff) (E : Deps D → Desc I O τ) → Desc I O τ
    π : (A : Set) (D : A → Desc I O ff) → Desc I O ff
  
  Deps : ∀{I O} → Desc I O ff → Set
  Deps {O = O} (δ i) = O i
  Deps (κ A) = A
  Deps (σ D E) = Σ (Deps D) (λ a → Deps (E a))
  Deps (π A D) = (a : A) → Deps (D a)

----------------------------------------------------------------------

mutual 
  data μ {I O} (D : Desc I O tt) : I → Set where
    init : (xs : Args D D) → μ D (idx D D xs)

  Args : ∀{I O τ} (R : Desc I O tt) (D : Desc I O τ) → Set
  Args R (ι i o) = ⊤
  Args R (δ i) = μ R i
  Args R (κ A) = A
  Args R (σ D E) = Σ (Args R D) (λ xs → Args R (E (deps R D xs)))
  Args R (π A D) = (a : A) → Args R (D a)

  deps : ∀{I O} (R :  Desc I O tt) (D : Desc I O ff) → Args R D → Deps D
  deps R (δ .(idx R R xs)) (init xs) = out R R xs
  deps R (κ A) a = a
  deps R (σ D E) (xs , ys) = deps R D xs , deps R (E (deps R D xs)) ys
  deps R (π A D) f = λ a → deps R (D a) (f a)

  idx : ∀{I O} (R D : Desc I O tt) (xs : Args R D) → I
  idx R (ι i o) tt = i
  idx R (σ D E) (xs , ys) = idx R (E (deps R D xs)) ys

  out : ∀{I O} (R D : Desc I O tt) (xs : Args R D) → O (idx R D xs)
  out R (ι i o) tt = o
  out R (σ D E) (xs , ys) = out R (E (deps R D xs)) ys

----------------------------------------------------------------------

mutual
  data `Set : Set where
    `⊥ `⊤ `Bool : `Set
    `μ : ∀{I O} (D : `Desc I O tt) (i : ⟦ I ⟧) → `Set

  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `μ D i ⟧ = μ ⟪ D ⟫ i
  
  data `Desc (I : `Set) (O : ⟦ I ⟧ → `Set) : Bool → Set where
    `ι : (i : ⟦ I ⟧) (o : ⟦ O i ⟧) → `Desc I O tt
    `δ : (i : ⟦ I ⟧) → `Desc I O ff
    `κ : (A : `Set) → `Desc I O ff
    `σ : ∀{τ} (D : `Desc I O ff) (E : Deps ⟪ D ⟫ → `Desc I O τ) → `Desc I O τ
    `π : (A : `Set) (D : ⟦ A ⟧ → `Desc I O ff) → `Desc I O ff

  ⟪_⟫ : ∀{I O τ} → `Desc I O τ → Desc ⟦ I ⟧ (λ i → ⟦ O i ⟧) τ
  ⟪ `ι i o ⟫ = ι i o
  ⟪ `δ i ⟫ = δ i
  ⟪ `κ A ⟫ = κ ⟦ A ⟧
  ⟪ `σ D E ⟫ = σ ⟪ D ⟫ (λ xs → ⟪ E xs ⟫)
  ⟪ `π A D ⟫ = π ⟦ A ⟧ (λ xs → ⟪ D xs ⟫)

----------------------------------------------------------------------

mutual
  data Path : (A : `Set) → ⟦ A ⟧ → Set where
    *! : ∀{A a} → Path A a
    μ↓ : ∀{I O} {D : `Desc I O tt} {xs}
      → Path' D D xs
      → Path (`μ D (idx ⟪ D ⟫ ⟪ D ⟫ xs)) (init xs)

  data Path' {I O} (R : `Desc I O tt)
    : ∀{τ} (D : `Desc I O τ) → Args ⟪ R ⟫ ⟪ D ⟫ → Set where
    δ↓ : ∀{i} {x : μ ⟪ R ⟫ i}
      → Path (`μ R i) x
      → Path' R (`δ i) x
    κ! : ∀{A a}
      → Path A a
      → Path' R (`κ A) a
    σ₁↓ : ∀{D τ} {E : Deps ⟪ D ⟫ → `Desc I O τ} {xs ys}
      → Path' R D xs
      → Path' R (`σ D E) (xs , ys)
    σ₂↓ : ∀{D xs τ} {E : Deps ⟪ D ⟫ → `Desc I O τ} {ys}
      → Path' R (E (deps ⟪ R ⟫ ⟪ D ⟫ xs)) ys
      → Path' R (`σ D E) (xs , ys)
    π↓ : ∀{A D f}
      (g : (a : ⟦ A ⟧) → Path' R (D a) (f a))
      → Path' R (`π A D) f

----------------------------------------------------------------------

mutual
  Lookup : {A : `Set} (a : ⟦ A ⟧) → Path A a → Set
  Lookup {A = A} a *! = ⟦ A ⟧
  Lookup .(init xs) (μ↓ {xs = xs} p) = Lookup' xs p

  Lookup' : ∀{I O τ} {R : `Desc I O tt} {D : `Desc I O τ} (xs : Args ⟪ R ⟫ ⟪ D ⟫)
    → Path' R D xs → Set
  Lookup' x (δ↓ p) = Lookup x p
  Lookup' a (κ! p) = Lookup a p
  Lookup' (xs , ys) (σ₁↓ p) = Lookup' xs p 
  Lookup' (xs , ys) (σ₂↓ p) = Lookup' ys p
  Lookup' f (π↓ {A = A} g) = (a : ⟦ A ⟧) → Lookup' (f a) (g a)

  lookup : {A : `Set} (a : ⟦ A ⟧) (p : Path A a) → Lookup a p
  lookup x *! = x
  lookup .(init xs) (μ↓ {xs = xs} p) = lookup' xs p

  lookup' : ∀{I O τ} {R : `Desc I O tt} {D : `Desc I O τ}
    (xs : Args ⟪ R ⟫ ⟪ D ⟫) (p : Path' R D xs) → Lookup' xs p
  lookup' x (δ↓ p) = lookup x p
  lookup' a (κ! p) = lookup a p
  lookup' (xs , ys) (σ₁↓ p) = lookup' xs p
  lookup' (xs , ys) (σ₂↓ p) = lookup' ys p
  lookup' f (π↓ g) = λ a → lookup' (f a) (g a)

----------------------------------------------------------------------

mutual
  Content : {A : `Set}
    (a : ⟦ A ⟧) → Path A a → Set
  Content {A = A} a *! = Maybe ⟦ A ⟧
  Content .(init xs) (μ↓ {xs = xs} p) = Content' xs p

  Content' : ∀{I O τ} {R : `Desc I O tt} {D : `Desc I O τ}
    (xs : Args ⟪ R ⟫ ⟪ D ⟫) → Path' R D xs → Set
  Content' x (δ↓ p) = Content x p
  Content' a (κ! p) = Content a p
  Content' (xs , ys) (σ₁↓ p) = Content' xs p
  Content' (xs , ys) (σ₂↓ p) = Content' ys p
  Content' f (π↓ {A = A} g) = (a : ⟦ A ⟧) → Content' (f a) (g a)

  Update : {A : `Set}
    (a : ⟦ A ⟧) (p : Path A a)
    → Content a p → Set
  Update {A = A} a *! a' = ⟦ A ⟧
  Update .(init xs) (μ↓ {D = D} {xs = xs} p) xs'
    with update' xs p xs'
  ... | hm =
    μ ⟪ D ⟫ (idx ⟪ D ⟫ ⟪ D ⟫ {!!})

  Update' : ∀{I O τ} {R : `Desc I O tt} {D : `Desc I O τ}
    (xs : Args ⟪ R ⟫ ⟪ D ⟫) (p : Path' R D xs)
    → Content' xs p → Set
  Update' x (δ↓ p) x' = Update x p x'
  Update' a (κ! p) a' = Update a p a'
  Update' (xs , ys) (σ₁↓ p) xs' = {!!}
  Update' (xs , ys) (σ₂↓ p) ys' = {!!}
  Update' f (π↓ g) f' = {!!}

  update : {A : `Set}
    (a : ⟦ A ⟧) (p : Path A a)
    (a' : Content a p) → Update a p a'
  update a *! nothing = a
  update a *! (just a') = a'
  update .(init xs) (μ↓ {xs = xs} p) xs' =
    {!!}

  update' : ∀{I O τ} {R : `Desc I O tt} {D : `Desc I O τ}
    (xs : Args ⟪ R ⟫ ⟪ D ⟫) (p : Path' R D xs)
    (xs' : Content' xs p) → Args ⟪ R ⟫ ⟪ D ⟫ -- Update' xs p xs'
  update' x (δ↓ p) x' = {!!} -- update x p x'
  update' a (κ! p) a' = {!!} -- update a p a'
  update' (xs , ys) (σ₁↓ p) xs' = {!!}
  update' (xs , ys) (σ₂↓ p) ys' = {!!}
  update' f (π↓ g) f' = {!!}

----------------------------------------------------------------------
