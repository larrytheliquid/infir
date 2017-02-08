open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool renaming ( true to tt ; false to ff )
open import Data.Product
open import Data.Maybe
module Infir.OregOpen where

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
  data Path {I O} (R : Desc I O tt) : {i : I} → μ R i → Set₁ where
    *! : ∀{i} {x : μ R i} → Path R x
    init↓ : ∀{xs}
      → Path' R R xs
      → Path R (init xs)

  data Path' {I O} (R : Desc I O tt)
    : ∀{τ} (D : Desc I O τ) → Args R D → Set₁ where
    δ↓ : ∀{i} {x : μ R i}
      → Path R x
      → Path' R (δ i) x
    κ! : ∀{A a}
      → Path' R (κ A) a
    σ₁↓ : ∀{D τ} {E : Deps D → Desc I O τ} {xs ys}
      → Path' R D xs
      → Path' R (σ D E) (xs , ys)
    σ₂↓ : ∀{D xs τ} {E : Deps D → Desc I O τ} {ys}
      → Path' R (E (deps R D xs)) ys
      → Path' R (σ D E) (xs , ys)
    π↓ : ∀{A D f}
      (g : (a : A) → Path' R (D a) (f a))
      → Path' R (π A D) f

----------------------------------------------------------------------

mutual
  Lookup : ∀{I O i} {R : Desc I O tt} (x : μ R i) → Path R x → Set
  Lookup {i = i} {R = R} x *! = μ R i
  Lookup (init xs) (init↓ p) = Lookup' xs p

  Lookup' : ∀{I O τ} {R : Desc I O tt} {D : Desc I O τ} (xs : Args R D)
    → Path' R D xs → Set
  Lookup' x (δ↓ p) = Lookup x p
  Lookup' a (κ! {A = A}) = A
  Lookup' (xs , ys) (σ₁↓ p) = Lookup' xs p 
  Lookup' (xs , ys) (σ₂↓ p) = Lookup' ys p
  Lookup' f (π↓ {A = A} g) = (a : A) → Lookup' (f a) (g a)

  lookup : ∀{I O i} {R : Desc I O tt} (x : μ R i) (p : Path R x) → Lookup x p
  lookup x *! = x
  lookup (init xs) (init↓ p) = lookup' xs p

  lookup' : ∀{I O τ} {R : Desc I O tt} {D : Desc I O τ}
    (xs : Args R D) (p : Path' R D xs) → Lookup' xs p
  lookup' x (δ↓ p) = lookup x p
  lookup' a κ! = a
  lookup' (xs , ys) (σ₁↓ p) = lookup' xs p
  lookup' (xs , ys) (σ₂↓ p) = lookup' ys p
  lookup' f (π↓ g) = λ a → lookup' (f a) (g a)

----------------------------------------------------------------------

mutual
  Content : ∀{I O i} {R : Desc I O tt} (x : μ R i) → Path R x → Set
  Content {i = i} {R = R} x *! = Maybe (μ R i)
  Content (init xs) (init↓ p) = Content' xs p

  Content' : ∀{I O τ} {R : Desc I O tt} {D : Desc I O τ} (xs : Args R D)
    → Path' R D xs → Set
  Content' x (δ↓ p) = Content x p
  Content' a (κ! {A = A}) = A
  Content' (xs , ys) (σ₁↓ p) = Content' xs p
  Content' (xs , ys) (σ₂↓ p) = Content' ys p
  Content' f (π↓ {A = A} g) = (a : A) → Content' (f a) (g a)

  replace : ∀{I O i} {R : Desc I O tt}
    (x : μ R i) (p : Path R x) → Content x p → μ R i
  replace x p hm = {!!}

  replace' : ∀{I O τ} {R : Desc I O tt} {D : Desc I O τ}
    (xs : Args R D) (p : Path' R D xs) → Content' xs p → Args R D
  replace' x (δ↓ p) x' = {!!}
  replace' a κ! a' = a'
  replace' (xs , ys) (σ₁↓ p) xs' = {!!}
  replace' (xs , ys) (σ₂↓ p) ys' = xs , replace' ys p ys'
  replace' f (π↓ g) f' = λ a → replace' (f a) (g a) (f' a)


----------------------------------------------------------------------
