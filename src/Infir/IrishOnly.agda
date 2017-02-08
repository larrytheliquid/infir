open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
module Infir.IrishOnly where

----------------------------------------------------------------------

mutual
  data Desc (I : Set) (O : I → Set) : Bool → Set₁ where
    ε : (i : I) (o : O i) → Desc I O true
    ι : (i : I) → Desc I O false
    κ : (A : Set) → Desc I O false
    σ : ∀{τ} (D : Desc I O false) (E : Deps D → Desc I O τ) → Desc I O τ
    π : (A : Set) (D : A → Desc I O false) → Desc I O false
  
  Deps : ∀{I O} → Desc I O false → Set
  Deps {O = O} (ι i) = O i
  Deps (κ A) = A
  Deps (σ D E) = Σ (Deps D) (λ a → Deps (E a))
  Deps (π A D) = (a : A) → Deps (D a)

----------------------------------------------------------------------

module idx-only where
  mutual 
    data μ {I O} (D : Desc I O true) : I → Set where
      init : (xs : Args D D) → μ D (proj₁ (idx D D xs))
  
    Args : ∀{I O τ} (R : Desc I O true) (D : Desc I O τ) → Set
    Args R (ε i o) = ⊤
    Args R (ι i) = μ R i
    Args R (κ A) = A
    Args R (σ D E) = Σ (Args R D) (λ xs → Args R (E (deps R D xs)))
    Args R (π A D) = (a : A) → Args R (D a)

    deps : ∀{I O} (R :  Desc I O true) (D : Desc I O false) → Args R D → Deps D
    deps R (ι .(proj₁ (idx R R xs))) (init xs) = proj₂ (idx R R xs)
    deps R (κ A) a = a
    deps R (σ D E) (xs , ys) = deps R D xs , deps R (E (deps R D xs)) ys
    deps R (π A D) f = λ a → deps R (D a) (f a)
  
    idx : ∀{I O} (R D : Desc I O true) (xs : Args R D) → Σ I O
    idx R (ε i o) tt = i , o
    idx R (σ D E) (xs , ys) = idx R (E (deps R D xs)) ys

mutual 
  data μ {I O} (D : Desc I O true) : I → Set where
    init : (xs : Args D D) → μ D (idx D D xs)

  Args : ∀{I O τ} (R : Desc I O true) (D : Desc I O τ) → Set
  Args R (ε i o) = ⊤
  Args R (ι i) = μ R i
  Args R (κ A) = A
  Args R (σ D E) = Σ (Args R D) (λ xs → Args R (E (deps R D xs)))
  Args R (π A D) = (a : A) → Args R (D a)

  deps : ∀{I O} (R :  Desc I O true) (D : Desc I O false) → Args R D → Deps D
  deps R (ι .(idx R R xs)) (init xs) = out R R xs
  deps R (κ A) a = a
  deps R (σ D E) (xs , ys) = deps R D xs , deps R (E (deps R D xs)) ys
  deps R (π A D) f = λ a → deps R (D a) (f a)

  idx : ∀{I O} (R D : Desc I O true) (xs : Args R D) → I
  idx R (ε i o) tt = i
  idx R (σ D E) (xs , ys) = idx R (E (deps R D xs)) ys

  out : ∀{I O} (R D : Desc I O true) (xs : Args R D) → O (idx R D xs)
  out R (ε i o) tt = o
  out R (σ D E) (xs , ys) = out R (E (deps R D xs)) ys

----------------------------------------------------------------------

mutual
  data `Desc (I : Set) (O : I → Set) : Bool → Set where
    `ε : (i : I) (o : O i) → `Desc I O true
    `ι : (i : I) → `Desc I O false
    `⊥ `⊤ `Bool : `Desc I O false
    `μ : {I' : `Set} {O' : ⟦ I' ⟧ → `Set}
      (D : `Desc ⟦ I' ⟧ (λ i → ⟦ O' i ⟧) true) (i : ⟦ I' ⟧) → `Desc I O false
    `Σ : ∀{τ} (D : `Desc I O false) (E : Deps ⟪ D ⟫ → `Desc I O τ) → `Desc I O τ
    `Π : (A : `Set) (D : ⟦ A ⟧ → `Desc I O false) → `Desc I O false

  `Set : Set
  `Set = `Desc ⊤ (const ⊤) true

  ⟦_⟧ : `Set → Set
  ⟦ A ⟧ = μ ⟪ A ⟫ tt
  
  ⟪_⟫ : ∀{I O τ} → `Desc I O τ → Desc I O τ
  ⟪ `ε i o ⟫ = ε i o
  ⟪ `ι i ⟫ = ι i
  ⟪ `⊥ ⟫ = κ ⊥
  ⟪ `⊤ ⟫ = κ ⊤
  ⟪ `Bool ⟫ = κ Bool
  ⟪ `μ D i ⟫ = κ (μ ⟪ D ⟫ i)
  ⟪ `Σ D E ⟫ = σ ⟪ D ⟫ (λ xs → ⟪ E xs ⟫)
  ⟪ `Π A D ⟫ = π ⟦ A ⟧ (λ xs → ⟪ D xs ⟫)


----------------------------------------------------------------------
