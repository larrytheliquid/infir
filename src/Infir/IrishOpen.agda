open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
module Infir.IrishOpen where

----------------------------------------------------------------------

mutual
  data Desc (I : Set) (O : I → Set) : Set₁ where
    ι : (i : I) → Desc I O
    κ : (A : Set) → Desc I O
    σ : (D : Desc I O) (E : Deps D → Desc I O) → Desc I O
    π : (A : Set) (D : A → Desc I O) → Desc I O
  
  Deps : ∀{I O} → Desc I O → Set
  Deps {O = O} (ι i) = O i
  Deps (κ A) = A
  Deps (σ D E) = Σ (Deps D) (λ a → Deps (E a))
  Deps (π A D) = (a : A) → Deps (D a)

Data : (I : Set) (O : I → Set) → Set₁
Data I O = Σ (Desc I O) (λ D → Deps D → Σ I (λ i → O i))

desc : ∀{I O} → Data I O → Desc I O
desc = proj₁

io : ∀{I O} (R : Data I O) → Deps (desc R) → Σ I (λ i → O i)
io = proj₂

io₁ : ∀{I O} (R : Data I O) → Deps (desc R) → I
io₁ R xs = proj₁ (io R xs)

io₂ : ∀{I O} (R : Data I O) → (xs : Deps (desc R)) → O (io₁ R xs)
io₂ R xs = proj₂ (io R xs)

----------------------------------------------------------------------

mutual 
  data μ {I O} (R : Data I O) : I → Set where
    init : (xs : Args R (desc R)) → μ R (io₁ R (deps R (desc R) xs))
 
  Args : ∀{I O} (R : Data I O) (D : Desc I O) → Set
  Args R (ι i) = μ R i
  Args R (κ A) = A
  Args R (σ D E) = Σ (Args R D) (λ a → Args R (E (deps R D a)))
  Args R (π A D) = (a : A) → Args R (D a)
  
  deps : ∀{I O} (R : Data I O) (D : Desc I O) → Args R D → Deps D
  deps R (ι ._) (init xs) = io₂ R (deps R (desc R) xs)
  deps R (κ A) a = a
  deps R (σ D E) (xs , ys) = deps R D xs , deps R (E (deps R D xs)) ys
  deps R (π A D) f = λ a → deps R (D a) (f a)

----------------------------------------------------------------------

mutual
  data `Desc (I : Set) (O : I → Set) : Set where
    `ι : (i : I) → `Desc I O
    `⊥ `⊤ `Bool : `Desc I O
    `μ : {I' : `Set} {O' : ⟦ I' ⟧ → `Set}
      (D : `Desc ⟦ I' ⟧ (λ i → ⟦ O' i ⟧))
      (f : Deps ⟪ D ⟫ → Σ ⟦ I' ⟧ (λ i → ⟦ O' i ⟧))
      (i : ⟦ I' ⟧)
      → `Desc I O
    `Σ : (D : `Desc I O) (E : Deps ⟪ D ⟫ → `Desc I O) → `Desc I O
    `Π : (A : `Set) (D : ⟦ A ⟧ → `Desc I O) → `Desc I O

  `Set : Set
  `Set = `Desc ⊤ (const ⊤)

  ⟦_⟧ : `Set → Set
  ⟦ A ⟧ = μ (⟪ A ⟫ , const (tt , tt)) tt
  
  ⟪_⟫ : ∀{I O} → `Desc I O → Desc I O
  ⟪ `ι i ⟫ = ι i
  ⟪ `⊥ ⟫ = κ ⊥
  ⟪ `⊤ ⟫ = κ ⊤
  ⟪ `Bool ⟫ = κ Bool
  ⟪ `μ D f i ⟫ = κ (μ (⟪ D ⟫ , f) i)
  ⟪ `Σ D E ⟫ = σ ⟪ D ⟫ (λ xs → ⟪ E xs ⟫)
  ⟪ `Π A D ⟫ = π ⟦ A ⟧ (λ xs → ⟪ D xs ⟫)

----------------------------------------------------------------------

mutual
  data Path {I O} (R : Data I O) : {i : I} → μ R i → Set₁ where
    *! : ∀{i} {x : μ R i} → Path R x
    init↓ : ∀{xs}
      → Path' R (desc R) xs
      → Path R (init xs)

  data Path' {I O} (R : Data I O)
    : (D : Desc I O) → Args R D → Set₁ where
    ι↓ : ∀{i} {x : μ R i}
      → Path R x
      → Path' R (ι i) x
    κ! : ∀{A a}
      → Path' R (κ A) a
    σ₁↓ : ∀{D E xs ys}
      → Path' R D xs
      → Path' R (σ D E) (xs , ys)
    σ₂↓ : ∀{D xs E ys}
      → Path' R (E (deps R D xs)) ys
      → Path' R (σ D E) (xs , ys)
    π↓ : ∀{A D f}
      (g : (a : A) → Path' R (D a) (f a))
      → Path' R (π A D) f

----------------------------------------------------------------------

mutual
  Lookup : ∀{I O i} {R : Data I O} (x : μ R i) → Path R x → Set
  Lookup {i = i} {R = R} x *! = μ R i
  Lookup (init xs) (init↓ p) = Lookup' xs p

  Lookup' : ∀{I O} {R : Data I O} {D : Desc I O} (xs : Args R D)
    → Path' R D xs → Set
  Lookup' x (ι↓ p) = Lookup x p
  Lookup' a (κ! {A = A}) = A
  Lookup' (xs , ys) (σ₁↓ p) = {!!}
  Lookup' (xs , ys) (σ₂↓ p) = {!!}
  Lookup' xs (π↓ f) = {!!}

----------------------------------------------------------------------
