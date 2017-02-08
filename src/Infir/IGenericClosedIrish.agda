open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
import Data.Product
open Data.Product public
module _ where

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

idx : ∀{I O} (R : Data I O) → Deps (desc R) → I
idx R xs = proj₁ (proj₂ R xs)

out : ∀{I O} (R : Data I O) → (xs : Deps (desc R)) → O (idx R xs)
out R xs = proj₂ (proj₂ R xs)

----------------------------------------------------------------------

mutual 
  data μ {I O} (R : Data I O) : I → Set where
    init : (xs : Args R (desc R)) → μ R (idx R (deps R (desc R) xs))
 
  Args : ∀{I O} (R : Data I O) (D : Desc I O) → Set
  Args R (ι i) = μ R i
  Args R (κ A) = A
  Args R (σ D E) = Σ (Args R D) (λ a → Args R (E (deps R D a)))
  Args R (π A D) = (a : A) → Args R (D a)
  
  deps : ∀{I O} (R : Data I O) (D : Desc I O) → Args R D → Deps D
  deps R (ι ._) (init xs) = out R (deps R (desc R) xs)
  deps R (κ A) a = a
  deps R (σ D E) (xs , ys) = deps R D xs , deps R (E (deps R D xs)) ys
  deps R (π A D) f = λ a → deps R (D a) (f a)

Hyps : ∀{I O} (R : Data I O) (P : (i : I) → μ R i → Set) (D : Desc I O) (xs : Args R D) → Set
Hyps R P (κ A) a = ⊤
Hyps R P (ι i) x = P i x
Hyps R P (σ D E) (xs , ys) = Hyps R P D xs × Hyps R P (E (deps R D xs)) ys
Hyps R P (π A D) f = (a : A) → Hyps R P (D a) (f a)

----------------------------------------------------------------------

mutual
  data `Set : Set where
    `⊥ `⊤ `Bool : `Set
    `μ : {I : `Set} {O : ⟦ I ⟧ → `Set} (R : `Data I O) (i : ⟦ I ⟧) → `Set 

  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `μ R i ⟧ = μ (⟨ R ⟩) i

  data `Desc (I : `Set) (O : ⟦ I ⟧ → `Set) : Set where
    `ι : (i : ⟦ I ⟧) → `Desc I O
    `κ : (A : `Set) → `Desc I O
    `σ : (D : `Desc I O) (E : Deps ⟪ D ⟫ → `Desc I O) → `Desc I O
    `π : (A : `Set) (D : ⟦ A ⟧ → `Desc I O) → `Desc I O

  ⟪_⟫ : ∀{I O} → `Desc I O → Desc ⟦ I ⟧ (λ i → ⟦ O i ⟧)
  ⟪ `ι i ⟫ = ι i
  ⟪ `κ A ⟫ = κ ⟦ A ⟧
  ⟪ `σ D E ⟫ = σ ⟪ D ⟫ (λ xs → ⟪ E xs ⟫)
  ⟪ `π A D ⟫ = π ⟦ A ⟧ (λ xs → ⟪ D xs ⟫)

  `Data : (I : `Set) (O : ⟦ I ⟧ → `Set) → Set
  `Data I O = Σ (`Desc I O) (λ D → Deps ⟪ D ⟫ → Σ ⟦ I ⟧ (λ i → ⟦ O i ⟧))

  ⟨_⟩ : {I : `Set} {O : ⟦ I ⟧ → `Set} → `Data I O → Data ⟦ I ⟧ (λ i → ⟦ O i ⟧)
  ⟨ (D , f) ⟩ = ⟪ D ⟫ , f

----------------------------------------------------------------------
