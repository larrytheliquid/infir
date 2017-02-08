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
module Infir.IGenericOpen where

----------------------------------------------------------------------

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

----------------------------------------------------------------------

data Desc (I : Set) (O : I → Set) : Set₁ where
  ι : (i : I) (o : O i) → Desc I O
  σ : (A : Set) (D : (a : A) → Desc I O) → Desc I O
  δ : (A : Set) (i : A → I) (D : (o : (a : A) → O (i a)) → Desc I O) → Desc I O

mutual
  data μ {I O} (D : Desc I O) : I → Set where
    init : (xs : Args D D) → μ D (idx D D xs)

  Args : ∀{I O} (R D : Desc I O) → Set
  Args R (ι i o) = ⊤
  Args R (σ A D) = Σ A (λ a → Args R (D a))
  Args R (δ A i D) = Σ ((a : A) → μ R (i a)) (λ f → Args R (D (out ∘ f)))
  
  out : ∀{I O} {D : Desc I O} {i} → μ D i → O i
  out {D = D} (init xs) = out' D D xs

  idx : ∀{I O} (R D : Desc I O) (xs : Args R D) → I
  idx R (ι i o) tt = i
  idx R (σ A D) (a , xs) = idx R (D a) xs
  idx R (δ A i D) (f , xs) = idx R (D (λ a → out (f a))) xs

  out' : ∀{I O} (R D : Desc I O) (xs : Args R D) → O (idx R D xs)
  out' R (ι i o) tt = o
  out' R (σ A D) (a , xs) = out' R (D a) xs
  out' R (δ A i D) (f , xs) = out' R (D (λ a → out (f a))) xs

----------------------------------------------------------------------

mutual
  data `Set : Set where
    `⊥ `⊤ `Bool : `Set
    `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `μ : {I : `Set} {O : ⟦ I ⟧ → `Set} (D : `Desc I O) (i : ⟦ I ⟧) → `Set 

  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `μ D i ⟧ = μ ⟪ D ⟫ i

  data `Desc (I : `Set) (O : ⟦ I ⟧ → `Set) : Set where
    `ι : (i : ⟦ I ⟧) (o : ⟦ O i ⟧) → `Desc I O
    `σ : (A : `Set) (D : ⟦ A ⟧ → `Desc I O) → `Desc I O
    `δ : (A : `Set) (i : ⟦ A ⟧ → ⟦ I ⟧) (D : (o : (a : ⟦ A ⟧) → ⟦ O (i a) ⟧) → `Desc I O)
      → `Desc I O

  ⟪_⟫ : ∀{I O} → `Desc I O → Desc ⟦ I ⟧ (λ i → ⟦ O i ⟧)
  ⟪ `ι i o ⟫ = ι i o
  ⟪ `σ A D ⟫ = σ ⟦ A ⟧ (λ a → ⟪ D a ⟫)
  ⟪ `δ A i D ⟫ = δ ⟦ A ⟧ i (λ o → ⟪ D o ⟫)

----------------------------------------------------------------------

mutual
  data Path : (A : `Set) → ⟦ A ⟧ → Set where
    here : ∀{A a} → Path A a
    there : ∀{I O} {D : `Desc I O} {xs}
      (p : Path' D D xs)
      → Path (`μ D (idx ⟪ D ⟫ ⟪ D ⟫ xs)) (init xs)

  data Path' {I O} (R : `Desc I O)
    : (D : `Desc I O) → Args ⟪ R ⟫ ⟪ D ⟫ → Set where
    thereσ₁ : ∀{A D a xs}
      (p : Path A a)
      → Path' R (`σ A D) (a , xs)
    thereσ₂ : ∀{A D a xs}
      (p : Path' R (D a) xs)
      → Path' R (`σ A D) (a , xs)
    thereδ₁ : ∀{A i D f xs}
      (g : (a : ⟦ A ⟧) → Path (`μ R (i a)) (f a))
      → Path' R (`δ A i D) (f , xs)
    thereδ₂ : ∀{A i D f xs}
      (p : Path' R (D (out ∘ f)) xs)
      → Path' R (`δ A i D) (f , xs)

----------------------------------------------------------------------

-- mutual
--   Lookup : {A : `Set} (a : ⟦ A ⟧) → Path A a → Set
--   Lookup {A = A} a here = ⟦ A ⟧
--   Lookup f (thereΠ {A = A} g) =
--     Π ⟦ A ⟧ λ a → Lookup (f a) (g a)
--   Lookup .(init xs) (thereμ {xs = xs} p) =
--     Lookup' xs p

--   lookup : {A : `Set} (a : ⟦ A ⟧) (i : Path A a)
--     → Lookup a i
--   lookup {A = A} a here = a
--   lookup f (thereΠ g) =
--     λ a → lookup (f a) (g a)
--   lookup .(init xs) (thereμ {xs = xs} p) =
--     lookup' xs p
  
--   Lookup' : ∀{I O} {R D : `Desc I O} (xs : Args ⟪ R ⟫ ⟪ D ⟫)
--     → Path' R D xs → Set
--   Lookup' {R = R} (a , xs) (thereσ₁ {D = D} p) =
--     Lookup a p
--   Lookup' (a , xs) (thereσ₂ p) =
--     Lookup' xs p
--   Lookup' {R = R} (f , xs) (thereδ₁ {A = A} {D = D} g) =
--     Π ⟦ A ⟧ λ a → Lookup (f a) (g a)
--   Lookup' (f , xs) (thereδ₂ p) =
--     Lookup' xs p

--   lookup' : ∀{I O} {R D : `Desc I O}
--     (xs : Args ⟪ R ⟫ ⟪ D ⟫) (i : Path' R D xs)
--     → Lookup' xs i
--   lookup' (a , xs) (thereσ₁ p) =
--     lookup a p
--   lookup' (a , xs) (thereσ₂ p) =
--     lookup' xs p
--   lookup' (f , xs) (thereδ₁ g) =
--     λ a → lookup (f a) (g a)
--   lookup' (f , xs) (thereδ₂ p) =
--     lookup' xs p

-- ----------------------------------------------------------------------

-- mutual
--   Update : {A : `Set} (a : ⟦ A ⟧) → Path A a → Set
--   Update {A = A} a here = ⟦ A ⟧ → ⟦ A ⟧
--   Update f (thereΠ {A = A} g) =
--     Π ⟦ A ⟧ λ a → Update (f a) (g a)
--   Update .(init xs) (thereμ {xs = xs} p) =
--     Update' xs p

--   update : {A : `Set} (a : ⟦ A ⟧) (i : Path A a)
--     → Update a i → ⟦ A ⟧
--   update {A = A} a here f = f a
--   update f (thereΠ g) f' =
--     λ a → update (f a) (g a) (f' a)
--   update .(init xs) (thereμ {xs = xs} p) xs'
--     with update' xs p xs' | pres xs p xs'
--   ... | ys | q rewrite q = init ys
  
--   Update' : ∀{I O} {R D : `Desc I O} (xs : Args ⟪ R ⟫ ⟪ D ⟫)
--     → Path' R D xs → Set
--   Update' {R = R} (a , xs) (thereσ₁ {D = D} p) =
--     Σ (Update a p) λ a' →
--     Π (Args ⟪ R ⟫ ⟪ D a ⟫) λ xs →
--     Σ (Args ⟪ R ⟫ ⟪ D (update a p a') ⟫) λ ys →
--     idx ⟪ R ⟫ ⟪ D a ⟫ xs ≡ idx ⟪ R ⟫ ⟪ D (update a p a') ⟫ ys
--   Update' (a , xs) (thereσ₂ p) =
--     Update' xs p
--   Update' {R = R} (f , xs) (thereδ₁ {A = A} {D = D} g) =
--     Σ (Π ⟦ A ⟧ λ a → Update (f a) (g a)) λ f' →
--     let h = λ a → update (f a) (g a) (f' a) in
--     Π (Args ⟪ R ⟫ ⟪ D (out ∘ f) ⟫) λ xs →
--     Σ (Args ⟪ R ⟫ ⟪ D (out ∘ h) ⟫) λ ys →
--     idx ⟪ R ⟫ ⟪ D (out ∘ f) ⟫ xs ≡ idx ⟪ R ⟫ ⟪ D (out ∘ h) ⟫ ys
--   Update' (f , xs) (thereδ₂ p) =
--     Update' xs p

--   update' : ∀{I O} {R D : `Desc I O}
--     (xs : Args ⟪ R ⟫ ⟪ D ⟫) (i : Path' R D xs)
--     → Update' xs i
--     → Args ⟪ R ⟫ ⟪ D ⟫
--   update' (a , xs) (thereσ₁ p) (a' , f) =
--     update a p a' , proj₁ (f xs)
--   update' (a , xs) (thereσ₂ p) xs' =
--     a , update' xs p xs'
--   update' (f , xs) (thereδ₁ g) (f' , h) =
--     (λ a → update (f a) (g a) (f' a)) , proj₁ (h xs)
--   update' (f , xs) (thereδ₂ p) xs' =
--     f , update' xs p xs'

--   pres : ∀{I O} {R D : `Desc I O}
--     (xs : Args ⟪ R ⟫ ⟪ D ⟫)
--     (i : Path' R D xs)
--     (xs' : Update' xs i)
--     → idx ⟪ R ⟫ ⟪ D ⟫ xs ≡ idx ⟪ R ⟫ ⟪ D ⟫ (update' xs i xs')
--   pres (a , xs) (thereσ₁ p) (a' , f) = proj₂ (f xs)
--   pres (a , xs) (thereσ₂ p) xs' = pres xs p xs'
--   pres (f , xs) (thereδ₁ g) (f' , h) = proj₂ (h xs)
--   pres (f , xs) (thereδ₂ p) xs' = pres xs p xs'

-- ----------------------------------------------------------------------

