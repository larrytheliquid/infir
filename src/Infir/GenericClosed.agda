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
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; refl )
open import Relation.Binary.PropositionalEquality
module Infir.GenericClosed where

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

data Desc (O : Set) : Set₁ where
  End : (o : O) → Desc O
  Arg : (A : Set) (D : (a : A) → Desc O) → Desc O
  Rec : (A : Set) (D : (o : A → O) → Desc O) → Desc O

mutual
  data Data {O : Set} (D : Desc O) : Set where
    con : Data′ D D → Data D

  Data′ : {O : Set} (R D : Desc O) → Set
  Data′ R (End o) = ⊤
  Data′ R (Arg A D) = Σ A (λ a → Data′ R (D a))
  Data′ R (Rec A D) = Σ (A → Data R) (λ f → Data′ R (D (fun R ∘ f)))
  
  fun : {O : Set} (D : Desc O) → Data D → O
  fun D (con xs) = fun′ D D xs

  fun′ : {O : Set} (R D : Desc O) → Data′ R D → O
  fun′ R (End o) tt = o
  fun′ R (Arg A D) (a , xs) = fun′ R (D a) xs
  fun′ R (Rec A D) (f , xs) = fun′ R (D (λ a → fun R (f a))) xs

----------------------------------------------------------------------

mutual
  data `Set : Set where
    `Empty `Unit `Bool : `Set
    `Fun : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `Data : {O : `Set} (D : `Desc O) → `Set 

  ⟦_⟧ : `Set → Set
  ⟦ `Empty ⟧ = ⊥
  ⟦ `Unit ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `Data D ⟧ = Data ⟪ D ⟫

  data `Desc (O : `Set) : Set where
    `End : (o : ⟦ O ⟧) → `Desc O
    `Arg : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
    `Rec : (A : `Set) (D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O)
      → `Desc O

  ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
  ⟪ `End o ⟫ = End o
  ⟪ `Arg A D ⟫ = Arg ⟦ A ⟧ (λ a → ⟪ D a ⟫)
  ⟪ `Rec A D ⟫ = Rec ⟦ A ⟧ (λ o → ⟪ D o ⟫)

----------------------------------------------------------------------

mutual
  data Path : (A : `Set) → ⟦ A ⟧ → Set where
    here : ∀{A a} → Path A a
    thereFun : ∀{A B f}
      (g : (a : ⟦ A ⟧) → Path (B a) (f a))
      → Path (`Fun A B) f
    thereData : ∀{O} {D : `Desc O} {xs}
      (i : Path′ D D xs)
      → Path (`Data D) (con xs)

  data Path′ {O : `Set} (R : `Desc O)
    : (D : `Desc O) → Data′ ⟪ R ⟫ ⟪ D ⟫ → Set where
    thereArg₁ : ∀{A D a xs}
      (i : Path A a)
      → Path′ R (`Arg A D) (a , xs)
    thereArg₂ : ∀{A D a xs}
      (i : Path′ R (D a) xs)
      → Path′ R (`Arg A D) (a , xs)
    thereRec₁ : ∀{A D f xs}
      (g : (a : ⟦ A ⟧) → Path (`Data R) (f a))
      → Path′ R (`Rec A D) (f , xs)
    thereRec₂ : ∀{A D f xs}
      (i : Path′ R (D (fun ⟪ R ⟫ ∘ f)) xs)
      → Path′ R (`Rec A D) (f , xs)

----------------------------------------------------------------------

mutual
  Lookup : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
  Lookup A a here = ⟦ A ⟧
  Lookup (`Fun A B) f (thereFun g) =
    (a : ⟦ A ⟧) → Lookup (B a) (f a) (g a)
  Lookup (`Data D) (con xs) (thereData i) =
    Lookup′ D D xs i

  lookup : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Lookup A a i
  lookup A a here = a
  lookup (`Fun A B) f (thereFun g) =
    λ a → lookup (B a) (f a) (g a)
  lookup (`Data D) (con xs) (thereData i) =
    lookup′ D D xs i

  Lookup′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
    → Path′ R D xs → Set
  Lookup′ R (`Arg A D) (a , xs) (thereArg₁ i) =
    Lookup A a i
  Lookup′ R (`Arg A D) (a , xs) (thereArg₂ i) =
    Lookup′ R (D a) xs i
  Lookup′ R (`Rec A D) (f , xs) (thereRec₁ g) =
    (a : ⟦ A ⟧) → Lookup (`Data R) (f a) (g a)
  Lookup′ R (`Rec A D) (f , xs) (thereRec₂ i) =
    Lookup′ R (D (fun ⟪ R ⟫ ∘ f)) xs i

  lookup′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
    (i : Path′ R D xs) → Lookup′ R D xs i
  lookup′ R (`Arg A D) (a , xs) (thereArg₁ i) =
    lookup A a i
  lookup′ R (`Arg A D) (a , xs) (thereArg₂ i) =
    lookup′ R (D a) xs i
  lookup′ R (`Rec A D) (f , xs) (thereRec₁ g) =
    λ a → lookup (`Data R) (f a) (g a)
  lookup′ R (`Rec A D) (f , xs) (thereRec₂ i) =
    lookup′ R (D (fun ⟪ R ⟫ ∘ f)) xs i

----------------------------------------------------------------------

mutual
  Update : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
  Update A a here = Maybe ⟦ A ⟧
  Update (`Fun A B) f (thereFun g) =
    (a : ⟦ A ⟧) → Update (B a) (f a) (g a)
  Update (`Data D) (con xs) (thereData i) =
    Update′ D D xs i

  update : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
    → Update A a i → ⟦ A ⟧
  update A a here X = maybe id a X
  update (`Fun A B) f (thereFun g) h =
    λ a → update (B a) (f a) (g a) (h a)
  update (`Data D) (con xs) (thereData i) X =
    con (update′ D D xs i X)
  
  Update′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
    → Path′ R D xs → Set
  Update′ R (`Arg A D) (a , xs) (thereArg₁ i) =
    Σ (Update A a i)
      (λ a' → Data′ ⟪ R ⟫ ⟪ D a ⟫
            → Data′ ⟪ R ⟫ ⟪ D (update A a i a') ⟫)
  Update′ R (`Arg A D) (a , xs) (thereArg₂ i) =
    Update′ R (D a) xs i
  Update′ R (`Rec A D) (f , xs) (thereRec₁ g) =
    Σ ((a : ⟦ A ⟧) → Update (`Data R) (f a) (g a))
      (λ h → let f' = λ a → update (`Data R) (f a) (g a) (h a)
          in Data′ ⟪ R ⟫ ⟪ D (fun ⟪ R ⟫ ∘ f) ⟫
          →  Data′ ⟪ R ⟫ ⟪ D (fun ⟪ R ⟫ ∘ f') ⟫)
  Update′ R (`Rec A D) (f , xs) (thereRec₂ i) =
    Update′ R (D (fun ⟪ R ⟫ ∘ f)) xs i

  update′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
    (i : Path′ R D xs) → Update′ R D xs i → Data′ ⟪ R ⟫ ⟪ D ⟫
  update′ R (`Arg A D) (a , xs) (thereArg₁ i) (X , f) =
    update A a i X , f xs
  update′ R (`Arg A D) (a , xs) (thereArg₂ i) X =
    a , update′ R (D a) xs i X
  update′ R (`Rec A D) (f , xs) (thereRec₁ g) (h , F) =
    (λ a → update (`Data R) (f a) (g a) (h a)) , F xs
  update′ R (`Rec A D) (f , xs) (thereRec₂ i) X =
    f , update′ R (D (fun ⟪ R ⟫ ∘ f)) xs i X

----------------------------------------------------------------------

lift : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Update A a i
lem : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
  → a ≡ update A a i (lift A a i)
lift′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
  (i : Path′ R D xs) → Update′ R D xs i
lem′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
  (i : Path′ R D xs)
  → xs ≡ update′ R D xs i (lift′ R D xs i)

----------------------------------------------------------------------

lift A a here = nothing
lift (`Fun A B) f (thereFun g) = λ a → lift (B a) (f a) (g a)
lift (`Data D) (con xs) (thereData i) = lift′ D D xs i

lem A a here = refl
lem (`Fun A B) f (thereFun g) = ext (λ a → lem (B a) (f a) (g a))
lem (`Data D) (con xs) (thereData i) = cong con (lem′ D D xs i)

lift′ R (`Arg A D) (a , xs) (thereArg₁ i) =
  lift A a i
  , subst (λ X → Data′ ⟪ R ⟫ ⟪ D X ⟫) (lem A a i)
lift′ R (`Arg A D) (a , xs) (thereArg₂ i) = lift′ R (D a) xs i
lift′ R (`Rec A D) (f , xs) (thereRec₁ g) =
  (λ a → lift (`Data R) (f a) (g a))
  , subst (λ X → Data′ ⟪ R ⟫ ⟪ D X ⟫)
    (ext (λ a → cong (fun ⟪ R ⟫) (lem (`Data R) (f a) (g a))))
lift′ R (`Rec A D) (f , xs) (thereRec₂ i) = lift′ R (D (fun ⟪ R ⟫ ∘ f)) xs i

lem′ R (`Arg A D) (a , xs) (thereArg₁ i)
  with lem A a i
... | q =
  eqpair {B = λ a → Data′ ⟪ R ⟫ ⟪ D a ⟫} q
    (subst-id (λ X → Data′ ⟪ R ⟫ ⟪ D X ⟫) q xs)
lem′ R (`Arg A D) (a , xs) (thereArg₂ i) =
  cong (λ X → a , X) (lem′ R (D a) xs i)
lem′ R (`Rec A D) (f , xs) (thereRec₁ g)
  with ext (λ a → lem (`Data R) (f a) (g a))
  | ext (λ a → cong (fun ⟪ R ⟫) (lem (`Data R) (f a) (g a)))
... | q₁ | q₂ =
  eqpair {B = λ h → Data′ ⟪ R ⟫ ⟪ D (λ a → fun ⟪ R ⟫ (h a)) ⟫} q₁
    (subst-id (λ X → Data′ ⟪ R ⟫ ⟪ D X ⟫) q₂ xs)
lem′ R (`Rec A D) (f , xs) (thereRec₂ i) =
  cong (λ X → f , X) (lem′ R (D (fun ⟪ R ⟫ ∘ f)) xs i)

----------------------------------------------------------------------

forget : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Update A a i → Lookup A a i
forget′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫)
  (i : Path′ R D xs) → Update′ R D xs i → Lookup′ R D xs i

forget A a here X = maybe id a X
forget (`Fun A B) f (thereFun g) h = λ a → forget (B a) (f a) (g a) (h a)
forget (`Data D) (con xs) (thereData i) X = forget′ D D xs i X

forget′ R (`Arg A D) (a , xs) (thereArg₁ i) (X , f) = forget A a i X
forget′ R (`Arg A D) (a , xs) (thereArg₂ i) X = forget′ R (D a) xs i X
forget′ R (`Rec A D) (f , xs) (thereRec₁ g) (h , F) = λ a → forget (`Data R) (f a) (g a) (h a)
forget′ R (`Rec A D) (f , xs) (thereRec₂ i) X = forget′ R (D (λ z → fun ⟪ R ⟫ (f z))) xs i X

----------------------------------------------------------------------

thm : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
  → lookup A a i ≡ forget A a i (lift A a i) 
thm′ : {O : `Set} (R D : `Desc O) (xs : Data′ ⟪ R ⟫ ⟪ D ⟫) (i : Path′ R D xs)
  → lookup′ R D xs i ≡ forget′ R D xs i (lift′ R D xs i) 

thm A a here = refl
thm (`Fun A B) f (thereFun g) = ext (λ a → thm (B a) (f a) (g a))
thm (`Data D) (con xs) (thereData i) = thm′ D D xs i

thm′ R (`Arg A D) (a , xs) (thereArg₁ i) = thm A a i
thm′ R (`Arg A D) (a , xs) (thereArg₂ i) = thm′ R (D a) xs i
thm′ R (`Rec A D) (f , xs) (thereRec₁ g) = ext (λ a → thm (`Data R) (f a) (g a))
thm′ R (`Rec A D) (f , xs) (thereRec₂ i) = thm′ R (D (fun ⟪ R ⟫ ∘ f)) xs i

----------------------------------------------------------------------

postulate
  `ℕ : `Set
  `Fin : ⟦ `ℕ ⟧ → `Set
  prod : (n : ⟦ `ℕ ⟧) (f : ⟦ `Fin n ⟧ → ⟦ `ℕ ⟧) → ⟦ `ℕ ⟧

ArithD : `Desc `ℕ
ArithD = `Arg `Bool λ
  { true → `Arg `ℕ (λ n → `End n)
  ; false
    → `Rec `Unit λ n
    → `Rec (`Fin (n tt)) λ f
    → `End (prod (n tt) f)
  }

----------------------------------------------------------------------
