open import Level using ( _⊔_ ; Lift ; lift )
  renaming ( zero to ∙ ; suc to ↑ )
open import Function
open import Data.String hiding ( show )
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat hiding ( _⊔_ )
open import Data.Fin hiding ( lift )
open import Data.Product
open import Data.Sum
open import Data.Maybe hiding ( Eq )
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; refl )
open import Relation.Binary.PropositionalEquality
module Infir.GenericOpenHier where

----------------------------------------------------------------------

prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (f ∘ suc)

----------------------------------------------------------------------

data Desc {ℓ} (O : Set ℓ) : Set (↑ ℓ) where
    End : (o : O) → Desc O
    Arg : (A : Set ℓ) (D : A → Desc O) → Desc O
    Rec : (A : Set ℓ) (D : (o : A → O) → Desc O) → Desc O  

mutual
  data Data {ℓ} {O : Set ℓ} (D : Desc O) : Set ℓ where
    con : Data′ D D → Data D

  Data′ : ∀{ℓ} {O : Set ℓ} (R D : Desc O) → Set ℓ
  Data′ R (End o) = Lift ⊤
  Data′ R (Arg A D) = Σ A (λ a → Data′ R (D a))
  Data′ R (Rec A D) = Σ (A → Data R) (λ f → Data′ R (D (fun R ∘ f)))
  
  fun : ∀{ℓ} {O : Set ℓ} (D : Desc O) → Data D → O
  fun D (con xs) = fun′ D D xs

  fun′ : ∀{ℓ} {O : Set ℓ} (R D : Desc O) → Data′ R D → O
  fun′ R (End o) (lift tt) = o
  fun′ R (Arg A D) (a , xs) = fun′ R (D a) xs
  fun′ R (Rec A D) (f , xs) = fun′ R (D (λ a → fun R (f a))) xs

----------------------------------------------------------------------

mutual
  data Path {ℓ} {O : Set ℓ} (D : Desc O) : Data D → Set (↑ ℓ) where
    here : {x : Data D} → Path D x
    there : {xs : Data′ D D}
      → Path′ D D xs
      → Path D (con xs)
  
  data Path′ {ℓ} {O : Set ℓ} (R : Desc O) : (D : Desc O) → Data′ R D → Set (↑ ℓ) where
    thereArg₁ : {A : Set ℓ} {D : A → Desc O}
      {a : A} {xs : Data′ R (D a)}
      → Path′ R (Arg A D) (a , xs)
    thereArg₂ : {A : Set ℓ} {D : A → Desc O}
      {a : A} {xs : Data′ R (D a)}
      → Path′ R (D a) xs
      → Path′ R (Arg A D) (a , xs)
    thereRec₁ : {A : Set ℓ} {D : (o : A → O) → Desc O}
      {f : A → Data R} {xs : Data′ R (D (fun R ∘ f))}
      → ((a : A) → Path R (f a))
      → Path′ R (Rec A D) (f , xs)
    thereRec₂ : {A : Set ℓ} {D : (o : A → O) → Desc O}
      {f : A → Data R} {xs : Data′ R (D (fun R ∘ f)) }
      → Path′ R (D (fun R ∘ f)) xs
      → Path′ R (Rec A D) (f , xs)

----------------------------------------------------------------------

mutual
  Lookup : ∀{ℓ} {O : Set ℓ} (D : Desc O) (x : Data D) → Path D x → Set ℓ
  Lookup′ : ∀{ℓ} {O : Set ℓ} (R D : Desc O) (xs : Data′ R D) → Path′ R D xs → Set ℓ
  
  Lookup D x here = Data D
  Lookup D (con xs) (there i) = Lookup′ D D xs i
  
  Lookup′ R (End o) (lift tt) ()
  Lookup′ R (Arg A D) (a , xs) thereArg₁ = A
  Lookup′ R (Arg A D) (a , xs) (thereArg₂ i) = Lookup′ R (D a) xs i
  Lookup′ R (Rec A D) (f , xs) (thereRec₁ g) = (a : A) → Lookup R (f a) (g a)
  Lookup′ R (Rec A D) (f , xs) (thereRec₂ i) = Lookup′ R (D (fun R ∘ f)) xs i

  lookup : ∀{ℓ} {O : Set ℓ} (D : Desc O) (x : Data D) (i : Path D x) → Lookup D x i
  lookup′ : ∀{ℓ} {O : Set ℓ} (R D : Desc O) (xs : Data′ R D) (i : Path′ R D xs)
    → Lookup′ R D xs i
  
  lookup D x here = x
  lookup D (con xs) (there i) = lookup′ D D xs i
  
  lookup′ R (End o) (lift tt) ()
  lookup′ R (Arg A D) (a , xs) thereArg₁ = a
  lookup′ R (Arg A D) (a , xs) (thereArg₂ i) = lookup′ R (D a) xs i
  lookup′ R (Rec A D) (f , xs) (thereRec₁ g) = λ a → lookup R (f a) (g a)
  lookup′ R (Rec A D) (f , xs) (thereRec₂ i) = lookup′ R (D (fun R ∘ f)) xs i

----------------------------------------------------------------------

mutual
  Update : ∀{ℓ} {O : Set ℓ} (D : Desc O) (x : Data D) → Path D x → Set ℓ
  Update′ : ∀{ℓ} {O : Set ℓ} (R D : Desc O) (xs : Data′ R D) → Path′ R D xs → Set ℓ
  update : ∀{ℓ} {O : Set ℓ} (D : Desc O) (x : Data D) (i : Path D x) (X : Update D x i) → Data D
  update′ : ∀{ℓ} {O : Set ℓ} (R D : Desc O) (xs : Data′ R D) (i : Path′ R D xs)
    → Update′ R D xs i → Data′ R D
  
  Update D x here = Maybe (Data D)
  Update D (con xs) (there i) = Update′ D D xs i
  
  Update′ R (End o) (lift tt) ()
  Update′ R (Arg A D) (a , xs) thereArg₁ =
    Σ (Maybe A)
      (maybe (λ a' → Data′ R (D a) → Data′ R (D a')) (Lift ⊤))
  Update′ R (Arg A D) (a , xs) (thereArg₂ i) = Update′ R (D a) xs i
  Update′ R (Rec A D) (f , xs) (thereRec₁ g) =
    Σ ((a : A) → Update R (f a) (g a))
      (λ h → Data′ R (D (fun R ∘ f))
        → Data′ R (D (λ a → fun R (update R (f a) (g a) (h a)))))
  Update′ R (Rec A D) (f , xs) (thereRec₂ i) =
    Update′ R (D (fun R ∘ f)) xs i
  
  update D x here X = maybe id x X
  update D (con xs) (there i) X = con (update′ D D xs i X)
  
  update′ R (End o) (lift tt) () X
  update′ R (Arg A D) (a , xs) thereArg₁ (nothing , f) = a , xs
  update′ R (Arg A D) (a , xs) thereArg₁ (just X , f) =
    X , f xs
  update′ R (Arg A D) (a , xs) (thereArg₂ i) X =
    a , update′ R (D a) xs i X
  update′ R (Rec A D) (f , xs) (thereRec₁ g) (h , F) =
    (λ a → update R (f a) (g a) (h a)) , F xs
  update′ R (Rec A D) (f , xs) (thereRec₂ i) X =
    f , update′ R (D (fun R ∘ f)) xs i X

----------------------------------------------------------------------

data TypeT : Set₁ where
  BaseT FunT : TypeT

TypeD : Desc Set
TypeD = Arg TypeT λ
  { BaseT → Arg Set (λ A → End A)
  ; FunT
    → Rec (Lift ⊤) λ A
    → Rec (Lift (A (lift tt))) λ B
    → End ((a : A (lift tt)) → B (lift a))
  }

----------------------------------------------------------------------

data ArithT : Set where
  NumT ProdT : ArithT

ArithD : Desc ℕ
ArithD = Arg ArithT λ
  { NumT → Arg ℕ (λ n → End n)
  ; ProdT
    → Rec (Lift ⊤) λ n
    → Rec (Fin (n (lift tt))) λ f
    → End (prod (n (lift tt)) f)
  }

----------------------------------------------------------------------
