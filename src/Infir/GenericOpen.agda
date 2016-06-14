open import Level using ( _⊔_ )
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
module Infir.GenericOpen where

----------------------------------------------------------------------

postulate
  ext : {A : Set} {B : A → Set}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

Π : ∀{a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
Π A B = (a : A) → B a

prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (λ x → f (suc x))

eqpair : ∀{a b} {A : Set a} {B : A → Set b}
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
  data Path {O : Set} (D : Desc O) : Data D → Set₁ where
    here : ∀{x} → Path D x
    there : ∀{xs}
      → Path′ D D xs
      → Path D (con xs)

  data Path′ {O : Set} (R : Desc O) 
    : (D : Desc O) → Data′ R D → Set₁ where
    thereArg₁ : ∀{A D a xs}
      → Path′ R (Arg A D) (a , xs)
    thereArg₂ : ∀{A D a xs}
      (i : Path′ R (D a) xs)
      → Path′ R (Arg A D) (a , xs)
    thereRec₁ : ∀{A D f xs}
      (g : (a : A) → Path R (f a))
      → Path′ R (Rec A D) (f , xs)
    thereRec₂ : ∀{A D f xs}
      (i : Path′ R (D (fun R ∘ f)) xs)
      → Path′ R (Rec A D) (f , xs)

----------------------------------------------------------------------

mutual
  Lookup : {O : Set} (D : Desc O) (x : Data D) → Path D x → Set
  Lookup D x here = Data D
  Lookup D (con xs) (there i) = Lookup′ D D xs i

  lookup : {O : Set} (D : Desc O) (x : Data D) (i : Path D x)
    → Lookup D x i
  lookup D x here = x
  lookup D (con xs) (there i) = lookup′ D D xs i

  Lookup′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
    → Path′ R D xs → Set
  Lookup′ R (Arg A D) (a , xs) thereArg₁ = A
  Lookup′ R (Arg A D) (a , xs) (thereArg₂ i) =
    Lookup′ R (D a) xs i
  Lookup′ R (Rec A D) (f , xs) (thereRec₁ g) =
    (a : A) → Lookup R (f a) (g a)
  Lookup′ R (Rec A D) (f , xs) (thereRec₂ i) =
    Lookup′ R (D (fun R ∘ f)) xs i

  lookup′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
    (i : Path′ R D xs) → Lookup′ R D xs i
  lookup′ R (Arg A D) (a , xs) thereArg₁ = a
  lookup′ R (Arg A D) (a , xs) (thereArg₂ i) =
    lookup′ R (D a) xs i
  lookup′ R (Rec A D) (f , xs) (thereRec₁ g) =
    λ a → lookup R (f a) (g a)
  lookup′ R (Rec A D) (f , xs) (thereRec₂ i) =
    lookup′ R (D (fun R ∘ f)) xs i

----------------------------------------------------------------------

mutual
  Update : {O : Set} (D : Desc O) (x : Data D)
    → Path D x → Set
  Update D x here = Maybe (Data D)
  Update D (con xs) (there i) = Update′ D D xs i

  update : {O : Set} (D : Desc O) (x : Data D)
    (i : Path D x) (X : Update D x i) → Data D
  update D x here X = maybe id x X
  update D (con xs) (there i) X = con (update′ D D xs i X)

  Update′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
    → Path′ R D xs → Set
  Update′ R (Arg A D) (a , xs) thereArg₁ =
    Σ (Maybe A)
      (maybe (λ a' → Data′ R (D a) → Data′ R (D a')) ⊤)
  Update′ R (Arg A D) (a , xs) (thereArg₂ i) =
    Update′ R (D a) xs i
  Update′ R (Rec A D) (f , xs) (thereRec₁ g) =
    Σ ((a : A) → Update R (f a) (g a))
      (λ h → let f' = λ a → update R (f a) (g a) (h a)
           in Data′ R (D (fun R ∘ f))
           →  Data′ R (D (fun R ∘ f')))
  Update′ R (Rec A D) (f , xs) (thereRec₂ i) =
    Update′ R (D (fun R ∘ f)) xs i

  update′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
    (i : Path′ R D xs) → Update′ R D xs i → Data′ R D
  update′ R (Arg A D) (a , xs) thereArg₁ (nothing , f) =
    a , xs
  update′ R (Arg A D) (a , xs) thereArg₁ (just X , f) =
    X , f xs
  update′ R (Arg A D) (a , xs) (thereArg₂ i) X =
    a , update′ R (D a) xs i X
  update′ R (Rec A D) (f , xs) (thereRec₁ g) (h , F) =
    (λ a → update R (f a) (g a) (h a)) , F xs
  update′ R (Rec A D) (f , xs) (thereRec₂ i) X =
    f , update′ R (D (fun R ∘ f)) xs i X

----------------------------------------------------------------------

lift : {O : Set} (D : Desc O) (x : Data D) (i : Path D x) → Update D x i
lift′ : {O : Set} (R D : Desc O) (xs : Data′ R D) (i : Path′ R D xs)
  → Update′ R D xs i
lem : {O : Set} (D : Desc O) (x : Data D) (i : Path D x)
  → x ≡ update D x i (lift D x i)
lem′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
  (i : Path′ R D xs)
  → xs ≡ update′ R D xs i (lift′ R D xs i)

----------------------------------------------------------------------

lift D x here = nothing
lift D (con xs) (there i) = lift′ D D xs i

lift′ R (Arg A D) (a , xs) thereArg₁ = nothing , tt
lift′ R (Arg A D) (a , xs) (thereArg₂ i) = lift′ R (D a) xs i
lift′ R (Rec A D) (f , xs) (thereRec₁ g) =
  (λ a → lift R (f a) (g a))
  , subst (λ X → Data′ R (D X))
      (ext (λ a → cong (λ X → fun R X) (lem R (f a) (g a))))
lift′ R (Rec A D) (f , xs) (thereRec₂ i) = lift′ R (D (fun R ∘ f)) xs i

lem D x here = refl
lem D (con xs) (there i) = cong con (lem′ D D xs i)

lem′ R (Arg A D) (a , xs) thereArg₁ = refl
lem′ R (Arg A D) (a , xs) (thereArg₂ i) = cong (λ X → a , X) (lem′ R (D a) xs i)
lem′ R (Rec A D) (f , xs) (thereRec₁ g)
  with ext (λ a → lem R (f a) (g a)) | ext (λ a → cong (fun R) (lem R (f a) (g a)))
... | q₁ | q₂ = eqpair q₁ (subst-id (λ X → Data′ R (D X)) q₂ xs)
lem′ R (Rec A D) (f , xs) (thereRec₂ i) =
  cong (λ X → f , X) (lem′ R (D (fun R ∘ f)) xs i)

----------------------------------------------------------------------

forget : {O : Set} (D : Desc O) (x : Data D) (i : Path D x) → Update D x i → Lookup D x i
forget′ : {O : Set} (R D : Desc O) (xs : Data′ R D)
  (i : Path′ R D xs) → Update′ R D xs i → Lookup′ R D xs i

forget D x here nothing = x
forget D x here (just x') = x'
forget D (con xs) (there i) X = forget′ D D xs i X

forget′ R (Arg A D) (a , xs) thereArg₁ (nothing , tt) = a
forget′ R (Arg A D) (a , xs) thereArg₁ (just X , f) = X
forget′ R (Arg A D) (a , xs) (thereArg₂ i) X = forget′ R (D a) xs i X
forget′ R (Rec A D) (f , xs) (thereRec₁ g) (h , _) = λ a → forget R (f a) (g a) (h a)
forget′ R (Rec A D) (f , xs) (thereRec₂ i) X = forget′ R (D (fun R ∘ f)) xs i X

----------------------------------------------------------------------

thm : {O : Set} (D : Desc O) (x : Data D) (i : Path D x)
  → lookup D x i ≡ forget D x i (lift D x i) 
thm′ : {O : Set} (R D : Desc O) (xs : Data′ R D) (i : Path′ R D xs)
  → lookup′ R D xs i ≡ forget′ R D xs i (lift′ R D xs i) 

thm D x here = refl
thm D (con xs) (there i) = thm′ D D xs i

thm′ R (Arg A D) (a , xs) thereArg₁ = refl
thm′ R (Arg A D) (a , xs) (thereArg₂ i) = thm′ R (D a) xs i
thm′ R (Rec A D) (f , xs) (thereRec₁ g) = ext (λ a → thm R (f a) (g a))
thm′ R (Rec A D) (f , xs) (thereRec₂ i) = thm′ R (D (fun R ∘ f)) xs i

----------------------------------------------------------------------

data ArithT {ℓ} : Set ℓ where
  NumT ProdT : ArithT

ArithD : Desc ℕ
ArithD = Arg ArithT λ
  { NumT → Arg ℕ λ n → End n
  ; ProdT → Rec ⊤ λ a → Rec (Fin (a tt)) λ f → End (prod (a tt) f)
  }

----------------------------------------------------------------------
