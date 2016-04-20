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
  Arg : (A : Set) (D : A → Desc O) → Desc O
  Rec : (A : Set) (D : (o : A → O) → Desc O) → Desc O

Func : {O : Set} (D : Desc O) (X : Set) (Y : X → O) → Set
Func (End o) X Y = ⊤
Func (Arg A D) X Y = Σ A (λ a → Func (D a) X Y)
Func (Rec A D) X Y = Σ (A → X) λ f → Func (D (λ a → Y (f a))) X Y

mutual
  data μ {O : Set} (D : Desc O) : Set where
    init : Func D (μ D) (rec D) → μ D
  
  rec : {O : Set} (D : Desc O) → μ D → O
  rec D (init xs) = recα D D xs

  recα : {O : Set} (D E : Desc O) → Func D (μ E) (rec E) → O
  recα (End o) E tt = o
  recα (Arg A D) E (a , xs) = recα (D a) E xs
  recα (Rec A D) E (f , xs) = recα (D (λ a → rec E (f a))) E xs

----------------------------------------------------------------------

mutual
  data `Set : Set where
    `⊥ `⊤ `Bool : `Set
    `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `μ : {O : `Set} (D : `Desc O) → `Set

  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
  ⟦ `Π A B ⟧ = Π ⟦ A ⟧ (λ a → ⟦ B a ⟧)
  ⟦ `μ D ⟧ = μ ⟪ D ⟫

  data `Desc (O : `Set) : Set where
    `End : (o : ⟦ O ⟧) → `Desc O
    `Arg : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
    `Rec : (A : `Set) (D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O) → `Desc O

  ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
  ⟪ `End o ⟫ = End o
  ⟪ `Arg A D ⟫ = Arg ⟦ A ⟧ λ a → ⟪ D a ⟫
  ⟪ `Rec A D ⟫ = Rec ⟦ A ⟧ λ o → ⟪ D o ⟫

----------------------------------------------------------------------

data Path : (A : `Set) → ⟦ A ⟧ → Set
data Pathα {O : `Set} (R : `Desc O) : (D : `Desc O) → Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫) → Set

data Path where
  here : {A : `Set} {a : ⟦ A ⟧} → Path A a
  thereΣ₁ : {A : `Set} {B : ⟦ A ⟧ → `Set} {a : ⟦ A ⟧} {b : ⟦ B a ⟧}
    → Path A a
    → Path (`Σ A B) (a , b)
  thereΣ₂ : {A : `Set} {B : ⟦ A ⟧ → `Set} {a : ⟦ A ⟧} {b : ⟦ B a ⟧}
    → Path (B a) b
    → Path (`Σ A B) (a , b)
  thereΠ : {A : `Set} {B : ⟦ A ⟧ → `Set} {f : (a : ⟦ A ⟧) → ⟦ B a ⟧}
    → Π ⟦ A ⟧ (λ a → Path (B a) (f a))
    → Path (`Π A B) f
  thereμ : {O : `Set} {D : `Desc O} {xs : Func ⟪ D ⟫ (μ ⟪ D ⟫) (rec ⟪ D ⟫)}
    → Pathα D D xs
    → Path (`μ D) (init xs)

data Pathα {O} R where
  thereArg₁ : {A : `Set} {D : ⟦ A ⟧ → `Desc O}
    {a : ⟦ A ⟧} {xs : Func ⟪ D a ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)}
    → Path A a
    → Pathα R (`Arg A D) (a , xs)
  thereArg₂ : {A : `Set} {D : ⟦ A ⟧ → `Desc O}
    {a : ⟦ A ⟧} {xs : Func ⟪ D a ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)}
    → Pathα R (D a) xs
    → Pathα R (`Arg A D) (a , xs)
  thereRec₁ : {A : `Set} {D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O}
    {f : ⟦ A ⟧ → μ ⟪ R ⟫} {xs : Func ⟪ D (rec ⟪ R ⟫ ∘ f) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)}
    → Π ⟦ A ⟧ (λ a → Path (`μ R) (f a))
    → Pathα R (`Rec A D) (f , xs)
  thereRec₂ : {A : `Set} {D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O}
    {f : ⟦ A ⟧ → μ ⟪ R ⟫} {xs : Func ⟪ D (rec ⟪ R ⟫ ∘ f) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)}
    → Pathα R (D (rec ⟪ R ⟫ ∘ f)) xs
    → Pathα R (`Rec A D) (f , xs)

----------------------------------------------------------------------

Lookup : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
Lookupα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
  → Pathα R D xs → Set

Lookup A a here = ⟦ A ⟧
Lookup (`Σ A B) (a , b) (thereΣ₁ i) = Lookup A a i
Lookup (`Σ A B) (a , b) (thereΣ₂ i) = Lookup (B a) b i
Lookup (`Π A B) f (thereΠ g) = Π ⟦ A ⟧ (λ a → Lookup (B a) (f a) (g a))
Lookup (`μ D) (init xs) (thereμ i) = Lookupα D D xs i

Lookupα R (`Arg A D) (a , xs) (thereArg₁ i) = Lookup A a i
Lookupα R (`Arg A D) (a , xs) (thereArg₂ i) = Lookupα R (D a) xs i
Lookupα R (`Rec A D) (f , xs) (thereRec₁ g) = Π ⟦ A ⟧ (λ a → Lookup (`μ R) (f a) (g a))
Lookupα R (`Rec A D) (f , xs) (thereRec₂ i) = Lookupα R (D (rec ⟪ R ⟫ ∘ f)) xs i

----------------------------------------------------------------------

lookup : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Lookup A a i
lookupα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
  (i : Pathα R D xs) → Lookupα R D xs i

lookup A a here = a
lookup (`Σ A B) (a , b) (thereΣ₁ i) = lookup A a i
lookup (`Σ A B) (a , b) (thereΣ₂ i) = lookup (B a) b i
lookup (`Π A B) f (thereΠ g) = λ a → lookup (B a) (f a) (g a)
lookup (`μ D) (init xs) (thereμ i) = lookupα D D xs i

lookupα R (`Arg A D) (a , xs) (thereArg₁ i) = lookup A a i
lookupα R (`Arg A D) (a , xs) (thereArg₂ i) = lookupα R (D a) xs i
lookupα R (`Rec A D) (f , xs) (thereRec₁ g) = λ a → lookup (`μ R) (f a) (g a)
lookupα R (`Rec A D) (f , xs) (thereRec₂ i) = lookupα R (D (rec ⟪ R ⟫ ∘ f)) xs i

----------------------------------------------------------------------

Update : (A : `Set) (a : ⟦ A ⟧) → Path A a → Set
Updateα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
  → Pathα R D xs → Set
update : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
  → Update A a i → ⟦ A ⟧
updateα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
  (i : Pathα R D xs)
  → Updateα R D xs i
  → Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)

----------------------------------------------------------------------

Update A a here = Maybe ⟦ A ⟧
Update (`Σ A B) (a , b) (thereΣ₁ i) =
  Σ (Update A a i) (λ a' → ⟦ B a ⟧ → ⟦ B (update A a i a') ⟧)
Update (`Σ A B) (a , b) (thereΣ₂ i) = Update (B a) b i
Update (`Π A B) f (thereΠ g) = Π ⟦ A ⟧ (λ a → Update (B a) (f a) (g a))
Update (`μ D) (init xs) (thereμ i) = Updateα D D xs i

Updateα R (`Arg A D) (a , xs) (thereArg₁ i) =
  Σ (Update A a i)
    (λ a' → Func ⟪ D a ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫) → Func ⟪ D (update A a i a') ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
Updateα R (`Arg A D) (a , xs) (thereArg₂ i) = Updateα R (D a) xs i
Updateα R (`Rec A D) (f , xs) (thereRec₁ g) =
  Σ (Π ⟦ A ⟧ (λ a → Update (`μ R) (f a) (g a)))
    (λ h → Func ⟪ D (λ a → rec ⟪ R ⟫ (f a)) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)
      → Func ⟪ D (λ a → rec ⟪ R ⟫ (update (`μ R) (f a) (g a) (h a))) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)
    )
Updateα R (`Rec A D) (f , xs) (thereRec₂ i) = Updateα R (D (rec ⟪ R ⟫ ∘ f)) xs i

----------------------------------------------------------------------

update A a here X = maybe id a X
update (`Σ A B) (a , b) (thereΣ₁ i) (X , f) = update A a i X , f b
update (`Σ A B) (a , b) (thereΣ₂ i) X = a , update (B a) b i X
update (`Π A B) f (thereΠ g) h = λ a → update (B a) (f a) (g a) (h a)
update (`μ D) (init xs) (thereμ i) X = init (updateα D D xs i X)

updateα R (`Arg A D) (a , xs) (thereArg₁ i) (X , f) = update A a i X , f xs
updateα R (`Arg A D) (a , xs) (thereArg₂ i) X = a , updateα R (D a) xs i X
updateα R (`Rec A D) (f , xs) (thereRec₁ g) (h , F) =
  (λ a → update (`μ R) (f a) (g a) (h a)) , F xs
updateα R (`Rec A D) (f , xs) (thereRec₂ i) X =
  f , updateα R (D (rec ⟪ R ⟫ ∘ f)) xs i X

----------------------------------------------------------------------

lift : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Update A a i
lem : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
  → a ≡ update A a i (lift A a i)
liftα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
  (i : Pathα R D xs) → Updateα R D xs i
lemα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
  (i : Pathα R D xs)
  → xs ≡ updateα R D xs i (liftα R D xs i)

----------------------------------------------------------------------

lift A a here = nothing
lift (`Σ A B) (a , b) (thereΣ₁ i) =
  lift A a i
  , subst (λ X → ⟦ B X ⟧) (lem A a i)
lift (`Σ A B) (a , b) (thereΣ₂ i) = lift (B a) b i
lift (`Π A B) f (thereΠ g) = λ a → lift (B a) (f a) (g a)
lift (`μ D) (init xs) (thereμ i) = liftα D D xs i

lem A a here = refl
lem (`Σ A B) (a , b) (thereΣ₁ i)
  with lem A a i
... | q = eqpair {B = λ X → ⟦ B X ⟧} q (subst-id (λ X → ⟦ B X ⟧) q b)
lem (`Σ A B) (a , b) (thereΣ₂ i) = cong (λ X → a , X) (lem (B a) b i)
lem (`Π A B) f (thereΠ g) = ext (λ a → lem (B a) (f a) (g a))
lem (`μ D) (init xs) (thereμ i) = cong init (lemα D D xs i)

liftα R (`Arg A D) (a , xs) (thereArg₁ i) =
  lift A a i
  , subst (λ X → Func ⟪ D X ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)) (lem A a i)
liftα R (`Arg A D) (a , xs) (thereArg₂ i) = liftα R (D a) xs i
liftα R (`Rec A D) (f , xs) (thereRec₁ g) =
  (λ a → lift (`μ R) (f a) (g a))
  , subst (λ X → Func ⟪ D X ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
    (ext (λ a → cong (rec ⟪ R ⟫) (lem (`μ R) (f a) (g a))))
liftα R (`Rec A D) (f , xs) (thereRec₂ i) = liftα R (D (rec ⟪ R ⟫ ∘ f)) xs i

lemα R (`Arg A D) (a , xs) (thereArg₁ i)
  with lem A a i
... | q =
  eqpair {B = λ a → Func ⟪ D a ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)} q
    (subst-id (λ X → Func ⟪ D X ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)) q xs)
lemα R (`Arg A D) (a , xs) (thereArg₂ i) =
  cong (λ X → a , X) (lemα R (D a) xs i)
lemα R (`Rec A D) (f , xs) (thereRec₁ g)
  with ext (λ a → lem (`μ R) (f a) (g a))
  | ext (λ a → cong (rec ⟪ R ⟫) (lem (`μ R) (f a) (g a)))
... | q₁ | q₂ =
  eqpair {B = λ h → Func ⟪ D (λ a → rec ⟪ R ⟫ (h a)) ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)} q₁
    (subst-id (λ X → Func ⟪ D X ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)) q₂ xs)
lemα R (`Rec A D) (f , xs) (thereRec₂ i) =
  cong (λ X → f , X) (lemα R (D (rec ⟪ R ⟫ ∘ f)) xs i)

----------------------------------------------------------------------

forget : (A : `Set) (a : ⟦ A ⟧) (i : Path A a) → Update A a i → Lookup A a i
forgetα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫))
  (i : Pathα R D xs) → Updateα R D xs i → Lookupα R D xs i

forget A a here X = maybe id a X
forget (`Σ A B) (a , b) (thereΣ₁ i) (X , f) = forget A a i X
forget (`Σ A B) (a , b) (thereΣ₂ i) X = forget (B a) b i X
forget (`Π A B) f (thereΠ g) h = λ a → forget (B a) (f a) (g a) (h a)
forget (`μ D) (init xs) (thereμ i) X = forgetα D D xs i X

forgetα R (`Arg A D) (a , xs) (thereArg₁ i) (X , f) = forget A a i X
forgetα R (`Arg A D) (a , xs) (thereArg₂ i) X = forgetα R (D a) xs i X
forgetα R (`Rec A D) (f , xs) (thereRec₁ g) (h , F) = λ a → forget (`μ R) (f a) (g a) (h a)
forgetα R (`Rec A D) (f , xs) (thereRec₂ i) X = forgetα R (D (λ z → rec ⟪ R ⟫ (f z))) xs i X

----------------------------------------------------------------------

thm : (A : `Set) (a : ⟦ A ⟧) (i : Path A a)
  → lookup A a i ≡ forget A a i (lift A a i) 
thmα : {O : `Set} (R D : `Desc O) (xs : Func ⟪ D ⟫ (μ ⟪ R ⟫) (rec ⟪ R ⟫)) (i : Pathα R D xs)
  → lookupα R D xs i ≡ forgetα R D xs i (liftα R D xs i) 

thm A a here = refl
thm (`Σ A B) (a , b) (thereΣ₁ i) = thm A a i
thm (`Σ A B) (a , b) (thereΣ₂ i) = thm (B a) b i
thm (`Π A B) f (thereΠ g) = ext (λ a → thm (B a) (f a) (g a))
thm (`μ D) (init xs) (thereμ i) = thmα D D xs i

thmα R (`Arg A D) (a , xs) (thereArg₁ i) = thm A a i
thmα R (`Arg A D) (a , xs) (thereArg₂ i) = thmα R (D a) xs i
thmα R (`Rec A D) (f , xs) (thereRec₁ g) = ext (λ a → thm (`μ R) (f a) (g a))
thmα R (`Rec A D) (f , xs) (thereRec₂ i) = thmα R (D (rec ⟪ R ⟫ ∘ f)) xs i

----------------------------------------------------------------------
