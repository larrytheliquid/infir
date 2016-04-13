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

Dyn : Set₁
Dyn = Σ Set id

DynCon : Set → Set₁
DynCon B = Σ Set (λ A → A → B)

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

data Path {O : Set} (D : Desc O) : μ D → Set₁
data Pathα {O : Set} (R : Desc O) : (D : Desc O) → Func D (μ R) (rec R) → Set₁

data Path {O} D where
  here : {x : μ D} → Path D x
  there : {xs : Func D (μ D) (rec D)}
    → Pathα D D xs
    → Path D (init xs)

data Pathα {O} R where
  thereArg : {A : Set} {D : A → Desc O}
    {a : A} {xs : Func (D a) (μ R) (rec R)}
    → Pathα R (D a) xs
    → Pathα R (Arg A D) (a , xs)
  thereRec₁ : {A : Set} {D : (o : A → O) → Desc O}
    {f : A → μ R} {xs : Func (D (rec R ∘ f)) (μ R) (rec R)}
    → Π A (λ a → Path R (f a))
    → Pathα R (Rec A D) (f , xs)
  thereRec₂ : {A : Set} {D : (o : A → O) → Desc O}
    {f : A → μ R} {xs : Func (D (rec R ∘ f)) (μ R) (rec R)}
    → Pathα R (D (rec R ∘ f)) xs
    → Pathα R (Rec A D) (f , xs)

----------------------------------------------------------------------

Lookup : {O : Set} (D : Desc O) (x : μ D) → Path D x → Set
Lookupα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) → Pathα R D xs → Set

Lookup D x here = μ D
Lookup D (init xs) (there i) = Lookupα D D xs i

Lookupα R (End o) tt ()
Lookupα R (Arg A D) (a , xs) (thereArg i) = Lookupα R (D a) xs i
Lookupα R (Rec A D) (f , xs) (thereRec₁ g) = Π A (λ a → Lookup R (f a) (g a))
Lookupα R (Rec A D) (f , xs) (thereRec₂ i) = Lookupα R (D (rec R ∘ f)) xs i

----------------------------------------------------------------------

lookup : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) → Lookup D x i
lookupα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) (i : Pathα R D xs)
  → Lookupα R D xs i

lookup D x here = x
lookup D (init xs) (there i) = lookupα D D xs i

lookupα R (End o) tt ()
lookupα R (Arg A D) (a , xs) (thereArg i) = lookupα R (D a) xs i
lookupα R (Rec A D) (f , xs) (thereRec₁ g) = λ a → lookup R (f a) (g a)
lookupα R (Rec A D) (f , xs) (thereRec₂ i) = lookupα R (D (rec R ∘ f)) xs i

----------------------------------------------------------------------

Update : {O : Set} (D : Desc O) (x : μ D) → Path D x → Set
Updateα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) → Pathα R D xs → Set
update : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) (X : Update D x i) → μ D
updateα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) (i : Pathα R D xs)
  → Updateα R D xs i → Func D (μ R) (rec R)

----------------------------------------------------------------------

Update D x here = Maybe (μ D)
Update D (init xs) (there i) = Updateα D D xs i

Updateα R (End o) tt ()
Updateα R (Arg A D) (a , xs) (thereArg i) = Updateα R (D a) xs i
Updateα R (Rec A D) (f , xs) (thereRec₁ g) =
  Σ (Π A (λ a → Update R (f a) (g a)))
    (λ h → Func (D (rec R ∘ f)) (μ R) (rec R)
      → Func (D (λ a → rec R (update R (f a) (g a) (h a)))) (μ R) (rec R))
Updateα R (Rec A D) (f , xs) (thereRec₂ i) =
  Updateα R (D (rec R ∘ f)) xs i

----------------------------------------------------------------------

update D x here X = maybe id x X
update D (init xs) (there i) X = init (updateα D D xs i X)

updateα R (End o) tt () X
updateα R (Arg A D) (a , xs) (thereArg i) X =
  a , updateα R (D a) xs i X
updateα R (Rec A D) (f , xs) (thereRec₁ g) (F , h) =
  (λ a → update R (f a) (g a) (F a)) , h xs
updateα R (Rec A D) (f , xs) (thereRec₂ i) X =
  f , updateα R (D (rec R ∘ f)) xs i X

----------------------------------------------------------------------

lift : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) → Update D x i
liftα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) (i : Pathα R D xs)
  → Updateα R D xs i
lem : {O : Set} (D : Desc O) (x : μ D) (i : Path D x)
  → x ≡ update D x i (lift D x i)
lemα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R))
  (i : Pathα R D xs)
  → xs ≡ updateα R D xs i (liftα R D xs i)

----------------------------------------------------------------------

lift D x here = nothing
lift D (init xs) (there i) = liftα D D xs i

liftα R (End o) tt ()
liftα R (Arg A D) (a , xs) (thereArg i) = liftα R (D a) xs i
liftα R (Rec A D) (f , xs) (thereRec₁ g) =
  (λ a → lift R (f a) (g a))
  , subst (λ X → Func (D X) (μ R) (rec R))
      (ext (λ a → cong (λ X → rec R X) (lem R (f a) (g a))))
liftα R (Rec A D) (f , xs) (thereRec₂ i) = liftα R (D (rec R ∘ f)) xs i

lem D x here = refl
lem D (init xs) (there i) = cong init (lemα D D xs i)

lemα R (End o) tt ()
lemα R (Arg A D) (a , xs) (thereArg i) = cong (λ X → a , X) (lemα R (D a) xs i)
lemα R (Rec A D) (f , xs) (thereRec₁ g)
  with ext (λ a → lem R (f a) (g a)) | ext (λ a → cong (rec R) (lem R (f a) (g a)))
... | q₁ | q₂ = eqpair q₁ (subst-id (λ X → Func (D X) (μ R) (rec R)) q₂ xs)
lemα R (Rec A D) (f , xs) (thereRec₂ i) =
  cong (λ X → f , X) (lemα R (D (rec R ∘ f)) xs i)

----------------------------------------------------------------------

forget : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) → Update D x i → Lookup D x i
forgetα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R))
  (i : Pathα R D xs) → Updateα R D xs i → Lookupα R D xs i

forget D x here nothing = x
forget D x here (just x') = x'
forget D (init xs) (there i) X = forgetα D D xs i X

forgetα R (Arg A D) (a , xs) (thereArg i) X = forgetα R (D a) xs i X
forgetα R (Rec A D) (f , xs) (thereRec₁ g) (h , _) = λ a → forget R (f a) (g a) (h a)
forgetα R (Rec A D) (f , xs) (thereRec₂ i) X = forgetα R (D (rec R ∘ f)) xs i X

----------------------------------------------------------------------

thm : {O : Set} (D : Desc O) (x : μ D) (i : Path D x)
  → lookup D x i ≡ forget D x i (lift D x i) 
thmα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) (i : Pathα R D xs)
  → lookupα R D xs i ≡ forgetα R D xs i (liftα R D xs i) 

thm D x here = refl
thm D (init xs) (there i) = thmα D D xs i

thmα R (Arg A D) (a , xs) (thereArg i) = thmα R (D a) xs i
thmα R (Rec A D) (f , xs) (thereRec₁ g) = ext (λ a → thm R (f a) (g a))
thmα R (Rec A D) (f , xs) (thereRec₂ i) = thmα R (D (rec R ∘ f)) xs i

----------------------------------------------------------------------

data ArithT {ℓ} : Set ℓ where
  NumT ProdT : ArithT

ArithD : Desc ℕ
ArithD = Arg ArithT λ
  { NumT → Arg ℕ λ n → End n
  ; ProdT → Rec ⊤ λ a → Rec (Fin (a tt)) λ f → End (prod (a tt) f)
  }

----------------------------------------------------------------------
