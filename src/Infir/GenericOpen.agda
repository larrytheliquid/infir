open import Function hiding ( id )
open import Data.String hiding ( show )
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin
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

prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (λ x → f (suc x))

eqpair : ∀{a b} {A : Set a} {B : A → Set b}
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (q : a₁ ≡ a₂) → b₁ ≅ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
eqpair refl refl = refl

subst-id : {A : Set} {x y : A} (P : A → Set) (q : x ≡ y) (p : P x) → p ≅ subst P q p
subst-id P refl p = refl -- ≡-subst-removable

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

Path : {O : Set} (D : Desc O) → μ D → Set
Pathα : {O : Set} (D E : Desc O) → Func D (μ E) (rec E) → Set

Path D (init xs) = ⊤ ⊎ Pathα D D xs
Pathα (End o) E tt = ⊥
Pathα (Arg A D) E (a , xs) = Pathα (D a) E xs
Pathα (Rec A D) E (f , xs) = ((a : A) → Path E (f a))
  ⊎ Pathα (D (rec E ∘ f)) E xs

----------------------------------------------------------------------

Drop : {O : Set} (D : Desc O) (x : μ D) → Path D x → Set
Dropα : {O : Set} (D E : Desc O) (xs : Func D (μ E) (rec E)) → Pathα D E xs → Set

Drop D (init xs) (inj₁ tt) = μ D
Drop D (init xs) (inj₂ i) = Dropα D D xs i

Dropα (End o) E tt ()
Dropα (Arg A D) E (a , xs) i = Dropα (D a) E xs i
Dropα (Rec A D) E (f , xs) (inj₁ g) =
  (a : A) → Drop E (f a) (g a)
Dropα (Rec A D) E (f , xs) (inj₂ i) =
  Dropα (D (rec E ∘ f)) E xs i

----------------------------------------------------------------------

drop : {O : Set} (D : Desc O) (x : μ D) (i : Path D x)
  → Drop D x i
dropα : {O : Set} (D E : Desc O) (xs : Func D (μ E) (rec E)) (i : Pathα D E xs)
  → Dropα D E xs i

drop D (init xs) (inj₁ tt) = init xs
drop D (init xs) (inj₂ i) = dropα D D xs i

dropα (End o) E tt ()
dropα (Arg A D) E (a , xs) i = dropα (D a) E xs i
dropα (Rec A D) E (f , xs) (inj₁ g) = λ a → drop E (f a) (g a)
dropα (Rec A D) E (f , xs) (inj₂ i) = dropα (D (rec E ∘ f)) E xs i

----------------------------------------------------------------------

Sub : {O : Set} (D : Desc O) (x : μ D) → Path D x → Set
Subα : {O : Set} (D E : Desc O) (xs : Func D (μ E) (rec E)) → Pathα D E xs → Set
update : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) (X : Sub D x i) → μ D
updateα : {O : Set} (D E : Desc O) (xs : Func D (μ E) (rec E)) (i : Pathα D E xs)
  → Subα D E xs i → Func D (μ E) (rec E)

Sub D (init xs) (inj₁ tt) = μ D
Sub D (init xs) (inj₂ i) = Subα D D xs i

Subα (End o) E tt ()
Subα (Arg A D) E (a , xs) i = Subα (D a) E xs i
Subα (Rec A D) E (f , xs) (inj₁ g) =
  Σ ((a : A) → Sub E (f a) (g a))
  λ F → Func (D (rec E ∘ f)) (μ E) (rec E)
  → Func (D (λ a → rec E (update E (f a) (g a) (F a)))) (μ E) (rec E)
Subα (Rec A D) E (f , xs) (inj₂ i) =
  Subα (D (rec E ∘ f)) E xs i

update D (init xs) (inj₁ tt) X = X
update D (init xs) (inj₂ i) X = init (updateα D D xs i X)

updateα (End o) E xs i X = tt -- updateα (End o) E tt () X
updateα (Arg A D) E (a , xs) i X = a , updateα (D a) E xs i X
updateα (Rec A D) E (f , xs) (inj₁ g) (F , h) =
  (λ a → update E (f a) (g a) (F a))
  , h xs
updateα (Rec A D) E (f , xs) (inj₂ i) X =
  f , updateα (D (rec E ∘ f)) E xs i X

----------------------------------------------------------------------

liftD : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) → Drop D x i → Sub D x i
liftDα : {O : Set} (D E : Desc O) (xs : Func D (μ E) (rec E)) (i : Pathα D E xs)
  → Dropα D E xs i → Subα D E xs i
lem : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) (p : Drop D x i)
  → x ≡ update D x i (liftD D x i p)
lemα : {O : Set} (D E : Desc O) (xs : Func D (μ E) (rec E))
  (i : Pathα D E xs) (p : Dropα D E xs i)
  → xs ≡ updateα D E xs i (liftDα D E xs i p)  

liftD D (init xs) (inj₁ tt) p = init xs
liftD D (init xs) (inj₂ i) p = liftDα D D xs i p

liftDα (End o) E tt () p
liftDα (Arg A D) E (a , xs) i p = liftDα (D a) E xs i p
liftDα (Rec A D) E (f , xs) (inj₁ g) h =
  (λ a → liftD E (f a) (g a) (h a)) , id where
  id : Func (D (λ a → rec E (f a))) (μ E) (rec E)
    → Func (D (λ a → rec E (update E (f a) (g a) (liftD E (f a) (g a) (h a))))) (μ E) (rec E)
  id = subst (λ X → Func (D X) (μ E) (rec E))
    (ext (λ a → cong (λ X → rec E X) (lem E (f a) (g a) (h a))))
liftDα (Rec A D) E (f , xs) (inj₂ i) p = liftDα (D (rec E ∘ f)) E xs i p

lem D (init xs) (inj₁ tt) p = refl
lem D (init xs) (inj₂ i) p = cong init (lemα D D xs i p)

lemα (End o) E tt () p
lemα (Arg A D) E (a , xs) i p = cong (λ X → a , X) (lemα (D a) E xs i p)
lemα (Rec A D) E (f , xs) (inj₁ g) h
  with ext (λ a → lem E (f a) (g a) (h a)) | ext (λ a → cong (rec E) (lem E (f a) (g a) (h a)))
... | q₁ | q₂ = eqpair q₁ (subst-id (λ X → Func (D X) (μ E) (rec E)) q₂ xs)
lemα (Rec A D) E (f , xs) (inj₂ i) p =
  cong (λ X → f , X) (lemα (D (rec E ∘ f)) E xs i p)

----------------------------------------------------------------------

thm : {O : Set} (D : Desc O) (x : μ D) (i : Path D x)
  → x ≡ update D x i (liftD D x i (drop D x i))
thm D x i = lem D x i (drop D x i)

----------------------------------------------------------------------

data ArithT {ℓ} : Set ℓ where
  NumT ProdT : ArithT

ArithD : Desc ℕ
ArithD = Arg ArithT λ
  { NumT → Arg ℕ λ n → End n
  ; ProdT → Rec ⊤ λ a → Rec (Fin (a tt)) λ f → End (prod (a tt) f)
  }

----------------------------------------------------------------------
