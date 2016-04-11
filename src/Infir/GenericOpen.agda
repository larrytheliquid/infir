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

lookup' : {O : Set} (D : Desc O) (x : μ D) → Path D x → Dyn
lookupα' : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) → Pathα R D xs → Dyn

Lookup : {O : Set} (D : Desc O) (x : μ D) → Path D x → Set
Lookup D x i = proj₁ (lookup' D x i)

lookup : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) → Lookup D x i
lookup D x i = proj₂ (lookup' D x i)

Lookupα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) → Pathα R D xs → Set
Lookupα R D xs i = proj₁ (lookupα' R D xs i)

lookupα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) (i : Pathα R D xs)
  → Lookupα R D xs i
lookupα R D xs i = proj₂ (lookupα' R D xs i)

--------------------------------------------------------------------------------

lookup' D x here = μ D , x
lookup' D (init xs) (there i) = lookupα' D D xs i

lookupα' R (End o) tt ()
lookupα' R (Arg A D) (a , xs) (thereArg i) = lookupα' R (D a) xs i
lookupα' R (Rec A D) (f , xs) (thereRec₁ g) =
  Π A (λ a → Lookup R (f a) (g a))
  , (λ a → lookup R (f a) (g a))
lookupα' R (Rec A D) (f , xs) (thereRec₂ i) =
  lookupα' R (D (rec R ∘ f)) xs i

----------------------------------------------------------------------

update' : {O : Set} (D : Desc O) (x : μ D) → Path D x → DynCon (μ D)
updateα' : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) → Pathα R D xs
  → DynCon (Func D (μ R) (rec R))

Update : {O : Set} (D : Desc O) (x : μ D) → Path D x → Set
Update D x i = proj₁ (update' D x i)

update : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) (X : Update D x i) → μ D
update D x i X = proj₂ (update' D x i) X

Updateα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) → Pathα R D xs → Set
Updateα R D xs i = proj₁ (updateα' R D xs i)

updateα : {O : Set} (R D : Desc O) (xs : Func D (μ R) (rec R)) (i : Pathα R D xs)
  → Updateα R D xs i → Func D (μ R) (rec R)
updateα R D xs i X = proj₂ (updateα' R D xs i) X

update' D x here = μ D , id
update' D (init xs) (there i) =
  Updateα D D xs i
  , init ∘ updateα D D xs i

updateα' R (End o) tt ()
updateα' R (Arg A D) (a , xs) (thereArg i) =
  Updateα R (D a) xs i
  , (λ X → a , updateα R (D a) xs i X)
updateα' R (Rec A D) (f , xs) (thereRec₁ g) =
  Σ (Π A (λ a → Update R (f a) (g a)))
    (λ F → Func (D (rec R ∘ f)) (μ R) (rec R)
      → Func (D (λ a → rec R (update R (f a) (g a) (F a)))) (μ R) (rec R))
  , λ { (F , h) → (λ a → update R (f a) (g a) (F a)) , h xs }
updateα' R (Rec A D) (f , xs) (thereRec₂ i) =
  Updateα R (D (rec R ∘ f)) xs i
  , (λ X → f , updateα R (D (rec R ∘ f)) xs i X)

----------------------------------------------------------------------

-- lift : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) → Lookup D x i → Update D x i
-- liftα : {O : Set} (D E : Desc O) (xs : Func D (μ E) (rec E)) (i : Pathα D E xs)
--   → Lookupα D E xs i → Updateα D E xs i
-- lem : {O : Set} (D : Desc O) (x : μ D) (i : Path D x) (p : Lookup D x i)
--   → x ≡ update D x i (lift D x i p)
-- lemα : {O : Set} (D E : Desc O) (xs : Func D (μ E) (rec E))
--   (i : Pathα D E xs) (p : Lookupα D E xs i)
--   → xs ≡ updateα D E xs i (liftα D E xs i p)  

-- lift D (init xs) (inj₁ tt) p = init xs
-- lift D (init xs) (inj₂ i) p = liftα D D xs i p

-- liftα (End o) E tt () p
-- liftα (Arg A D) E (a , xs) i p = liftα (D a) E xs i p
-- liftα (Rec A D) E (f , xs) (inj₁ g) h =
--   (λ a → lift E (f a) (g a) (h a))
--   , subst (λ X → Func (D X) (μ E) (rec E))
--       (ext (λ a → cong (λ X → rec E X) (lem E (f a) (g a) (h a))))
-- liftα (Rec A D) E (f , xs) (inj₂ i) p = liftα (D (rec E ∘ f)) E xs i p

-- lem D (init xs) (inj₁ tt) p = refl
-- lem D (init xs) (inj₂ i) p = cong init (lemα D D xs i p)

-- lemα (End o) E tt () p
-- lemα (Arg A D) E (a , xs) i p = cong (λ X → a , X) (lemα (D a) E xs i p)
-- lemα (Rec A D) E (f , xs) (inj₁ g) h
--   with ext (λ a → lem E (f a) (g a) (h a)) | ext (λ a → cong (rec E) (lem E (f a) (g a) (h a)))
-- ... | q₁ | q₂ = eqpair q₁ (subst-id (λ X → Func (D X) (μ E) (rec E)) q₂ xs)
-- lemα (Rec A D) E (f , xs) (inj₂ i) p =
--   cong (λ X → f , X) (lemα (D (rec E ∘ f)) E xs i p)

-- ----------------------------------------------------------------------

-- thm : {O : Set} (D : Desc O) (x : μ D) (i : Path D x)
--   → x ≡ update D x i (lift D x i (lookup D x i))
-- thm D x i = lem D x i (lookup D x i)

-- ----------------------------------------------------------------------

-- data ArithT {ℓ} : Set ℓ where
--   NumT ProdT : ArithT

-- ArithD : Desc ℕ
-- ArithD = Arg ArithT λ
--   { NumT → Arg ℕ λ n → End n
--   ; ProdT → Rec ⊤ λ a → Rec (Fin (a tt)) λ f → End (prod (a tt) f)
--   }

-- ----------------------------------------------------------------------
