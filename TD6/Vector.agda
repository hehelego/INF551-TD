-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

open import Data.List
open import Data.Nat
open import Data.Nat.Properties using (+-assoc)
open import Data.Product hiding (zip)
open import Relation.Binary.PropositionalEquality 

-- This type/set is not inhabitable because it is not generally possible to construct a term of type A with nothing in the context.
-- hd : {A : Set} → List A → A
-- hd [] = {! !}
-- hd (x ∷ xs) = x

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)


-- The head/tail functions are projections.

vec-hd : {A : Set} {n : ℕ} → Vec A (suc n) → A
vec-hd (x ∷ xs) = x

vec-tl : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
vec-tl (x ∷ xs) = xs

vec-concat : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
vec-concat [] ys = ys
vec-concat (x ∷ xs) ys = x ∷ vec-concat xs ys

vec-append : {A : Set} {n : ℕ} → Vec A n → A → Vec A (suc n)
vec-append [] y = y ∷ []
vec-append (x ∷ xs) y = x ∷ vec-append xs y

vec-rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
vec-rev [] = []
vec-rev (x ∷ xs) = vec-append (vec-rev xs) x

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

-- With k : Fin n in scope, agda determines that n is non-zero.
vec-ith : {A : Set} {n : ℕ} → Vec A n → Fin n → A
vec-ith (x ∷ xs) zero = x
vec-ith (x ∷ xs) (suc i) = vec-ith xs i

vec-zip : {A B : Set} {n : ℕ} → Vec A n → Vec B n → Vec (A × B) n
vec-zip [] [] = []
vec-zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ (vec-zip xs ys)


-- vec-concat-assoc : {A : Set} {m n p : ℕ} → (xs : Vec A m) (ys : Vec A n) (zs : Vec A p)
--                  → vec-concat (vec-concat xs ys) zs ≡ vec-concat xs (vec-concat ys zs)
-- 
-- The equality is not typable.
-- For x ≡ y to be a type, x and y must have the exactly same type.
--
-- Vec A ((m + n) + p)             Vec A (m + (n + p))
-- They are distinct types, though they are isomorphic.


coe : {A B : Set} → A ≡ B → A → B
coe refl x = x

vec-eq-shape : {A : Set} {m n : ℕ} → m ≡ n → Vec A m ≡ Vec A n
vec-eq-shape {A} eq = cong (Vec A) eq

vec-shape-+assoc : {A : Set} (m n p : ℕ) → Vec A ((m + n) + p) ≡ Vec A (m + (n + p))
vec-shape-+assoc {A} m n p = vec-eq-shape (+-assoc m n p)

cons-eq : {A : Set} {n n' : ℕ} {n=n' : n ≡ n'} {xs : Vec A n} {ys : Vec A n'} → (x : A)
        → coe (vec-eq-shape n=n')                  xs ≡ ys
        → coe (vec-eq-shape (cong suc n=n')) (x ∷ xs) ≡ x ∷ ys
cons-eq {A} {n} {.n} {refl} {xs} {ys} x refl = refl


concat-assoc : {A : Set} {m n p : ℕ}
             → (xs : Vec A m) (ys : Vec A n) (zs : Vec A p)
             → coe (vec-shape-+assoc m n p)
                   (vec-concat (vec-concat xs ys) zs)
                 ≡  vec-concat xs (vec-concat ys zs)
concat-assoc [] ys zs = refl
concat-assoc (x ∷ xs) ys zs = cons-eq x (concat-assoc xs ys zs)

data _=~=_ : {A B : Set} → A → B → Set where
  hrefl : {A : Set} {x : A} → x =~= x

hcong : {A B : Set} {x y : A} (f : A → B) → x =~= y → f x =~= f y
hcong f hrefl = hrefl

-- It it crucial to have the equal length evidence {n=m : n ≡ m} in the context,
-- otherwise, agda cannot conclude that {Vec A (suc n)} and {Vec A (suc m)} are equal,
-- which makes it impossible to inhabit the equality type =~=
cons-eq' : {A : Set} {n m : ℕ} {xs : Vec A n} {ys : Vec A m} {n=m : n ≡ m}
         → (x : A) → xs =~= ys → _=~=_ {Vec A (suc n)} {Vec A (suc m)} (x ∷ xs) (x ∷ ys)
cons-eq' {A} {n} {.n} {xs} {ys} {refl} x eq = hcong (x ∷_) eq

concat-assoc' : {A : Set} {m n p : ℕ}
              → (xs : Vec A m) (ys : Vec A n) (zs : Vec A p)
              → vec-concat (vec-concat xs ys) zs =~= vec-concat xs (vec-concat ys zs)
concat-assoc' [] ys zs = hrefl
concat-assoc' {A} {suc n} {m} {p} (x ∷ xs) ys zs = let IH = concat-assoc' xs ys zs in cons-eq' {n=m = +-assoc n m p} x IH
