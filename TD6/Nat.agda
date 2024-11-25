-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

-- Give access to negation
open import Relation.Nullary
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + m = m
(suc n) + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m = zero
(suc n) * m = m + (n * m)

data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

infix 4 _≡_

cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- By doing a case-analysis on (e : m ≡ n),
-- the type checker find out the two parameters m and n are equal,
-- changing the goal from (suc m ≡ suc n) to (suc m ≡ suc m),
-- which is inhabited by refl
suc-≡ : {m n : ℕ} → (m ≡ n) → (suc m ≡ suc n)
suc-≡ refl = refl


+-unit-l : {n : ℕ} →  0 + n ≡ n
+-unit-l = refl

+-unit-r : {n : ℕ} → n + 0 ≡ n
+-unit-r {zero} = refl
+-unit-r {suc n} = cong suc (+-unit-r {n})

+-assoc : {m n p : ℕ} → (m + n) + p ≡ m + (n + p)
+-assoc {zero} {n} {p} = refl
+-assoc {suc m} {n} {p} = cong suc (+-assoc {m} {n} {p})

+-suc : {m n : ℕ} → suc (m + n) ≡ m + (suc n)
+-suc {zero} {n} = refl
+-suc {suc m} {n} = cong suc (+-suc {m} {n})

suc-nzero : {n : ℕ} → ¬ 0 ≡ suc n
suc-nzero {zero} ()
suc-nzero {suc n} ()

+-comm : {m n : ℕ} → m + n ≡ n + m
+-comm {zero} {n} = sym +-unit-r
+-comm {suc m} {n} = let IH = +-comm {m} {n} ; IH' = cong suc IH
                      in trans IH' (+-suc {n} {m})

rec : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → ((n : ℕ) → P n)
rec P base-case induction-step zero = base-case
rec P base-case induction-step (suc n) =
  let IH = rec P base-case induction-step n
   in induction-step n IH

rec-example : {n : ℕ} → n + 0 ≡ n
rec-example {n} = rec P base step n
  where
    P : ℕ → Set
    P n = n + 0 ≡ n
    base : P zero
    base = refl
    step : (n : ℕ) → P n → P (suc n)
    step n IH = cong suc IH


suc-inj : {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc-inj {n} {m} refl = refl

nat-dec : (m n : ℕ) → (m ≡ n) ∨ ¬ (m ≡ n)
nat-dec zero zero = left refl
nat-dec zero (suc n) = right (λ ())
nat-dec (suc m) zero = right (λ ())
nat-dec (suc m) (suc n) with nat-dec m n
... | left m=n = left (cong suc m=n)
... | right m≠n = right λ { refl → m≠n refl }

J : (A : Set) → (P : (x : A) → (y : A) → (p : x ≡ y) → Set) → (r : (x : A) → P x x refl) → (x : A) → (y : A) → (p : x ≡ y) → P x y p
J A P r x .x refl = r x
