data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixr 20 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

infixr 30 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + m * n

infix 10 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- Credit: Authors of the PLFA book
-- Url: https://plfa.github.io/Equality/
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 step-≡-∣ step-≡-⟩
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y  =  x≡y

  step-≡-∣ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-∣ x x≡y  =  x≡y

  step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y  =  trans x≡y y≡z

  syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎  =  refl

open ≡-Reasoning


+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) =
  trans
    (+-suc m n)
    (cong suc (+-comm m n))

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p = trans
  (cong (p +_) (*-distrib-+ m n p))
  (sym (+-assoc p (m * p) (n * p)))


*-assoc : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p = let IH = *-assoc m n p in
  trans
    (*-distrib-+ n (m * n) p)
    (cong (n * p +_) IH)

mul0 : (n : ℕ) → 0 ≡ n * 0
mul0 zero = refl
mul0 (suc n) = cong (0 +_) (mul0 n)

*-id : (m : ℕ) → m ≡ m * 1
*-id zero = refl
*-id (suc m) = cong suc (*-id m)

lemma : (m p : ℕ) → m * (1 + p) ≡ m * 1 + m * p
lemma zero p = refl
lemma (suc m) p = cong suc
  (begin
     p + m * suc p
   ≡⟨ cong (p +_) (lemma m p) ⟩
     p + (m * 1 + m * p)
   ≡⟨ sym (+-assoc p (m * 1) (m * p)) ⟩
     (p + m * 1) + m * p
   ≡⟨ cong (_+ m * p) (+-comm p (m * 1)) ⟩
     (m * 1 + p) + m * p
   ≡⟨ +-assoc (m * 1) p (m * p) ⟩
     m * 1 + (p + m * p)
   ∎)


*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm zero n = mul0 n
*-comm (suc m) n =
  begin
    n + m * n
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + n * m
  ≡⟨ cong (_+ n * m) (*-id n) ⟩
    n * 1 + n * m
  ≡⟨ sym (lemma n m) ⟩
    n * suc m
  ∎
