-- tested on
-- agda 2.6.3
-- agda-stdlib 2.1
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)


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

trans : (x y z : ℕ) → x ≡ y → y ≡ z → x ≡ z
trans x y z refl refl = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) =
  trans
    -- operators
    (m + suc n) (suc m + n) (suc n + m)
    -- equalities
    (+-suc m n)
    (cong suc (+-comm m n))

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p = Eq.trans
  (cong (p +_) (*-distrib-+ m n p))
  (sym (+-assoc p (m * p) (n * p)))


*-assoc : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p = let IH = *-assoc m n p in
  Eq.trans
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
