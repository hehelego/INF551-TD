-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Div2

-- Haskell ($) operator.
infixr 5 _$_
_$_ : {A B : Set} → (A → B) → A → B
f $ x = f x

+-com : (m n : ℕ) → m + n ≡ n + m
+-com zero    n = sym $ +-identityʳ n
+-com (suc m) n = begin
  suc m + n   ≡⟨ refl ⟩
  suc (m + n) ≡⟨ cong suc $ +-com m n  ⟩
  suc (n + m) ≡⟨ sym $ +-suc n m ⟩
  n + suc m   ∎

2*n=n+n : (n : ℕ) → 2 * n ≡ n + n
2*n=n+n n = cong (n +_) $ +-identityʳ n

sn+sn=2+2n : (n : ℕ) → (suc n) + (suc n) ≡ 2 + 2 * n
sn+sn=2+2n n = begin
   (suc n) + (suc n) ≡⟨ +-suc (suc n) n ⟩
   suc ((suc n) + n) ≡⟨ refl ⟩
   2 + (n + n) ≡⟨ cong (2 +_) $ sym (2*n=n+n n) ⟩
   2 + 2 * n ∎

div2-double : (n : ℕ) → div2 (2 * n) ≡ n
div2-double zero = refl
div2-double (suc n) = begin
  div2 (2 * (suc n))       ≡⟨ cong div2 $ 2*n=n+n (suc n) ⟩
  div2 ((suc n) + (suc n)) ≡⟨ cong div2 $ sn+sn=2+2n n ⟩
  div2 ( 2 + 2 * n)        ≡⟨ cong suc $ div2-double n ⟩
  suc n ∎

triangular : ℕ → ℕ
triangular zero = zero
triangular (suc n) = (suc n) + (triangular n)

gauss' : (n : ℕ) → triangular n + triangular n ≡ n * suc n
gauss' zero = refl
gauss' (suc n) = begin
  triangular (suc n) + triangular (suc n) ≡⟨ refl ⟩
  (suc n + triangular n) + (suc n + triangular n) ≡⟨ sum-perm (suc n) (triangular n) ⟩
  (suc n + suc n) + (triangular n + triangular n) ≡⟨ cong ((suc n + suc n) +_) $ gauss' n ⟩
  (suc n + suc n) + n * suc n                     ≡⟨ cong (_+ (n * suc n)) $ sym $ 2*n=n+n (suc n) ⟩
  2 * (suc n) + n * suc n                         ≡⟨ sym $ *-distribʳ-+ (suc n) 2 n ⟩
  (suc (suc n)) * (suc n)                         ≡⟨ *-comm (2 + n) (suc n) ⟩
  (suc n) * (suc (suc n)) ∎
  where
    sum-perm : (a b : ℕ) → (a + b) + (a + b) ≡ (a + a) + (b + b)
    sum-perm a b = begin
      (a + b) + (a + b) ≡⟨ cong ((a + b) +_) $ +-com a b ⟩
      (a + b) + (b + a) ≡⟨ +-assoc a b (b + a) ⟩
      a + (b + (b + a)) ≡⟨ cong (a +_) $ sym $ +-assoc b b a ⟩
      a + ((b + b) + a) ≡⟨ cong (a +_) $ +-com (b + b) a ⟩
      a + (a + (b + b)) ≡⟨ sym $ +-assoc a a (b + b) ⟩
      (a + a) + (b + b) ∎


gauss : (n : ℕ) → triangular n ≡ div2 (n * suc n)
gauss n = begin
  triangular n                       ≡⟨ sym $ div2-double (triangular n) ⟩
  div2 (2 * triangular n)            ≡⟨ cong div2 $ 2*n=n+n (triangular n) ⟩
  div2 (triangular n + triangular n) ≡⟨ cong div2 $ gauss' n ⟩
  div2 (n * suc n) ∎
