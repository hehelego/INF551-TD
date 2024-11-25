-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

-- TODO: properly encode the evidence of termination of well-founded recursion
-- links:
-- https://en.wikipedia.org/wiki/Well-founded_relation
-- https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/7.sorting.html#well-founded-definition-of-merge-sort
-- https://armkeh.github.io/blog/WellFoundedRecursion.html
-- https://xavierleroy.org/publi/wf-recursion.pdf

open import Data.Bool hiding (_<_ ; _≤_ ; _<?_ ; _≤?_)
open import Data.Nat
open import Data.Sum renaming (inj₁ to left ; inj₂ to right)
open import Data.Product
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Trichotomy : ℕ → ℕ → Set where
  tri-= : {m n : ℕ} → m ≡ n → Trichotomy m n
  tri-< : {m n : ℕ} → m < n → Trichotomy m n
  tri-> : {m n : ℕ} → n < m → Trichotomy m n

trichotomy : (m n : ℕ) → Trichotomy m n
trichotomy zero zero    = tri-= refl
trichotomy zero (suc n) = tri-< z<s
trichotomy (suc m) zero = tri-> z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | tri-= m=n = tri-= (cong suc m=n)
... | tri-< m<n = tri-< (s<s m<n)
... | tri-> m>n = tri-> (s<s m>n)

{-# TERMINATING #-}
-- the quotient (m // n)
quotient : (m n : ℕ) {n≠0 : n ≢ 0} → ℕ
quotient m n {n≠0} with trichotomy m n
... | tri-< m<n = 0
... | tri-= m=n = 1
... | tri-> m>n = 1 + quotient (m ∸ n) n {n≠0}

{-# TERMINATING #-}
-- the remainder (m mod n)
remainder : (m n : ℕ) {n≠0 : n ≢ 0} → ℕ
remainder m n {n≠0} with trichotomy m n
... | tri-< m<n = m
... | tri-= m=n = 0
... | tri-> m>n = remainder (m ∸ n) n {n≠0}

m-n+n=m : (m n : ℕ) (m>n : n < m) → (m ∸ n) + n ≡ m
m-n+n=m m zero m>n = +-identityʳ m
m-n+n=m (suc m) (suc n) (s<s m>n) = begin
                                      (suc m ∸ suc n) + suc n ≡⟨ refl ⟩
                                      (m ∸ n) + suc n         ≡⟨ +-suc (m ∸ n) n ⟩
                                      suc ((m ∸ n) + n)       ≡⟨ cong suc (m-n+n=m m n m>n) ⟩
                                      suc m ∎

{-# TERMINATING #-}
-- correctness :
-- m = q * n + r
-- remainder r is less than n
correct : (m n : ℕ) {n≠0 : n ≢ 0} → remainder m n {n≠0} < n × (quotient m n {n≠0}) * n + (remainder m n {n≠0}) ≡ m
correct m zero {n≠0} = ⊥-elim (n≠0 refl)
correct m n@(suc n') {n≠0}
  with trichotomy m n
... | tri-= m=n = (z<s , (begin
                            1 * n + 0 ≡⟨ +-identityʳ (1 * n) ⟩
                            1 * n     ≡⟨ *-identityˡ n ⟩
                            n         ≡⟨ sym m=n ⟩
                            m ∎))
... | tri-< m<n = (m<n , (begin
                            0 * n + m ≡⟨ refl ⟩
                            0 + m     ≡⟨ refl ⟩
                            m ∎))
... | tri-> m>n
    with correct (m ∸ n) n {n≠0}
... | (r<n , qn+r=m-n) = let q = quotient (m ∸ n) n {n≠0} ; r = remainder (m ∸ n) n {n≠0}
                          in (r<n , (begin
                                       (suc q) * n + r ≡⟨ refl ⟩
                                       n + q * n + r   ≡⟨ +-assoc n (q * n) r ⟩
                                       n + (q * n + r) ≡⟨ cong (n +_) qn+r=m-n ⟩
                                       n + (m ∸ n)     ≡⟨ +-comm n (m ∸ n) ⟩
                                       (m ∸ n) + n     ≡⟨ m-n+n=m m n m>n ⟩
                                       m ∎))

{-# TERMINATING #-}
euclid-div : (m n : ℕ) {n≠0 : n ≢ 0} → Σ (ℕ × ℕ) (λ (q , r) → (r < n) × (q * n + r ≡ m))
euclid-div m zero {n≠0} = ⊥-elim (n≠0 refl)
euclid-div m n@(suc n') {n≠0}
  with trichotomy m n
... | tri-< m<n = (0 , m) , (m<n , refl)
... | tri-= m=n = (1 , 0) , (z<s , ( begin
                                       1 * n + 0  ≡⟨ cong (_+ 0) (*-identityˡ n) ⟩
                                       n + 0      ≡⟨ +-identityʳ n ⟩
                                       n          ≡⟨ sym m=n ⟩
                                       m ∎))
... | tri-> m>n
    with euclid-div (m ∸ n) n {n≠0}
...   | (q , r) , (r<n , qn+r=m-n) = (suc q , r) , (r<n , sq*n+r=m)
      where
        sq*n+r=m : suc q * n + r ≡ m
        sq*n+r=m = begin
          suc q * n + r   ≡⟨ refl ⟩
          n + q * n + r   ≡⟨ +-assoc n (q * n) r ⟩
          n + (q * n + r) ≡⟨ cong (n +_) qn+r=m-n ⟩
          n + (m ∸ n)     ≡⟨ +-comm n (m ∸ n) ⟩
          (m ∸ n) + n     ≡⟨ m-n+n=m m n m>n ⟩
          m ∎
