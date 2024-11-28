-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

open import Induction.WellFounded

open import Data.Bool hiding (_<_ ; _≤_ ; _<?_ ; _≤?_)
open import Data.Nat
open import Data.Sum renaming (inj₁ to left ; inj₂ to right)
open import Data.Product
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

wf-nat : WellFounded _<_
wf-nat n = wf n n ≤-refl
  where
    split-leq : (n m : ℕ) → n ≤ m → n ≡ m ⊎ n < m
    split-leq zero zero n≤m = left refl
    split-leq zero (suc m) n≤m = right z<s
    split-leq (suc n) (suc m) (s≤s n≤m)
      with split-leq n m n≤m
    ... | left  n≡m = left  (cong suc n≡m)
    ... | right n<m = right (s<s n<m)

    wf : (n m : ℕ) → n ≤ m → Acc _<_ n
    wf zero m n≤m = acc λ { () }
    wf (suc n) (suc m) (s≤s n≤m) = acc λ { {y} sy≤sn → wf y m (≤-trans (≤-pred sy≤sn) n≤m) }


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

minus-mono : (m n : ℕ) → (m ∸ suc n) ≤ (m ∸ n)
minus-mono zero zero = z≤n
minus-mono (suc m) zero = n≤1+n m
minus-mono zero (suc n) = z≤n
minus-mono (suc m) (suc n) = minus-mono m n

minus-dec : (m n : ℕ) → (suc m ∸ suc n) < suc m
minus-dec m zero = ≤-refl
minus-dec m (suc n) = let m-sn≤m-n = s≤s (minus-mono m n) in ≤-trans m-sn≤m-n (minus-dec m n)

{-# TERMINATING #-}
-- the quotient (m // n)
quotient : (m n : ℕ) {n≠0 : n ≢ 0} → ℕ
quotient m n {n≠0} with trichotomy m n
... | tri-< m<n = 0
... | tri-= m=n = 1
... | tri-> m>n = 1 + quotient (m ∸ n) n {n≠0}

quotient-wf : (m n : ℕ) {rs : Acc _<_ m} {n≠0 : n ≢ 0} → ℕ
quotient-wf zero n {rs} {n≠0} = zero
quotient-wf (suc m) zero {rs} {n≠0} = ⊥-elim (n≠0 refl)
quotient-wf (suc m) (suc n) {acc rs} {n≠0} with trichotomy m n
... | tri-< m<n = 0
... | tri-= m=n = 1
... | tri-> m>n = 1 + quotient-wf (m ∸ n) (suc n) {rs (minus-dec m n)} {n≠0}

quotient' : (m n : ℕ) {n≠0 : n ≢ 0} → ℕ
quotient' m n {n≠0} = quotient-wf m n {wf-nat m} {n≠0}

{-# TERMINATING #-}
-- the remainder (m mod n)
remainder : (m n : ℕ) {n≠0 : n ≢ 0} → ℕ
remainder m n {n≠0} with trichotomy m n
... | tri-< m<n = m
... | tri-= m=n = 0
... | tri-> m>n = remainder (m ∸ n) n {n≠0}

remainder-wf : (m n : ℕ) {rs : Acc _<_ m} {n≠0 : n ≢ 0} → ℕ
remainder-wf zero n {rs} {n≠0} = 0
remainder-wf (suc m) zero {rs} {n≠0} = ⊥-elim (n≠0 refl)
remainder-wf (suc m) (suc n) {acc rs} {n≠0} with trichotomy m n
... | tri-< m<n = suc m
... | tri-= m=n = 0
... | tri-> m>n = remainder-wf (m ∸ n) (suc n) {rs (minus-dec m n)} {n≠0}

remainder' : (m n : ℕ) {n≠0 : n ≢ 0} → ℕ
remainder' m n {n≠0} = remainder-wf m n {wf-nat m} {n≠0}


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
correct : (m n : ℕ) {n≠0 : n ≢ 0}
        → remainder m n {n≠0} < n
        × (quotient m n {n≠0}) * n + (remainder m n {n≠0}) ≡ m
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

correct-wf : (m n : ℕ) {rs : Acc _<_ m} {n≠0 : n ≢ 0}
           → remainder m n {n≠0} < n
           × (quotient m n {n≠0}) * n + (remainder m n {n≠0}) ≡ m
correct-wf m zero {rs} {n≠0} = ⊥-elim (n≠0 refl)
correct-wf zero (suc n) {rs} {n≠0} = z<s , refl
correct-wf m@(suc m') n@(suc n') {acc rs} {n≠0}
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
    with correct-wf (m ∸ n) n {rs (minus-dec m' n')} {n≠0}
... | (r<n , qn+r=m-n) = let q = quotient (m ∸ n) n {n≠0} ; r = remainder (m ∸ n) n {n≠0}
                          in (r<n , (begin
                                       (suc q) * n + r ≡⟨ refl ⟩
                                       n + q * n + r   ≡⟨ +-assoc n (q * n) r ⟩
                                       n + (q * n + r) ≡⟨ cong (n +_) qn+r=m-n ⟩
                                       n + (m ∸ n)     ≡⟨ +-comm n (m ∸ n) ⟩
                                       (m ∸ n) + n     ≡⟨ m-n+n=m m n m>n ⟩
                                       m ∎))

correct' : (m n : ℕ) {n≠0 : n ≢ 0} → remainder m n {n≠0} < n × (quotient m n {n≠0}) * n + (remainder m n {n≠0}) ≡ m
correct' m n {n≠0} = correct-wf m n {wf-nat m} {n≠0}

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

euclid-div-wf : (m n : ℕ) {rs : Acc _<_ m} {n≠0 : n ≢ 0} → Σ (ℕ × ℕ) (λ (q , r) → (r < n) × (q * n + r ≡ m))
euclid-div-wf m zero {rs} {n≠0} = ⊥-elim (n≠0 refl)
euclid-div-wf zero (suc n) {rs} {n≠0} = (0 , 0) , (z<s , refl)
euclid-div-wf m@(suc m') n@(suc n') {acc rs} {n≠0}
  with trichotomy m n
... | tri-< m<n = (0 , m) , (m<n , refl)
... | tri-= m=n = (1 , 0) , (z<s , ( begin
                                       1 * n + 0  ≡⟨ cong (_+ 0) (*-identityˡ n) ⟩
                                       n + 0      ≡⟨ +-identityʳ n ⟩
                                       n          ≡⟨ sym m=n ⟩
                                       m ∎))
... | tri-> m>n
    with euclid-div-wf (m ∸ n) n {rs (minus-dec m' n')} {n≠0}
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


-- Comments on coding well-founded recursions: roughly a pure syntactic transform.
