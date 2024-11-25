-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1

open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Nat.Properties using (+-suc)

open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

module Div2 where

-- Extrinsic approach

div2 : ℕ → ℕ
div2 zero = zero
div2 (suc zero) = zero
div2 (suc (suc n)) = suc (div2 n)

+-netural-r : {n : ℕ} → n + 0 ≡ n
+-netural-r {zero} = refl
+-netural-r {suc n} = let IH = +-netural-r {n} in cong suc IH

div2-correct : (n : ℕ) → (2 * div2 n ≡ n ∨ suc (2 * div2 n) ≡ n)
div2-correct zero = left refl
div2-correct (suc zero) = right refl
div2-correct (2+ n) with div2-correct n
... | left  rem0 = let step1 = cong suc (+-suc (div2 n) (div2 n + 0)) ;
                         IH' = cong (2+) rem0
                    in left (trans step1 IH')
... | right rem1 = let step1 = cong (2+) (+-suc (div2 n) (div2 n + 0)) ;
                         IH' = cong (2+) rem1
                    in right (trans step1 IH')

-- Intrinsic approach
div2' : (n : ℕ) → Σ ℕ (λ q → (2 * q ≡ n) ∨ (suc (2 * q) ≡ n))
div2' zero = zero , left refl
div2' (suc zero) = zero , right refl
div2' (2+ n) with div2' n
... | q , left  2q=n   = suc q , left  (let step = +-suc q (q + 0) ; 2q+1=n+1 = cong suc 2q=n
                                         in cong suc (trans step 2q+1=n+1))
... | q , right 2q+1=n = suc q , right (let step = +-suc q (q + 0) in cong (2+) (trans step 2q+1=n))
