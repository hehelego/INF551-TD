-- Tested on
-- agda 2.6.3
-- agda-stdlib 2.1


open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

length : {A : Set} → List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)


concat : {A : Set} → List A → List A → List A
concat [] ys = ys
concat (x ∷ xs) ys = x ∷ (concat xs ys)

concat-length : {A : Set} (xs ys : List A) → length (concat xs ys) ≡ length xs + length ys
concat-length [] ys = refl
concat-length (x ∷ xs) ys = let IH = concat-length xs ys in cong suc IH

concat-assoc : {A : Set} (xs ys zs : List A) → concat (concat xs ys) zs ≡ concat xs (concat ys zs)
concat-assoc [] ys zs = refl
concat-assoc (x ∷ xs) ys zs = let IH = concat-assoc xs ys zs in cong (x ∷_) IH

snoc : {A : Set} → A → List A → List A
snoc x [] = x ∷ []
snoc x (y ∷ ys) = y ∷ snoc x ys


rev : {A : Set} → List A → List A
rev [] = []
rev (x ∷ xs) = snoc x (rev xs)

rev-length : {A : Set} → (xs : List A) → length (rev xs) ≡ length xs
rev-length [] = refl
rev-length (x ∷ xs) = let step1 = lemma x (rev xs) ;
                            IH  = rev-length xs ;
                            IH' = cong suc IH 
                       in trans step1 IH'
  where
    lemma : {A : Set} → (x : A) → (xs : List A) → length (snoc x xs) ≡ suc (length xs)
    lemma x [] = refl
    lemma x (y ∷ xs) = let IH = lemma x xs in cong suc IH

rev-rev : {A : Set} → (xs : List A) → rev (rev xs) ≡ xs
rev-rev [] = refl
rev-rev (x ∷ xs) = let step1 = lemma x (rev xs) ;
                         IH  = rev-rev xs ;
                         IH' = cong (x ∷_) IH
                    in trans step1 IH'
  where
    lemma : {A : Set} → (y : A) → (xs : List A) → rev (snoc y xs) ≡ y ∷ rev xs
    lemma y [] = refl
    lemma y (x ∷ xs) = let IH = lemma y xs in cong (snoc x) IH

filter : {A : Set} → (p : A → Bool) → (l : List A) → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true = x ∷ filter p xs
... | false = filter p xs


filter-false : {A : Set} → (xs : List A) → filter (λ _ → false) xs ≡ []
filter-false [] = refl
filter-false (x ∷ xs) = filter-false xs

filter-true : {A : Set} → (xs : List A) → filter (λ _ → true) xs ≡ xs
filter-true [] = refl
filter-true (x ∷ xs) = let IH = filter-true xs in cong (x ∷_) IH
